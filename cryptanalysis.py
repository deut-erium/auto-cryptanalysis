from collections import Counter, defaultdict
from tqdm import tqdm
from math import log2
import random
import statistics
from itertools import product, islice
from fractions import Fraction
from z3 import *
from spn import SPN, gen_pbox
from abc import ABC, abstractmethod


def all_smt(s, initial_terms):
    def block_term(s, m, t):
        s.add(t != m.eval(t))

    def fix_term(s, m, t):
        s.add(t == m.eval(t))

    def all_smt_rec(terms):
        if sat == s.check():
            m = s.model()
            yield m
            for i in range(len(terms)):
                s.push()
                block_term(s, m, terms[i])
                for j in range(i):
                    fix_term(s, m, terms[j])
                yield from all_smt_rec(terms[i:])
                s.pop()
    yield from all_smt_rec(list(initial_terms))


class CharacteristicSolver:
    def __init__(self, sbox, pbox, num_rounds, mode='linear'):
        self.sbox = sbox
        self.pbox = pbox
        self.num_rounds = num_rounds
        self.block_size = len(pbox)
        self.box_size = int(log2(len(sbox)))
        self.num_blocks = len(pbox) // self.box_size
        self.mode = mode
        if mode == 'linear':
            self.bias = Cryptanalysis.calculate_linear_bias(sbox)
        elif mode == 'differential':
            self.bias = Cryptanalysis.calculate_difference_table(sbox)
        self.solutions = defaultdict(list)

    def initialize_sbox_structure(self):
        n = self.box_size
        self.solver = Optimize()
        self.inps = [[BitVec('r{}_i{}'.format(r, i), n)
                      for i in range(self.num_blocks)] for r in range(self.num_rounds + 1)]
        self.oups = [[BitVec('r{}_o{}'.format(r, i), n) for i in range(self.num_blocks)]
                     for r in range(self.num_rounds)]
        # permutation of output of sboxes are inputs of next round
        for i in range(self.num_rounds):
            if self.num_blocks == 1:
                self.solver.add(self.bitvec_permutation(
                    self.oups[i][0], self.inps[i + 1][0]))
            else:
                self.solver.add(self.bitvec_permutation(
                    Concat(self.oups[i]), Concat(self.inps[i + 1])))
        # all first layer inputs should not be 0
        self.solver.add(
            Not(And(*[self.inps[0][i] == 0 for i in range(self.num_blocks)])))
        for r in range(self.num_rounds):
            for i in range(self.num_blocks):
                # if sbox has input, it should have output
                self.solver.add(
                    Implies(
                        self.inps[r][i] != 0,
                        self.oups[r][i] != 0))
                # if sbox has no input it should not have any output
                self.solver.add(
                    Implies(
                        self.inps[r][i] == 0,
                        self.oups[r][i] == 0))

        # just a concatanated view of the input and output layers
        if self.num_blocks == 1:
            self.bv_inp_masks = [self.inps[i][0]
                                 for i in range(self.num_rounds + 1)]
            self.bv_oup_masks = [self.oups[i][0]
                                 for i in range(self.num_rounds)]
        else:
            self.bv_inp_masks = [Concat(self.inps[i])
                                 for i in range(self.num_rounds + 1)]
            self.bv_oup_masks = [Concat(self.oups[i])
                                 for i in range(self.num_rounds)]

    def bitvec_permutation(self, inp, oup):
        pn = len(self.pbox)
        constraints = []
        for i, v in enumerate(self.pbox):
            constraints.append(
                Extract(pn - 1 - i, pn - 1 - i, inp) ==
                Extract(pn - 1 - v, pn - 1 - v, oup)
            )
        return constraints

    def initialize_objectives(self):
        self.objectives = {
            # the actual objective, which is just product of bias [0,1/2]
            'original_linear': lambda rounds: 2**(self.num_blocks * rounds - 1) * Product([self.sboxf(
                self.inps[i // self.num_blocks][i % self.num_blocks],
                self.oups[i // self.num_blocks][i % self.num_blocks])
                for i in range(self.num_blocks * rounds)
            ]),
            # reducing optimization problem of product to sums
            'reduced': lambda rounds: sum([
                self.sboxf(
                    self.inps[i // self.num_blocks][i % self.num_blocks],
                    self.oups[i // self.num_blocks][i % self.num_blocks])
                for i in range(self.num_blocks * rounds)
            ]),
            # objective when the input biases are [0,2**n] just the final
            # division
            'differential': lambda rounds: Product([
                self.sboxf(
                    self.inps[i // self.num_blocks][i % self.num_blocks],
                    self.oups[i // self.num_blocks][i % self.num_blocks])
                for i in range(self.num_blocks * rounds)
            ]) / ((2**self.box_size)**(self.num_blocks * rounds)),
            'linear': lambda rounds: 2**(self.num_blocks * rounds - 1) * Product([
                self.sboxf(
                    self.inps[i // self.num_blocks][i % self.num_blocks],
                    self.oups[i // self.num_blocks][i % self.num_blocks])
                for i in range(self.num_blocks * rounds)
            ]) / ((2**self.box_size)**(self.num_blocks * rounds))
        }

    def add_bias_constraints(self, prune_level):
        for i in range(2**self.box_size):
            for j in range(2**self.box_size):
                # just some pruning of very small biases
                if self.bias[(i, j)] >= 2**(prune_level):
                    self.solver.add(self.sboxf(i, j) == self.bias[(i, j)])
                else:
                    self.solver.add(self.sboxf(i, j) == 0)

        for r in range(self.num_rounds):
            for i in range(self.num_blocks):
                # skip taking input/outputs with no bias
                self.solver.add(
                    Implies(
                        And(self.inps[r][i] != 0, self.oups[r][i] != 0),
                        self.sboxf(self.inps[r][i], self.oups[r][i]) != 0
                    )
                )

    def init_characteristic_solver(self, prune_level=-1):
        self.initialize_sbox_structure()
        self.sboxf = Function(
            'sbox', BitVecSort(
                self.box_size), BitVecSort(
                self.box_size), RealSort())
        self.initialize_objectives()
        assert self.solver.check()

        if prune_level < 0:
            print("searching best pruning level")
            low, high = 0, len(self.sbox) // 4
            while low <= high:
                mid = (low + high) // 2
                print("trying pruning", mid)
                self.solver.push()
                self.solver.set(timeout=10000)
                self.add_bias_constraints(mid)
                if self.solver.check() == sat:
                    print("success")
                    low = mid + 1
                else:
                    print("failure")
                    high = mid - 1
                self.solver.pop()
            self.solver.set(timeout=0)
            print("best pruning", high)
            self.prune_level = high
            self.add_bias_constraints(high)
        else:
            self.add_bias_constraints(prune_level)
            if self.solver.check() == sat:
                self.prune_level = prune_level
            else:
                print("Provided pruning level unsat, searching optimal pruning")
                self.init_characteristic_solver(-1)  # search best pruning

    def solve_for_blocks(self, include_blocks=[], exclude_blocks=[],
            num_rounds=0,
            num_sols=1,
            display_paths=True):
        if num_rounds == 0:
            num_rounds = self.num_rounds
        else:
            # cap to initialized struct
            num_rounds = min(self.num_rounds, num_rounds)
        while len(self.solver.objectives()):
            self.solver.pop()  # remove any previous include/exclude block constraints
        self.solver.push()  # set this as the checkpoint
        # specify which blocks to definitely include in the characteristic
        for i in include_blocks:
            self.solver.add(self.inps[num_rounds - 1][i] != 0)
        # specify which blocks to definitely exclude in the characteristic
        for i in exclude_blocks:
            self.solver.add(self.inps[num_rounds - 1][i] == 0)
        print(include_blocks, exclude_blocks)
        # if a block is neither in include_blocks or exclude_blocks
        # the solver finds the best path which may or may not set it to active
        self.solver.maximize(self.objectives['reduced'](num_rounds))
        solutions = self.get_masks(num_rounds, num_sols, display_paths)
        self.solutions[(tuple(sorted(include_blocks)),
                        tuple(sorted(exclude_blocks)))].extend(solutions)
        return [(inp_masks[0], inp_masks[-1], calc_bias)
                for inp_masks, _, calc_bias, _ in solutions]

    def search_best_masks(self, tolerance=1, choose_best=10, display_paths=True):
        prune_level = self.init_characteristic_solver()
        nr = self.num_rounds
        discovered = [False for _ in range(self.num_blocks)]

        def istolerable(x):
            return sum((not i) and j
                       for i, j in zip(discovered, x[3])) in range(1, tolerance + 1)
        masks = []
        while self.solver.check() == sat:
            curr_masks = self.get_masks(self.num_rounds, choose_best, display_paths=False)
            for i in curr_masks:
                self.solutions[i[2]].append(i)
            curr_masks = list(filter(istolerable, curr_masks))
            if len(curr_masks):
                inp_masks, oup_masks, total_bias, active = max(
                    curr_masks, key=lambda x: (x[2], -sum(x[3])))
                if display_paths:
                    self.print_bitrelations(inp_masks, oup_masks)
                    print("total bias:", total_bias)
                    print()
                masks.append((inp_masks[0], inp_masks[nr - 1], total_bias))
                for i, v in enumerate(discovered):
                    if (not v) and active[i]:
                        discovered[i] = True
                print("discovered", "".join(map(lambda x: str(int(x)), discovered)))
                # dont discover biases where all the active blocks come from discovered blocks
                # i.e. if all the active blocks come from discovered blocks,
                # it means, all the undiscovered blocks are inactive
                # i.e it should not be the case where all the undiscovered blocks are
                # inactive i.e 0
                self.solver.add(Not(And(
                        [self.inps[nr - 1][i] == 0 for i, v in enumerate(discovered) if not v]
                        )))
        return masks

    def search_exclusive_masks(self, prune_level=-1, repeat=1):
        self.init_characteristic_solver(prune_level)
        masks = []
        for i in range(self.num_blocks):
            include_blocks = {i}
            exclude_blocks = set(range(self.num_blocks)) - include_blocks
            masks.extend(self.solve_for_blocks(include_blocks, exclude_blocks, num_sols=repeat))
        return masks

    def get_masks(self, num_rounds, n=1, display_paths=True):
        masks = []
        for m in islice(all_smt(self.solver, [self.bv_inp_masks[num_rounds - 1]]), n):
            inp_masks = [m.eval(i).as_long()
                         for i in self.bv_inp_masks[:num_rounds]]
            oup_masks = [m.eval(i).as_long()
                         for i in self.bv_oup_masks[:num_rounds]]
            total_bias = m.eval(
                self.objectives[self.mode](num_rounds)).as_fraction()
            active = [m.eval(i).as_long() != 0 for i in self.inps[num_rounds - 1]]
            if display_paths:
                self.print_bitrelations(inp_masks, oup_masks)
                print("total bias:", total_bias)
                print()
            masks.append((inp_masks, oup_masks, total_bias, active))
        return masks

    def print_bitrelations(self, inp_masks, out_masks):
        """
        Print the input and output masks of a block cipher in a formatted manner.

        :param inp_masks: List of integers, input masks for each round.
        :param out_masks: List of integers, output masks for each round.
        """
        s = self.box_size
        n = self.num_blocks * s

        def bin_sep(val):
            v = bin(val)[2:].zfill(n)
            return "|".join(v[i:i + s] for i in range(0, n, s))

        rounds = len(out_masks)
        for i in range(rounds):
            imask, omask = inp_masks[i], out_masks[i]
            print(bin_sep(imask))
            print(' '.join(['-' * s] * (n // s)))
            print(bin_sep(omask))
            print()
        print(bin_sep(inp_masks[-1]))


class Cryptanalysis(SPN, ABC):
    def __init__(self, sbox, pbox, num_rounds, mode='differential'):
        super().__init__(sbox, pbox, 0, num_rounds)
        self.mode = mode
        self.characteristic_searcher = CharacteristicSolver(
            self.SBOX, self.PBOX, num_rounds - 1, mode)
        self.encryptions = {}  # store of the encryptions utilized by the cryptanalysis

    def dec_partial_last_noperm(self, ct, round_keys):
        # partial decryption
        # round keys in reverse order
        ct = ct ^ round_keys[0]
        ct = self.inv_sbox(ct)
        for round_key in round_keys[1:self.rounds]:
            ct ^= round_key
            ct = self.inv_perm(ct)
            ct = self.inv_sbox(ct)
        if len(round_keys) == self.rounds + 1:
            ct ^= round_keys[-1]
        return ct

    def dec_partial_last_withperm(self, ct, round_keys):
        for round_key in round_keys[:self.rounds]:
            ct ^= round_key
            ct = self.inv_perm(ct)
            ct = self.inv_sbox(ct)
        if len(round_keys) == self.rounds + 1:
            ct ^= round_keys[-1]
        return ct

    @staticmethod
    def parity(x):
        """
        Calculate the parity of an integer x.

        :param x: Integer, input value for which parity is calculated.
        :return: Integer, 0 if the number of set bits in x is even, 1 otherwise.
        """
        res = 0
        while x:
            res ^= 1
            x = x & (x - 1)
        return res

    @staticmethod
    def calculate_linear_bias(sbox, no_sign=True, fraction=False):
        """
        Calculate the linear bias of an S-box.

        :param sbox: List of integers, representing the S-box.
        :param no_sign: Optional, boolean, if True, the absolute value of the bias is returned (default: True).
        :param fraction: Optional, boolean, if True, the bias is returned as a fraction (default: False).
        :return: Counter dictionary, containing the linear biases for each input and output mask pair.
        """
        n = len(sbox)
        bias = Counter({(i, j): -(n // 2) for i in range(n) for j in range(n)})
        for imask in tqdm(range(n), desc='calculating sbox bias'):
            for omask in range(n):
                for i in range(n):
                    bias[(imask, omask)] += Cryptanalysis.parity((sbox[i] & omask) ^ (i & imask)) ^ 1
        if no_sign:
            for i in bias:
                bias[i] = abs(bias[i])
        if fraction:
            for i in bias:
                bias[i] /= n
        return bias

    @staticmethod
    def calculate_difference_table(sbox):
        """
        Calculate the difference table for an S-box.

        :param sbox: List of integers, representing the S-box.
        :return: Counter dictionary, containing the count of output
                differences for each input difference.
        """
        n = len(sbox)
        bias = Counter()
        for inp_diff in tqdm(range(n), desc='calculating sbox differences'):
            for inp in range(n):
                out_diff = sbox[inp] ^ sbox[inp ^ inp_diff]
                bias[(inp_diff, out_diff)] += 1
        return bias

    def update_encryptions(self, multiple=10000):
        to_encrypt = [i for i, v in self.encryptions.items() if v is None]
        for i in range(0, len(to_encrypt) + multiple, multiple):
            current_batch = to_encrypt[i:i + multiple]
            if current_batch == []:
                break
            for j, e in zip(current_batch, self.batch_encrypt(current_batch)):
                self.encryptions[j] = e

    def batch_encrypt(self, pt_list):
        """
        takes a list of integers, returns a list of integers
        """
        return [self.encrypt(i) for i in pt_list]

    @abstractmethod
    def find_keybits(self, in_mask, out_mask, encryption_pairs, known_keyblocks=[]):
        pass

    @abstractmethod
    def generate_encryption_pairs(self, outmasks):
        pass

    @abstractmethod
    def find_last_roundkey(self, outmasks, cutoff):
        pass

class DifferentialCryptanalysis(Cryptanalysis):
    def __init__(self, sbox, pbox, num_rounds):
        super().__init__(sbox, pbox, num_rounds, 'differential')

    def find_keybits(self, out_mask, ct_pairs, known_keyblocks=[]):
        out_blocks = self.int_to_list(out_mask)
        active_blocks = [i for i, v in enumerate(out_blocks) if v and i not in known_keyblocks]
        key_diffcounts = Counter()
        pairs = defaultdict(list)
        for klst in product(range(len(self.SBOX)), repeat=len(active_blocks)):
            key = [0] * self.NUM_SBOX
            for i, v in zip(active_blocks, klst):
                key[i] = v
            key = self.list_to_int(key)
            for ct1, ct2 in ct_pairs:
                diff = self.dec_partial_last_noperm(ct1, [key]) ^ self.dec_partial_last_noperm(ct2, [key])
                diff = self.int_to_list(diff)
                key_diffcounts[key] += all(out_blocks[i] == diff[i] for i in active_blocks)
                # key_diffcounts[key] += all(i==j for i,j in zip(out_blocks,diff))
        topn = key_diffcounts.most_common(self.BOX_SIZE)
        for i, v in topn:
            print(self.int_to_list(i), v)
        return topn[0]

    def find_last_roundkey(self, outmasks, cutoff=10000, multiple=1000):
        final_key = [None] * self.NUM_SBOX
        all_pt_ct_pairs = self.generate_encryption_pairs(outmasks, cutoff, multiple=multiple)
        for pt_ct_pairs, (inp_mask, out_mask, bias) in zip(all_pt_ct_pairs, outmasks):
            ct_pairs = [i[1] for i in pt_ct_pairs]
            # print("out mask",self.int_to_list(out_mask))
            k = self.find_keybits(out_mask, ct_pairs, [
                    i for i, v in enumerate(final_key) if v is not None])
            kr = self.int_to_list(k[0])
            print(kr)
            for i, v in enumerate(self.int_to_list(out_mask)):
                if v and final_key[i] is None:
                    final_key[i] = kr[i]
            print(final_key)
            print()
        return final_key


    def generate_encryption_pairs(self, outmasks, cutoff=10000, multiple=1000):
        """
        get pt-ct pairs for a set of differentials such that number of
        encryptions is minimised
        """
        all_pt_pairs = []
        for inp_mask, out_mask, bias in outmasks:
            pt_pairs = []
            new_encs = {}  # new encryptions + seen encryptions
            threshold = min(100 * int(1 / bias), cutoff)
            # first pass, look for already existing pairs
            for i in self.encryptions:
                if len(pt_pairs) >= threshold:
                    break
                if i in new_encs:
                    # already added the pair i.e i^inp_mask
                    continue
                if i ^ inp_mask in self.encryptions:
                    new_encs[i] = self.encryptions[i]
                    new_encs[i ^ inp_mask] = self.encryptions[i ^ inp_mask]
                    pt_pairs.append((i, i ^ inp_mask))
            for i in set(self.encryptions) - set(new_encs):
                if len(pt_pairs) >= threshold:
                    break
                # only add if we have exhausted our already encrypted pairs
                new_encs[i] = self.encryptions[i]
                # new_encs[i^inp_mask] = self.encrypt(i^inp_mask)
                new_encs[i ^ inp_mask] = None  # marked to be encrypted
                pt_pairs.append((i, i ^ inp_mask))
            self.encryptions |= new_encs
            while len(pt_pairs) < threshold:
                r = random.randint(0, 2**(self.NUM_SBOX * self.BOX_SIZE) - 1)
                if r in self.encryptions or r ^ inp_mask in self.encryptions:
                    continue
                self.encryptions[r] = None
                self.encryptions[r ^ inp_mask] = None
                pt_pairs.append((r, r ^ inp_mask))
            all_pt_pairs.append(pt_pairs)

        self.update_encryptions(multiple=multiple)

        all_pt_ct_pairs = []
        for pt_pairs in all_pt_pairs:
            pt_ct_pairs = []
            for (p1, p2) in pt_pairs:
                pt_ct_pairs.append(
                    ((p1, p2), (self.encryptions[p1], self.encryptions[p2])))
            all_pt_ct_pairs.append(pt_ct_pairs)
        return all_pt_ct_pairs


class LinearCryptanalysis(Cryptanalysis):
    def __init__(self, sbox, pbox, num_rounds):
        super().__init__(sbox, pbox, num_rounds, 'linear')


    def find_keybits_multimasks(self, in_out_masks, ptct_pairs, known_keyblocks=[]):
        key_diffcounts = [Counter() for i in range(self.NUM_SBOX)]
        for in_mask, out_mask, _ in tqdm(in_out_masks):
            out_blocks = self.int_to_list(out_mask)
            active_blocks = [i for i, v in enumerate(
                out_blocks) if v and i not in known_keyblocks]
            key_diffcount_curr = Counter()
            for klst in product(range(len(self.SBOX)), repeat=len(active_blocks)):
                key = [0] * self.NUM_SBOX
                for i, v in zip(active_blocks, klst):
                    key[i] = v
                key = self.list_to_int(key)
                for pt, ct in ptct_pairs:
                    ct_last = self.dec_partial_last_noperm(ct, [key])
                    key_diffcount_curr[key] += self.parity((pt & in_mask) ^ (ct_last & out_mask))
            for i in key_diffcount_curr:
                count = abs(key_diffcount_curr[i] - len(ptct_pairs) // 2)
                key_list = self.int_to_list(i)
                for j in active_blocks:
                    key_diffcounts[j][key_list[j]] += count
            topn = key_diffcounts[j].most_common(self.BOX_SIZE)
            for i, v in topn:
                print(i, v)
        return key_diffcounts


    def find_keybits(self, in_mask, out_mask, ptct_pairs, known_keyblocks=[]):
        out_blocks = self.int_to_list(out_mask)
        active_blocks = [i for i, v in enumerate(
            out_blocks) if v and i not in known_keyblocks]
        key_diffcounts = Counter()
        for klst in product(range(len(self.SBOX)), repeat=len(active_blocks)):
            key = [0] * self.NUM_SBOX
            for i, v in zip(active_blocks, klst):
                key[i] = v
            key = self.list_to_int(key)
            for pt, ct in ptct_pairs:
                ct_last = self.dec_partial_last_noperm(ct, [key])
                key_diffcounts[key] += self.parity((pt & in_mask) ^ (ct_last & out_mask))
        for i in key_diffcounts:
            key_diffcounts[i] = abs(key_diffcounts[i] - len(ptct_pairs) // 2)
        topn = key_diffcounts.most_common(self.BOX_SIZE)
        for i, v in topn:
            print(self.int_to_list(i), v)
        return topn[0]

    def find_last_roundkey(self, outmasks, cutoff=50000, multiple=1000):
        final_key = [None] * self.NUM_SBOX
        all_pt_ct_pairs = self.generate_encryption_pairs(outmasks, cutoff, multiple=multiple)
        for ptct_pairs, (inp_mask, out_mask, bias) in zip(all_pt_ct_pairs, outmasks):
            k = self.find_keybits(inp_mask, out_mask, ptct_pairs, [
                    i for i, v in enumerate(final_key) if v is not None])
            kr = self.int_to_list(k[0])
            print(kr)
            for i, v in enumerate(self.int_to_list(out_mask)):
                if v and final_key[i] is None:
                    final_key[i] = kr[i]
            print(final_key)
            print()
        return final_key

    def generate_encryption_pairs(self, outmasks, cutoff=10000, multiple=1000):
        max_threshold = max(100 * int(1 / (bias * bias)) for _, _, bias in outmasks)
        threshold = min(cutoff, max_threshold)
        all_pt = list(self.encryptions)[:threshold]
        while len(all_pt) < threshold:
            r = random.randint(0, 2**(self.NUM_SBOX * self.BOX_SIZE) - 1)
            if r in self.encryptions:
                continue
            self.encryptions[r] = None
            all_pt.append(r)
        self.update_encryptions(multiple=multiple)
        all_ptct = [(i, self.encryptions[i]) for i in all_pt]
        return [all_ptct]*len(outmasks)

