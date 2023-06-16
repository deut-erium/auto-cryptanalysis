from collections import Counter, defaultdict
from tqdm import tqdm
from math import log2
import random
from itertools import product, islice
from z3 import *
from spn import SPN, gen_pbox


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
        self.inps = [[BitVec('r{}_i{}'.format(r, i), n) for i in range(
            self.num_blocks)] for r in range(self.num_rounds + 1)]
        self.oups = [[BitVec('r{}_o{}'.format(r, i), n) for i in range(
            self.num_blocks)] for r in range(self.num_rounds)]
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

    def init_characteristic_solver(self, bias_inp='linear', prune_level=0):
        self.initialize_sbox_structure()
        self.sboxf = Function(
            'sbox', BitVecSort(
                self.box_size), BitVecSort(
                self.box_size), RealSort())
        self.initialize_objectives()
        self.add_bias_constraints(prune_level)
        assert self.solver.check() == sat, "prune_level is unsat, set a lower value"

    def solve_for_blocks(
            self,
            include_blocks=[],
            exclude_blocks=[],
            num_rounds=0,
            num_sols=1,
            display_paths=True):
        if num_rounds == 0:
            num_rounds = self.num_rounds
        else:
            # cap to initialized struct
            num_rounds = min(self.num_rounds, num_rounds)
        self.solver.pop()  # remove any previous include/exclude block constraints
        self.solver.push()  # set this as the checkpoint
        # specify which blocks to definitely include in the characteristic
        for i in include_blocks:
            self.solver.add(self.inps[num_rounds - 1][i] != 0)
        # specify which blocks to definitely exclude in the characteristic
        for i in exclude_blocks:
            self.solver.add(self.inps[num_rounds - 1][i] == 0)
        # if a block is neither in include_blocks or exclude_blocks
        # the solver finds the best path which may or may not set it to active
        self.solver.maximize(self.objectives['reduced'](num_rounds))
        solutions = self.get_masks(num_rounds, num_sols, display_paths)
        self.solutions[(tuple(sorted(include_blocks)),
                        tuple(sorted(exclude_blocks)))].extend(solutions)
        return [(inp_masks[0], inp_masks[-1], calc_bias)
                for inp_masks, _, calc_bias in solutions]

    def get_masks(self, num_rounds, n=1, display_paths=True):
        masks = []
        for m in islice(all_smt(
                self.solver, [self.bv_inp_masks[0], self.bv_inp_masks[num_rounds - 1]]), n):
            inp_masks = [m.eval(i).as_long()
                         for i in self.bv_inp_masks[:num_rounds]]
            oup_masks = [m.eval(i).as_long()
                         for i in self.bv_oup_masks[:num_rounds]]
            total_bias = m.eval(
                self.objectives[self.mode](num_rounds)).as_fraction()
            if display_paths:
                self.print_bitrelations(inp_masks, oup_masks)
                print("total bias:", total_bias)
                print()
            masks.append((inp_masks, oup_masks, total_bias))
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


class Cryptanalysis(SPN):
    def __init__(self, sbox, pbox, num_rounds):
        super(Cryptanalysis, self).__init__(sbox, pbox, 0, num_rounds)
        self.linear_bias = self.calculate_linear_bias(sbox)
        self.difference_table = self.calculate_difference_table(sbox)

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
                    bias[(imask, omask)] += Cryptanalysis.parity((sbox[i]
                                                                  & omask) ^ (i & imask)) ^ 1
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
        :return: Counter dictionary, containing the count of output differences for each input difference.
        """
        n = len(sbox)
        bias = Counter()
        for inp_diff in tqdm(range(n), desc='calculating sbox differences'):
            for inp in range(n):
                out_diff = sbox[inp] ^ sbox[inp ^ inp_diff]
                bias[(inp_diff, out_diff)] += 1
        return bias


# def find_keybits(out_mask, ct_pairs, sbox, pbox):
#     spn = SPN(sbox,pbox,0,1) #dummy to use functionalities
#     out_blocks = spn.int_to_list(out_mask)
#     active_blocks = [i for i,v in enumerate(out_blocks) if v]
#     key_diffcounts = Counter()
#     for klst in product(range(len(sbox)), repeat=len(active_blocks)):
#         key = [0]*spn.NUM_SBOX
#         for i,v in zip(active_blocks, klst):
#             key[i] = v
#         key = spn.list_to_int(key)
#         for ct1,ct2 in ct_pairs:
#             diff = dec_partial_last_noperm(spn,ct1, [key])^dec_partial_last_noperm(spn,ct2,[key])
#             diff = spn.int_to_list(diff)
#             key_diffcounts[key] += all(out_blocks[i] == diff[i] for i in active_blocks)
#     return key_diffcounts.most_common()[0]

# sbox = list(range(2**5))
# pbox = list(range(5*5))

# random.shuffle(sbox)
# random.shuffle(pbox)
# # c = Cryptanalysis(sbox, pbox, 4)
# c = CharacteristicSolver(sbox, pbox, 10)
# c.init_characteristic_solver('linear',2)
# # c.solve_for_blocks(include_blocks=(1,2),exclude_blocks=(0,3,4),num_rounds=7,num_sols=20)
# x = c.solve_for_blocks(include_blocks=(0,),exclude_blocks=(1,2,3,4),num_rounds=5,num_sols=20)

# for sbox_size in [4,5]:
#     for num_sbox in range(4,6):
#         sbox = list(range(2**sbox_size))
#         pbox = list(range(sbox_size*num_sbox))
#         random.shuffle(sbox)
#         random.shuffle(pbox)
#         for num_rounds in [4]:
#             spn = SPN(sbox, pbox, random.randint(0,2**(num_sbox*sbox_size)-1), num_rounds)
#             inp_masks, oup_masks, bias = find_optimal_characteristics(sbox, pbox, num_rounds-1, ['differential',None])
#             inp_mask, out_mask = inp_masks[0], inp_masks[-1]
#             ct_pairs = []
#             seen = set()
#             for _ in range(int(10/bias)):
#                 i = random.randint(0,2**(num_sbox*sbox_size)-1)
#                 if i in seen or i^inp_mask in seen:
#                     continue
#                 seen.add(i^inp_mask)
#                 seen.add(i)
#                 ct_pairs.append((spn.encrypt(i), spn.encrypt(i^inp_mask)))
#             res = find_keybits(inp_mask, out_mask, ct_pairs, sbox, pbox)
#             print(Fraction(res[1],len(ct_pairs)))
#             print(spn.int_to_list(res[0]))
#             print(spn.int_to_list(spn.round_keys[-1]))
