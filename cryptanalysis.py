from collections import Counter
from tqdm import tqdm
from math import log2
import random
from itertools import product
from z3 import *
from spn import SPN, gen_pbox


def print_bitrelations(inp_masks, out_masks, n, s):
    """
    Print the input and output masks of a block cipher in a formatted manner.

    :param inp_masks: List of integers, input masks for each round.
    :param out_masks: List of integers, output masks for each round.
    :param n: Integer, block size in bits.
    :param s: Integer, number of bits in the S-box.
    """
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
                bias[(imask, omask)] += parity((sbox[i] & omask) ^ (i & imask)) ^ 1
    if no_sign:
        for i in bias:
            bias[i] = abs(bias[i])
    if fraction:
        for i in bias:
            bias[i] /= n
    return bias


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

def find_optimal_characteristics(sbox, pbox, num_rounds, bias_inp=['linear', None],
                                include_blocks=[],
                                exclude_blocks=[],
                                prune_level=0,
                                display_paths=True):
    """
    Find the optimal linear or differential characteristics for a given S-box and P-box combination over a specified number of rounds.

    :param sbox: List of integers, representing the S-box.
    :param pbox: List of integers, representing the P-box.
    :param num_rounds: Integer, number of rounds for the block cipher.
    :param bias_inp: Optional, tuple, specifying the type of bias ('linear' or 'differential') and the bias dictionary (default: ['linear', None]).
    :param include_blocks: Optional, list of integers, block indices that must be included in the final characteristic (default: [0]).
    :param exclude_blocks: Optional, list of integers, block indices that must be excluded from the final characteristic (default: []).
    :param prune_level: Optional, integer, pruning level for small biases (default: 0).
    :param display_paths: Optional, bool, display the characteristic paths and bits chosen (default: True)

    :return: Tuple, containing the input masks, output masks, and total bias of the optimal characteristic.

    This function finds the optimal linear or differential characteristics for a given S-box and P-box combination over a specified number of rounds. It uses z3.Optimize to maximize the bias of the input/output masks, while also considering constraints such as include_blocks, exclude_blocks, and pruning level.

    The input masks, output masks, and total bias are returned as a tuple. If no optimal characteristic is found, the function returns None.
    """
    n = int(log2(len(sbox)))
    num_blocks = len(pbox) // n
    if bias_inp[0] == 'linear':
        if bias_inp[1] is None:
            bias = calculate_linear_bias(sbox)
        else:
            bias = bias_inp[1]
    elif bias_inp[0] == 'differential':
        if bias_inp[1] is None:
            bias = calculate_difference_table(sbox)
        else:
            bias = bias_inp[1]
    sboxf = Function('sbox', BitVecSort(n), BitVecSort(n), RealSort())

    def permutation(inp, oup, pbox):
        pn = len(pbox)
        constraints = []
        for i, v in enumerate(pbox):
            constraints.append(
                Extract(pn - 1 - i, pn - 1 - i, inp) == Extract(pn - 1 - v, pn - 1 - v, oup))
        return constraints
    constraints = []
    for i in range(2**n):
        for j in range(2**n):
            # just some pruning of very small biases
            if bias[(i, j)] >= 2**(prune_level):
                constraints.append(sboxf(i, j) == bias[(i, j)])
            else:
                constraints.append(sboxf(i, j) == 0)
    s = Optimize()
    inps = [[BitVec('r{}_i{}'.format(r, i), n) for i in range(num_blocks)]
            for r in range(num_rounds + 1)]
    oups = [[BitVec('r{}_o{}'.format(r, i), n) for i in range(num_blocks)]
            for r in range(num_rounds)]
    objectives = {
        # the actual objective, which is just product of bias [0,1/2]
        'original_linear': 2**(num_blocks * num_rounds - 1) * Product([
            sboxf(
                inps[i // num_blocks][i % num_blocks],
                oups[i // num_blocks][i % num_blocks])
            for i in range(num_blocks * num_rounds)
        ]),
        # reducing optimization problem of product to sums
        'reduced': Sum([
            sboxf(
                inps[i // num_blocks][i % num_blocks],
                oups[i // num_blocks][i % num_blocks])
            for i in range(num_blocks * num_rounds)
        ]),
        # objective when the input biases are [0,2**n] just the final
        # division
        'differential': Product([
            sboxf(
                inps[i // num_blocks][i % num_blocks],
                oups[i // num_blocks][i % num_blocks])
            for i in range(num_blocks * num_rounds)
        ]) / ((2**n)**(num_blocks * num_rounds)),
        'linear': 2**(num_blocks * num_rounds - 1) * Product([
            sboxf(
                inps[i // num_blocks][i % num_blocks],
                oups[i // num_blocks][i % num_blocks])
            for i in range(num_blocks * num_rounds)
        ]) / ((2**n)**(num_blocks * num_rounds))
    }
    s.maximize(objectives['reduced'])
    s.add(constraints)
    # the last layer is input, which we would like to be
    # reduced to as few sboxes as possible
    s.add(Not(And(*[inps[0][i] == 0 for i in range(num_blocks)])))

    # specify which blocks to definitely include in the characteristic
    for i in include_blocks:
        s.add(inps[-1][i] != 0)
    # specify which blocks to definitely exclude in the characteristic
    for i in exclude_blocks:
        s.add(inps[-1][i] == 0)
    # if a block is neither in include_blocks or exclude_blocks
    # the solver finds the best path which may or may not set it to active

    for r in range(num_rounds):
        for i in range(num_blocks):
            # if sbox has input, it should have output
            s.add(Implies(inps[r][i] != 0, oups[r][i] != 0))
            # if sbox has no input it should not have any output
            s.add(Implies(inps[r][i] == 0, oups[r][i] == 0))
            # skip taking input/outputs with no bias
            s.add(
                Implies(
                    And(inps[r][i] != 0, oups[r][i] != 0),
                    sboxf(inps[r][i], oups[r][i]) != 0
                )
            )
    # permutation of output of sboxes are inputs of next round
    for i in range(num_rounds):
        if num_blocks==1:
            s.add(permutation(oups[i][0],inps[i+1][0],pbox))
        else:
            s.add(permutation(Concat(oups[i]), Concat(inps[i + 1]), pbox))
    results = []
    if s.check() == sat:
        m = s.model()
        if num_blocks == 1:
            inp_masks = [m.eval(inps[i][0]).as_long()
                         for i in range(num_rounds + 1)]
            oup_masks = [m.eval(oups[i][0]).as_long()
                         for i in range(num_rounds)]
        else:
            inp_masks = [m.eval(Concat(inps[i])).as_long()
                         for i in range(num_rounds + 1)]
            oup_masks = [m.eval(Concat(oups[i])).as_long()
                         for i in range(num_rounds)]
        total_bias = m.eval(objectives[bias_inp[0]]).as_fraction()
        if display_paths:
            print_bitrelations(inp_masks, oup_masks, len(pbox), n)
            print("total bias:", total_bias)
        return inp_masks, oup_masks, total_bias

def dec_partial_last_noperm(spn,ct,round_keys):
    # partial decryption
    # round keys in reverse order
    ct = ct^round_keys[0]
    ct = spn.inv_sbox(ct)
    for round_key in round_keys[1:spn.rounds]:
        ct^= round_key
        ct = spn.inv_perm(ct)
        ct = spn.inv_sbox(ct)
    if len(round_keys)==spn.rounds+1:
        ct^=round_keys[-1]
    return ct


def dec_partial_last_withperm(spn,ct, round_keys):
    for round_key in round_keys[:spn.rounds]:
        ct ^= round_key
        ct = spn.inv_perm(ct)
        ct = spn.inv_sbox(ct)
    if len(round_keys)==spn.rounds+1:
        ct ^= round_keys[-1]
    return ct

def find_keybits(inp_mask, out_mask, ct_pairs, sbox, pbox):
    spn = SPN(sbox,pbox,0,1) #dummy to use functionalities
    out_blocks = spn.int_to_list(out_mask)
    active_blocks = [i for i,v in enumerate(out_blocks) if v]
    key_diffcounts = Counter()
    for klst in product(range(len(sbox)), repeat=len(active_blocks)):
        key = [0]*spn.NUM_SBOX
        for i,v in zip(active_blocks, klst):
            key[i] = v
        key = spn.list_to_int(key)
        for ct1,ct2 in ct_pairs:
            diff = dec_partial_last_noperm(spn,ct1, [key])^dec_partial_last_noperm(spn,ct2,[key])
            diff = spn.int_to_list(diff)
            key_diffcounts[key] += all(out_blocks[i] == diff[i] for i in active_blocks)
    return key_diffcounts.most_common()[0]



for sbox_size in [4,5]:
    for num_sbox in range(4,6):
        sbox = list(range(2**sbox_size))
        pbox = list(range(sbox_size*num_sbox))
        random.shuffle(sbox)
        random.shuffle(pbox)
        for num_rounds in [4]:
            spn = SPN(sbox, pbox, random.randint(0,2**(num_sbox*sbox_size)-1), num_rounds)
            inp_masks, oup_masks, bias = find_optimal_characteristics(sbox, pbox, num_rounds-1, ['differential',None])
            inp_mask, out_mask = inp_masks[0], inp_masks[-1]
            ct_pairs = []
            seen = set()
            for _ in range(int(10/bias)):
                i = random.randint(0,2**(num_sbox*sbox_size)-1)
                if i in seen or i^inp_mask in seen:
                    continue
                seen.add(i^inp_mask)
                seen.add(i)
                ct_pairs.append((spn.encrypt(i), spn.encrypt(i^inp_mask)))
            res = find_keybits(inp_mask, out_mask, ct_pairs, sbox, pbox)
            print(Fraction(res[1],len(ct_pairs)))
            print(spn.int_to_list(res[0]))
            print(spn.int_to_list(spn.round_keys[-1]))


