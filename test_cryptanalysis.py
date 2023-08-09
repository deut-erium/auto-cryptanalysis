import unittest
import random
from fractions import Fraction
from collections import Counter
from spn import SPN
from cryptanalysis import Cryptanalysis, DifferentialCryptanalysis, LinearCryptanalysis, CharacteristicSearcher
from z3 import sat

class TestHeys(unittest.TestCase):
    """
    testcases for sample implementation as per heys' tutorial
    """
    def setUp(self):
        self.sbox = [0xE, 4, 0xD, 1, 2, 0xF, 0xB, 8, 3, 0xA, 6, 0xC, 5, 9, 0, 7]
        self.pbox = [0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15]
        self.spn = SPN(self.sbox, self.pbox, 1, 4)

    def test_linear_approx_table(self):
        return
        output_table = [
            [+8,  0, 0,   0, 0,   0, 0,   0, 0,   0, 0,   0, 0,   0, 0,   0],
            [0,   0, -2, -2, 0,   0, -2, +6, +2, +2, 0,   0, +2, +2, 0,   0],
            [0,   0, -2, -2, 0,   0, -2, -2, 0,   0, +2, +2, 0,   0, -6, +2],
            [0,   0, 0,   0, 0,   0, 0,   0, +2, -6, -2, -2, +2, +2, -2, -2],
            [0,  +2, 0,  -2, -2, -4, -2,  0, 0,  -2, 0,  +2, +2, -4, +2,  0],
            [0,  -2, -2,  0, -2,  0, +4, +2, -2,  0, -4, +2, 0,  -2, -2,  0],
            [0,  +2, -2, +4, +2,  0, 0,  +2, 0,  -2, +2, +4, -2,  0, 0,  -2],
            [0,  -2, 0,  +2, +2, -4, +2,  0, -2,  0, +2,  0, +4, +2, 0,  +2],
            [0,   0, 0,   0, 0,   0, 0,   0, -2, +2, +2, -2, +2, -2, -2, -6],
            [0,   0, -2, -2, 0,   0, -2, -2, -4,  0, -2, +2, 0,  +4, +2, -2],
            [0,  +4, -2, +2, -4,  0, +2, -2, +2, +2, 0,   0, +2, +2, 0,   0],
            [0,  +4, 0,  -4, +4,  0, +4,  0, 0,   0, 0,   0, 0,   0, 0,   0],
            [0,  -2, +4, -2, -2,  0, +2,  0, +2,  0, +2, +4, 0,  +2, 0,  -2],
            [0,  +2, +2,  0, -2, +4, 0,  +2, -4, -2, +2,  0, +2,  0, 0,  +2],
            [0,  +2, +2,  0, -2, -4, 0,  +2, -2,  0, 0,  -2, -4, +2, -2,  0],
            [0,  -2, -4, -2, -2,  0, +2,  0, 0,  -2, +4, -2, -2,  0, +2,  0],
        ]
        linear_approx_table = Cryptanalysis.calculate_linear_bias(self.sbox, False)
        for (i,j),v in linear_approx_table.items():
            self.assertEqual(v, output_table[i][j])

    def test_difference_distribution_table(self):
        return
        output_table = [
            [16,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
            [0,0,0,2,0,0,0,2,0,2,4,0,4,2,0,0],
            [0,0,0,2,0,6,2,2,0,2,0,0,0,0,2,0],
            [0,0,2,0,2,0,0,0,0,4,2,0,2,0,0,4],
            [0,0,0,2,0,0,6,0,0,2,0,4,2,0,0,0],
            [0,4,0,0,0,2,2,0,0,0,4,0,2,0,0,2],
            [0,0,0,4,0,4,0,0,0,0,0,0,2,2,2,2],
            [0,0,2,2,2,0,2,0,0,2,2,0,0,0,0,4],
            [0,0,0,0,0,0,2,2,0,0,0,4,0,4,2,2],
            [0,2,0,0,2,0,0,4,2,0,2,2,2,0,0,0],
            [0,2,2,0,0,0,0,0,6,0,0,2,0,0,4,0],
            [0,0,8,0,0,2,0,2,0,0,0,0,0,2,0,2],
            [0,2,0,0,2,2,2,0,0,0,0,2,0,6,0,0],
            [0,4,0,0,0,0,0,4,2,0,2,0,2,0,2,0],
            [0,0,2,4,2,0,0,0,6,0,0,0,0,0,2,0],
            [0,2,0,0,6,0,0,0,0,4,0,2,0,0,2,0],
        ]
        difference_distribution_table = Cryptanalysis.calculate_difference_table(self.sbox)
        for (i,j),v in difference_distribution_table.items():
            self.assertEqual(v, output_table[i][j])


class TestCharacteristicSearcher(unittest.TestCase):
    def test_random_sbox(self):
        return
        for sbox_size in range(2,9):
            sbox = list(range(2**sbox_size))
            random.shuffle(sbox)
            linear_approx_table = Cryptanalysis.calculate_linear_bias(sbox, False)
            difference_distribution_table = Cryptanalysis.calculate_difference_table(sbox)
            row_sum = 2**(sbox_size-1)
            for i in range(len(sbox)):
                for j in range(len(sbox)):
                    self.assertEqual(linear_approx_table[(i,j)]&1,0) #always even
                    self.assertEqual(difference_distribution_table[(i,j)]&1,0) #always even
                # sum of any row or any column would be +-len(sbox)//2
                self.assertEqual(abs(sum(linear_approx_table[(i,j)] for j in range(len(sbox)))),row_sum)
                self.assertEqual(abs(sum(linear_approx_table[(j,i)] for j in range(len(sbox)))),row_sum)
                # sum of any row or column of difference distribution would be len(sbox)
                self.assertEqual(sum(difference_distribution_table[(i,j)] for j in range(len(sbox))),len(sbox))
                self.assertEqual(sum(difference_distribution_table[(j,i)] for j in range(len(sbox))),len(sbox))

    def test_initialize_sbox_structure(self):
        for sbox_size in range(1,6):
            sbox = list(range(2**sbox_size))
            random.shuffle(sbox)
            for num_sbox in range(1,6):
                pbox = list(range(sbox_size*num_sbox))
                random.shuffle(pbox)
                for num_rounds in range(1,6):
                    spn = SPN(sbox, pbox, 1, num_rounds)
                    characteristic_searcher = CharacteristicSearcher(sbox, pbox, num_rounds, 'differential')
                    characteristic_searcher.initialize_sbox_structure()
                    self.assertEqual(characteristic_searcher.solver.check(), sat)
                    model = characteristic_searcher.solver.model()
                    breakpoint()



    def test_final_bias_linear(self):
        return
        for sbox_size in range(1,6):
            sbox = list(range(2**sbox_size))
            random.shuffle(sbox)
            for num_sbox in range(1,6):
                pbox = list(range(sbox_size*num_sbox))
                random.shuffle(pbox)
                for num_rounds in range(1,6):
                    spn = SPN(sbox, pbox, 1, num_rounds)

                    characteristic_searcher = CharacteristicSearcher(sbox, pbox, num_rounds, 'linear')
                    characteristic_searcher.init_characteristic_solver(1)
                    for inp_masks, oup_masks, optimal_bias, _ in characteristic_searcher.get_masks(num_rounds,10,False):

                        inp_masks = [spn.int_to_list(i) for i in inp_masks]
                        oup_masks = [spn.int_to_list(i) for i in oup_masks]
                        probability = Fraction(1,2)
                        for inpi, oupi in zip(inp_masks, oup_masks):
                            for inpii, oupii in zip(inpi, oupi):
                                probability*=2
                                probability*=characteristic_searcher.bias[(inpii,oupii)]
                                probability/=2**(sbox_size)
                        self.assertEqual(probability, optimal_bias)
                        print("sbox size={}, number_sboxes={}, number_rounds={}, best absolute linear bias={}".format(sbox_size, num_sbox, num_rounds,optimal_bias))

    def test_final_bias_differential(self):
        return
        for sbox_size in range(1,6):
            sbox = list(range(2**sbox_size))
            random.shuffle(sbox)
            for num_sbox in range(1,6):
                pbox = list(range(sbox_size*num_sbox))
                random.shuffle(pbox)
                for num_rounds in range(1,6):
                    spn = SPN(sbox, pbox, 1, num_rounds)
                    characteristic_searcher = CharacteristicSearcher(sbox, pbox, num_rounds, 'differential')
                    characteristic_searcher.init_characteristic_solver(1)
                    for inp_masks, oup_masks, optimal_bias, _ in characteristic_searcher.get_masks(num_rounds,10,False):
                        # testing differential characteristics
                        inp_masks = [spn.int_to_list(i) for i in inp_masks]
                        oup_masks = [spn.int_to_list(i) for i in oup_masks]
                        probability = Fraction(1,1)
                        for inpi, oupi in zip(inp_masks, oup_masks):
                            for inpii, oupii in zip(inpi, oupi):
                                probability*=characteristic_searcher.bias[(inpii,oupii)]
                                probability/=2**(sbox_size)
                        self.assertEqual(probability, optimal_bias)
                        print("sbox size={}, number_sboxes={}, number_rounds={}, best difference probability={}".format(sbox_size, num_sbox, num_rounds,optimal_bias))

    def test_linear_characteristics(self):
        """
        testing linear characteristics
        """
        return
        linear_bias = Cryptanalysis.calculate_linear_bias(self.sbox)
        max_bias = max([linear_bias[(i,j)] for i in range(1,len(self.sbox)) for j in range(1,len(self.sbox))])
        _,_,optimal_bias = find_optimal_characteristics(self.sbox, self.pbox, 1,['linear',linear_bias],display_paths=False)
        self.assertEqual(optimal_bias, max_bias/len(self.sbox))
        for i in range(1,2**4):
            include_blocks = {j for j in range(4) if (1>>j)&1 }
            exclude_blocks = set(range(4))-include_blocks
            inp_masks, oup_masks, optimal_bias = find_optimal_characteristics(
                    self.sbox, self.pbox, 1, ['linear',linear_bias], include_blocks, exclude_blocks,display_paths=False)
            last_block_masks = self.spn.int_to_list(inp_masks[-1])
            for i in include_blocks:
                self.assertNotEqual(0, last_block_masks[i])

    def test_small_sbox_linear_bias(self):
        return
        max_block_size = 20
        for sbox_size in range(1,6):
            sbox = list(range(2**sbox_size))
            random.shuffle(sbox)
            linear_bias = Cryptanalysis.calculate_linear_bias(sbox)
            for num_sbox in range(1,max_block_size//sbox_size):
                pbox = list(range(sbox_size*num_sbox))
                random.shuffle(pbox)
                for num_rounds in range(1,6):
                    spn = SPN(sbox, pbox, 1, num_rounds+1)
                    inp_masks, oup_masks, optimal_bias = find_optimal_characteristics(
                    sbox, pbox, num_rounds, ['linear',linear_bias],display_paths=False)
                    inp_mask, out_mask = inp_masks[0], inp_masks[-1]
                    correct_count = 0
                    for i in range(2**(sbox_size*num_sbox)):
                        enc = spn.encrypt(i)
                        d = dec_partial_last_noperm(spn, enc, spn.round_keys[-1:])
                        correct_count += parity((d&out_mask)^(i&inp_mask))
                    observed_bias = Fraction(correct_count, 2**(sbox_size*num_sbox)) - Fraction(1,2)
                    print(sbox_size, num_sbox, num_rounds, observed_bias, optimal_bias)

    def test_small_sbox_difference_bias(self):
        return
        max_block_size = 20
        for sbox_size in range(3,6):
            sbox = list(range(2**sbox_size))
            random.shuffle(sbox)
            difference_table = Cryptanalysis.calculate_difference_table(sbox)
            for num_sbox in range(3,max_block_size//sbox_size):
                pbox = list(range(sbox_size*num_sbox))
                random.shuffle(pbox)
                for num_rounds in range(4,6):
                    spn = SPN(sbox, pbox, 1, num_rounds+1)
                    inp_masks, oup_masks, optimal_bias = find_optimal_characteristics(
                    sbox, pbox, num_rounds, ['differential',difference_table],display_paths=False)
                    inp_mask, out_mask = inp_masks[0], inp_masks[-1]
                    out_block = spn.list_to_int([(1<<sbox_size)-1 if i else 0 for i in spn.int_to_list(out_mask)])
                    correct_count = 0
                    cnt = Counter()
                    seen = set()
                    for i in range(2**(sbox_size*num_sbox)):
                        if i in seen:
                            continue
                        seen.add(i^inp_mask)
                        enc = spn.encrypt(i)
                        enc2 = spn.encrypt(i^inp_mask)
                        d1 = dec_partial_last_noperm(spn, enc, spn.round_keys[-1:])
                        d2 = dec_partial_last_noperm(spn, enc2, spn.round_keys[-1:])
                        cnt[(d1^d2)&out_block]+=1
                        correct_count += ((d1^d2)&out_block==out_mask)
                    observed_bias = Fraction(correct_count, 2**(sbox_size*num_sbox))
                    print(sbox_size, num_sbox, num_rounds, observed_bias, optimal_bias)
                    print(out_mask,out_block,cnt[out_mask],cnt.most_common(7))

