import unittest
import sys
sys.path.append('../auto_cryptanalysis')
import random
from fractions import Fraction
from collections import Counter
from spn import SPN
from utils import calculate_linear_bias, calculate_difference_table, parity
from cryptanalysis import Cryptanalysis
from differential_cryptanalysis import DifferentialCryptanalysis
from linear_cryptanalysis import LinearCryptanalysis
from characteristic_searcher import CharacteristicSearcher
from z3 import sat

class TestCharacteristicSearcher(unittest.TestCase):
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
                    # breakpoint()



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
        linear_bias = calculate_linear_bias(self.sbox)
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
            linear_bias = calculate_linear_bias(sbox)
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
            difference_table = calculate_difference_table(sbox)
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

