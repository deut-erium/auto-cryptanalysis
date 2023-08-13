import unittest
import random
from fractions import Fraction
from cryptanalysis.spn import SPN
from cryptanalysis.utils import calculate_linear_bias, calculate_difference_table, parity
from cryptanalysis.characteristic_searcher import CharacteristicSearcher
from z3 import sat, BitVecVal, BoolVal

class TestCharacteristicSearcher(unittest.TestCase):
    def test_initialize_sbox_structure(self):
        for sbox_size in range(3,6):
            sbox = list(range(2**sbox_size))
            random.shuffle(sbox)
            for num_sbox in range(3,6):
                pbox = list(range(sbox_size*num_sbox))
                random.shuffle(pbox)
                for num_rounds in range(3,6):
                    spn = SPN(sbox, pbox, 1, num_rounds)
                    characteristic_searcher = CharacteristicSearcher(sbox, pbox, num_rounds, 'differential')

                    # check bitvector permutation
                    for _ in range(100):
                        r = random.randint(0, 2**(sbox_size*num_sbox)-1)
                        inp_bv = BitVecVal(r, sbox_size*num_sbox)
                        out_bv = BitVecVal(spn.perm(r), sbox_size*num_sbox)
                        cont = characteristic_searcher.bitvec_permutation(inp_bv, out_bv)
                        self.assertEqual(bool(BoolVal(cont)), True)

                    # check objective functions are behaving as expected
                    characteristic_searcher.init_characteristic_solver(1)
                    self.assertEqual(characteristic_searcher.solver.check(), sat)
                    model = characteristic_searcher.solver.model()
                    for key in ["linear", "differential"]:
                        obj_fun = characteristic_searcher.objectives[key]
                        obj_evals = [model.eval(obj_fun(r)).as_fraction() for r in range(1,num_rounds+1)]
                        for i,j in zip(obj_evals, obj_evals[1:]):
                            self.assertLessEqual(j, i)
                    for key in ["reduced", "original_linear"]:
                        obj_fun = characteristic_searcher.objectives[key]
                        obj_evals = [model.eval(obj_fun(r)).as_fraction() for r in range(1,num_rounds+1)]
                        for i,j in zip(obj_evals, obj_evals[1:]):
                            self.assertLessEqual(i, j)



    def test_final_bias_linear(self):
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

    def test_single_round_characteristics(self):
        """
        testing linear characteristics
        """
        for sbox_size in range(1,6):
            sbox = list(range(2**sbox_size))
            random.shuffle(sbox)
            for num_sbox in range(1,6):
                pbox = list(range(sbox_size*num_sbox))
                random.shuffle(pbox)
                spn = SPN(sbox, pbox, 1, 6)
                c_s = CharacteristicSearcher(sbox, pbox, 6, 'linear')
                c_s.init_characteristic_solver(0)

                max_bias = max([c_s.bias[(i,j)] for i in range(1,len(c_s.sbox)) for j in range(1,len(c_s.sbox))])
                masks = c_s.get_masks(1,10,False)
                optimal_bias = max([i[2] for i in masks])
                # should have been equal, but objective is not entirely linear
                # so optimality not guranteed
                self.assertLessEqual(optimal_bias, max_bias/len(c_s.sbox))

                c_s = CharacteristicSearcher(sbox, pbox, 6, 'differential')
                c_s.init_characteristic_solver(0)

                max_bias = max([c_s.bias[(i,j)] for i in range(1,len(c_s.sbox)) for j in range(1,len(c_s.sbox))])
                masks = c_s.get_masks(1,10,False)
                optimal_bias = max([i[2] for i in masks])
                # should have been equal, but objective is not entirely linear
                # so optimality not guranteed
                self.assertLessEqual(optimal_bias, max_bias/len(c_s.sbox))


    def test_solve_for_blocks(self):
        for sbox_size in range(1,6):
            sbox = list(range(2**sbox_size))
            random.shuffle(sbox)
            for num_sbox in range(1,6):
                for num_rounds in range(1,6):
                    pbox = list(range(sbox_size*num_sbox))
                    random.shuffle(pbox)
                    spn = SPN(sbox, pbox, 1, num_rounds)
                    c_s = CharacteristicSearcher(sbox, pbox, num_rounds, 'linear')
                    c_s.init_characteristic_solver(0)

                    for i in range(1,2**num_sbox):
                        include_blocks = {j for j in range(num_sbox) if (i>>j)&1 }
                        exclude_blocks = set(range(num_sbox))-include_blocks
                        for inp_masks, oup_masks, optimal_bias in c_s.solve_for_blocks(include_blocks, exclude_blocks, 1, 1, display_paths=False):
                            last_block_masks = spn.int_to_list(inp_masks)
                            for i in include_blocks:
                                self.assertNotEqual(0, last_block_masks[i])
                            for i in exclude_blocks:
                                self.assertEqual(0, last_block_masks[i])


