import random
import unittest
from cryptanalysis.utils import calculate_linear_bias, calculate_difference_table

class TestHeys(unittest.TestCase):
    """
    testcases for sample implementation as per heys' tutorial
    """
    def setUp(self):
        self.sbox = [0xE, 4, 0xD, 1, 2, 0xF, 0xB, 8, 3, 0xA, 6, 0xC, 5, 9, 0, 7]
        self.pbox = [0,4,8,12,1,5,9,13,2,6,10,14,3,7,11,15]

    def test_linear_approx_table(self):

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
        linear_approx_table = calculate_linear_bias(self.sbox, False)
        for (i,j),v in linear_approx_table.items():
            self.assertEqual(v, output_table[i][j])

    def test_difference_distribution_table(self):

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
        difference_distribution_table = calculate_difference_table(self.sbox)
        for (i,j),v in difference_distribution_table.items():
            self.assertEqual(v, output_table[i][j])

    def test_random_sbox(self):
        for sbox_size in range(2,9):
            sbox = list(range(2**sbox_size))
            random.shuffle(sbox)
            linear_approx_table = calculate_linear_bias(sbox, False)
            difference_distribution_table = calculate_difference_table(sbox)
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
