import unittest
import random
from cryptanalysis.spn import SPN, gen_pbox


class TestSPN(unittest.TestCase):
    def test_sbox(self):
        for sbox_size in range(1, 10):
            for _ in range(10):
                sbox = list(range(2**sbox_size))
                random.shuffle(sbox)
                pbox = list(range(sbox_size * 10))
                spn = SPN(sbox, pbox, 1, 1)
                for i in range(2**sbox_size):
                    self.assertEqual(spn.inv_sub(spn.sub(i)), i)
                    self.assertEqual(spn.sub(spn.inv_sub(i)), i)

    def test_pbox(self):
        for sbox_size in range(1, 10):
            for num_sbox in range(1, 20):
                for _ in range(10):
                    sbox = list(range(2**sbox_size))
                    random.shuffle(sbox)
                    pbox = list(range(sbox_size * num_sbox))
                    random.shuffle(pbox)
                    spn = SPN(sbox, pbox, 1, 1)
                    for i in range(len(spn.pbox)):
                        self.assertEqual(
                            spn.perm(
                                1 << (
                                    spn.block_size -
                                    1 -
                                    i)) >> (
                                spn.block_size -
                                1 -
                                spn.pbox[i]),
                            1)
                        self.assertEqual(
                            spn.inv_perm(
                                1 << (
                                    spn.block_size -
                                    1 -
                                    i)) >> (
                                spn.block_size -
                                1 -
                                spn.pinv[i]),
                            1)
                    for _ in range(10):
                        i = random.randint(0, 2**(sbox_size * num_sbox) - 1)
                        self.assertEqual(spn.inv_perm(spn.perm(i)), i)
                        self.assertEqual(spn.perm(spn.inv_perm(i)), i)

    def test_enc_dec(self):
        for sbox_size in range(1, 10):
            for num_sboxes in range(1, 10):
                sbox = list(range(2**sbox_size))
                pbox = list(range(sbox_size * num_sboxes))
                random.shuffle(sbox)
                random.shuffle(pbox)
                spn = SPN(sbox, pbox, 1, 3)
                self.assertEqual(spn.block_size, sbox_size * num_sboxes)
                self.assertEqual(spn.num_sbox, num_sboxes)
                self.assertEqual(spn.box_size, sbox_size)
                rand_inputs = set()
                for _ in range(100):
                    inp = random.randint(0, 2**(sbox_size * num_sboxes) - 1)
                    rand_inputs.add(inp)
                    self.assertEqual(
                        spn._enc_last_noperm(
                            spn._dec_last_noperm(inp)), inp)
                    self.assertEqual(
                        spn._dec_last_noperm(
                            spn._enc_last_noperm(inp)), inp)
                    self.assertEqual(
                        spn._enc_last_withperm(
                            spn._dec_last_withperm(inp)), inp)
                    self.assertEqual(
                        spn._dec_last_withperm(
                            spn._enc_last_withperm(inp)), inp)
                # roughly checking if encryption and decryption are one-one
                self.assertEqual(len(rand_inputs),
                                 len({spn.encrypt(i) for i in rand_inputs}))
                self.assertEqual(len(rand_inputs),
                                 len({spn.decrypt(i) for i in rand_inputs}))

    def test_gen_pbox(self):
        for s in range(1, 10):
            for n in range(1, 20):
                pbox = gen_pbox(s, n)
                self.assertEqual(set(pbox), set(range(s * n)))

    def test_list_to_int(self):
        for sbox_size in range(1, 10):
            for num_sboxes in range(1, 10):
                sbox = list(range(2**sbox_size))
                pbox = list(range(sbox_size * num_sboxes))
                spn = SPN(sbox, pbox, 1, 3)
                for _ in range(10):
                    r_int = random.randint(0, 2**(sbox_size * num_sboxes) - 1)
                    r_list = spn.int_to_list(r_int)
                    for i in r_list:
                        self.assertLess(i, 2**sbox_size)
                    self.assertEqual(len(r_list), num_sboxes)
                    self.assertEqual(spn.list_to_int(r_list), r_int)
