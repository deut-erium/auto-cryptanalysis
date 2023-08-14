"""
Module for performing differential cryptanalysis on Substitution Permutation Network based ciphers.

Classes:
- DifferentialCryptanalysis: Class for performing differential cryptanalysis.

Usage:
Import the `differential_cryptanalysis` module to access the `DifferentialCryptanalysis` class.
"""
from itertools import product
from collections import Counter
import random
from .cryptanalysis import Cryptanalysis

__all__ = ["DifferentialCryptanalysis"]


class DifferentialCryptanalysis(Cryptanalysis):
    """
    Class for performing differential cryptanalysis.

    Methods:
    - __init__: Initialize the differential cryptanalysis algorithm.
    - find_keybits: Find the key bits using differential cryptanalysis.
    - find_last_roundkey: Find the last round key using differential cryptanalysis.
    - generate_encryption_pairs: Generate encryption pairs for differential cryptanalysis.
    """

    def __init__(self, sbox, pbox, num_rounds):
        """
        Initialize the DifferentialCryptanalysis algorithm.

        Parameters:
        - sbox: The substitution box used in the SPN
        - pbox: The permutation box used in the SPN
        - num_rounds: The number of rounds in the SPN

        Notes:
        - This method is called when creating an instance of the DifferentialCryptanalysis class.
        """
        super().__init__(sbox, pbox, num_rounds, 'differential')

    def find_keybits(self, out_mask, ct_pairs, known_keyblocks=()):
        """Finds the key bits based on the output mask and ciphertext pairs.

        This method overrides the abstract `find_keybits` method in the `Cryptanalysis` class.
        It takes an output mask, a list of ciphertext pairs, and an optional list of known key blocks as input.
        It implements the logic to find the key bits based on the provided parameters.

        Args:
            out_mask (int): The output mask for the difference in encrypted pairs.
            ct_pairs (list): A list of ciphertext pairs used for analysis.
            known_keyblocks (list, optional): A list of known key blocks. Defaults to an empty list.

        Returns:
            int: A value representing the most likely key bits
        """
        out_blocks = self.int_to_list(out_mask)
        active_blocks = [i for i, v in enumerate(out_blocks) if v and i not in known_keyblocks]
        key_diffcounts = Counter()
        for klst in product(range(len(self.sbox)), repeat=len(active_blocks)):
            key = [0] * self.num_sbox
            for i, v in zip(active_blocks, klst):
                key[i] = v
            key = self.list_to_int(key)
            for ct1, ct2 in ct_pairs:
                diff = self.dec_partial_last_noperm(
                    ct1, [key]) ^ self.dec_partial_last_noperm(
                    ct2, [key])
                diff = self.int_to_list(diff)
                key_diffcounts[key] += all(out_blocks[i] == diff[i] for i in active_blocks)
                # key_diffcounts[key] += all(i==j for i,j in zip(out_blocks,diff))
        topn = key_diffcounts.most_common(self.box_size)
        for i, v in topn:
            print(self.int_to_list(i), v)
        return topn[0]

    def find_last_roundkey(self, outmasks, cutoff=10000, multiple=1000):
        """Finds the last round key based on output masks.

        This method overrides the abstract `find_last_roundkey` method in the `Cryptanalysis` class.
        It takes a list of output masks, a cutoff value, and a multiple value as input.
        It implements the logic to find the last round key based on the output masks and the specified parameters.

        Args:
            outmasks (list): A list of tuples of (input, output masks, bias) for which
                                the last round key needs to be found.
            cutoff (int, optional): The cutoff value used for the maximum number of encryptions
                                    called from oracle in determining the last round key. Defaults to 10000.
            multiple (int, optional): The multiple indicating the size of the batch of values to be
                                encrypted at once used for generating encryption pairs. Defaults to 1000.

        Returns:
            list: The last round key determined based on the output masks.
        """
        final_key = [None] * self.num_sbox
        all_pt_ct_pairs = self.generate_encryption_pairs(outmasks, cutoff, multiple=multiple)
        for pt_ct_pairs, (_, out_mask, _) in zip(all_pt_ct_pairs, outmasks):
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
        """Generates encryption pairs for a set of output masks.

        This method overrides the abstract `generate_encryption_pairs` method in the `Cryptanalysis` class.
        It takes a list of output masks, a cutoff value, and a multiple value as input.
        It generates plaintext-ciphertext pairs for each output mask based on the specified parameters.

        Args:
            outmasks (list): A list of tuples of (input_diff_mask, output_diff_mask and bias)
                            for which encryption pairs need to be generated.
            cutoff (int, optional): The cutoff value of the max number of encryptions invoked. Defaults to 10000.
            multiple (int, optional): The multiple indicating the size of the batch of values to be
                                encrypted at once used for generating encryption pairs. Defaults to 1000.

        Returns:
            list: A list of plaintext-ciphertext pairs for each output mask.
        """
        all_pt_pairs = []
        for inp_mask, _, bias in outmasks:
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
            self.encryptions.update(new_encs)
            while len(pt_pairs) < threshold:
                r = random.randint(0, 2**(self.num_sbox * self.box_size) - 1)
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
