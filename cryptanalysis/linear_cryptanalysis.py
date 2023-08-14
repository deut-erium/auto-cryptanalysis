"""
Module for performing linear cryptanalysis on Substitution Permutation Network based ciphers.

Classes:
- LinearCryptanalysis: Class for performing linear cryptanalysis.

Usage:
Import the `linear_cryptanalysis` module to access the `LinearCryptanalysis` class.
"""
from collections import Counter
from itertools import product
import random
from tqdm import tqdm
from .cryptanalysis import Cryptanalysis
from .utils import parity

__all__ = ["LinearCryptanalysis"]


class LinearCryptanalysis(Cryptanalysis):
    """
    Class for performing linear cryptanalysis.

    Methods:
    - __init__: Initialize the linear cryptanalysis algorithm.
    - find_keybits: Find the key bits using linear cryptanalysis.
    - _find_keybits_multimasks: Expeimental method utilising mutiple linear characteristics on the same block to find key bits
    - find_last_roundkey: Find the last round key using linear cryptanalysis.
    - generate_encryption_pairs: Generate encryption pairs for linear cryptanalysis.
    """

    def __init__(self, sbox, pbox, num_rounds):
        """
        Initialize the LinearCryptanalysis algorithm.

        Parameters:
        - sbox: The substitution box used in the SPN
        - pbox: The permutation box used in the SPN
        - num_rounds: The number of rounds in the SPN

        Notes:
        - This method is called when creating an instance of the LinearCryptanalysis class.
        """
        super().__init__(sbox, pbox, num_rounds, 'linear')

    def _find_keybits_multimasks(self, in_out_masks, ptct_pairs, known_keyblocks=()):
        """Finds the key bits based on multiple input-output masks for a given block and plaintext-ciphertext pairs.

        This method takes a list of input-output masks, a list of plaintext-ciphertext pairs,
        and an optional list of known key blocks as input.
        Note that this method is experimental to try out using more than one linear characteristic ending on a block.

        Args:
            in_out_masks (list): A list of input-output masks for key search.
            ptct_pairs (list): A list of plaintext-ciphertext pairs used for analysis.
            known_keyblocks (list, optional): A list of known key blocks. Defaults to an empty list.

        Returns:
            list: A list of Counter objects containing the key bit differences for each active block.
        """
        key_diffcounts = [Counter() for i in range(self.num_sbox)]
        for in_mask, out_mask, _ in tqdm(in_out_masks):
            out_blocks = self.int_to_list(out_mask)
            active_blocks = [i for i, v in enumerate(
                out_blocks) if v and i not in known_keyblocks]
            key_diffcount_curr = Counter()
            for klst in product(range(len(self.sbox)), repeat=len(active_blocks)):
                key = [0] * self.num_sbox
                for i, v in zip(active_blocks, klst):
                    key[i] = v
                key = self.list_to_int(key)
                for pt, ct in ptct_pairs:
                    ct_last = self.dec_partial_last_noperm(ct, [key])
                    key_diffcount_curr[key] += parity((pt & in_mask) ^ (ct_last & out_mask))
            for i in key_diffcount_curr:
                count = abs(key_diffcount_curr[i] - len(ptct_pairs) // 2)
                key_list = self.int_to_list(i)
                for j in active_blocks:
                    key_diffcounts[j][key_list[j]] += count
            for j in active_blocks:
                topn = key_diffcounts[j].most_common(self.box_size)
                for i, v in topn:
                    print(i, v)
        return key_diffcounts

    def find_keybits(self, in_mask, out_mask, ptct_pairs, known_keyblocks=()):
        """Finds the key bits based on an input mask, an output mask, and plaintext-ciphertext pairs.

        This method takes an input mask, an output mask, a list of plaintext-ciphertext
        pairs, and an optional list of known key blocks as input.
        It implements the logic to find the key bits based on the provided parameters.

        Args:
            in_mask (int): The input mask for the key search.
            out_mask (int): The output mask for the key search.
            ptct_pairs (list): A list of tuples of plaintext-ciphertext pairs used for analysis.
            known_keyblocks (list, optional): A list of known key blocks. Defaults to an empty list.

        Returns:
            int: A integer representing the most probable keybits
        """

        out_blocks = self.int_to_list(out_mask)
        active_blocks = [i for i, v in enumerate(
            out_blocks) if v and i not in known_keyblocks]
        key_diffcounts = Counter()
        for klst in product(range(len(self.sbox)), repeat=len(active_blocks)):
            key = [0] * self.num_sbox
            for i, v in zip(active_blocks, klst):
                key[i] = v
            key = self.list_to_int(key)
            for pt, ct in ptct_pairs:
                ct_last = self.dec_partial_last_noperm(ct, [key])
                key_diffcounts[key] += parity((pt & in_mask) ^ (ct_last & out_mask))
        for i in key_diffcounts:
            key_diffcounts[i] = abs(key_diffcounts[i] - len(ptct_pairs) // 2)
        topn = key_diffcounts.most_common(self.box_size)
        for i, v in topn:
            print(self.int_to_list(i), v)
        return topn[0]

    def find_last_roundkey(self, outmasks, cutoff=50000, multiple=1000):
        """Finds the last round key based on output masks.

        This method overrides the abstract `find_last_roundkey` method in the `Cryptanalysis` class.
        It takes a list of output masks, a cutoff value, and a multiple value as input.
        It implements the logic to find the last round key based on the output
        masks and the specified parameters.

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
        for ptct_pairs, (inp_mask, out_mask, _) in zip(all_pt_ct_pairs, outmasks):
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
        """Generates encryption pairs for a set of output masks.

        This method takes a list of output masks, a cutoff value, and a multiple value as input.
        It generates plaintext-ciphertext pairs for each output mask based on the specified parameters.

        Args:
            outmasks (list): A list of tuples of (input, output masks, bias) for which
                                the last round key needs to be found.
            cutoff (int, optional): The cutoff value used for the maximum number of encryptions
                                    called from oracle in determining the last round key. Defaults to 10000.
            multiple (int, optional): The multiple indicating the size of the batch of values to be
                                encrypted at once used for generating encryption pairs. Defaults to 1000.
        Returns:
            list: A list of plaintext-ciphertext pairs for each output mask.
        """
        max_threshold = max(100 * int(1 / (bias * bias)) for _, _, bias in outmasks)
        threshold = min(cutoff, max_threshold)
        all_pt = list(self.encryptions)[:threshold]
        while len(all_pt) < threshold:
            r = random.randint(0, 2**(self.num_sbox * self.box_size) - 1)
            if r in self.encryptions:
                continue
            self.encryptions[r] = None
            all_pt.append(r)
        self.update_encryptions(multiple=multiple)
        all_ptct = [(i, self.encryptions[i]) for i in all_pt]
        return [all_ptct] * len(outmasks)
