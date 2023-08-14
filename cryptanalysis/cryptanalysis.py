"""
Module for performing cryptanalysis on Substitution Permutation Network cipher.

Classes:
- Cryptanalysis: Abstract base class for cryptanalysis algorithms.

Usage:
Import the `cryptanalysis` module to access the `Cryptanalysis` class.
"""
from abc import ABC, abstractmethod
from .spn import SPN
from .characteristic_searcher import CharacteristicSearcher

__all__ = ["Cryptanalysis"]


class Cryptanalysis(SPN, ABC):
    """
    Abstract base class for cryptanalysis algorithms.

    Methods:
    - __init__: Initialize the cryptanalysis class.
    - dec_partial_last_noperm: Partially decrypt the ciphertext using last round without permutation.
    - dec_partial_last_withperm: Partially decrypt the ciphertext using last round with permutation.
    - update_encryptions: Update the encryption pairs used for analysis.
    - batch_encrypt: Encrypt multiple plaintexts in batch mode.
    - find_keybits: Find the key bits of the encryption algorithm.
    - generate_encryption_pairs: Generate encryption pairs for cryptanalysis.
    - find_last_roundkey: Find the last round key of the encryption algorithm.
    """
    def __init__(self, sbox, pbox, num_rounds, mode='differential'):
        """
        This method initializes the Cryptanalysis class by calling the __init__ method of the SPN class
        (the parent class) and setting the mode and characteristic_searcher attributes. It also initializes
        the encryptions dictionary.

        Args:
            sbox (list): A list of integers representing the S-box.
            pbox (list): A list of integers representing the P-box.
            num_rounds (int): The number of rounds in the block cipher.
            mode (str, optional): The mode of the cryptanalysis. Defaults to 'differential'.
        """
        super().__init__(sbox, pbox, 0, num_rounds)
        self.mode = mode
        self.characteristic_searcher = CharacteristicSearcher(
            self.sbox, self.pbox, num_rounds - 1, mode)
        self.encryptions = {}  # store of the encryptions utilized by the cryptanalysis

    def dec_partial_last_noperm(self, ciphertext, round_keys):
        """Performs partial decryption without permutation on the last round.
        Args:
            ciphertext (int): The ciphertext to decrypt.
            round_keys (list): A list of round keys in reverse order.

        Returns:
            int: The partially decrypted ciphertext.
        """
        # partial decryption
        # round keys in reverse order
        ciphertext = ciphertext ^ round_keys[0]
        ciphertext = self.inv_sub(ciphertext)
        for round_key in round_keys[1:self.rounds]:
            ciphertext ^= round_key
            ciphertext = self.inv_perm(ciphertext)
            ciphertext = self.inv_sub(ciphertext)
        if len(round_keys) == self.rounds + 1:
            ciphertext ^= round_keys[-1]
        return ciphertext

    def dec_partial_last_withperm(self, ciphertext, round_keys):
        """Performs partial decryption with permutation on last round
        Args:
            ciphertext (int): The ciphertext to decrypt.
            round_keys (list): A list of round keys.

        Returns:
            int: The partially decrypted ciphertext.
        """
        for round_key in round_keys[:self.rounds]:
            ciphertext ^= round_key
            ciphertext = self.inv_perm(ciphertext)
            ciphertext = self.inv_sub(ciphertext)
        if len(round_keys) == self.rounds + 1:
            ciphertext ^= round_keys[-1]
        return ciphertext


    def update_encryptions(self, multiple=10000):
        """Updates the encryptions dictionary.

        This method updates the encryptions dictionary by encrypting the ciphertexts
        that have not been encrypted yet. It encrypts the ciphertexts in batches to
        improve performance.

        Args:
            multiple (int, optional): The number of ciphertexts to encrypt in each batch. Defaults to 10000.
        """
        to_encrypt = [i for i, v in self.encryptions.items() if v is None]
        for i in range(0, len(to_encrypt) + multiple, multiple):
            current_batch = to_encrypt[i:i + multiple]
            if current_batch == []:
                break
            for j, enc in zip(current_batch, self.batch_encrypt(current_batch)):
                self.encryptions[j] = enc

    def batch_encrypt(self, pt_list):
        """Encrypts a list of plaintexts.

        This method takes a list of integers representing plaintexts and returns a
        list of integers representing the corresponding ciphertexts.
        Override this function in case oracle is remote and to get encryptions from it.

        Args:
            pt_list (list): A list of integers representing the plaintexts.

        Returns:
            list: A list of integers representing the ciphertexts.
        """
        return [self.encrypt(i) for i in pt_list]

    @abstractmethod
    def find_keybits(self, in_mask, out_mask, encryption_pairs, known_keyblocks=()):
        """Finds the key bits based on input and output masks.

        This abstract method is meant to be overridden by subclasses. It takes an input mask,
        an output mask, a list of encryption pairs, and an optional list of known key blocks
        as input. It should implement the logic to find the key bits based on the provided parameters.

        Args:
            in_mask (int): The input mask for the key search.
            out_mask (int): The output mask for the key search.
            encryption_pairs (list): A list of tuples of encryption pairs used for analysis.
            known_keyblocks (list, optional): A list of known key blocks. Defaults to an empty list.

        Returns:
            list: A list of key bits that are determined based on the provided parameters.
        """

    @abstractmethod
    def generate_encryption_pairs(self, outmasks, cutoff, multiple):
        """Generates encryption pairs for analysis.

        This abstract method is meant to be overridden by subclasses. It takes a list of output masks
        and generates encryption pairs for analysis. The encryption pairs should be suitable for
        cryptanalysis purposes.

        Args:
            outmasks (list): A list of tuples of (input, output masks, bias) for which
                                the last round key needs to be found.
            cutoff (int, optional): The cutoff value used for the maximum number of encryptions
                                    called from oracle in determining the last round key. Defaults to 10000.
            multiple (int, optional): The multiple indicating the size of the batch of values to be
                                encrypted at once used for generating encryption pairs. Defaults to 1000.

        Returns:
            list: A list of encryption pairs suitable for cryptanalysis.
        """

    @abstractmethod
    def find_last_roundkey(self, outmasks, cutoff, multiple):
        """Finds the last round key based on output masks.

        This abstract method is meant to be overridden by subclasses. It takes a list of output masks
        and a cutoff value. It should implement the logic to find the last round key based on the output
        masks and the specified cutoff value.

        Args:
            outmasks (list): A list of tuples of (input, output masks, bias) for which
                                the last round key needs to be found.
            cutoff (int): The cutoff value used for determining the number of encryptions used to
                            determine the last round key
            multiple (int): The multiple indicating the size of the batch of values to be
                                encrypted at once used for generating encryption pairs.


        Returns:
            int: The last round key determined based on the output masks and the cutoff value.
        """
