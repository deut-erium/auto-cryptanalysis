"""
The `spn` module implements the Substitution-Permutation Network (SPN) encryption algorithm.

SPN is a symmetric-key block cipher that operates on fixed-size blocks of plaintext and produces
corresponding blocks of ciphertext. It consists of several rounds of substitutions and permutations
and key additions applied to the input data.

Classes:
- SPN: Implementation of the SPN encryption algorithm.

Usage:
Initialize an instance of the `SPN` class with the required parameters, then use the provided methods
to perform encryption and decryption operations.
"""
from math import log2

__all__ = ["rotate_left", "gen_pbox", "SPN"]


def rotate_left(val, shift, mod):
    """
    Rotate the bits of the value to the left by the shift amount.

    Parameters
    ----------
    val : int
        The value to be rotated.
    shift : int
        The number of places to shift the value to the left.
    mod : int
        The modulo to be applied on the result.

    Returns
    -------
    int
        The rotated value.

    Notes
    -----
    The function rotates the bits of the value to the left by the shift amount,
    wrapping the bits that overflow. The result is then masked by (1<<mod)-1
    to only keep the mod number of least significant bits.

    """
    shift = shift % mod
    return (val << shift | val >> (mod - shift)) & ((1 << mod) - 1)


def gen_pbox(s, n):
    """
    Generate a balanced permutation box for an SPN.

    Parameters
    ----------
    s : int
        Number of bits per S-box.
    n : int
        Number of S-boxes.

    Returns
    -------
    list of int
        The generated P-box.

    """
    return [(s * i + j) % (n * s) for j in range(s) for i in range(n)]


class SPN:
    """
    Class representing the SPN (Substitution-Permutation Network) encryption algorithm.

    Methods
    -------
    perm(inp)
        Apply the P-box permutation on the input.
    inv_perm(inp)
        Apply the inverse P-box permutation on the input.
    sub(inp)
        Apply the S-box substitution on the input.
    inv_sub(inp)
        Apply the inverse S-box substitution on the input.
    int_to_list(inp)
        Convert a len(pbox)-sized integer to a list of S-box sized integers.
    list_to_int(lst)
        Convert a list of S-box sized integers to a len(pbox)-sized integer.
    expand_key(key, rounds)
        Derive round keys deterministically from the given key.
    _enc_last_noperm(pt)
        Encrypt plaintext using the SPN, where the last round doesn't contain the permute operation.
    _enc_last_withperm(ct)
        Encrypt plaintext using the SPN, where the last round contains the permute operation.
    _dec_last_noperm(ct)
        Decrypt ciphertext using the SPN, where the last round doesn't contain the permute operation.
    _dec_last_withperm(ct)
        Decrypt ciphertext using the SPN, where the last round contains the permute operation.
    """

    def __init__(self, sbox, pbox, key, rounds, implementation=0):
        """
        Initialize the SPN class with the provided parameters.

        Parameters
        ----------
        sbox : list of int
            List of integers representing the S-box.

        pbox : list of int
            List of integers representing the P-box.

        key : list of int or bytes or bytearray
            List of integers, bytes, or bytearray representing the key.
            LSB block_size bits will be used.

        rounds : int
            Number of rounds for the SPN.

        implementation : int, optional
            Implementation option. Default is 0.
            0: Last round doesn't contain the permute operation.
            1: Last round contains the permute operation.
        """
        self.sbox = sbox
        self.pbox = pbox
        self.sinv = [sbox.index(i) for i in range(len(sbox))]
        self.pinv = [pbox.index(i) for i in range(len(pbox))]
        self.block_size = len(pbox)
        self.box_size = int(log2(len(sbox)))
        self.num_sbox = len(pbox) // self.box_size
        self.rounds = rounds
        self.round_keys = self.expand_key(key, rounds)
        if implementation == 0:
            self.encrypt = self._enc_last_noperm
            self.decrypt = self._dec_last_noperm
        else:
            self.encrypt = self._enc_last_withperm
            self.decrypt = self._dec_last_withperm

    def perm(self, inp: int) -> int:
        """
        Apply the P-box permutation on the input.

        Parameters
        ----------
        inp : int
            The input value to apply the P-box permutation on.

        Returns
        -------
        int
            The permuted value after applying the P-box.
        """
        ct = 0
        for i, v in enumerate(self.pbox):
            ct |= (inp >> (self.block_size - 1 - i) & 1) << (
                self.block_size - 1 - v)
        return ct

    def inv_perm(self, inp: int) -> int:
        """
        Apply the inverse P-box permutation on the input.

        Parameters
        ----------
        inp : int
            The input value to apply the inverse P-box permutation on.

        Returns
        -------
        int
            The permuted value after applying the inverse P-box.
        """
        ct = 0
        for i, v in enumerate(self.pinv):
            ct |= (inp >> (self.block_size - 1 - i) & 1) << (
                self.block_size - 1 - v)
        return ct

    def sub(self, inp: int) -> int:
        """
        Apply the S-box substitution on the input.

        Parameters
        ----------
        inp : int
            The input value to apply the S-box substitution on.

        Returns
        -------
        int
            The substituted value after applying the S-box.
        """
        ct, bs = 0, self.box_size
        for i in range(self.num_sbox):
            ct |= self.sbox[(inp >> (i * bs)) & ((1 << bs) - 1)] << (bs * i)
        return ct

    def inv_sub(self, inp: int) -> int:
        """
        Apply the inverse S-box substitution on the input.

        Parameters
        ----------
        inp : int
            The input value to apply the inverse S-box substitution on.

        Returns
        -------
        int
            The substituted value after applying the inverse S-box.
        """
        ct, bs = 0, self.box_size
        for i in range(self.num_sbox):
            ct |= self.sinv[(inp >> (i * bs)) & ((1 << bs) - 1)] << (bs * i)
        return ct

    def int_to_list(self, inp):
        """
        Convert a len(pbox)-sized integer to a list of S-box sized integers.

        Parameters
        ----------
        inp : int
            An integer representing a len(pbox)-sized input.

        Returns
        -------
        list of int
            A list of integers, each representing an S-box sized input.
        """
        bs = self.box_size
        return [(inp >> (i * bs)) & ((1 << bs) - 1)
                for i in range(self.num_sbox - 1, -1, -1)]

    def list_to_int(self, lst):
        """
        Convert a list of S-box sized integers to a len(pbox)-sized integer.

        Parameters
        ----------
        lst : list of int
            A list of integers, each representing an S-box sized input.

        Returns
        -------
        int
            An integer representing the combined input as a len(pbox)-sized integer.
        """
        res = 0
        for i, v in enumerate(lst[::-1]):
            res |= v << (i * self.box_size)
        return res

    def expand_key(self, key, rounds):
        """
        Derive round keys deterministically from the given key.

        Parameters
        ----------
        key : list of int or bytes or bytearray
            A list of integers, bytes, or bytearray representing the key.
        rounds : int
            The number of rounds for the SPN.

        Returns
        -------
        list of int
            A list of integers representing the derived round keys.
        """
        if isinstance(key, list):
            key = self.list_to_int(key)
        elif isinstance(key, (bytes, bytearray)):
            key = int.from_bytes(key, 'big')
        block_mask = (1 << self.block_size) - 1
        key = key & block_mask
        keys = [key]
        for _ in range(rounds):
            keys.append(self.sub(rotate_left(
                keys[-1], self.box_size + 1, self.block_size)))
        return keys

    def _enc_last_noperm(self, pt: int) -> int:
        """
        Encrypt plaintext using the SPN, where the last round doesn't contain the permute operation.

        Parameters
        ----------
        pt : int
            The plaintext input to be encrypted.

        Returns
        -------
        int
            The ciphertext after encryption.
        """
        ct = pt ^ self.round_keys[0]
        for round_key in self.round_keys[1:-1]:
            ct = self.sub(ct)
            ct = self.perm(ct)
            ct ^= round_key
        ct = self.sub(ct)
        return ct ^ self.round_keys[-1]

    def _enc_last_withperm(self, ct: int) -> int:
        """
        Encrypt plaintext using the SPN, where the last round contains the permute operation.
        Note, the last permutation provides no additional security.

        Parameters
        ----------
        ct : int
            The plaintext input to be encrypted.

        Returns
        -------
        int
            The ciphertext after encryption.
        """
        for round_key in self.round_keys[:-1]:
            ct ^= round_key
            ct = self.sub(ct)
            ct = self.perm(ct)
        return ct ^ self.round_keys[-1]

    def _dec_last_noperm(self, ct: int) -> int:
        """
        Decrypt ciphertext using the SPN, where the last round doesn't contain the permute operation.

        Parameters
        ----------
        ct : int
            The ciphertext input to be decrypted.

        Returns
        -------
        int
            The plaintext after decryption.
        """
        ct = ct ^ self.round_keys[-1]
        ct = self.inv_sub(ct)
        for rk in self.round_keys[-2:0:-1]:
            ct ^= rk
            ct = self.inv_perm(ct)
            ct = self.inv_sub(ct)
        return ct ^ self.round_keys[0]

    def _dec_last_withperm(self, ct: int) -> int:
        """
        Decrypt ciphertext using the SPN, where the last round contains the permute operation.

        Parameters
        ----------
        ct : int
            The ciphertext input to be decrypted.

        Returns
        -------
        int
            The plaintext after decryption.
        """
        ct = ct ^ self.round_keys[-1]
        for rk in self.round_keys[-2::-1]:
            ct = self.inv_perm(ct)
            ct = self.inv_sub(ct)
            ct ^= rk
        return ct
