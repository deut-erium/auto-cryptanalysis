from collections import Counter
from tqdm import tqdm

def parity(x):
    """Calculates the parity of an integer.

    This method calculates the parity of an integer by counting the number
    of set bits in the binary representation of the integer. It returns 0 if the
    number of set bits is even, and 1 otherwise.

    Args:
        x (int): The input value for which the parity is calculated.

    Returns:
        int: 0 if the number of set bits is even, 1 otherwise.
    """
    res = 0
    while x:
        res ^= 1
        x &= (x - 1)
    return res

def calculate_linear_bias(sbox, no_sign=True, fraction=False):
    """Calculates the linear bias of an S-box.

    This method calculates the linear bias of an S-box. It iterates over
    all possible input and output mask pairs and computes the linear bias using
    the Cryptanalysis.parity method.

    Args:
        sbox (list): A list of integers representing the S-box.
        no_sign (bool, optional): If True, the absolute value of the bias is returned. Defaults to True.
        fraction (bool, optional): If True, the bias is returned as a fraction. Defaults to False.

    Returns:
        Counter: A Counter dictionary containing the linear biases for each input and output mask pair.
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
    """Calculates the difference distribution table for an S-box.

    This method calculates the difference table for an S-box. It iterates
    over all possible input and input difference pairs and counts the number of
    output differences for each input difference.

    Args:
        sbox (list): A list of integers representing the S-box.

    Returns:
        Counter: A Counter dictionary containing the count of output differences for each input difference.
    """
    n = len(sbox)
    bias = Counter()
    for inp_diff in tqdm(range(n), desc='calculating sbox differences'):
        for inp in range(n):
            out_diff = sbox[inp] ^ sbox[inp ^ inp_diff]
            bias[(inp_diff, out_diff)] += 1
    return bias
