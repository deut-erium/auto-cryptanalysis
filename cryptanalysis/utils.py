"""
The `utils` module provides utility functions for various operations.

Functions:
- all_smt: Generate all satisfying models for a given set of terms using an SMT solver.
- parity: Calculate the parity of a binary number.
- calculate_linear_bias: Calculate the linear bias of a binary function.
- calculate_difference_table: Calculate the difference table for a binary function.

Usage:
Import the `utils` module to access the utility functions. Call the desired function with the required parameters.
"""
from collections import Counter
from tqdm import tqdm
from z3 import sat

__all__ = [
    "all_smt",
    "parity",
    "calculate_linear_bias",
    "calculate_difference_table"]


def all_smt(solver, initial_terms):
    """
    Generate all satisfying models for a given set of initial terms using an SMT solver.

    Parameters
    ----------
    solver : z3.Solver or z3.Optimize instance
        An instance of an SMT solver.

    initial_terms : list
        A list of initial terms to generate satisfying models for.

    Yields
    ------
    model : Model
        A satisfying model for the set of initial terms.

    Notes
    -----
    This function uses a recursive approach to generate all satisfying models for a given set of initial terms.
    It relies on the `block_term` and `fix_term` helper functions.

    The `block_term` function adds a constraint to the solver that blocks a specific term from being equal to its
    value in the current model.

    The `fix_term` function adds a constraint to the solver that fixes a specific term to its value in the current model.

    The `all_smt_rec` function is a recursive helper function that performs the actual generation of satisfying models.
    """
    def block_term(solver, model, term):
        """
        Add a constraint to the solver that blocks a specific term from being equal to its value in the current model.

        Parameters
        ----------
        solver : z3.Solver
            An instance of an SMT solver.

        model : Model
            The current satisfying model.

        term : Term
            The term to block in the solver.
        """
        solver.add(term != model.eval(term))

    def fix_term(solver, model, term):
        """
        Add a constraint to the solver that fixes a specific term to its value in the current model.

        Parameters
        ----------
        solver : z3.Solver
            An instance of an SMT solver.

        model : Model
            The current satisfying model.

        term : Term
            The term to fix in the solver.
        """
        solver.add(term == model.eval(term))

    def all_smt_rec(terms):
        """
        Recursive helper function to generate all satisfying models for a given set of terms.

        Parameters
        ----------
        terms : list
            A list of terms to generate satisfying models for.

        Yields
        ------
        model : Model
            A satisfying model for the set of terms.
        """
        if sat == solver.check():
            model = solver.model()
            yield model
            for i in range(len(terms)):
                solver.push()
                block_term(solver, model, terms[i])
                for j in range(i):
                    fix_term(solver, model, terms[j])
                yield from all_smt_rec(terms[i:])
                solver.pop()

    yield from all_smt_rec(list(initial_terms))


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
