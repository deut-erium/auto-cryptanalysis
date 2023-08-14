"""
characteristic_searcher
===========

This module provides the CharacteristicSearcher class for performing characteristic search in cryptanalysis.

Classes:
- CharacteristicSearcher: Implements the search algorithm for finding linear and differential characteristics in substitution permutation network based cipher.

"""
from collections import defaultdict
from math import log2
from itertools import islice
from z3 import Optimize, BitVec, sat, Concat, And, Not, Implies, Extract, Function, BitVecSort, RealSort, Product
from .utils import calculate_linear_bias, calculate_difference_table, all_smt

__all__ = ["CharacteristicSearcher"]


class CharacteristicSearcher:
    """A class for finding characteristics (linear or differential) of a substitution
    permutation network with provided S-box and P-box with a given number of rounds.

    Attributes:
        sbox: A list representing the substitution box.
        pbox: A list representing the permutation box.
        num_rounds: An integer representing the number of rounds.
        block_size: An integer representing the number of bits in the block.
        box_size: An integer representing the size of the S-box in bits.
        num_blocks: An integer representing the number of sboxes in a block
        mode: A string representing the mode, which can be 'linear' or 'differential'.
        bias: A Counter dictionary representing linear or differential bias
              of sbox input/output pairs
        solutions: A dictionary containing list of valid characteristic masks for a given
            set of included and excluded blocks
        solver: SMT solver (optimize) instance to search the characteristics
    """

    def __init__(self, sbox, pbox, num_rounds, mode='linear'):
        """Initializes the CharacteristicSolver with the given sbox, pbox, num_rounds and mode.

        Args:
            sbox (list): The substitution box.
            pbox (list): The permutation box.
            num_rounds (int): The number of rounds.
            mode (str, optional): The mode of operation. Defaults to 'linear'.
        """
        self.sbox = sbox
        self.pbox = pbox
        self.num_rounds = num_rounds
        self.block_size = len(pbox)
        self.box_size = int(log2(len(sbox)))
        self.num_blocks = len(pbox) // self.box_size
        self.mode = mode
        if mode == 'linear':
            self.bias = calculate_linear_bias(sbox)
        elif mode == 'differential':
            self.bias = calculate_difference_table(sbox)
        self.solutions = defaultdict(list)
        self.solver = Optimize()
        self.prune_level = 0
        self.sboxf = None
        self.inps = None
        self.oups = None
        self.bv_inp_masks = None
        self.bv_oup_masks = None
        self.objectives = None

    def initialize_sbox_structure(self):
        """Initializes the S-box structure for the cryptographic solver.

        This method sets up the structure of the S-box by creating an optimized solver,
        initializing input and output bit vectors for each round, and adding
        constraints for the solver. It also creates a concatenated view of the input
        and output layers for further processing.
        """
        n = self.box_size
        self.inps = [[BitVec('r{}_i{}'.format(r, i), n) for i in range(
            self.num_blocks)] for r in range(self.num_rounds + 1)]
        self.oups = [[BitVec('r{}_o{}'.format(r, i), n) for i in range(
            self.num_blocks)] for r in range(self.num_rounds)]
        # permutation of output of sboxes are inputs of next round
        for i in range(self.num_rounds):
            if self.num_blocks == 1:
                self.solver.add(self.bitvec_permutation(
                    self.oups[i][0], self.inps[i + 1][0]))
            else:
                self.solver.add(self.bitvec_permutation(
                    Concat(self.oups[i]), Concat(self.inps[i + 1])))
        # all first layer inputs should not be 0
        self.solver.add(
            Not(And(*[self.inps[0][i] == 0 for i in range(self.num_blocks)])))
        for r in range(self.num_rounds):
            for i in range(self.num_blocks):
                # if sbox has input, it should have output
                self.solver.add(
                    Implies(
                        self.inps[r][i] != 0,
                        self.oups[r][i] != 0))
                # if sbox has no input it should not have any output
                self.solver.add(
                    Implies(
                        self.inps[r][i] == 0,
                        self.oups[r][i] == 0))

        # just a concatanated view of the input and output layers
        if self.num_blocks == 1:
            self.bv_inp_masks = [self.inps[i][0]
                                 for i in range(self.num_rounds + 1)]
            self.bv_oup_masks = [self.oups[i][0]
                                 for i in range(self.num_rounds)]
        else:
            self.bv_inp_masks = [Concat(self.inps[i])
                                 for i in range(self.num_rounds + 1)]
            self.bv_oup_masks = [Concat(self.oups[i])
                                 for i in range(self.num_rounds)]

    def bitvec_permutation(self, inp, oup):
        """Performs bit vector permutation based on pbox.

        Args:
            inp (BitVec): The input bit vector.
            oup (BitVec): The output bit vector.

        Returns:
            list: A list of constraints for the permutation.
        """
        pn = len(self.pbox)
        constraints = []
        for i, v in enumerate(self.pbox):
            constraints.append(
                Extract(pn - 1 - i, pn - 1 - i, inp) ==
                Extract(pn - 1 - v, pn - 1 - v, oup)
            )
        return constraints

    def initialize_objectives(self):
        """Initializes the objective functions for the cryptographic solver.

        The method sets up four types of objective functions: 'original_linear',
        'reduced', 'differential', and 'linear'. These objective functions are
        used to guide the solver in finding the optimal solution. Each objective
        function is associated with a lambda function that calculates the objective
        value for a given number of rounds.
        'reduced' objective is called for both linear and differential search
        Other objective functions are just there for reference and easy evaluation
        of bias directly from the model
        """
        self.objectives = {
            # the actual objective, which is just product of bias [0,1/2]
            'original_linear': lambda rounds: 2**(self.num_blocks * rounds - 1) * Product([self.sboxf(
                self.inps[i // self.num_blocks][i % self.num_blocks],
                self.oups[i // self.num_blocks][i % self.num_blocks])
                for i in range(self.num_blocks * rounds)
            ]),
            # reducing optimization problem of product to sums
            'reduced': lambda rounds: sum([
                self.sboxf(
                    self.inps[i // self.num_blocks][i % self.num_blocks],
                    self.oups[i // self.num_blocks][i % self.num_blocks])
                for i in range(self.num_blocks * rounds)
            ]),
            # objective when the input biases are [0,2**n] just the final
            # division
            'differential': lambda rounds: Product([
                self.sboxf(
                    self.inps[i // self.num_blocks][i % self.num_blocks],
                    self.oups[i // self.num_blocks][i % self.num_blocks])
                for i in range(self.num_blocks * rounds)
            ]) / ((2**self.box_size)**(self.num_blocks * rounds)),
            'linear': lambda rounds: 2**(self.num_blocks * rounds - 1) * Product([
                self.sboxf(
                    self.inps[i // self.num_blocks][i % self.num_blocks],
                    self.oups[i // self.num_blocks][i % self.num_blocks])
                for i in range(self.num_blocks * rounds)
            ]) / ((2**self.box_size)**(self.num_blocks * rounds))
        }

    def add_bias_constraints(self, prune_level):
        """Adds bias constraints to the solver based on the biases of the S-box.

        This method adds constraints to the solver that are based on the biases of the S-box.
        If the bias of a particular input-output pair is greater than or equal to 2**prune_level,
        the method adds a constraint that the S-box function of the pair is equal to the bias.
        Otherwise, it adds a constraint that the S-box function of the pair is 0. This helps in
        pruning the search space of the solver.

        Args:
            prune_level (int): The level at which to prune the biases.
        """
        for i in range(2**self.box_size):
            for j in range(2**self.box_size):
                # just some pruning of very small biases
                if self.bias[(i, j)] >= 2**(prune_level):
                    self.solver.add(self.sboxf(i, j) == self.bias[(i, j)])
                else:
                    self.solver.add(self.sboxf(i, j) == 0)

        for r in range(self.num_rounds):
            for i in range(self.num_blocks):
                # skip taking input/outputs with no bias
                self.solver.add(
                    Implies(
                        And(self.inps[r][i] != 0, self.oups[r][i] != 0),
                        self.sboxf(self.inps[r][i], self.oups[r][i]) != 0
                    )
                )

    def init_characteristic_solver(self, prune_level=-1):
        """Initializes the S-box structure, S-box function, objective functions, and pruning level.

        This method initializes the structure of the S-box, the S-box function,
        and the objective functions for the solver. It also sets the pruning level
        for the solver. If no pruning level is provided, the method will search for
        the best pruning level.

        Args:
            prune_level (int, optional): The level at which to prune the biases.
            If not provided or less than 0, the method will search for the best pruning level.
        """
        self.initialize_sbox_structure()
        self.sboxf = Function(
            'sbox', BitVecSort(
                self.box_size), BitVecSort(
                self.box_size), RealSort())
        self.initialize_objectives()
        assert self.solver.check()

        if prune_level < 0:
            print("searching best pruning level")
            low, high = 0, len(self.sbox) // 4
            while low <= high:
                mid = (low + high) // 2
                print("trying pruning", mid)
                self.solver.push()
                self.solver.set(timeout=10000)
                self.add_bias_constraints(mid)
                if self.solver.check() == sat:
                    print("success")
                    low = mid + 1
                else:
                    print("failure")
                    high = mid - 1
                self.solver.pop()
            self.solver.set(timeout=0)
            print("best pruning", high)
            self.prune_level = high
            self.add_bias_constraints(high)
        else:
            self.add_bias_constraints(prune_level)
            if self.solver.check() == sat:
                self.prune_level = prune_level
            else:
                print("Provided pruning level unsat, searching optimal pruning")
                self.init_characteristic_solver(-1)  # search best pruning

    def solve_for_blocks(self, include_blocks=(), exclude_blocks=(),
                         num_rounds=0,
                         num_sols=1,
                         display_paths=True):
        """Solves the characteristic for the specified blocks and maximizes the objective function.

            This method searches the characteristic for the specified blocks,
            maximizes the objective function, and returns the solutions.
            The blocks to include and exclude in the characteristic can be specified.
            The number of rounds and the number of solutions can also be specified.

            Args:
                include_blocks (list, optional): The blocks to definitely include in the characteristic.
                exclude_blocks (list, optional): The blocks to definitely exclude in the characteristic.
                num_rounds (int, optional): The number of rounds for which to solve the characteristic.
                                             If not provided or 0, the number of rounds will be set to the
                                             number of rounds of the solver.
                num_sols (int, optional): The number of solutions to return.
                display_paths (bool, optional): Whether to display the paths of the solutions.

            Returns:
                list: A list of tuples. Each tuple contains the input masks, the output masks, and the
                      calculated bias for a solution.
            """
        if num_rounds == 0:
            num_rounds = self.num_rounds
        else:
            # cap to initialized struct
            num_rounds = min(self.num_rounds, num_rounds)
        while len(self.solver.objectives()):
            self.solver.pop()  # remove any previous include/exclude block constraints
        self.solver.push()  # set this as the checkpoint
        # specify which blocks to definitely include in the characteristic
        for i in include_blocks:
            self.solver.add(self.inps[num_rounds - 1][i] != 0)
        # specify which blocks to definitely exclude in the characteristic
        for i in exclude_blocks:
            self.solver.add(self.inps[num_rounds - 1][i] == 0)
        # print(include_blocks, exclude_blocks)
        # if a block is neither in include_blocks or exclude_blocks
        # the solver finds the best path which may or may not set it to active
        self.solver.maximize(self.objectives['reduced'](num_rounds))
        solutions = self.get_masks(num_rounds, num_sols, display_paths)
        self.solutions[(tuple(sorted(include_blocks)),
                        tuple(sorted(exclude_blocks)))].extend(solutions)
        return [(inp_masks[0], inp_masks[-1], calc_bias)
                for inp_masks, _, calc_bias, _ in solutions]

    def search_best_masks(self, tolerance=1, choose_best=10, display_paths=True):
        """Searches for the best masks with the highest total bias and limited undiscovered active blocks.

        This method searches for the best masks with the highest total bias and a limited number
        of undiscovered active blocks.

        Args:
            tolerance (int, optional): The maximum number of undiscovered active blocks allowed.
            choose_best (int, optional): The number of best masks to choose from.
            display_paths (bool, optional): Whether to display the characteristic paths
                                        (containing the bits involved) of the solutions.

        Returns:
            list: A list of tuples. Each tuple contains the input masks, the output masks, and the
                  total bias for a solution.
        """

        self.init_characteristic_solver()
        nr = self.num_rounds
        discovered = [False for _ in range(self.num_blocks)]

        def istolerable(x):
            return sum((not i) and j
                       for i, j in zip(discovered, x[3])) in range(1, tolerance + 1)
        masks = []
        while self.solver.check() == sat:
            curr_masks = self.get_masks(self.num_rounds, choose_best, display_paths=False)
            for i in curr_masks:
                self.solutions[i[2]].append(i)
            curr_masks = list(filter(istolerable, curr_masks))
            if len(curr_masks) > 0:
                inp_masks, oup_masks, total_bias, active = max(
                    curr_masks, key=lambda x: (x[2], -sum(x[3])))
                if display_paths:
                    self.print_bitrelations(inp_masks, oup_masks)
                    print("total bias:", total_bias)
                    print()
                masks.append((inp_masks[0], inp_masks[nr - 1], total_bias))
                for i, v in enumerate(discovered):
                    if (not v) and active[i]:
                        discovered[i] = True
                print("discovered", "".join(map(lambda x: str(int(x)), discovered)))
                # dont discover biases where all the active blocks come from discovered blocks
                # i.e. if all the active blocks come from discovered blocks,
                # it means, all the undiscovered blocks are inactive
                # i.e it should not be the case where all the undiscovered blocks are
                # inactive i.e 0
                self.solver.add(Not(And(
                    [self.inps[nr - 1][i] == 0 for i, v in enumerate(discovered) if not v]
                )))
        return masks

    def search_exclusive_masks(self, prune_level=-1, repeat=1):
        """Searches for the masks for each block by including only one block and excluding all the others.

        This method searches for the masks for each block by including only one block and excluding
        all the others.

        Args:
            prune_level (int, optional): The level at which to prune the biases.
            repeat (int, optional): The number of times to repeat the search for each block.

        Returns:
            list: A list of tuples. Each tuple contains the input masks, the output masks, and the
                  total bias for a solution.
        """
        self.init_characteristic_solver(prune_level)
        masks = []
        for i in range(self.num_blocks):
            include_blocks = {i}
            exclude_blocks = set(range(self.num_blocks)) - include_blocks
            masks.extend(self.solve_for_blocks(include_blocks, exclude_blocks, num_sols=repeat))
        return masks

    def get_masks(self, num_rounds, n=1, display_paths=True):
        """Returns the input masks, output masks, total bias, and active blocks of the solutions.

        This method returns the input masks, output masks, total bias, and active blocks of the solutions.

        Args:
            num_rounds (int): The number of rounds for which to get the masks.
            n (int, optional): The number of masks to get.
            display_paths (bool, optional): Whether to display the paths of the solutions.

        Returns:
            list: A list of tuples. Each tuple contains the input masks, the output masks, the total bias,
                  and the active blocks for a solution.
        """
        masks = []
        for m in islice(all_smt(self.solver, [self.bv_inp_masks[num_rounds - 1]]), n):
            inp_masks = [m.eval(i).as_long()
                         for i in self.bv_inp_masks[:num_rounds]]
            oup_masks = [m.eval(i).as_long()
                         for i in self.bv_oup_masks[:num_rounds]]
            total_bias = m.eval(
                self.objectives[self.mode](num_rounds)).as_fraction()
            active = [m.eval(i).as_long() != 0 for i in self.inps[num_rounds - 1]]
            if display_paths:
                self.print_bitrelations(inp_masks, oup_masks)
                print("total bias:", total_bias)
                print()
            masks.append((inp_masks, oup_masks, total_bias, active))
        return masks

    def print_bitrelations(self, inp_masks, out_masks):
        """
        Print the input and output masks of a block cipher in a formatted manner.

        :param inp_masks: List of integers, input masks for each round.
        :param out_masks: List of integers, output masks for each round.
        """
        s = self.box_size
        n = self.num_blocks * s

        def bin_sep(val):
            v = bin(val)[2:].zfill(n)
            return "|".join(v[i:i + s] for i in range(0, n, s))

        rounds = len(out_masks)
        for i in range(rounds):
            imask, omask = inp_masks[i], out_masks[i]
            print(bin_sep(imask))
            print(' '.join(['-' * s] * (n // s)))
            print(bin_sep(omask))
            print()
        print(bin_sep(inp_masks[-1]))
