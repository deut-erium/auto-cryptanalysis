# List of Tasks and Enhancements
## Performance Benchmarking
- Conduct performance benchmarking experiments with variations on different sizes of sboxes, number of sboxes, and number of rounds.
- Identify special cases where cryptanalysis is easier or faster.
- Determine the optimal number of encryptions from the oracle for a given set of parameters for recovery.

## Aesthetics
- Implement a GUI to display characteristic paths

## Extending Attacks
Implement additional cryptanalysis attacks and their various flavors:

- Implement Impossible Differentials, which should be easily achievable with additional constraints.
- Incorporate the Boomerang attack, requiring the addition of characteristic search from the opposite direction.
- Explore the Square attack.
- Investigate the Slide attack.

## Improving Attack Confidence
Enhance the confidence in attack results by implementing the following:

- Add a verification routine to check the correctness of the last round key using encryption/decryption.
- Implement a strategy to brute force over the top n candidates (with low confidence) for recovering each key bit.
- Develop a methodology to identify incorrect key bits.

## Performance Optimization
- Optimize the key-finding routines in the LinearCryptanalysis and DifferentialCryptanalysis modules for faster key search. Consider rewriting these routines in C or other efficient languages, while keeping the CharacteristicSearcher module as it is, since it mostly relies on z3.

## Exploring Research Ideas
- Combine different attacks for improved confidence, such as combining multiple linear characteristics for the same block and determining how to add positive and negative biases.
- Explore the combination of linear and differential characteristics or verifying key bits found with differential characteristics using multiple linear characteristics.
- Utilize a large number of linear characteristics to obtain sufficient equations for internal key bits and model these equations together with the key expansion schedule to find keys.
- Explore the feasibility of incorporating the key expansion schedule into the characteristic search/cryptanalysis process.

## Expanding Test Suite
Enhance the test suite by adding more comprehensive tests to ensure the robustness and accuracy of the code.
