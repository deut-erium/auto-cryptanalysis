from cryptanalysis import *
from spn import *
import random



# PBOX = gen_pbox(6, 8)
PBOX = list(range(6 * 8))
SBOX = list(range(2**6))
random.shuffle(SBOX)
random.shuffle(PBOX)
cryptanal = LinearCryptanalysis(SBOX, PBOX, 5)
randkey = random.randint(0, 2**cryptanal.BLOCK_SIZE - 1)
cryptanal.round_keys = cryptanal.expand_key(randkey, cryptanal.rounds)
characteristics = cryptanal.characteristic_searcher.search_exclusive_masks(repeat=4, prune_level=1)

ptct_pairs = cryptanal.generate_encryption_pairs(characteristics[:1], 500000)[0]
x = cryptanal.find_keybits_multimasks(characteristics, ptct_pairs, known_keyblocks=[])
print(cryptanal.int_to_list(cryptanal.round_keys[-1]))
# cryptanal.characteristic_searcher.init_characteristic_solver()
# characteristics = []
# for i in range(10):
#     characteristics.extend(cryptanal.characteristic_searcher.solve_for_blocks({0}, {1,2,3,4,5,6,7}))
# characteristics = cryptanal.characteristic_searcher.search_best_masks()
# characteristics = cryptanal.characteristic_searcher.search_best_masks()


# last_round_key_blocks = cryptanal.find_last_roundkey(characteristics, 1000000)
# print(cryptanal.int_to_list(cryptanal.round_keys[-1]))
