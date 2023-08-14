import random
import cryptanalysis

sbox_size = 6 # bits
pbox_size = sbox_size * 16 # 16 sboxes
num_rounds = 4
sbox = list(range(2**sbox_size))
pbox = list(range(pbox_size))
# random pbox and sbox
random.shuffle(sbox)
random.shuffle(pbox)

random_key = random.randint(0, (2**pbox_size) - 1)
# random spn instance whose key is unknown to us
spn = cryptanalysis.SPN(sbox, pbox, random_key, num_rounds)

d_c = cryptanalysis.differential_cryptanalysis.DifferentialCryptanalysis(sbox, pbox, num_rounds+1)
# override batch_encrypt with the oracle

max_num_encryptions = 50000
def batch_encrypt(plaintexts):
    return [spn.encrypt(i) for i in plaintexts]

d_c.batch_encrypt = batch_encrypt
differential_characteristics = d_c.characteristic_searcher.search_exclusive_masks()
last_round_key_blocks = d_c.find_last_roundkey(differential_characteristics, max_num_encryptions//16)

print("recovered last round key:",last_round_key_blocks)
print("original last round key:",d_c.int_to_list(spn.round_keys[-1]))


