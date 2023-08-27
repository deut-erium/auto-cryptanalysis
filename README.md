# Auto Cryptanalysis
This project implements python module for automatic cryptanalysis of Substitution Permutation Network
ciphers by performing extensive linear and differential characteristic search and finding keybits

## Structure
The project is structured as follows:

- The `cryptanalysis` directory contains the main Python module for cryptanalysis.
- The `tests` directory contains unit tests for the module
- The `examples` directory contains examples for using the module
- The `docs` directory contains html documentation autogenerated from code doc-strings

## Installation

### Pip
The project can be installed directly from pip
```bash
pip install cryptanalysis
```

Otherwise clone and install is also viable

```bash
git clone https://github.com/deut-erium/auto-cryptanalysis.git
cd auto-cryptanalysis
pip install .
```

### Requirements
This project requires Python3.6+ and the following Python packages:
- z3-solver
- tqdm

Requirements are auto installed as a part of the installation process but

You can also install these packages using pip:
```bash
pip install -r requirements.txt
```

## Usage
```python
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
```

## Tests
You can run the tests using the following command:
```bash
python -m unittest discover
```

## Documentation
Read the [documentation](https://deut-erium.github.io/auto-cryptanalysis)  
Autogenerated documentation from code doc-strings can be found under [docs](docs)  

## Contributing
Please feel free to submit pull requests or create issues if you find any bugs or have any suggestions for improvements.  
List of ideas to implement/TODO is present in [CONTRIBUTING.md](CONTRIBUTING.md)

## License
This project is licensed under the GPL License.


