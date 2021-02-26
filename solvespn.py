#from pwn import remote
from collections import Counter
from pprint import pprint
from itertools import product
from functools import reduce
from operator import xor
from tqdm import tqdm
from math import log2

from pairs import pairs
pairs = list(map(lambda x: (int.to_bytes(x[0],8,'big'),int.to_bytes(x[1],8,'big')),pairs)) 

sbox = [13, 14, 0, 1, 5, 10, 7, 6, 11, 3, 9, 12, 15, 8, 2, 4]
pbox = [0, 5, 10, 15, 4, 9, 14, 3, 8, 13, 2, 7, 12, 1, 6, 11]


SBOX = [237, 172, 175, 254, 173, 168, 187, 174, 53, 188, 165, 166, 161, 162, 131, 227, 191, 152, 63, 182, 169, 136, 171, 184, 149, 148, 183, 190, 181, 177, 163, 186, 207, 140, 143, 139, 147, 138, 155, 170, 134, 132, 135, 18, 193, 128, 129, 130, 157, 156, 151, 158, 153, 24, 154, 11, 141, 144, 21, 150, 146, 145, 179, 22, 245, 124, 236, 206, 105, 232, 43, 194, 229, 244, 247, 242, 233, 224, 235, 96, 253, 189, 219, 234, 241, 248, 251, 226, 117, 252, 213, 246, 240, 176, 249, 178, 205, 77, 231, 203, 137, 200, 107, 202, 133, 204, 228, 230, 225, 196, 195, 198, 201, 221, 199, 95, 216, 217, 159, 218, 209, 214, 215, 222, 83, 208, 211, 243, 44, 40, 46, 142, 32, 36, 185, 42, 45, 38, 47, 34, 33, 164, 167, 98, 41, 56, 55, 126, 57, 120, 59, 250, 37, 180, 119, 54, 52, 160, 51, 58, 5, 14, 79, 30, 8, 12, 13, 10, 68, 0, 39, 6, 1, 16, 3, 2, 23, 28, 29, 31, 27, 9, 7, 62, 4, 60, 19, 20, 48, 17, 87, 26, 239, 110, 111, 238, 109, 104, 35, 106, 101, 102, 103, 70, 49, 100, 99, 114, 61, 121, 223, 255, 88, 108, 123, 122, 84, 92, 125, 116, 112, 113, 115, 118, 197, 76, 15, 94, 73, 72, 75, 74, 81, 212, 69, 66, 65, 64, 97, 82, 93, 220, 71, 90, 25, 89, 91, 78, 85, 86, 127, 210, 80, 192, 67, 50]

PBOX = [1, 57, 6, 31, 30, 7, 26, 45, 21, 19, 63, 48, 41, 2, 0, 3, 4, 15, 43, 16, 62, 49, 55, 53, 50, 25, 47, 32, 14, 38, 60, 13, 10, 23, 35, 36, 22, 52, 51, 28, 18, 39, 58, 42, 8, 20, 33, 27, 37, 11, 12, 56, 34, 29, 46, 24, 59, 54, 44, 5, 40, 9, 61, 17]



class SPN:
    def __init__(self,SBOX,PBOX,key,rounds):
        self.SBOX = SBOX
        self.PBOX = PBOX
        self.SINV = [SBOX.index(i) for i in range(len(SBOX))]
        self.PINV = [PBOX.index(i) for i in range(len(PBOX))]
        self.BLOCK_SIZE = len(PBOX)
        self.key = key
        self.NUM_SBOX = len(PBOX)//int(log2(len(SBOX)))
        self.rounds = rounds
        #self.BIAS = calc_bias(SBOX)
    
    def sbox(self,inp:bytes) -> bytes:
        return [self.SBOX[i] for i in inp]

    def inv_sbox(self,inp:bytes) -> bytes:
        return [self.SINV[i] for i in inp]

    def perm(self,inp:bytes) -> bytes:
        #[inp[self.PBOX[i]] for i in range(len(inp))]
        inp = bin(int.from_bytes(inp,'big'))[2:].zfill(self.BLOCK_SIZE)
        ct = [None]*self.BLOCK_SIZE
        for i,v in enumerate(inp):
            ct[self.PBOX[i]] = v
        return  int.to_bytes(int("".join(ct),2),self.NUM_SBOX,'big')

    def inv_perm(self,inp):
        #return [ inp[self.PINV[i]] for i in range(len(inp)) ]
        inp = bin(int.from_bytes(inp,'big'))[2:].zfill(self.BLOCK_SIZE)
        ct = [None]*self.BLOCK_SIZE
        for i,v in enumerate(inp):
            ct[self.PINV[i]] = v
        return  int.to_bytes(int("".join(ct),2),self.NUM_SBOX,'big')

    def add_key(self,inp,key):
        return bytes(a^b for a,b in zip(key,inp))
    
    def expand_key(self):
        key = self.key
        keys = [None]*5
        keys[0] = key[0:4] + key[8:12]
        keys[1] = key[4:8] + key[12:16]
        keys[2] = key[0:4] + key[8:12]
        keys[3] = key[4:8] + key[12:16]
        keys[4] = key[0:4] + key[8:12]
        return keys
    
    def enc(self,pt):
        round_keys = self.expand_key()
        ct = pt
        ct = self.add_key(round_keys[0],ct)
        for round_key in round_keys[1:]:
            ct = self.sbox(ct)
            ct = self.perm(ct)
            ct = self.add_key(round_key,ct)
        return ct

    def dec(self,ct,round_keys):
        #print(round_keys)
        for round_key in round_keys:
            ct = self.add_key(round_key,ct)
            ct = self.inv_perm(ct)
            ct = self.inv_sbox(ct)
        #ct = self.add_key(round_key[-1],ct)
        return ct

    def get_mask(self,bit_pos):
        inp_mask = 0
        #print(bit_pos)
        for bit in bit_pos:
            inp_mask |= 1<<(self.BLOCK_SIZE-1-bit)
        return int.to_bytes(inp_mask,self.NUM_SBOX,'big')

    #def find_best_bias(self,bit_pos):
    def get_templates(self,in_bits,out_bits):
        inp_mask = self.get_mask(in_bits)
        out_mask = self.get_mask(out_bits)
        out_indices = [i for i in range(self.NUM_SBOX) if out_mask[i]]
        block_perms = self.perm(bytes([255 if i in out_indices 
                                       else 0 for i in range(self.NUM_SBOX)]))
        #print(block_perms)
        block_bin=bin(int.from_bytes(block_perms,
                                'big'))[2:].zfill(self.BLOCK_SIZE)
        key_bits = [i for i in range(self.BLOCK_SIZE) if block_bin[i]=='1']
        return inp_mask,out_mask,out_indices,key_bits[::-1]

    def get_key(self,n,key_bits):
        key_int = 0
        for b in key_bits:
            key_int |= (n&1)<<(self.BLOCK_SIZE-1-b)
            n>>=1
        return int.to_bytes(key_int,self.NUM_SBOX,'big')
            

    def parity_bias(self,in_bits,out_bits,pt_ct_pairs,round_keys_rev):
        inp_mask,out_mask,out_indices,key_bits = self.get_templates(in_bits,out_bits)
        #print(inp_mask,out_mask,out_indices,key_bits)
        key_guesses = []
        for i in tqdm(range(256**len(out_indices))):
            key = self.get_key(i,key_bits)
            bias = Counter()
            for pt,ct in pt_ct_pairs:
                ct_upto_key_round = self.dec(ct,round_keys_rev + [key])
                bias[parity_bytes(mask_and(pt,inp_mask)) ^
                     parity_bytes(mask_and(ct_upto_key_round,out_mask))]+=1
            key_guesses.append(bias)

        score,key_i = max((abs(key_guesses[i][1]-len(pt_ct_pairs)/2),i) 
            for i in range(256**len(out_indices) ))
        return self.get_key(key_i,key_bits)

    def recover_key(self,rounds,pt_ct_pairs):
        def distinct_io(rounds):
            def permute_block(i):
                x = self.get_mask([i])
                for _ in range(rounds):
                    x = self.perm(x)
                x = bin(int.from_bytes(x,'big'))[2:].zfill(self.BLOCK_SIZE)
                return x.index('1')
            outs = [None for i in range(self.NUM_SBOX)]
            for i in range(self.BLOCK_SIZE):
                v = permute_block(i)
                outs[v//8] = i,v
                if all(outs):
                    break
            return outs
        recovered_keys = []
        for level in range(rounds):
            key = bytes(self.NUM_SBOX)
            for i,v in distinct_io(rounds-1-level):
                key_bits = self.parity_bias([i],[v],pt_ct_pairs,recovered_keys)
                key = mask_or(key,key_bits)
                print(key)
            recovered_keys.append(key)
        return recovered_keys

def parity(x):
    res = 0
    while x:
        res^=1
        x=x&(x-1)
    return res

def parity_bytes(value:bytes):
    return reduce(xor,map(parity,value))

def mask_and(value,mask):
    return [a&b for a,b in zip(value,mask)]

def mask_or(value,mask):
    return bytes([a|b for a,b in zip(value,mask)])

def calc_bias(sbox):
    n = len(sbox)
    bias = Counter({(i,j):-(n//2) for i in range(1,n) for j in range(1,n)})
    for imask in tqdm(range(1,n),desc='calculating sbox bias'):
        for omask in range(1,n):
            for i in range(n):
                bias[(imask,omask)]+= parity(sbox[i]&omask)^parity(i&imask)==0
    matrix = [[bias[(i,j)] for i in range(n)] for j in range(n)]
    return bias

s = SPN(SBOX,PBOX,b'flag{151121d998f',4)

#n=3
#for x in tqdm(itertools.product(range(256),repeat=n),total=256**n):
#    h = get_hash(bytes(x))
#    if h.startswith('000000'):
#        print(h,bytes(x))
