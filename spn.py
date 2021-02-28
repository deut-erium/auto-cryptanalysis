#from pwn import remote
from collections import Counter
from pprint import pprint
from itertools import product,chain,combinations
from functools import reduce
from operator import xor
from tqdm import tqdm
from math import log2
import random
from z3 import *
from pairs import pairs
import time

sbox = [14, 4, 13, 1, 2, 15, 11, 8, 3, 10, 6, 12, 5, 9, 0, 7]
pbox = [0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14, 3, 7, 11, 15]


SBOX = [237, 172, 175, 254, 173, 168, 187, 174, 53, 188, 165, 166, 161, 162, 131, 227, 191, 152, 63, 182, 169, 136, 171, 184, 149, 148, 183, 190, 181, 177, 163, 186, 207, 140, 143, 139, 147, 138, 155, 170, 134, 132, 135, 18, 193, 128, 129, 130, 157, 156, 151, 158, 153, 24, 154, 11, 141, 144, 21, 150, 146, 145, 179, 22, 245, 124, 236, 206, 105, 232, 43, 194, 229, 244, 247, 242, 233, 224, 235, 96, 253, 189, 219, 234, 241, 248, 251, 226, 117, 252, 213, 246, 240, 176, 249, 178, 205, 77, 231, 203, 137, 200, 107, 202, 133, 204, 228, 230, 225, 196, 195, 198, 201, 221, 199, 95, 216, 217, 159, 218, 209, 214, 215, 222, 83, 208, 211, 243, 44, 40, 46, 142, 32, 36, 185, 42, 45, 38, 47, 34, 33, 164, 167, 98, 41, 56, 55, 126, 57, 120, 59, 250, 37, 180, 119, 54, 52, 160, 51, 58, 5, 14, 79, 30, 8, 12, 13, 10, 68, 0, 39, 6, 1, 16, 3, 2, 23, 28, 29, 31, 27, 9, 7, 62, 4, 60, 19, 20, 48, 17, 87, 26, 239, 110, 111, 238, 109, 104, 35, 106, 101, 102, 103, 70, 49, 100, 99, 114, 61, 121, 223, 255, 88, 108, 123, 122, 84, 92, 125, 116, 112, 113, 115, 118, 197, 76, 15, 94, 73, 72, 75, 74, 81, 212, 69, 66, 65, 64, 97, 82, 93, 220, 71, 90, 25, 89, 91, 78, 85, 86, 127, 210, 80, 192, 67, 50]

PBOX = [1, 57, 6, 31, 30, 7, 26, 45, 21, 19, 63, 48, 41, 2, 0, 3, 4, 15, 43, 16, 62, 49, 55, 53, 50, 25, 47, 32, 14, 38, 60, 13, 10, 23, 35, 36, 22, 52, 51, 28, 18, 39, 58, 42, 8, 20, 33, 27, 37, 11, 12, 56, 34, 29, 46, 24, 59, 54, 44, 5, 40, 9, 61, 17]

SBOX2 = [13, 18, 20, 55, 23, 24, 34, 1, 62, 49, 11, 40, 36, 59, 61, 30, 33, 46, 56, 27, 41, 52, 14, 45, 0, 29, 39, 4, 8, 7, 17, 50, 2, 54, 12, 47, 35, 44, 58, 25, 10, 5, 19, 48, 43, 31, 37, 6, 21, 26, 32, 3, 15, 16, 22, 53, 38, 57, 63, 28, 60, 51, 9, 42]

class SPN:
    def __init__(self,SBOX,PBOX,key,rounds):
        self.SBOX = SBOX
        self.PBOX = PBOX
        self.SINV = [SBOX.index(i) for i in range(len(SBOX))]
        self.PINV = [PBOX.index(i) for i in range(len(PBOX))]
        self.BLOCK_SIZE = len(PBOX)
        self.BOX_SIZE = int(log2(len(SBOX)))
        self.NUM_SBOX = len(PBOX)//self.BOX_SIZE
        self.rounds = rounds
        self.round_keys = self.expand_key(key,rounds)
        #self.BIAS = calc_bias(SBOX)

    def perm(self,inp:int) -> int:
        ct = 0
        for i,v in enumerate(self.PBOX):
            ct |= (inp>>(self.BLOCK_SIZE-1-i)&1)<<(self.BLOCK_SIZE-1-v)
        return ct

    def inv_perm(self,inp:int) -> int:
        ct = 0
        for i,v in enumerate(self.PINV):
            ct |= (inp>>(self.BLOCK_SIZE-1-i)&1)<<(self.BLOCK_SIZE-1-v)
        return ct

    def sbox(self,inp:int) -> int:
        ct,BS = 0,self.BOX_SIZE
        for i in range(self.NUM_SBOX):
            ct |= self.SBOX[(inp>>(i*BS))&((1<<BS)-1)]<<(BS*i)
        return ct

    def inv_sbox(self,inp:int) -> int:
        ct,BS = 0,self.BOX_SIZE
        for i in range(self.NUM_SBOX):
            ct |= self.SINV[(inp>>(i*BS))&((1<<BS)-1)]<<(BS*i)
        return ct
         
    def int_to_list(self,inp):
        BS = self.BOX_SIZE
        return [ (inp>>(i*BS))&((1<<BS)-1) 
                for i in range(self.NUM_SBOX-1,1,-1) ]

    def list_to_int(self,lst):
        res = 0
        for i,v in enumerate(lst[::-1]):
            res |= v<<(i*self.BOX_SIZE)
        return res

    def expand_key(self,key,rounds):
        if isinstance(key,(list)):
            key = self.list_to_int(key)
        elif isinstance(key,(bytes,bytearray)):
            key = int.from_bytes(key,'big')
        key = key&((1<<self.BLOCK_SIZE)-1)
        keys = [key]
        for _ in range(rounds):
            key = ROTL(key,self.BOX_SIZE,self.BLOCK_SIZE)
            keys.append(key)
        return keys

    def enc(self,pt:int) -> int:
        ct = pt^self.round_keys[0]
        for round_key in self.round_keys[1:]:
            ct = self.sbox(ct)
            ct = self.perm(ct)
            ct^=round_key
        return ct
    
    def dec(self,ct,round_keys,full=True):
        # partial decryption
        # round keys in reverse order
        last_key = 0
        if full:
            last_key = round_keys[-1]
            round_keys = round_keys[:-1]
        for round_key in round_keys:
            ct^= round_key
            ct = self.inv_perm(ct)
            ct = self.inv_sbox(ct)
        return ct^last_key
    
    def get_mask(self,bit_pos):
        mask = 0
        for bit in bit_pos:
            mask |= 1<<(self.BLOCK_SIZE-1-bit)
        return mask

    def get_templates(self,in_bits,out_bits):
        inp_mask = self.get_mask(in_bits)
        out_mask = self.get_mask(out_bits)
        out_indices = [self.BLOCK_SIZE-1-i
                       for i in range(self.BLOCK_SIZE) if (out_mask>>i)&1]
        out_blocks = {i//self.BOX_SIZE for i in out_indices}
        block_perms = self.perm( 
            int.from_bytes( bytes([
                (1<<(self.BOX_SIZE))-1 if i in out_blocks else 0 
                for i in range(self.NUM_SBOX)  
            ]),'big' ) 
        )
        
        key_bits = [i for i in range(self.BLOCK_SIZE) 
                    if (block_perms>>i)&1  ]
        return inp_mask,out_mask,len(out_blocks),key_bits

    def key_into_bits(self,n,key_bits):
        key_int = 0
        for b in key_bits:
            key_int |= (n&1)<<b
            n>>=1
        return key_int

    def parity_bias(self,in_bits,out_bits,pt_ct_pairs,round_keys_rev):
        inp_mask,out_mask,b_count,key_bits = self.get_templates(
            in_bits,out_bits)
        key_guesses = []
        for i in tqdm(range((1<<self.BOX_SIZE)**b_count)):
            key = self.key_into_bits(i,key_bits)
            bias = Counter()
            for pt,ct in pt_ct_pairs:
                ct_partial = self.dec(ct,round_keys_rev + [key],full=False)
                bias[parity((pt&inp_mask)^(ct_partial&out_mask))]+=1
            key_guesses.append(bias)
        score,key_i = max((abs(key_guesses[i][1]-len(pt_ct_pairs)/2),i) 
            for i in range( (1<<self.BOX_SIZE)**b_count ))
        print("bias:",score/(len(pt_ct_pairs)))
        return self.key_into_bits(key_i,key_bits)

    def permute_block(self,i,rounds):
        x = self.get_mask([i])
        for _ in range(rounds):
            x = self.perm(x)
        for i in range(self.BLOCK_SIZE-1,-1,-1):
            if (x>>i)&1:
                return self.BLOCK_SIZE-1-i

    def distinct_io(self,rounds):
        outs = [None for i in range(self.NUM_SBOX)]
        for i in range(self.BLOCK_SIZE):
            v = self.permute_block(i,rounds)
            outs[v//self.BOX_SIZE] = i,v
            if all(outs):
                break
        return outs

    def recover_key(self,rounds,pt_ct_pairs):
        recovered_keys = []
        for level in range(rounds):
            key = 0
            for i,v in self.distinct_io(rounds-1-level):
                key_bits = self.parity_bias([i],[v],pt_ct_pairs,recovered_keys)
                key |= key_bits
                print(self.int_to_list(key))
            recovered_keys.append(key)
            # save the round overhead of already decrypted keys
            #for i in range(len(pt_ct_pairs)):
            #   pt_ct_pairs[i][1] = self.dec(pt_ct_pairs[i][1],[key])
        return recovered_keys


def ROTL(value, bits, size): return \
            ((value % (1 << bits)) << (size - bits)) | (value >> bits)

def parity(x):
    res = 0
    while x:
        res^=1
        x=x&(x-1)
    return res


def bias_order(bias):
    return sorted(bias.items(),key=lambda x: abs(x[1]),reverse=True)


def calc_bias(sbox):
    n = len(sbox)
    bias = Counter({(i,j):-(n//2) for i in range(n) for j in range(n)})
    for imask in tqdm(range(n),desc='calculating sbox bias'):
        for omask in range(n):
            for i in range(n):
                bias[(imask,omask)]+= parity((sbox[i]&omask)^(i&imask))^1
    return bias

def calc_bias_no_sign(sbox):
    n = len(sbox)
    bias = calc_bias(sbox)
    for i in bias:
        bias[i]=abs(bias[i])#/n
    return bias


def get_optimal_masks(sbox,pbox,num_rounds,bias=None,non_zero=[0]):
    n = int(log2(len(sbox)))
    num_blocks = len(pbox)//n
    #print(n,num_blocks)
    if not bias:
        bias = calc_bias_no_sign(sbox)
    sboxf = Function('sbox',BitVecSort(n),BitVecSort(n),RealSort())
    def permutation(inp,oup,pbox):
        n = len(pbox)
        constraints = []
        for i,v in enumerate(pbox):
            constraints.append(
                Extract(n-1-i,n-1-i,inp)==Extract(n-1-v,n-1-v,oup)
            )
        return constraints
    constraints = []
    for i in range(2**n):
        for j in range(2**n):
            # just some pruning of very small biases
            if bias[(i,j)]>=2**(n//2):
                constraints.append(sboxf(i,j)==bias[(i,j)])
            else:
                constraints.append(sboxf(i,j)==0)
    s = Optimize()
    inps = [[BitVec('r{}_i{}'.format(r,i),n) for i in range(num_blocks)] 
            for r in range(num_rounds+1)]
    oups = [[BitVec('r{}_o{}'.format(r,i),n) for i in range(num_blocks)] 
            for r in range(num_rounds)]
    objectives = [
        # the actual objective, which is just product of bias [0,1/2]
        2**(num_blocks*num_rounds-1)*Product([
            sboxf(
                inps[i//num_blocks][i%num_blocks],
                oups[i//num_blocks][i%num_blocks]) 
            for i in range(num_blocks*num_rounds)
        ]),        
        # reducing optimization problem of product to sums 
        Sum([
            sboxf(
                inps[i//num_blocks][i%num_blocks],
                oups[i//num_blocks][i%num_blocks]) 
            for i in range(num_blocks*num_rounds)
        ]),
        # objective when the input biases are [0,2**n] just the final 
        # division
        2**(num_blocks*num_rounds-1)*Product([
            sboxf(
                inps[i//num_blocks][i%num_blocks],
                oups[i//num_blocks][i%num_blocks]) 
            for i in range(num_blocks*num_rounds)
        ])/((2**n)**(num_blocks*num_rounds))
    ]
    #for objective in objectives:
    s.maximize(objectives[1])
    s.add(constraints)
    s.add(Not(And( *[inps[0][i]==0 for i in range(num_blocks)])))
    # the last layer is input, which we would like to be
    # reduced to as few sboxes as possible
    for i in range(num_blocks):
        if i in non_zero:
            s.add(inps[-1][i]!=0)
        else:
            s.add(inps[-1][i]==0)
    #s.add(PbEq([(i!=0,1) for i in inps[-1]],1))
    for r in range(num_rounds):
        for i in range(num_blocks):
            s.add(Implies(inps[r][i]!=0,oups[r][i]!=0))
            s.add(Implies(inps[r][i]==0,oups[r][i]==0))
            s.add(
                Implies(
                    And(inps[r][i]!=0,oups[r][i]!=0),
                    sboxf(inps[r][i],oups[r][i])!=0
                )
            )
    for i in range(num_rounds):
        s.add(permutation(Concat(oups[i]),Concat(inps[i+1]),pbox))
    results = []
    #print("began searching")
    if s.check()==sat:
        m = s.model()
        inp_masks = [ m.eval( Concat(inps[i])).as_long() 
                     for i in range(num_rounds) ]
        oup_masks = [ m.eval( Concat(oups[i])).as_long() 
                         for i in range(num_rounds) ]
        total_bias = m.eval(objectives[2]).as_fraction()
        print("total bias:",total_bias)
        return inp_masks,oup_masks,total_bias

def get_all_pos_masks(sbox,pbox,num,num_key_blocks=1):
    n = int(log2(len(sbox)))
    num_blocks = len(pbox)//n
    bias = calc_bias_no_sign(sbox)
    round_masks = []
    try:
        for num_rounds in range(1,num+1):
            masks_this_round = []
            print("depth:",num_rounds)
            for pos in combinations(range(num_blocks),num_key_blocks):
                print("block positions:",pos)
                io_masks = get_optimal_masks(sbox,pbox,num_rounds,bias,pos)
                masks_this_round.append(io_masks)
            round_masks.append(masks_this_round)
    except KeyboardInterrupt:
        return round_masks
    return round_masks





#bias = calc_bias_no_sign(sbox)

def bias_from_masks(inp_masks,oup_masks,bias,n_boxes=4):
    n = int(log2(len(bias))/2)
    rounds = min(len(inp_masks),len(oup_masks))
    res = 2**(n_boxes*rounds-1)
    mod = (1<<4)-1
    for im,om in zip(inp_masks,oup_masks):
        for i in range(n_boxes):
            res*= bias[(im&mod,om&mod)]
            print(im&mod,om&mod,bias[(im&mod,om&mod)])
            im>>=4
            om>>=4
    return res


#s = SPN(SBOX,PBOX,b'ABCDEFGH',8)
s = SPN(sbox,pbox,1231231,4)
#pairs = []
#for i in range(20000):
#    x = random.getrandbits(s.BLOCK_SIZE)
#    pairs.append([x,s.enc(x)])

