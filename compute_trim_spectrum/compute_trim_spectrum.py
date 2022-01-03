#!/usr/bin/sage

# this script needs sboxU

from sage.all import *
from sboxU import *
from random import *


# as an example, we check for APN trims in the trim spectra of the EA-equivalence classes of the non-quadratic APN function in dimension six
S = [0,0,0,8,0,26,40,58,0,33,10,35,12,55,46,29,0,11,12,15,4,21,32,57,20,62,18,48,28,44,50,10,0,6,18,28,10,22,48,36,8,47,16,63,14,51,62,11,5,24,27,14,11,12,61,50,25,37,13,57,27,61,39,9]
for i in range(len(S)):
	S[i] = int(S[i])


# this computes and returns the trims spectrum of s
def all_trims(s):
    N = int(log(len(s), 2))
    # precomputing all the linear mappings
    mask = (1 << (N-1)) - 1
    all_L_a = [None]
    all_L_b = [None]
    not_orthogonal = [None]
    for a in range(1, 2**N):
        l = FastLinearMapping(F_2t_to_space(orthogonal_basis([a], N), N))
        lut = [l(x) for x in range(0, 2**N)]
        all_L_a.append(lut)
        lut_inv = inverse(lut)
        all_L_b.append([lut_inv[x] & mask for x in range(0, 2**N)])
        for ortho in range(1, 2**N):
            if scal_prod(ortho, a) == 1:
                not_orthogonal.append(ortho)
                break
    # looping over all possible trims
    result = []
    for b in range(1, 2**N):
	g = not_orthogonal[b]
        L_out = all_L_b[g]
        for a in range(1, 2**N):
		e_0 = 0
        	e_1 = not_orthogonal[a]
        	L_in = all_L_a[a]
            	for e in [e_0, e_1]:
                	f = []
                	for x in range(0, 2**(N-1)):
                    		s_xe = s[oplus(L_in[x], e)]
                    		f.append( L_out[oplus(s_xe, b*scal_prod(s_xe, g))] )
                	result.append(f)
    return result



EAC = enumerate_ea_classes(S)
print('checking ' + repr(len(EAC)) + ' EA classes')
for s in EAC:
	print('\nchecking the following function with algebraic degree ' + repr(algebraic_degree(s)) + ':')
	print(s)
	ts = all_trims(s)
	print('APN trims:')
	for k in ts:
		if(max(differential_spectrum(k))==2):
			print(k)
			print('algebraic degree ' + repr(algebraic_degree(k)))



