#!/usr/bin/sage
#-*- Python -*-

from sboxU import *
from collections import defaultdict



def func_label(s):
    """Returns a string that is intended to define the CCZ-class of a
    function. Assumes that `s` is a quadratic APN function.

    For N != 5, it relies on the ortho-derivative by returning a
    string presentation of the differential and extended Walsh spectra
    of the ortho-derivative of `s`. For N=5, we know that the only two
    quadratic APN functions CCZ-equivalence classes contain functions
    for which the differential and linear properties of the
    ortho-derivative are identical. As a consequence, we instead rely
    on a direct (but very costly) CCZ-equivalence test.

    """
    if len(s) == 2**5:
        if s == all_funcs[5][0]:
            return "n=5, 0"
        elif s == all_funcs[5][1]:
            return "n=5, 1"
        elif are_ccz_equivalent(s, all_funcs[5][0]):
            return "n=5, 0"
        else:
            return "n=5, 1"
    o = ortho_derivative(s)
    result = "ortho dif: {} ortho wal: {}".format(
        pretty_spectrum(differential_spectrum(o)),
        pretty_spectrum(walsh_spectrum(o), absolute=True),
    )
    return result
            

def not_orthogonal_elmt(a):
    """Returns an element which is not orthogonal to `a` for the usual
    scalar product in (F_2)^n."""
    result = 1
    while scal_prod(result, a) != 1:
        result += 1
    return result


def all_apn_trimmings(s, n):
    """Interpreting `s` as the lookup table of a function operating on `n`
    bits, returns a list containing all the trimmings of this function
    that are APN. Thus, may return an empty list.

    It is assumed that the global variables ALL_A, NOT_ORTHOGONAL and
    ALL_B have been setup to contain the lookup table of all the needed
    linear mappings.

    """
    result = []
    for a in range(1, 2**n):
        e_0 = 0
        e_1 = NOT_ORTHOGONAL[a]
        L_in = ALL_L_A[a]
        for e in [e_0, e_1]:
            for b in range(1, 2**n):
                L_out = ALL_L_B[b]
                g = NOT_ORTHOGONAL[b]
                f = []
                for x in range(0, 2**(n-1)):
                    s_xe = s[oplus(L_in[x], e)]
                    f.append( L_out[oplus(s_xe, b*scal_prod(s_xe, g))] )
                if is_differential_uniformity_smaller_than(f, 2):
                    result.append(f)
    return result


def pretty_polynomial_string(s):
    """Returns a pretty representation of the polynomial whose LUT is
    `s`. Assumes that the global variables `POLY_RING` and `FIELD`
    correspond to a field length that is coherent with the size of `s`.

    """
    p = POLY_RING.lagrange_polynomial(
        [(FIELD.fetch_int(i), FIELD.fetch_int(s[i])) for i in range(0, len(s))]
    )
    result = ""
    for i, k in enumerate(p):
        if k == 1:
            result += "X^{:d} + ".format(i)
        elif k == FIELD.gen():
            result += "g X^{:d} + ".format(i)
        elif k != 0:
            result += "g^{" + k._log_repr() + "}X^{" + str(i) + "} + "
    return result[:-2]


if __name__ == '__main__':
    # getting all known functions contained in sboxU
    from sboxU.known_functions import *

    # storing them in a unique data structure according to the number
    # of bits on which they operate
    all_funcs = {
        3: [[0, 1, 3, 4, 5, 6, 7, 2]],
        4: [[0,0,0,1,0,2,4,7,0,4,6,3,8,14,10,13]],
        5: [[0,0,0,1,0,2,4,7,0,4,8,13,16,22,28,27,0,8,16,25,5,15,17,26,22,26,14,3,3,13,31,16],
            [0,0,0,1,0,2,4,7,0,4,8,13,16,22,28,27,0,8,16,25,5,15,17,26,27,23,3,14,14,0,18,29]],
        6: sixBitAPN.all_quadratics(),
        7: sevenBitAPN.all_quadratics(),
        # 8: eightBitAPN.all_quadratics(),
    }            

    # the options for the graph to look the way it does in our paper
    print("""DiGraph {
graph [pad="0.05", nodesep="0.05", ranksep="6.5"];
splines="false";
node[shape = point, label="", color="red", fillcolor="red", width="0.25"];
edge[arrowsize="0.4"];""")

    # the rest of this file extracts information about the trimming
    # graph of known quadratic APN functions.
    index = 0  # used to assign a unique index to all functions considered
    nodes = [] # the nodes of the graph (i.e., quadratic APN
               # functions), where each function is represented by its
               # "label" as returned by `func_label`
    edges = [] # the edges of the graph (i.e., trimming connections)
    funcs_reversed_index = {} # stores the index of each function, the
                              # key being their labels
    
    for N in sorted(all_funcs.keys()):
        # we set global variables related to field arithmetic in order
        # to be able to print the univariate representations of
        # trimless functions
        FIELD = GF(2**N)
        POLY_RING = PolynomialRing(FIELD, "x")
        # Precomputations common to all functions with this N
        print("// --- ", N)       
        MASK = (1 << (N-1)) - 1
        ALL_L_A = [None] # contains the LUT of the linear functions
                         # mapping x \in F_2^{n-1} to a^\perp
        ALL_L_B = [None] # contains the LUT of linear projections
                         # mapping x \in F_2^{n} to F_2^{n-1} such
                         # that B(v) = 0 for a v that is orthogonal
                         # to b.
        for a in range(1, 2**N):
            l = FastLinearMapping(F_2t_to_space(orthogonal_basis([a], N), N))
            lut = [l(x) for x in range(0, 2**N)]
            ALL_L_A.append(lut)
            lut_inv = inverse(lut)
            ALL_L_B.append([lut_inv[x] & MASK for x in range(0, 2**N)])
        # we also precompute an element not orthogonal to each element of F_2^n
        NOT_ORTHOGONAL = [None] + [not_orthogonal_elmt(x) for x in range(1, 2**N)]

        # we are now ready to loop over all N-bit functions
        for s in all_funcs[N]:
            no_trims = [] # stores all the functions without APN trims
            # we store s in all the relevant data structures
            l = func_label(s)
            nodes.append(index)
            funcs_reversed_index[l] = index
            # we now look at the trimmings of s (if it operates on
            # strictly more than the minimum number of bits
            # considered, otherwise its trims will be useless).
            if N > min(all_funcs.keys()):
                # we generate all the APN trimmings
                truncated_children = defaultdict(int)
                for t in all_apn_trimmings(s, N):
                    child_index = funcs_reversed_index[func_label(t)]
                    truncated_children[child_index] += 1
                    if N == 6 and len(truncated_children.keys()) == 2:
                        # this `if` is special shortcut to save time
                        # when investigating the trimmings of 6 bit
                        # functions (since the 5-bit label imply a ccz
                        # equivalence check, they are very slow)
                        break # we leave because both functions have
                              # been reached
                if len(truncated_children) > 0:
                    # if some trimmings were found, we store the
                    # corresponding edges
                    for c in truncated_children.keys():
                        edges.append([index, c])
                        print("node_{} -> node_{};".format(index, c))
                else:
                    # if not, we store s as such
                    no_trims.append(s)
                    print("// trimless: ", pretty_polynomial_string(s))
            index += 1
        print("// no trims for {:d} functions:".format(len(no_trims))) 

    print("}") # closing the curly brace in the graph definition
