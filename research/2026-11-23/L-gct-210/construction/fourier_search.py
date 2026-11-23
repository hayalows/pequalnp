"""Search tensor subsets of separate permutation-cycle Fourier bases.

A linear space spanned by chosen rank-one tensors is admissible exactly
when the coefficient supports of the row and column products are disjoint
outside degree zero. Finite-field coefficient evaluations can exclude a
candidate over the cyclotomic integers when they are nonzero. Any surviving
candidate still needs verification over C.
"""
from collections import defaultdict
from itertools import combinations_with_replacement, permutations
from math import gcd
import sys
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix
from sympy import isprime, primitive_root

P = 2521
assert isprime(P) and (P - 1) % 60 == 0
G = int(primitive_root(P))
TYPES = ((5,), (4, 1), (3, 2), (3, 1, 1), (2, 2, 1), (2, 1, 1, 1), (1, 1, 1, 1, 1))

def basis(typ):
    vectors = []
    base = 0
    for d in typ:
        root = pow(G, (P - 1) // d, P)
        for j in range(d):
            vectors.append([pow(root, j * i, P) if 0 <= i < d else 0 for i in range(-base, 5 - base)])
        base += d
    return vectors

def grouped_coeffs(b):
    coefficients = {(): 1}
    for i in range(5):
        new = defaultdict(int, coefficients)
        for powers, coefficient in coefficients.items():
            for j in range(5):
                if b[j][i]:
                    factors = tuple(sorted(powers + (j,)))
                    new[factors] = (new[factors] + coefficient * b[j][i]) % P
        coefficients = new
    return {degree: [powers for powers in combinations_with_replacement(range(5), degree)
                     if coefficients.get(powers,0)]
            for degree in range(1,6)}

def forbidden_sets(bs, cs):
    forbidden = []
    seen = set()
    for degree in range(1, 6):
        possible = set()
        for left in bs[degree]:
            for right in cs[degree]:
                for r in set(permutations(right)):
                    mask = 0
                    for i, j in zip(left, r):
                        mask |= 1 << (5 * i + j)
                    possible.add(mask)
        for mask in sorted(possible, key=int.bit_count):
            if mask not in seen and not any(mask & prev == prev for prev in forbidden):
                forbidden.append(mask)
                seen.add(mask)
    return forbidden

def solve(forbidden):
    mat = lil_matrix((len(forbidden),25), dtype=np.int8)
    for i, mask in enumerate(forbidden):
        mat[i, [j for j in range(25) if mask >> j & 1]] = 1
    res = milp(-np.ones(25), integrality=np.ones(25), bounds=Bounds(0,1),
               constraints=LinearConstraint(mat.tocsc(), 0,
                   np.array([mask.bit_count() - 1 for mask in forbidden])),
               options={'time_limit':15})
    return res, [] if res.x is None else [(j//5,j%5) for j,x in enumerate(res.x) if x > .5]

def main():
    bc = [grouped_coeffs(basis(t)) for t in TYPES]
    maximum = 0
    for i, u in enumerate(TYPES):
        for j in range(i,len(TYPES)):
            v = TYPES[j]
            forbidden = forbidden_sets(bc[i],bc[j])
            res, selection = solve(forbidden)
            print(u, v, len(forbidden), res.status, len(selection), selection, flush=True)
            maximum = max(maximum, len(selection))
    print('maximum',maximum)

if __name__ == '__main__':
    main()
