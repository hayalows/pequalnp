"""Bound extension dimensions by exact Gaussian-rational derivative samples."""
from itertools import permutations
from math import prod
from random import Random
import sympy as S

perms = list(permutations(range(5)))
I = S.I

def basis_cross():
    ans=[]
    for j in range(1,5):
        v=[0]*25
        v[0], v[j] = -1,1
        ans.append(v)
    for i in range(2,5):
        v=[0]*25
        v[5], v[5*i] = -1,1
        ans.append(v)
    return ans

def basis_fourth_root():
    ans=basis_cross()[:4]
    for j in range(3):
        v=[0]*25
        for i,a in enumerate([1,I,-1,-I],start=1):
            v[5*i+j]=a
        ans.append(v)
    return ans

def gradients(Space, seed=57):
    rng=Random(seed)
    grads=[]
    for k in range(54):
        coeff=[rng.choice([-2,-1,0,1,2]) for _ in Space]
        entries=[S.expand(1+sum(a*b[j] for a,b in zip(coeff,Space))) for j in range(25)]
        gradient=[0]*25
        for perm in perms:
            inds=[5*i+j for i,j in enumerate(perm)]
            for h,j in enumerate(inds):
                gradient[j] += prod(entries[x] for x in inds if x!=j)
        grads.append([S.expand(z) for z in gradient])
    return grads

for name, space in [('cross',basis_cross()),('fourth-root',basis_fourth_root())]:
    G = S.Matrix(gradients(space))
    assert (G*S.Matrix(space).T).applyfunc(S.expand) == S.zeros(G.rows,len(space))
    # Exact elimination over the Gaussian rational field.
    from sympy.polys.matrices import DomainMatrix
    null=DomainMatrix.from_Matrix(G, extension=True).to_field().nullspace()
    print(name, 'dimension',len(space),'sampled derivative nullity',null.shape[0],flush=True)
    if null.shape[0]>len(space):
        v=null.to_Matrix()[-1, :]
        v=[S.simplify(a/next(b for b in v if b!=0)) for a in v]
        print('extra direction', v)
        trace=[sum(prod(1+z*v[5*i+j] for i,j in enumerate(perm)) for perm in perms) for z in range(6)]
        print('permanents along extra direction', [S.simplify(a) for a in trace])
