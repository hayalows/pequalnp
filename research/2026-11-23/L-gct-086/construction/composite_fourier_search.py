"""Exact support constraints for small composite rectangular Fourier grids."""
import argparse
from collections import defaultdict
from itertools import permutations, combinations_with_replacement
from math import factorial, lcm
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix
from sympy import prime, isprime, primitive_root

def grouped_coeffs(n, cutoff, p, g):
    root=pow(g,(p-1)//n,p)
    weights=[[pow(root,j*i,p) for j in range(n)] for i in range(n)]
    co={():1}
    for w in weights:
        new=defaultdict(int,co)
        for fs,v in co.items():
            if len(fs)>=cutoff:continue
            for j in range(n):
                gs=tuple(sorted((*fs,j)))
                new[gs]=(new[gs]+v*w[j])%p
        co=new
    return {k:[f for f in combinations_with_replacement(range(n),k)
                 if co.get(f,0)] for k in range(1,cutoff+1)}

def forbidden(R,S,p,g):
    l,r=(grouped_coeffs(k,min(R,S),p,g) for k in (R,S))
    forb=[]
    for k in range(1,min(R,S)+1):
        poss=set()
        perms={b:tuple(set(permutations(b))) for b in r[k]}
        for a in l[k]:
            for arrangements in perms.values():
                for b in arrangements:
                    mask=0
                    for i,j in zip(a,b):
                        mask|=1<<(i*S+j)
                    poss.add(mask)
        by_size={}
        for mask in sorted(poss,key=int.bit_count):
            if all(mask & old!=old for old in forb):
                by_size[mask]=None
                forb.append(mask)
        print(f'degree {k}: cumulative {len(forb)} constraints',flush=True)
    return forb

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('R',type=int)
    parser.add_argument('S',type=int)
    parser.add_argument('--deadline',type=int,default=30)
    args=parser.parse_args()
    R,S=args.R,args.S
    period=lcm(R,S)
    p=(factorial(max(R,S))//period+1)*period+1
    while not isprime(p):p+=period
    g=int(primitive_root(p))
    print('size',R,S,'prime',p,flush=True)
    f=forbidden(R,S,p,g)
    m=lil_matrix((len(f)+1,R*S),dtype=np.int8)
    for k,mask in enumerate(f):
        m[k,[j for j in range(R*S) if mask>>j&1]]=1
    m[-1,:]=1
    sol=milp(np.zeros(R*S),integrality=np.ones(R*S),bounds=Bounds(0,1),
             constraints=LinearConstraint(m.tocsc(),[0]*len(f)+[max(R,S)+1],
                                          [t.bit_count()-1 for t in f]+[np.inf]),
             options={'time_limit':args.deadline})
    print('feasibility status',sol.status,sol.message,flush=True)
    if sol.x is not None:
        print('size',sum(sol.x>.5),'cells',[(j//S,j%S) for j in range(R*S) if sol.x[j]>.5],flush=True)

if __name__=='__main__':
    main()
