"""Test the variable-weight nonzero transport property for selected small profiles.

Each vertex has a prescribed positive integer weight. Find an incidence graph with
minimum degree strictly larger than the weight of every vertex and no nonzero
transport saturating all used vertices. The search for a fixed profile is
cutting-plane ILP: a feasible transport yields a forbidden support.
"""
from collections import defaultdict
from itertools import combinations, combinations_with_replacement, product
from math import gcd
from random import Random
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import lil_matrix
from time import perf_counter

def subsets(weights):
    result=defaultdict(list)
    for mask in range(1, 1 << len(weights)):
        inds=tuple(i for i in range(len(weights)) if (mask >> i) & 1)
        result[sum(weights[i] for i in inds)].append(inds)
    return result

def find_flow(selected, a, b, sides):
    """Return support as a cell-index tuple, or prove none by complete checks."""
    R,S=len(a),len(b)
    nw=[tuple(j for j in range(S) if selected[i*S+j]) for i in range(R)]
    for rows,cols in sides:
        cs=set(cols)
        adj=[tuple(j for j in nw[i] if j in cs) for i in rows]
        if any(sum(b[j] for j in e)<a[i] for i,e in zip(rows,adj)):continue
        if any(sum(a[i] for i in rows if j in nw[i])<b[j] for j in cols):continue
        # Integral augmenting paths in the selected transportation instance.
        residual={(-1,i):a[i] for i in rows}
        residual.update({(R+j,R+S):b[j] for j in cols})
        for i,e in zip(rows,adj):
            residual.update({(i,R+j):sum(a[k] for k in rows) for j in e})
        original=residual.copy()
        while any(residual.get((-1,i),0)>0 for i in rows):
            parents={-1:None}
            queue=[-1]
            for u in queue:
                for (x,v),capacity in residual.items():
                    if x==u and capacity and v not in parents:
                        parents[v]=u
                        queue.append(v)
                if R+S in parents:break
            if R+S not in parents:break
            path=[]
            u=R+S
            while u!=-1:
                p=parents[u]
                path.append((p,u));u=p
            amt=min(residual[e] for e in path)
            for e in path:
                residual[e]-=amt
                rev=e[::-1]
                residual[rev]=residual.get(rev,0)+amt
        else:
            return tuple(i*S+j for i,e in zip(rows,adj) for j in e
                         if residual[i,R+j]<original[i,R+j])
    return ()

def run(a,b,target=None,deadline=10):
    row,col=subsets(a),subsets(b)
    sides=[(r,c) for t in sorted(row.keys() & col.keys())
           for r,c in product(row[t],col[t])]
    R,S=len(a),len(b)
    forbid=set()
    # Seed with every isolated transportation edge and one-center star.
    for i,js in enumerate(a):
        for cols in col.get(js,[]):
            forbid.add(tuple(i*S+j for j in cols))
    for j,is_ in enumerate(b):
        for rows in row.get(is_,[]):
            forbid.add(tuple(i*S+j for i in rows))
    start=perf_counter()
    checked=0
    while (remaining:=deadline-(perf_counter()-start))>0:
        cons=[]
        if target is None:
            cons.extend((tuple(i*S+j for j in range(S)),a[i]+1,np.inf) for i in range(R))
            cons.extend((tuple(i*S+j for i in range(R)),b[j]+1,np.inf) for j in range(S))
        else:
            cons.append((tuple(range(R*S)),target,np.inf))
        cons.extend((f,0,len(f)-1) for f in sorted(forbid))
        mat=lil_matrix((len(cons),R*S),dtype=np.int8)
        for k,(indices,_,_) in enumerate(cons):
            mat[k,list(indices)]=1
        sol=milp(np.zeros(R*S),bounds=Bounds(0,1),
                 constraints=LinearConstraint(mat.tocsc(),[c[1] for c in cons],
                                              [c[2] for c in cons]),
                 integrality=np.ones(R*S),options={'time_limit':remaining})
        if sol.status==2:return 'UNSAT',checked,len(forbid),None
        if sol.x is None:return 'TIMEOUT',checked,len(forbid),None
        selected=sol.x>.5
        f=find_flow(selected,a,b,sides)
        checked+=1
        if not f:return 'FOUND',checked,len(forbid),[i for i,v in enumerate(selected) if v]
        assert f not in forbid
        forbid.add(f)
    return 'TIMEOUT',checked,len(forbid),None

def main():
    gen=Random(240)
    profiles=[]
    for r in range(3,8):
        for s in range(r,r+2):
            for _ in range(16):
                a=tuple(sorted(gen.choices(range(1,s),k=r)))
                b=tuple(sorted(gen.choices(range(1,r),k=s)))
                if (a,b) not in profiles:profiles.append((a,b))
    for i,(a,b) in enumerate(profiles,1):
        result=run(a,b,deadline=1)
        print(i,a,b,result,flush=True)

if __name__=='__main__':
    main()
