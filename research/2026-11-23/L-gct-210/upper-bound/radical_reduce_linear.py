"""Iteratively use forced radical membership and exact higher gradients."""
from itertools import combinations, permutations
from collections import Counter
from pathlib import Path

import sympy as s

D=Path(__file__).resolve().parent
percandidates=[[(r,c) for r,c in zip(rr,cc)]
      for k in range(3,6)
      for rr in combinations(range(5),k)
      for cc in permutations(range(5),k)]
record=Counter()
examples={}
for line in (D/'radical_supports.txt').read_text().splitlines():
    m,*rows=map(int,line.split())
    at=[(i,j) for i in range(5) for j in range(5) if rows[i]&(1<<j)]
    ind={k:j for j,k in enumerate(at)}
    profiles=[[ind[k] for k in f] for f in percandidates if all(k in ind for k in f)]
    mat=s.Matrix(m,m,lambda a,b: int(at[a][0]!=at[b][0] and at[a][1]!=at[b][1]))
    p=s.eye(m).col_insert(0,s.zeros(m,0))[:,:-1]-s.eye(m)[:,-1]*s.ones(1,m-1)
    q=p.T*mat*p
    k=s.eye(m-1)
    count=0
    reason='fixed'
    while True:
        qpart=k.T*q*k
        null=qpart.nullspace()
        bound=(k.cols+len(null))//2
        if bound<9:
            reason='hessian'
            break
        if bound>9:
            raise ValueError('unexpected Witt bound')
        zrows=[]
        for v0 in null:
            v=p*k*v0
            val=s.zeros(3,1)
            g=s.zeros(3,m)
            for f in profiles:
                degree=len(f)-3
                val[degree]+=s.prod(v[e] for e in f)
                for j in f:
                    g[degree,j]+=s.prod(v[e] for e in f if e!=j)
            if val!=s.zeros(3,1):
                reason='nonlevel radical'
                break
            zrows.extend((g*p*k).tolist())
        if reason=='nonlevel radical':
            break
        zg=s.Matrix(zrows)
        d=zg.nullspace()
        if len(d)==k.cols:
            break
        if not len(d):
            reason='gradient'
            break
        k=k*s.Matrix.hstack(*d)
        count+=1
    record[m,count,reason]+=1
    examples.setdefault((m,count,reason),rows)
print(record)
print(examples)
