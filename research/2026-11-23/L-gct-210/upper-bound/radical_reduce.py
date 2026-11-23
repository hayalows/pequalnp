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
fixed=[]
for line in (D/'radical_supports.txt').read_text().splitlines():
    m,*rows=map(int,line.split())
    at=[(i,j) for i in range(5) for j in range(5) if rows[i]&(1<<j)]
    ind={k:j for j,k in enumerate(at)}
    profiles=[[ind[k] for k in f] for f in percandidates if all(k in ind for k in f)]
    mat=s.Matrix(m,m,lambda a,b: int(at[a][0]!=at[b][0] and at[a][1]!=at[b][1]))
    p=s.eye(m)[:,:-1]-s.eye(m)[:,-1]*s.ones(1,m-1)
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
        quads=[]
        tests=null+[x+y for x,y in combinations(null,2)]
        for v0 in tests:
            v=p*k*v0
            val=s.zeros(3,1)
            g=s.zeros(3,m)
            h=[s.zeros(m,m) for _ in range(3)]
            for f in profiles:
                degree=len(f)-3
                val[degree]+=s.prod(v[e] for e in f)
                for j in f:
                    g[degree,j]+=s.prod(v[e] for e in f if e!=j)
                for j,l in combinations(f,2):
                    valh=s.prod(v[e] for e in f if e!=j and e!=l)
                    h[degree][j,l]+=valh
                    h[degree][l,j]+=valh
            if val!=s.zeros(3,1):
                reason='nonlevel radical'
                break
            zrows.extend((g*p*k).tolist())
            quads.extend(k.T*p.T*hh*p*k for hh in h if hh != s.zeros(m,m))
        if reason=='nonlevel radical':
            break
        if quads:
            combo=sum(quads, s.zeros(k.cols,k.cols))
            forms=[*quads, combo]
            if any((k.cols + len((qpart+v*i).nullspace()))//2<9 for v in forms for i in (1,2,3)):
                reason='polarized Hessian'
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
    if reason=='fixed': fixed.append((m, *rows))
    record[m,count,reason]+=1
    examples.setdefault((m,count,reason),rows)
print(record)
print(examples)
(D/'radical_fixed.txt').write_text(''.join(' '.join(map(str, x))+'\n' for x in fixed))
