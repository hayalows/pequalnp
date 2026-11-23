"""Check necessary membership of radical in any dimension-nine level space."""
from itertools import combinations, permutations
from collections import Counter
from pathlib import Path

import sympy as s

N=5
D=Path(__file__).resolve().parent
record=Counter()
examples={}
for line in (D/'radical_supports.txt').read_text().splitlines():
    size,*rows=map(int,line.split())
    at=[(i,j) for i in range(N) for j in range(N) if rows[i]&(1<<j)]
    mat=s.Matrix(size,size,lambda a,b: int(at[a][0]!=at[b][0] and at[a][1]!=at[b][1]))
    q=mat[:-1,:-1]-s.ones(size-1,1)*mat[-1,:-1]-mat[:-1,-1]*s.ones(1,size-1)
    v=q.nullspace()
    if not v:
        record[size, 'modular_rank_loss']+=1
        continue
    assert len(v)==1
    a=s.zeros(N)
    for (i,j),k in zip(at, list(v[0])+[-sum(v[0])]):
        a[i,j]=k
    sums=[sum(s.prod(a[i,j] for i,j in zip(rr,cc))
                for rr in combinations(range(N),k)
                for cc in permutations(range(N),k))
          for k in range(1,6)]
    assert sums[:2]==[0,0]
    first_nonzero=next((i+1 for i,z in enumerate(sums) if z), None)
    record[size, first_nonzero]+=1
    examples.setdefault((size,first_nonzero), (rows, a, sums))
print(record)
for k,v in examples.items():
    print(k,v)
