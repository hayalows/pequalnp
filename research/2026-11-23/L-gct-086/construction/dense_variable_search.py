"""Tightly grouped disjoint weight sets have no one-center star witnesses."""
from random import Random
from itertools import combinations
from weighted_blocks import run

gen=Random(20866)
seen=set()
for r,s in [(6,6),(7,7),(8,8),(8,9),(9,9),(10,10),(11,11)]:
    values=list(range((r+1)//2,r))
    for sizes in [1,2,3]:
        for _ in range(6):
            gen.shuffle(values)
            k=min(sizes,len(values)//2)
            if k==0:continue
            va,vb=values[:k],values[k:2*k]
            a=tuple(sorted(gen.choices(va,k=r)))
            b=tuple(sorted(gen.choices(vb,k=s)))
            if (a,b) in seen:continue
            seen.add((a,b))
            print(a,b,run(a,b,deadline=4),flush=True)
