from itertools import permutations
import sympy as s
from collections import Counter
import argparse
import sys
ap=argparse.ArgumentParser()
ap.add_argument('mode');ap.add_argument('prime',type=int)
a=ap.parse_args()
z=s.symbols('z:5');x=s.symbols('x')
mult=Counter(tuple(sorted((c-r)%5 for r,c in enumerate(p))) for p in permutations(range(5)))
P=sum(v*s.prod(z[i] for i in k) for k,v in mult.items())
if a.mode=='sing':
    polys=[s.diff(P,a).subs(z[0],1) for a in z]
elif a.mode=='flat':
    perp=s.Poly(P.subs(dict(zip(z,[1+x*y for y in z])),simultaneous=True),x)
    polys=[perp.nth(j).subs(z[0],1) for j in range(1,6)]
else:
    raise ValueError
print('starting',a.mode,a.prime,flush=True)
G=s.groebner(polys,*z[1:],modulus=a.prime,order='grevlex')
print('groebner basis length',len(G),flush=True)
print('zero dimensional affine ideal',G.is_zero_dimensional)
for g in G:print(g,flush=True)
