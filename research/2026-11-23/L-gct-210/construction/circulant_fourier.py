from itertools import combinations_with_replacement
from collections import Counter
from math import prod,factorial
import sympy as s
def partition(seq):
    if not seq:
        yield []
    else:
        for p in partition(seq[1:]):
            yield [[seq[0]]] + p
            for i in range(len(p)):
                yield p[:i] + [[seq[0]] + p[i]] + p[i+1:]
def coeff(seq):
    distinct = sum(prod((-1)**(len(B)-1)*factorial(len(B)-1)*5
                       if sum(seq[i] for i in B)%5 == 0 else 0 for B in p)
        for p in partition(list(range(len(seq)))))
    return (distinct*distinct*factorial(5-len(seq)))//prod(factorial(c) for c in Counter(seq).values())
c=s.symbols('c1:5')
f=[s.expand(sum(coeff(q)*prod(c[i-1] for i in q) for q in combinations_with_replacement(range(1,5),d))) for d in range(2,6)]
for x in f:
    print(s.factor(x),flush=True)
for p in [7,11,13,17,19,31]:
    gg=s.groebner([z.subs(c[0],1) for z in f],*c[1:],modulus=p)
    print(p,list(gg),flush=True)
gg=s.groebner([z.subs(c[0],1) for z in f],*c[1:])
print('QQ',list(gg),flush=True)
