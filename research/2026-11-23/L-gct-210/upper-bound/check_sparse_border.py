"""Verify the two residual support orbits and their border coefficients."""
from itertools import combinations, permutations
from pathlib import Path
import sympy as s

root = Path(__file__).resolve().parent
core = s.Matrix(3, 3, s.symbols('b:9'))
h = s.symbols('h')
levels = [sum(s.prod(core[i,j] for i,j in zip(rr,cc))
              for rr in combinations(range(3),k)
              for cc in permutations(range(3),k))
          for k in range(1,4)]

def per(a):
    return sum(s.prod(a[i,j] for i,j in enumerate(p))
               for p in permutations(range(a.rows)))

def mix(matrix, a, b):
    return s.expand(sum(a[i]*b[j]*per(matrix.minor_submatrix(i,j))
               for i in range(4) for j in range(4)))

A = s.Matrix(4,4,lambda i,j: 1+core[i-1,j] if i>0 and j<3 else 1)
B = s.Matrix(4,4,lambda i,j: 1+h if (i,j)==(0,0) else 1+core[i-1,j-1] if i>0 and j>0 else 1)
b1,b2,b3=levels
assert s.expand(mix(A,(-3,1,1,1),(1,1,1,-3)) - (2*b1+4*b2+9*b3)) == 0
assert s.expand(mix(B,(3,-1,-1,-1),(-3,1,1,1)) + (2*b1+18*h+4*b2+4*h*b1+9*b3+h*b2)) == 0
print('Exact border coefficients verified.')

def col_perms(shape):
    return {tuple(sorted(sum(1<<p[i] for i in range(5) if (row>>i)&1) for row in shape))
            for p in permutations(range(5))}
assert len(col_perms([1,15,15,15,31]))==len(col_perms([3,29,29,29,31]))==20

fixed={18:set(),19:set()}
for line in (root/'radical_fixed.txt').read_text().splitlines():
    size, *rows=map(int,line.split())
    fixed[size].add(tuple(rows))
assert fixed[18]==col_perms([1,15,15,15,31])
assert fixed[19]==col_perms([3,29,29,29,31])
print('Each residual support list consists of one full column-permutation orbit.')

def for_shape(shape, edge_values=None):
    cells = [(i,j) for i in range(5) for j in range(5) if shape[i]&(1<<j)]
    n = len(cells)
    rowcol = s.Matrix(n,n,lambda i,j: int(cells[i][0]!=cells[j][0] and cells[i][1]!=cells[j][1]))
    e=s.ones(1,n)
    p=s.Matrix.hstack(*e.nullspace())
    def vec(entries):
        return s.Matrix([entries.get(i,0) for i in cells])
    def mat(x):
        a=s.zeros(5)
        for ij,v in zip(cells,x):
            a[ij]=v
        return a
    def entry_sum(rect):
        return s.Matrix([[int(ij in rect) for ij in cells]])
    return rowcol, p, vec, mat, entry_sum

q,p,vec,mat,entry_sum=for_shape([1,15,15,15,31])
r1=vec({(i,0):v for i,v in enumerate((-3,1,1,1))})
r2=vec({(4,j):v for j,v in enumerate((1,1,1,-3),1)})
assert s.Matrix.hstack(*(p*v for v in (p.T*q*p).nullspace())).rank()==1
assert p.T*q*(r2-r1)==s.zeros(p.cols,1)
core_cells={(i,j) for i in range(1,4) for j in range(1,4)}
ell=entry_sum(core_cells)*p
abar=mat(r2-r1)
assert (r2-r1)!=s.zeros(r1.rows,1)
dper=s.Matrix([[sum(abar[i,j]*abar[u,v] for (i,j),(u,v) in combinations(
             [(i,j) for i in range(5) for j in range(5) if i!=a and j!=b],2)
             if i!=u and j!=v)
          for a in range(5) for b in range(5) if [1,15,15,15,31][a]&(1<<b)]])
weighted=dper*p
assert ell.rank()==weighted.rank()==ell.col_join(weighted).rank()==1
p0=p*s.Matrix.hstack(*ell.nullspace())
q0=p0.T*q*p0
assert len(q0.nullspace())==2
assert p0.T*q*r1==p0.T*q*r2==s.zeros(p0.cols,1)
assert entry_sum(core_cells)*r1==entry_sum(core_cells)*r2==s.zeros(1,1)
assert sum(r1)==sum(r2)==0
assert s.Matrix.hstack(r1,r2).rank()==2

q,p,vec,_,_=for_shape([3,29,29,29,31])
r=vec({**{(i,0):v for i,v in enumerate((3,-1,-1,-1))},
       **{(4,j):v for j,v in enumerate((-3,1,1,1),1)}})
assert sum(r)==0 and len((p.T*q*p).nullspace())==1
assert p.T*q*r==s.zeros(p.cols,1)
print('Forced radical vectors and size-18 gradient restriction checked over the rationals.')
