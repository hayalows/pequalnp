"""Exact coefficient checks for the 5-by-5 moment reduction."""
from itertools import combinations, permutations
from math import factorial
from sympy import I, Matrix, Rational, expand, symbols

N = 5
J = range(N)
x = Matrix(N, N, symbols('x:25'))

def row_sums(a):
    return [sum(a[i,j] for j in J) for i in J]

def col_sums(a):
    return row_sums(a.T)

def ordered_matching(a, k):
    return factorial(k) * sum(
        aproduct(a[i,j] for i,j in zip(rows,cols))
        for rows in combinations(J,k)
        for cols in permutations(J,k)
    )

def aproduct(es):
    p = 1
    for e in es:
        p *= e
    return p

r, c = row_sums(x), col_sums(x)
s = sum(r)
second = s**2 - sum(t**2 for t in r+c) + sum(t**2 for t in x)
assert expand(ordered_matching(x,2) - second) == 0

third = (
    s**3 - 3*s*sum(t**2 for t in r+c)
    + 3*s*sum(t**2 for t in x)
    + 2*sum(t**3 for t in r+c)
    + 6*sum(x[i,j]*r[i]*c[j] for i in J for j in J)
    - 6*sum(x[i,j]**2 * (r[i]+c[j]) for i in J for j in J)
    + 4*sum(t**3 for t in x)
)
assert expand(ordered_matching(x,3) - third) == 0

y = Matrix(N,N,lambda i,j: x[i,j] - (r[i]+c[j])/2)
z = [-Rational(3,10)*v for v in r+c]
assert expand(second - sum(v**2 for v in y)
              + Rational(125,9)*sum(v**2 for v in z)) == expand(s**2/2)
assert expand((third/4 - sum(v**3 for v in y)
              + Rational(125,9)*sum(v**3 for v in z)).subs(x[4,4],x[4,4]-s)) == 0

a = Matrix(N,N,lambda i,j: x[i,j] if i<4 and j<4 else 0)
for i in range(4):
    a[i,4] = -sum(a[i,j] for j in range(4))
for j in range(4):
    a[4,j] = -sum(a[i,j] for i in range(4))
a[4,4] = -sum(a[4,j] for j in range(4))
assert all(expand(v)==0 for v in row_sums(a)+col_sums(a))

fourth = (
    36 * sum(v**4 for v in a)
    -18 * sum(sum(a[i,j]**2 for j in J)**2 for i in J)
    -18 * sum(sum(a[i,j]**2 for i in J)**2 for j in J)
    +3 * sum(v**2 for v in a)**2
    +6 * ((a*a.T)**2).trace()
)
assert expand(ordered_matching(a,4)-fourth)==0

u = Matrix([1,-1,I,-I,0])
v = Matrix([1,-1,0,0,0])
level = u*v.T
assert all(expand(ordered_matching(level,k))==0 for k in range(1,6))
assert expand(sum(t**4 for t in level)) == 8
b = Matrix([[1,-1],[-1,1]])
same_second_third = Matrix.diag(b,I*b,0)
assert [expand(ordered_matching(same_second_third,k)) for k in range(1,5)] == [0,0,0,-96]
assert expand(sum(t**4 for t in same_second_third)) == 8
print('Exact quadratic, cubic, shifted, quartic identities and fourth-moment obstruction verified.')
