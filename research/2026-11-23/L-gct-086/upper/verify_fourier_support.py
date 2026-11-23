"""Compute exact support of the Fourier product in a root-of-unity group ring."""
import sympy as s

def group_ring_coefficients(n):
    # Maps a monomial exponent tuple to its integer coefficients in 1,zeta,...,zeta^(n-1).
    zero=(0,)*n
    coefficients={zero:[1]+[0]*(n-1)}
    for i in range(n):
        new={}
        for exponent,vector in coefficients.items():
            for a in range(n):
                key=exponent[:a]+(exponent[a]+1,)+exponent[a+1:]
                target=new.setdefault(key,[0]*n)
                for t,value in enumerate(vector):
                    target[(t+a*i)%n]+=value
        coefficients=new
    return coefficients

def unsupported_balanced(n):
    x=s.symbols('x')
    minimal=s.Poly(s.cyclotomic_poly(n,x),x)
    coeffs=group_ring_coefficients(n)
    failed=[]
    for exponent,weights in coeffs.items():
        expr=sum(w*x**k for k,w in enumerate(weights))
        is_nonzero=not s.Poly(expr,x).rem(minimal).is_zero
        balanced=sum(k*e for k,e in enumerate(exponent))%n==0
        if is_nonzero:
            assert balanced, (n,exponent)
        elif balanced:
            failed.append(exponent)
    print(n,len(coeffs),len(failed),failed[:2],flush=True)
    return failed

for n in (2,3,4,5,7,8,9):
    assert not unsupported_balanced(n)
assert unsupported_balanced(6)
