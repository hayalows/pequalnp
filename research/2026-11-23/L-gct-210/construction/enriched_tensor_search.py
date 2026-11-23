"""Exact size-nine exclusion in selected families of algebraic tensor bases."""
from itertools import combinations, product
from sympy import sqrt_mod
from fourier_search import P, G, TYPES, basis, grouped_coeffs, forbidden_sets

def std(i):
    return [int(i == j) for j in range(5)]

def lin(a, b, s, t):
    return [(s*x+t*y) % P for x, y in zip(a,b)]

def sub(a, b):
    return lin(a, b, 1, -1)

def has_size(forbidden, target):
    """Exact DFS with pruning by the forbidden sets."""
    def go(available, used, count, constraints):
        if count == target:
            return used
        if len(available) < target - count:
            return None
        for i, bit in enumerate(available[: len(available) - (target - count) + 1]):
            active = used | bit
            next_available = available[i+1:]
            future_mask = sum(next_available)
            next_constraints = []
            for m in constraints:
                if m & bit:
                    remainder = m ^ bit
                    if not remainder:
                        break
                    if remainder & future_mask == remainder:
                        next_constraints.append(remainder)
                elif m & future_mask == m:
                    next_constraints.append(m)
            else:
                result = go(next_available, active, count+1, next_constraints)
                if result is not None:
                    return result
        return None
    singletons = sum(m for m in forbidden if m.bit_count() == 1)
    return go([1<<i for i in range(25) if not singletons>>i & 1], 0, 0,
              [m for m in forbidden if m.bit_count() > 1 and not (m & singletons)])

def basis_list():
    for typ in TYPES:
        b = basis(typ)
        yield ('ordinary', typ), b
        offsets = [sum(typ[:i]) for i in range(len(typ))]
        if len(offsets) == 1: continue
        for choice in [0,len(offsets)-1]:
            r = offsets[choice]
            altered = b[:]
            for p, d in zip(offsets, typ):
                if p != r:
                    altered[p] = lin(b[p], b[r], typ[choice], -d)
            yield ('triv-diff',typ,choice), altered
            extended = altered[:]
            extended[r] = [1]*5
            yield ('triv-const',typ,choice), extended
    differences = [sub(std(i),std(4)) for i in range(4)]
    helmert = [[1]*i + [-i] + [0]*(4-i) for i in range(1,5)]
    balanced_pairs = [[1,-1,0,0,0],[0,0,1,-1,0],[1,1,-1,-1,0],[1,1,1,1,-4]]
    for k, row_set in enumerate([differences,helmert,balanced_pairs]):
        for e in [[1]*5,std(4)]:
            yield ('standard-zero-sum',k,e[-2]), [e] + row_set
        if k == 0:
            continue
        normalized = []
        for v in row_set:
            r = int(sqrt_mod(sum(x*x for x in v),P))
            normalized.append([(x * pow(r,-1,P)) % P for x in v])
        imag = pow(G,(P-1)//4,P)
        for j in range(1,4):
            i,l = [f for f in range(1,4) if f != j]
            a,b,c,d = [normalized[x] for x in [0,j,i,l]]
            for e in [[1]*5,std(4)]:
                yield ('Witt',k,j,e[-2]), [e,lin(a,b,1,imag),lin(a,b,1,-imag),
                          lin(c,d,1,imag),lin(c,d,1,-imag)]
    # Root-of-unity split of four centered coordinates.
    bh = basis((4,1))
    for anchor in [[1]*5,std(4)]:
        yield ('centered-four',anchor[-2]), [anchor,[1,1,1,1,-4],bh[1],bh[2],bh[3]]

def main():
    entries = list(basis_list())
    coeffs = [grouped_coeffs(b) for _,b in entries]
    best = 0
    for i, (ut, u) in enumerate(entries):
        found = []
        for j in range(i,len(entries)):
            vt,v = entries[j]
            forbidden = forbidden_sets(coeffs[i],coeffs[j])
            solution = has_size(forbidden,9)
            if solution is not None:
                print('SIZE NINE',ut,vt,solution,flush=True)
            if best < 8:
                for size in range(8,best,-1):
                    if (candidate:=has_size(forbidden,size)) is not None:
                        best = size
                        print('size',size,ut,vt,[(k//5,k%5) for k in range(25) if candidate>>k & 1],flush=True)
                        break
            found.append(solution is not None)
        print(i+1,'/',len(entries),ut,len(found),sum(found),flush=True)
    print('best',best,'unordered basis pairs',len(entries)*(len(entries)+1)//2)

if __name__ == '__main__':
    main()
