"""Exact search in tensor products of cycle Fourier bases for partitions of 5."""
from collections import Counter
from functools import cache
from itertools import combinations_with_replacement, product
from math import factorial

def partitions(n, m=1):
    if n == 0:
        yield ()
    for k in range(m, n + 1):
        for p in partitions(n-k, k):
            yield (k,) + p

def patterns(p):
    vectors = [(i, a) for i, length in enumerate(p) for a in range(length)]

    @cache
    def injective_sum(indices):
        if not indices:
            return 1
        cycle, exponent = vectors[indices[0]]
        others = indices[1:]
        total = 0
        for subset in range(1 << len(others)):
            block = [vectors[others[i]] for i in range(len(others)) if subset >> i & 1]
            if any(c != cycle for c, e in block):
                continue
            length = p[cycle]
            if (exponent + sum(e for c,e in block)) % length:
                continue
            rest = tuple(j for i,j in enumerate(others) if not (subset >> i & 1))
            total += length*(-1)**len(block)*factorial(len(block))*injective_sum(rest)
        return total

    return vectors, injective_sum

def solve(rows, cols):
    row_modes, row_sum = patterns(rows)
    col_modes, col_sum = patterns(cols)
    modes = []
    for i,j in product(range(5), repeat=2):
        if not any(row_sum((i,)*k) and col_sum((j,)*k) for k in range(1, 6)):
            modes.append((i,j))
    minimal = []
    known = set()
    for k in range(2, 6):
        for t in combinations_with_replacement(range(len(modes)), k):
            ids = set(t)
            if len(ids) < 2:
                continue
            s = sum(1 << i for i in ids)
            if s in known or any(s & g == g for g in minimal):
                continue
            a,b = zip(*(modes[i] for i in t))
            if row_sum(tuple(sorted(a))) and col_sum(tuple(sorted(b))):
                minimal.append(s)
                known.add(s)
    groups = [[] for _ in modes]
    for s in minimal:
        groups[s.bit_length()-1].append(s)
    best = 0
    def dfs(i,subset):
        nonlocal best
        if subset.bit_count() + len(modes)-i <= best.bit_count():
            return
        if i == len(modes):
            best = subset
            return
        take = subset | (1<<i)
        if all(take & s != s for s in groups[i]):
            dfs(i+1,take)
        dfs(i+1,subset)
    dfs(0,0)
    return len(modes),Counter(m.bit_count() for m in minimal),[tuple((row_modes[i],col_modes[j])) for k,(i,j) in enumerate(modes) if best>>k&1]

maximum = 0
ps = list(partitions(5))
for j, rows in enumerate(ps):
    for cols in ps[j:]:
        n, cnt, sol = solve(rows,cols)
        print(rows,cols,n,dict(cnt),'max',len(sol),flush=True)
        if len(sol) > maximum:
            maximum = len(sol)
            print('best basis',sol,flush=True)
print('maximum over all pairs of partitions',maximum)
