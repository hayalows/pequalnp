"""Exhaust the 25 coordinate subsets in the product Fourier basis over Z/5."""
from itertools import combinations_with_replacement, product
from functools import cache
from math import factorial

N = 5
modes = list(product(range(N), repeat=2))

@cache
def injective_sum(exponents):
    """Sum over distinct slots of product of powers of a primitive fifth root."""
    if not exponents:
        return 1
    first = exponents[0]
    others = exponents[1:]
    total = 0
    for selection in range(1 << len(others)):
        block = [a for i, a in enumerate(others) if (selection >> i) & 1]
        if (first + sum(block)) % N == 0:
            rest = tuple(a for i, a in enumerate(others) if not ((selection >> i) & 1))
            total += N * (-1)**len(block) * factorial(len(block)) * injective_sum(rest)
    return total

forbidden = set()
for degree in range(1, N + 1):
    for inds in combinations_with_replacement(range(len(modes)), degree):
        support = sum(1 << i for i in set(inds))
        if any(support & g == g for g in forbidden if g.bit_count() <= 2):
            continue
        row, col = zip(*(modes[i] for i in inds))
        if injective_sum(tuple(sorted(row))) and injective_sum(tuple(sorted(col))):
            forbidden.add(support)

minimal = []
for g in sorted(forbidden, key=int.bit_count):
    if not any(g & f == f for f in minimal):
        minimal.append(g)
groups = [[] for _ in modes]
for g in minimal:
    groups[g.bit_length() - 1].append(g)

best = 0
num = 0
def search(i, subset):
    global best, num
    if i == len(modes):
        if subset.bit_count() > best.bit_count():
            best, num = subset, 0
            print('new maximum', best.bit_count(), [m for j,m in enumerate(modes) if subset>>j&1], flush=True)
        if best.bit_count() == subset.bit_count():
            num += 1
        return
    if subset.bit_count() + len(modes) - i < best.bit_count():
        return
    take = subset | (1 << i)
    if not any(take & g == g for g in groups[i]):
        search(i+1, take)
    search(i+1, subset)

print('minimal obstructions by support size', [sum(g.bit_count() == k for g in minimal) for k in range(1,6)])
search(0, 0)
print('maximum Fourier-subset dimension', best.bit_count(), 'number of maximizers', num)
