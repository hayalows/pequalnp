import itertools as it
import numpy as np
import random
import time
import sys

P = 1073742361
ROOT = 7
N = 5
vector_set = set()
for size in range(1, N + 1):
    zeta = pow(ROOT, (P - 1) // size, P)
    powers = [pow(zeta, i, P) for i in range(1, size)]
    for support in it.combinations(range(N), size):
        for vals in it.permutations(powers):
            vec = [0] * N
            for i, val in zip(support, (1,) + vals):
                vec[i] = val
            vector_set.add(tuple(vec))
vectors = sorted(vector_set)
def poly(vecs, sub=range(N)):
    result = {0: 1}
    for i in sub:
        new = result.copy()
        for k, v in result.items():
            for j, vec in enumerate(vecs):
                if x := vec[i]:
                    key = k + (1 << (3*j))
                    new[key] = (new.get(key, 0) + v*x) % P
        result = {k: v for k, v in new.items() if v}
    return result

supports = [sum(1 << k for k in poly([v]) if k) for v in vectors]
pairs = [(i,j) for i,j in it.product(range(len(vectors)), repeat=2) if not (supports[i]&supports[j])]
V = len(vectors)
print('vectors', V, 'rank-one directions', len(pairs),flush=True)
powers = [(a,b) for a in range(1,5) for b in range(1,6-a)]
cross = np.zeros((V,V), dtype=np.int64)
for i,j in it.product(range(V),repeat=2):
    ps = poly([vectors[i],vectors[j]])
    cross[i,j] = sum(1 << k for k,(a,b) in enumerate(powers) if ps.get(a+8*b,0))
ix,jx = np.array(pairs).T
allowed = (cross[ix[:,None],ix[None,:]] & cross[jx[:,None],jx[None,:]]) == 0
np.fill_diagonal(allowed,False)
print('pair compatibility density',allowed.mean(),flush=True)

subs = [[(s, tuple(i for i in range(N) if i not in s))
         for s in it.combinations(range(N),k)] for k in range(1,N+1)]
def subset_polys(ids):
    vs = [vectors[i] for i in ids]
    return [[(s, poly(vs,rest)) for s,rest in g] for g in subs]
def relevant_coeffs(polys, vec, k):
    result = {}
    for s, poly_s in polys[k]:
        w = 1
        for i in s:
            w = (w*vec[i])%P
        if not w:
            continue
        for e,v in poly_s.items():
            result[e] = (result.get(e,0) + w*v)%P
    return result

products = np.array([[u*v%P for u in vectors[i] for v in vectors[j]] for i,j in pairs],dtype=np.int64)
def add_dir(basis, ind):
    v = products[ind].copy()
    for p,u in basis:
        v = (v - v[p]*u)%P
    nz = np.flatnonzero(v)
    if len(nz)==0:
        return None
    p=int(nz[0])
    return basis+[(p, v*pow(int(v[p]),P-2,P)%P)]

rng = random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 1)
best = []
start = time.monotonic()
prev_report = start
runs = int(sys.argv[2]) if len(sys.argv)>2 else 10000
for step in range(runs):
    chosen = []
    basis = []
    avail = np.arange(len(pairs))
    # Select a learned prefix occasionally, but restart fresh often.
    if len(best)>=4 and step%3==0:
        chosen = rng.sample(best, rng.randrange(2,len(best)))
        for a in chosen:
            avail = avail[allowed[a,avail]]
            basis = add_dir(basis,a)
    while len(avail) and len(chosen) < 9:
        if len(chosen)>=2:
            rpolys = subset_polys([pairs[a][0] for a in chosen])
            cpolys = subset_polys([pairs[a][1] for a in chosen])
        while len(avail):
            idx = rng.randrange(len(avail))
            a = int(avail[idx])
            bnew = add_dir(basis,a)
            i,j = pairs[a]
            if bnew is not None:
                if len(chosen) >= 2:
                    good = True
                    for k in range(N):
                        rr = relevant_coeffs(rpolys,vectors[i],k)
                        if not rr:
                            continue
                        cc = relevant_coeffs(cpolys,vectors[j],k)
                        if any(v and cc.get(e,0) for e,v in rr.items()):
                            good = False
                            break
                else:
                    good = True
                if good:
                    break
            avail[idx] = avail[-1]
            avail = avail[:-1]
        if not len(avail):
            break
        chosen.append(a)
        basis = bnew
        avail = avail[allowed[a,avail]]
    if len(chosen) > len(best):
        best = chosen[:]
        print('best',step,len(best), [pairs[x] for x in best],time.monotonic()-start,flush=True)
        with open('/workspace/pnp-session/upper-bound/best.txt','w') as f:
            for a in best: print(vectors[pairs[a][0]],vectors[pairs[a][1]],file=f)
        if len(best)>=9:
            break
    now=time.monotonic()
    if now-prev_report>=20:
        print('progress',step,len(best),now-start,flush=True)
        prev_report=now
