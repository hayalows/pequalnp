"""Small counterexample search for weighted saturated-edge support."""
import argparse
import itertools as it
import random
import time

def subset_sums(ws):
    sums=[0]
    for w in ws:
        sums += [s+w for s in sums]
    return sums

def subset_unions(ms):
    unions=[0]
    for m in ms:
        unions += [u|m for u in unions]
    return unions

def has_balanced(adj, left, right):
    """An exact weighted Hall test over all pairs of nonempty vertex subsets."""
    if any(a==b for i,a in enumerate(left) for j,b in enumerate(right) if adj[i]&(1<<j)):
        return True
    ls,rs=subset_sums(left),subset_sums(right)
    unions=subset_unions(adj)
    tgt={}
    for j,w in enumerate(rs[1:],1):
        tgt.setdefault(w,[]).append(j)
    for i,w in enumerate(ls[1:],1):
        for j in tgt.get(w,()):
            if unions[i]&j!=j:
                continue
            valid=True
            u=i
            while u:
                if ls[u]>rs[unions[u]&j]:
                    valid=False
                    break
                u=(u-1)&i
            if valid:
                return True
    return False

def admissible_weights(adj, cols, strict):
    dl=[a.bit_count() for a in adj]
    dr=[sum(bool(a&(1<<j)) for a in adj) for j in range(cols)]
    if min(dl+dr)<=strict:
        return
    for left in it.product(*(range(1,x+1-strict) for x in dl)):
        for right in it.product(*([x for x in range(1,dr[j]+1-strict)
               if not any(a&(1<<j) and x==w for a,w in zip(adj,left))] for j in range(cols))):
            yield left,right

def exact(rows, cols, strict):
    count=0
    for adj in it.combinations_with_replacement(range(1,1<<cols),rows):
        for left,right in admissible_weights(adj,cols,strict):
            if any(adj[i]==adj[i+1] and left[i]>left[i+1] for i in range(rows-1)):
                continue
            count+=1
            if not has_balanced(adj,left,right):
                print("counterexample",adj,left,right,flush=True)
                return False
    print("exact",rows,cols,"strict",strict,"configurations",count,flush=True)
    return True

def random_trials(trials, max_side, seed, strict):
    rng=random.Random(seed)
    started=time.monotonic()
    count=0
    for _ in range(trials):
        rows=rng.randint(3,max_side)
        cols=rng.randint(3,max_side)
        p=rng.uniform(.3,.9)
        adj=[sum(1<<j for j in range(cols) if rng.random()<p) for i in range(rows)]
        dl=[m.bit_count()-strict for m in adj]
        dr=[sum(bool(m&(1<<j)) for m in adj)-strict for j in range(cols)]
        if min(dl+dr)<1:
            continue
        left=[rng.randint(1,a) for a in dl]
        choices=[[x for x in range(1,dr[j]+1) if not any((m>>j)&1 and x==a
                    for m,a in zip(adj,left))] for j in range(cols)]
        if not all(choices):
            continue
        right=[rng.choice(ws) for ws in choices]
        count+=1
        if not has_balanced(adj,left,right):
            print("random counterexample",adj,left,right,flush=True)
            return False
    print("random tested",count,"out of",trials,"time",time.monotonic()-started,flush=True)
    return True

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--exact",type=int,nargs=2)
    p.add_argument("--trials",type=int,default=10000)
    p.add_argument("--max-side",type=int,default=10)
    p.add_argument("--seed",type=int,default=2086)
    p.add_argument("--strict",type=int,default=0)
    a=p.parse_args()
    if a.exact:
        exact(*a.exact,a.strict)
    else:
        random_trials(a.trials,a.max_side,a.seed,a.strict)
