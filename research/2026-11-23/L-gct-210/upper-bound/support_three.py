from itertools import combinations_with_replacement, combinations
import numpy as np
R=5
choices=list(combinations(range(R),3))
counts={}
exceptions=[]
for rows in combinations_with_replacement(choices,R):
    coords=[(i,j) for i, cols in enumerate(rows) for j in cols]
    k=len(coords)
    M=(np.array([[int(i!=u and j!=v) for u,v in coords] for i,j in coords],dtype=np.int64))
    # Change basis to e_p-e_last, an integral basis for the zero-sum space.
    Q=M[:-1,:-1]-M[-1,:-1]-M[:-1,-1,None]+M[-1,-1]
    # Rank over a prime is a certified lower bound for rank over Q.
    p=1009
    B=Q%p
    rk=0
    for j in range(k-1):
        ss=np.flatnonzero(B[rk:,j])
        if len(ss):
            i=rk+int(ss[0])
            B[[i,rk]]=B[[rk,i]]
            B[rk]=B[rk]*pow(int(B[rk,j]),-1,p)%p
            B[rk+1:]=(B[rk+1:]-B[rk+1:,j,None]*B[rk])%p
            rk+=1
    counts[rk]=counts.get(rk,0)+1
    if rk<=10: # Orthogonal Grassmannian upper bound permits d>=9.
        exceptions.append((rows,rk))
print(counts)
print('Exceptional supports',len(exceptions))
for x in exceptions[:10]:
    print(x)
