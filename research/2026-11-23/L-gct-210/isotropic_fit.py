"""Heuristic search on a chart of the 9-dimensional complex isotropic Grassmannian."""
import argparse
import itertools
import numpy as np
from scipy.linalg import null_space
from scipy.optimize import minimize

def incidence(k):
    ans = []
    for rows in itertools.combinations(range(5), k):
        for cols in itertools.permutations(range(5), k):
            ans.append([5*i+j for i,j in zip(rows,cols)])
    return np.array(ans)

def sampler(seed, dim, batch):
    rng = np.random.default_rng(seed)
    c = rng.standard_normal((batch, dim)) + 1j*rng.standard_normal((batch,dim))
    return c / np.linalg.norm(c,axis=1,keepdims=True)

def setup(seed, dim, coeffs):
    rng=np.random.default_rng(seed)
    row = np.repeat(np.eye(5),5,axis=1)
    col = np.tile(np.eye(5),(1,5))
    H = np.eye(25) - row.T@row - col.T@col
    T = null_space(np.ones((1,25)))
    lam,Q = np.linalg.eigh(T.T@H@T)
    P = T@Q@np.diag(1/np.sqrt(lam.astype(complex)))
    O=np.linalg.qr(rng.standard_normal((24,24)))[0]
    P=P@O
    U=(P[:,:dim]+1j*P[:,dim:2*dim])/np.sqrt(2)
    V=(P[:,:dim]-1j*P[:,dim:2*dim])/np.sqrt(2)
    N=P[:,2*dim:]
    ii,jj=np.triu_indices(dim,1)
    n=len(ii)
    m=24-2*dim
    shapes=[incidence(k) for k in (3,4,5)]
    # Derivative matchings grouped by the one coordinate removed.
    patterns=[[np.stack([np.delete(row,np.where(row==x)[0][0]) for row in rows if x in row])
               for x in range(25)] for rows in shapes]
    patterns=[np.array(x) for x in patterns]
    scales=[2.5**k / len(rows) for k,rows in zip((3,4,5),shapes)]
    def chart(values):
        A = np.zeros((dim,dim),dtype=complex)
        A[ii,jj] = values[:n]
        A[jj,ii] = -values[:n]
        W = values[n:].reshape(m,dim)
        return U + V@(A-0.5*W.T@W) + N@W, W
    def f(values, c=coeffs):
        values = values[:len(values)//2] + 1j*values[len(values)//2:]
        Y,W = chart(values)
        x=c@Y.T
        gx=np.zeros_like(x)
        total=0.0
        for k,inds,di,scale in zip((3,4,5),shapes,patterns,scales):
            vals = np.prod(x[:,inds],axis=2).sum(axis=1)*scale
            total += np.mean(np.abs(vals)**2)
            der = np.prod(x[:,di],axis=3).sum(axis=2)*scale
            gx += 2*np.conj(vals)[:,None]*der/len(c)
        G=gx.T@c
        g=V.T@G
        gw=N.T@G - W@(g+g.T)/2
        grad=np.concatenate([(g-g.T)[ii,jj],gw.ravel()])
        return total,np.concatenate([grad.real,-grad.imag])
    start = 0.18*rng.standard_normal(2*(n+m*dim))
    return f, chart, start

if __name__ == '__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--dim',type=int,default=9)
    p.add_argument('--seeds',type=int,default=5)
    p.add_argument('--batch',type=int,default=72)
    p.add_argument('--iterations',type=int,default=300)
    p.add_argument('--output',default='fit')
    a=p.parse_args()
    for seed in range(a.seeds):
        f,chart,start = setup(seed,a.dim,sampler(seed+100,a.dim,a.batch))
        _,g=f(start)
        eps=1e-6
        v=np.eye(1,len(start),seed%len(start))[0]
        gd=(f(start+eps*v)[0]-f(start-eps*v)[0])/(2*eps)
        assert abs(gd-g@v)<1e-6
        result=minimize(f,start,jac=True,method='L-BFGS-B',
                        options={'maxiter':a.iterations,'gtol':1e-11,'ftol':1e-13})
        check=f(result.x,sampler(seed+500,a.dim,2*a.batch))[0]
        print(seed,'iterations',result.nit,'train',result.fun,'held out',check,flush=True)
        z=result.x[:len(start)//2]+1j*result.x[len(start)//2:]
        y,_=chart(z)
        np.save(f'{a.output}-{seed}.npy',y)
