# Check: colour-first identity for Latin outlines.
# n^2[H(S|RC)+H(C|RS)+H(R|CS)] + sum n^2 Q (log(n Q^2/(rho gam sig)) - 2) == n^2 (log n - 2 - TC)
import numpy as np, itertools
rng=np.random.default_rng(1)
def H(p): p=p[p>0]; return -(p*np.log(p)).sum()
for trial in range(5):
    k=rng.integers(2,5,size=3)
    rho,gam,sig=[rng.dirichlet(np.ones(m))+0.2 for m in k]; rho/=rho.sum(); gam/=gam.sum(); sig/=sig.sum()
    base=np.einsum('i,j,l->ijl',rho,gam,sig)
    # perturbation with all pairwise marginals zero: f = a_i b_j c_l with weighted zero means
    a=rng.normal(size=k[0]); a-= (a*rho).sum()
    b=rng.normal(size=k[1]); b-= (b*gam).sum()
    c=rng.normal(size=k[2]); c-= (c*sig).sum()
    f=np.einsum('i,j,l->ijl',a,b,c); eps=0.5/np.abs(f).max()
    Q=base*(1+eps*f)
    assert np.allclose(Q.sum((2,)),np.outer(rho,gam)) and np.allclose(Q.sum(1),np.outer(rho,sig)) and np.allclose(Q.sum(0),np.outer(gam,sig))
    n=1000.0
    HRCS=H(Q.ravel()); HR,HC,HS=H(rho),H(gam),H(sig)
    HRC,HRS,HCS=H(Q.sum(2).ravel()),H(Q.sum(1).ravel()),H(Q.sum(0).ravel())
    col=n*n*((HRCS-HRC)+(HRCS-HRS)+(HRCS-HCS))
    D=n*Q**2/base
    match=(n*n*Q*(np.log(D)-2)).sum()
    TC=HR+HC+HS-HRCS
    lhs=col+match; rhs=n*n*(np.log(n)-2-TC)
    print(trial, k, f"TC={TC:.5f}", f"lhs-rhs={lhs-rhs:.3e}")
