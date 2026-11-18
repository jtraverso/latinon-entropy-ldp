# check: entropy(colouring) + sum_tau t_tau (log D_tau - 2) == sum_tau t_tau (log(N_tau/t_tau) - 2)
import numpy as np
from math import log
rng=np.random.default_rng(1)
def check(c,t):
    k=len(c); lhs=0; rhs=0; M=0
    for X in range(k):
        # XX pairs: colour Y w.p. beta_XY
        beta={Y: c[Y]*2*t[X][Y]/(c[X]*c[Y])/c[X] for Y in range(k) if Y!=X}
        assert abs(sum(beta.values())-1)<1e-5, sum(beta.values())
        lhs += -(c[X]**2/2)*sum(b*log(b) for b in beta.values())
        for Y in range(X+1,k):
            a=2*t[X][Y]/(c[X]*c[Y]); b=2*t[Y][X]/(c[X]*c[Y]); assert abs(a+b-1)<1e-5
            lhs += -c[X]*c[Y]*(a*log(a)+b*log(b))
    for X in range(k):
        for Y in range(k):
            if X==Y: continue
            a=2*t[X][Y]/(c[X]*c[Y]); D=c[Y]*a*a
            lhs += t[X][Y]*(log(D)-2)
            N=c[X]**2*c[Y]/2; rhs += t[X][Y]*(log(N/t[X][Y])-2); M+=t[X][Y]
    return lhs,rhs
# k=3 symmetric, and a random interior target with 4 classes (continuous version of the identities)
n=1000.0
print(check([n/3]*3,[[0,n*n/36,n*n/36],[n*n/36,0,n*n/36],[n*n/36,n*n/36,0]]))
# k=4: use the I-projection target from the rate script
import importlib.util,sys
spec=importlib.util.spec_from_file_location("s","stsrate2.py")
