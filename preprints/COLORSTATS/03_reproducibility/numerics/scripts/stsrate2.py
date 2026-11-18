# I-projection by exact dual: Q_XY = P0_XY * exp(a_X + b_{XY}) ; solve with a convex dual (Newton via scipy)
import numpy as np
from scipy.optimize import minimize
def rate(g):
    g=np.array(g); k=len(g); idx=[(X,Y) for X in range(k) for Y in range(k) if X!=Y]
    P0=np.array([3*g[X]**2*g[Y] for X,Y in idx])
    rows=[]; b=[]
    for X in range(k): rows.append([1.0 if x==X else 0 for x,y in idx]); b.append(3*g[X]**2)
    for X in range(k):
        for Y in range(X+1,k): rows.append([1.0 if {x,y}=={X,Y} else 0 for x,y in idx]); b.append(3*g[X]*g[Y])
    A=np.array(rows); b=np.array(b)
    # dual: max_l  l.b - sum P0 exp(A^T l - 1)
    dual=lambda l: -(l@b - np.sum(P0*np.exp(A.T@l-1)))
    grad=lambda l: -(b - A@(P0*np.exp(A.T@l-1)))
    r=minimize(dual,np.zeros(len(b)),jac=grad,method='BFGS',options={'gtol':1e-13,'maxiter':10000})
    Q=P0*np.exp(A.T@r.x-1)
    D=np.sum(Q*np.log(Q/P0))
    return D, -np.log(P0.sum()), np.abs(A@Q-b).max(), Q
for g in [[1/3]*3,[1/2,1/6,1/6,1/6]]:
    D,c,res,Q=rate(g); print(np.round(g,4),"minD=%.6f -logP0(bic)=%.6f resid=%.1e"%(D,c,res)); print("  Q=",np.round(Q,5))
from scipy.optimize import brentq
# interior k=4 profile with sum g^2 = 1/3: g=(x, 0.8-x, 0.1, 0.1)
y=brentq(lambda y: 0.47**2+y*y+2*((0.53-y)/2)**2-1/3, 0.2, 0.4); x=0.47
g=[x,y,(0.53-y)/2,(0.53-y)/2]; D,c,res,Q=rate(g)
print("k=4",np.round(g,4),"minD=%.4f -logP0(bic)=%.4f minQ=%.4f resid=%.1e"%(D,c,Q.min(),res))
