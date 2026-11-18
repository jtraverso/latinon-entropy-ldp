"""E3 checks on random dense graphs: (1) triangle lattice via SNF; (2) exact diffuse seeds by LP;
(3) the two-step K4 averaging operator: ||E|| = ||I - A Phi_tilde|| on random G(m,p)."""
import itertools, random
import numpy as np, sympy
from sympy.matrices.normalforms import smith_normal_form
from scipy.optimize import linprog
from scipy.sparse import lil_matrix

def rand_graph(m,p,seed):
    rng=random.Random(seed)
    E=[e for e in itertools.combinations(range(m),2) if rng.random()<p]
    return E
def triangles(m,E):
    Es=set(E); return [T for T in itertools.combinations(range(m),3) if all(e in Es for e in itertools.combinations(T,2))]

print('(1) triangle lattice of G(m,p): expect rank(span)=|E| and torsion (Z/2)^(m-1) + Z/3')
for m,p,s in [(8,0.8,1),(9,0.75,2),(10,0.7,3)]:
    E=rand_graph(m,p,s); ei={e:i for i,e in enumerate(E)}; T=triangles(m,E)
    rows=[[1 if e in itertools.combinations(t,2) else 0 for e in E] for t in T]
    D=smith_normal_form(sympy.Matrix(rows),domain=sympy.ZZ)
    d=[abs(D[i,i]) for i in range(min(D.shape)) if D[i,i]!=0]
    tors=sorted(x for x in d if x!=1)
    print('   m=%d |E|=%d rank=%d torsion=%s'%(m,len(E),len(d),tors))

print('(2) exact seed LP on G(m,p), all triangles: max min-weight relative to 1/(p^2 m)')
for m,p,s in [(20,0.7,4),(30,0.7,5),(40,0.6,6)]:
    E=rand_graph(m,p,s); ei={e:i for i,e in enumerate(E)}; T=triangles(m,E)
    A=lil_matrix((len(E),len(T)+1))
    for j,t in enumerate(T):
        for e in itertools.combinations(t,2): A[ei[e],j]=1
    G=lil_matrix((len(T),len(T)+1))
    for j in range(len(T)): G[j,j]=-1; G[j,len(T)]=1
    c=np.zeros(len(T)+1); c[-1]=-1
    base=1/(p*p*m)
    r=linprog(c,A_ub=G.tocsr(),b_ub=np.zeros(len(T)),A_eq=A.tocsr(),b_eq=np.ones(len(E)),
              bounds=[(0,4*base)]*len(T)+[(None,None)],method='highs')
    print('   m=%d p=%.2f: %s'%(m,p,'infeasible' if r.status else 'min/base=%.3f'%(r.x[:-1].min()/base)))

print('(3) two-step K4 averaging: ||I - A Phi_tilde||_inf on G(m,p) (needs < 1)')
def two_step(m,p,seed):
    E=rand_graph(m,p,seed); Es=set(E); ei={e:i for i,e in enumerate(E)}; T=triangles(m,E); ti={t:i for i,t in enumerate(T)}
    nE=len(E)
    A=np.zeros((nE,len(T)))
    for j,t in enumerate(T):
        for e in itertools.combinations(t,2): A[ei[e],j]=1
    adj=[set() for _ in range(m)]
    for a,b in E: adj[a].add(b); adj[b].add(a)
    def k4(e,f):
        a,b=e; x,y=f
        return len({a,b,x,y})==4 and all(v in adj[u] for u in (a,b) for v in (x,y))
    pi0=E  # single class: reference class = all edges
    partners=[[ei[f] for f in pi0 if k4(e,f)] for e in E]
    # g(e,f) as triangle vector
    def gvec(e,f):
        a,b=e; x,y=f; v=np.zeros(len(T))
        for t,s in [((a,b,x),1),((a,b,y),1),((a,x,y),-1),((b,x,y),-1)]:
            v[ti[tuple(sorted(t))]]+=0.5*s
        return v
    # Phi1 and T as matrices
    Phi1=np.zeros((len(T),nE)); Tm=np.zeros((nE,nE))
    for i,e in enumerate(E):
        P=partners[i]
        if not P: return None
        for j in P:
            Phi1[:,i]+=gvec(e,E[j])/len(P); Tm[j,i]+=1/len(P)
    # constant correction: weight w on every triangle so that mean load matches
    codeg=A.sum(1)
    Wc=np.ones((len(T),1))/codeg.mean()   # A Wc ~ 1 on every edge
    sig=np.ones((1,nE))/nE                # c(r) = sum r / |E|  (single class)
    Phit=Phi1+Phi1@Tm+Wc@(sig@Tm@Tm*nE/nE)
    Err=np.eye(nE)-A@Phit
    return np.abs(Err).sum(1).max(), np.abs(Phit).sum(1).max()*m
for m,p,s in [(12,0.8,7),(16,0.8,8),(20,0.8,9),(24,0.8,10)]:
    out=two_step(m,p,s); print('   m=%d p=%.1f: ||E||_inf=%.3f, ||Phi_tilde||*m=%.2f'%((m,p)+out) if out else '   m=%d: no partners'%m)
