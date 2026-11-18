"""E1 finite checks: (1) explicit inverse for all triangles of K_m; (2) hub basis b_sigma and
explicit Pasch-trade certificates; (3) colour-first identity and degree symmetry for all types."""
import itertools, random
import numpy as np
from fractions import Fraction as Fr

# (1) inverse for the full triangle incidence of K_m
def inv_check(m, seed=0):
    rng=np.random.default_rng(seed)
    E=list(itertools.combinations(range(m),2)); ei={e:i for i,e in enumerate(E)}
    x=rng.normal(size=len(E)); X=np.zeros(m)
    for (u,v),val in zip(E,x): X[u]+=val; X[v]+=val
    S=X.sum()/(3*m-6)                       # S = 2 sigma_x/(3m-6), with sum X = 2 sigma_x
    Y=(X-S)/(2*m-6)
    y=np.array([(x[ei[(u,v)]]-Y[u]-Y[v])/(m-4) for (u,v) in E])
    psi={}
    for T in itertools.combinations(range(m),3):
        psi[T]=sum(y[ei[e]] for e in itertools.combinations(T,2))
    back=np.zeros(len(E))
    for T,w in psi.items():
        for e in itertools.combinations(T,2): back[ei[e]]+=w
    err=abs(back-x).max(); ratio=max(abs(w) for w in psi.values())*m/abs(x).max()
    return err, ratio
print('(1) A Phi x = x for all triangles of K_m: (max error, max|psi| m/||x||)')
for m in [6,9,14,20]: print('   m=%d'%m, inv_check(m,m))

# (2) hub basis and Pasch certificates
def types_of(k): return list(itertools.combinations_with_replacement(range(k),3))
def pair_mult(t):
    d={}
    for a,b in itertools.combinations(t,2):
        key=tuple(sorted((a,b))); d[key]=d.get(key,0)+1
    return d
def kernel_basis(k,o):
    """b_sigma for o-free sigma via the triangular solve; verify it is integral and in the kernel."""
    T=types_of(k); res={}
    for s in T:
        if o in s: continue
        v={t:Fr(0) for t in T}; v[s]=Fr(1)
        others=[c for c in range(k) if c!=o]
        # pairs {A,B} with A,B != o: t_{ABo} = -m_AB(s)
        for A,B in itertools.combinations_with_replacement(others,2):
            v[tuple(sorted((A,B,o)))]=-Fr(pair_mult(s).get((A,B),0))
        for A in others:
            tot=sum(pair_mult(t).get(tuple(sorted((A,o))),0)*v[t] for t in T if t!=tuple(sorted((A,o,o))))
            v[tuple(sorted((A,o,o)))]=-tot/2
        tot=sum(pair_mult(t).get((o,o),0)*v[t] for t in T if t!=(o,o,o))
        v[(o,o,o)]=-tot/3
        # verify kernel and integrality
        for P in itertools.combinations_with_replacement(range(k),2):
            assert sum(pair_mult(t).get(P,0)*v[t] for t in T)==0
        assert all(c.denominator==1 for c in v.values())
        res[s]={t:int(c) for t,c in v.items() if c!=0}
    return res
P1=[(0,1,2),(0,3,4),(1,3,5),(2,4,5)]; P2=[(0,1,3),(0,2,4),(1,2,5),(3,4,5)]
def trade(col):
    d={}
    for b in P1: t=tuple(sorted(col[x] for x in b)); d[t]=d.get(t,0)+1
    for b in P2: t=tuple(sorted(col[x] for x in b)); d[t]=d.get(t,0)-1
    return {t:c for t,c in d.items() if c}
def certificate(k,o,target):
    vecs={}
    for col in itertools.product(range(k),repeat=6):
        tv=trade(col)
        if tv: vecs.setdefault(tuple(sorted(tv.items())),col)
    items=list(vecs.items())
    tgt=tuple(sorted(target.items()))
    def add(a,b,s=1):
        d=dict(a)
        for t,c in b: d[t]=d.get(t,0)+s*c
        return tuple(sorted((t,c) for t,c in d.items() if c))
    for (v,col) in items:
        for s in (1,-1):
            if add((),v,s)==tgt: return [(s,col)]
    for (v,c1),(w,c2) in itertools.combinations(items,2):
        for s1 in (1,-1):
            for s2 in (1,-1):
                if add(add((),v,s1),w,s2)==tgt: return [(s1,c1),(s2,c2)]
    return None
print('(2) hub basis b_sigma (o = last class), integral, and Pasch certificates (sign, colouring of points 0..5):')
for k,sig in [(2,(0,0,0)),(3,(0,0,1)),(4,(0,1,2))]:
    o=k-1; B=kernel_basis(k,o); b=B[sig]
    print('   sigma=%s, k=%d: b ='%(str(sig),k), b)
    print('      certificate:', certificate(k,o,b))

# (3) colour-first identity and degree symmetry, generic random sizes
def identity_check(k,seed):
    rng=random.Random(seed)
    c=[rng.randint(40,90) for _ in range(k)]
    T=types_of(k)
    def N(t):
        from math import comb
        cnt={}
        for a in t: cnt[a]=cnt.get(a,0)+1
        r=1
        for a,m in cnt.items(): r*=comb(c[a],m)
        return r
    # random positive t with pair identities: start from proportional t = N(t)/(n-2) * w, adjust is hard;
    # instead check the algebraic identity for arbitrary positive t with e_pi := sum m_pi t
    t={tt:rng.uniform(1,5)*N(tt)/sum(c) for tt in T}
    pairs=list(itertools.combinations_with_replacement(range(k),2))
    e={P:sum(pair_mult(tt).get(P,0)*t[tt] for tt in T) for P in pairs}
    prob={(tt,P):pair_mult(tt).get(P,0)*t[tt]/e[P] for tt in T for P in pairs}
    import math
    H=-sum(e[P]*sum(prob[(tt,P)]*math.log(prob[(tt,P)]) for tt in T if prob[(tt,P)]>0) for P in pairs)
    # degrees from each of the three pairs, with third-point counts using pair identities in expectation
    def third_count(tt,i,j):
        z=[x for n_,x in enumerate(tt) if n_ not in (i,j)][0]
        return c[z]-sum(1 for n_,x in enumerate(tt) if n_ in (i,j) and x==z)
    worst=0; total=0
    for tt in T:
        Ds=[]
        for (i,j) in [(0,1),(0,2),(1,2)]:
            P1_=tuple(sorted((tt[i],tt[j])))
            others=[x for x in [(0,1),(0,2),(1,2)] if x!=(i,j)]
            D=third_count(tt,i,j)
            for a,b in others: D*=prob[(tt,tuple(sorted((tt[a],tt[b]))))]
            Ds.append(D)
        worst=max(worst,max(Ds)/min(Ds)-1)
        total+=t[tt]*(math.log(Ds[0])-2)
    Phi=sum(t[tt]*(math.log(N(tt)/t[tt])-2) for tt in T)
    return worst, (H+total)-Phi
print('(3) colour-first identity for all types: (max relative spread of the three degrees, H + sum t(log D - 2) - Phi)')
for k,s in [(1,1),(2,2),(3,3),(4,4)]: print('   k=%d'%k, identity_check(k,s))
