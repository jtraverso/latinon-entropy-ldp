"""Colour-first identity for all types, with t satisfying the pair identities exactly."""
import itertools, random, math, importlib.util, sys
import itertools
from fractions import Fraction as Fr
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

def check(k,seed):
    rng=random.Random(seed); c=[rng.randint(40,90) for _ in range(k)]; n=sum(c)
    T=types_of(k)
    def N(t):
        r=1; cnt={}
        for a in t: cnt[a]=cnt.get(a,0)+1
        for a,m in cnt.items(): r*=math.comb(c[a],m)
        return r
    t={tt:N(tt)/(n-2) for tt in T}
    if k>=2:
        B=kernel_basis(k,k-1)
        for s,b in B.items():
            lam=rng.uniform(-0.3,0.3)*min(t.values())
            for tt,cf in b.items(): t[tt]+=lam*cf
    assert min(t.values())>0
    pairs=list(itertools.combinations_with_replacement(range(k),2))
    e={P:(c[P[0]]*c[P[1]] if P[0]!=P[1] else math.comb(c[P[0]],2)) for P in pairs}
    for P in pairs: assert abs(sum(pair_mult(tt).get(P,0)*t[tt] for tt in T)-e[P])<1e-6*e[P]
    prob={(tt,P):pair_mult(tt).get(P,0)*t[tt]/e[P] for tt in T for P in pairs}
    H=-sum(e[P]*sum(prob[(tt,P)]*math.log(prob[(tt,P)]) for tt in T if prob[(tt,P)]>0) for P in pairs)
    spread=0; tot=0
    for tt in T:
        Ds=[]
        for (i,j) in [(0,1),(0,2),(1,2)]:
            z=[tt[q] for q in range(3) if q not in (i,j)][0]
            third=c[z]-sum(1 for q in (i,j) if tt[q]==z)
            D=third
            for (a,b) in [(0,1),(0,2),(1,2)]:
                if (a,b)!=(i,j): D*=prob[(tt,tuple(sorted((tt[a],tt[b]))))]
            Ds.append(D)
        spread=max(spread,max(Ds)/min(Ds)-1); tot+=t[tt]*(math.log(Ds[0])-2)
    Phi=sum(t[tt]*(math.log(N(tt)/t[tt])-2) for tt in T)
    return spread, (H+tot-Phi)/Phi
for k in [1,2,3,4,5]: print('k=%d spread=%.2e identity_rel_error=%.2e'%((k,)+check(k,k)))
