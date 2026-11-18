"""E2 (1-factorizations as triangle decompositions of K_m v C_h): finite checks."""
import itertools, random, math
import numpy as np
import sympy
from sympy.matrices.normalforms import smith_normal_form

# (a) explicit inverse on balanced vectors
def inv_check(m,h,seed):
    rng=np.random.default_rng(seed)
    V=range(m); C=range(h)
    VV=list(itertools.combinations(V,2)); VC=[(u,c) for u in V for c in C]
    tris=[(u,v,c) for (u,v) in VV for c in C]
    w=rng.normal(size=len(tris))
    x={}
    for wt,(u,v,c) in zip(w,tris):
        for e in [('VV',u,v),('VC',u,c),('VC',v,c)]: x[e]=x.get(e,0)+wt
    nrm=max(abs(a) for a in x.values())
    XV=[sum(x[('VV',*sorted((u,v)))] for v in V if v!=u) for u in V]
    XC=[sum(x[('VC',u,c)] for c in C) for u in V]
    assert max(abs(a-b) for a,b in zip(XV,XC))<1e-9
    Zx=[sum(x[('VC',u,c)] for u in V) for c in C]
    W=sum(x[('VV',u,v)] for (u,v) in VV)
    chi=[(Zx[c]-2*W/h)/(2*m-2) for c in C]
    y={}
    for (u,v) in VV: y[('VV',u,v)]=x[('VV',u,v)]/h
    for (u,c) in VC: y[('VC',u,c)]=(x[('VC',u,c)]-XV[u]/h-chi[c])/(m-2)
    psi={(u,v,c):y[('VV',u,v)]+y[('VC',u,c)]+y[('VC',v,c)] for (u,v,c) in tris}
    back={}
    for (u,v,c),p in psi.items():
        for e in [('VV',u,v),('VC',u,c),('VC',v,c)]: back[e]=back.get(e,0)+p
    err=max(abs(back[e]-x[e]) for e in x)
    return err, max(abs(p) for p in psi.values())*min(m,h)/nrm
print('(a) inverse on balanced vectors of K_m v C_h: (max error, max|psi| min(m,h)/||x||)')
for m,h,s in [(6,5,1),(8,7,2),(10,9,3),(12,6,4),(7,14,5)]: print('   m=%d h=%d'%(m,h), inv_check(m,h,s))

# (b) lattice of the host minus random edges: rank(span)+rank(constraints)=|E| and no torsion?
def lattice_check(m,h,dels,seed):
    rng=random.Random(seed)
    E=[('VV',u,v) for u,v in itertools.combinations(range(m),2)]+[('VC',u,c) for u in range(m) for c in range(h)]
    for e in rng.sample(E,dels): E.remove(e)
    idx={e:i for i,e in enumerate(E)}
    rows=[]
    for (u,v) in itertools.combinations(range(m),2):
        for c in range(h):
            es=[('VV',u,v),('VC',u,c),('VC',v,c)]
            if all(e in idx for e in es):
                r=[0]*len(E)
                for e in es: r[idx[e]]=1
                rows.append(r)
    D=smith_normal_form(sympy.Matrix(rows),domain=sympy.ZZ)
    d=[abs(D[i,i]) for i in range(min(D.shape)) if D[i,i]!=0]
    # constraints: balance at V vertices (integer), parity at colour vertices (mod 2)
    B=[]
    for u in range(m):
        r=[0]*len(E)
        for i,e in enumerate(E):
            if e[0]=='VV' and u in e[1:]: r[i]=1
            if e[0]=='VC' and e[1]==u: r[i]=-1
        B.append(r)
    rB=sympy.Matrix(B).rank()
    return {'edges':len(E),'rank_span':len(d),'rank_balance':rB,'torsion':sorted(x for x in d if x!=1),
            'expected_torsion_rank': h-1}
print('(b) lattice: rank(span)+rank(balance) should be |E|; torsion (Z/2)^(h-1) from colour-vertex parities')
for m,h,dl,s in [(5,4,2,1),(6,5,3,2)]: print('  ', m,h, lattice_check(m,h,dl,s))

# (c) types (XY,Gamma): lattice of pair-preserving changes and 4-cycle swaps
def types(k,l): return [(X,Y,g) for X,Y in itertools.combinations_with_replacement(range(k),2) for g in range(l)]
def constraints(k,l):
    T=types(k,l); rows=[]
    for X,Y in itertools.combinations_with_replacement(range(k),2):
        rows.append([1 if (t[0],t[1])==(X,Y) else 0 for t in T])
    for X in range(k):
        for g in range(l):
            rows.append([ (1+(t[0]==t[1]))*(X in t[:2]) if t[2]==g else 0 for t in T])
    return T,sympy.Matrix(rows)
def swap_vec(k,l,cls,g1,g2):
    T=types(k,l); ti={t:i for i,t in enumerate(T)}; v=[0]*len(T)
    def ty(a,b,g): return ti[(min(a,b),max(a,b),g)]
    X1,X2,X3,X4=cls
    for (a,b,g,s) in [(X1,X2,g1,1),(X3,X4,g1,1),(X2,X3,g2,1),(X4,X1,g2,1),(X1,X2,g2,-1),(X3,X4,g2,-1),(X2,X3,g1,-1),(X4,X1,g1,-1)]:
        v[ty(a,b,g)]+=s
    return v
for k,l in [(1,2),(2,2),(2,3),(3,2),(3,3)]:
    T,Cm=constraints(k,l); ker=len(T)-Cm.rank()
    vecs={tuple(swap_vec(k,l,cls,g1,g2)) for cls in itertools.product(range(k),repeat=4) for g1 in range(l) for g2 in range(l)}
    vecs=[list(v) for v in vecs if any(v)]
    if not vecs: print('(c) k=%d l=%d kernel rank %d, no swaps'%(k,l,ker)); continue
    M=sympy.Matrix(vecs); D=smith_normal_form(M,domain=sympy.ZZ)
    d=sorted({abs(D[i,i]) for i in range(min(D.shape)) if D[i,i]!=0})
    # saturation check: is span_Z(swaps) = kernel ∩ Z^T ? compare with integer kernel basis via sympy nullspace (rational)
    ns=Cm.nullspace()
    print('(c) k=%d l=%d: kernel rank %d, swap rank %d, swap SNF divisors %s'%(k,l,ker,M.rank(),d))

# (d) colour-first identity for the 1F host
def identity(k,l,seed):
    rng=random.Random(seed); c=[rng.randint(30,60)*2 for _ in range(k)]; n=sum(c); hsz=[0]*l
    rem=n-1
    for g in range(l-1): hsz[g]=rng.randint(rem//(l+1),rem//l); rem-=hsz[g]
    hsz[-1]=rem
    T=types(k,l)
    e=lambda X,Y: c[X]*c[Y] if X!=Y else math.comb(c[X],2)
    # t0 proportional: t(XY,g) = e(X,Y) h_g/(n-1) satisfies identities
    t={(X,Y,g):e(X,Y)*hsz[g]/(n-1) for (X,Y,g) in T}
    T_,Cm=constraints(k,l)
    for v in Cm.nullspace():
        lam=rng.uniform(-0.2,0.2)*min(t.values())/max(abs(float(a)) for a in v)
        for i,tt in enumerate(T_): t[tt]+=lam*float(v[i])
    assert min(t.values())>0
    PVV={(X,Y,g):t[(X,Y,g)]/e(X,Y) for (X,Y,g) in T}
    def PVC(X,g,Y):
        a,b=min(X,Y),max(X,Y); return (1+(X==Y))*t[(a,b,g)]/(c[X]*hsz[g])
    H=-sum(e(X,Y)*PVV[(X,Y,g)]*math.log(PVV[(X,Y,g)]) for (X,Y,g) in T)
    H+=-sum(c[X]*hsz[g]*PVC(X,g,Y)*math.log(PVC(X,g,Y)) for X in range(k) for g in range(l) for Y in range(k))
    spread=0; tot=0
    for (X,Y,g) in T:
        D1=hsz[g]*PVC(X,g,Y)*PVC(Y,g,X)
        D2=(c[Y]-(X==Y))*PVV[(X,Y,g)]*PVC(Y,g,X)
        D3=(c[X]-(X==Y))*PVV[(X,Y,g)]*PVC(X,g,Y)
        spread=max(spread,max(D1,D2,D3)/min(D1,D2,D3)-1); tot+=t[(X,Y,g)]*(math.log(D1)-2)
    Phi=sum(t[tt]*(math.log(e(tt[0],tt[1])*hsz[tt[2]]/t[tt])-2) for tt in T)
    return spread,(H+tot-Phi)/Phi
print('(d) colour-first identity for 1-factorization types: (degree spread, relative identity error)')
for k,l in [(1,1),(1,3),(2,2),(3,2),(2,3)]: print('   k=%d l=%d'%(k,l), identity(k,l,k*10+l))
