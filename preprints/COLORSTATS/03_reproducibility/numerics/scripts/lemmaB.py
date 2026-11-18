# End-to-end small test of Lemma B: exact split of a leftover L into typed graphs G_tau, then SAT-decompose each.
import random, itertools, sys
import networkx as nx
from pysat.card import CardEnc, EncType
from pysat.formula import CNF
from pysat.solvers import Cadical153
def flow_bipartite(rows, cols, cap, rsum, csum):
    G=nx.DiGraph(); s,t='s','t'
    for r in rows: G.add_edge(s,('r',r),capacity=rsum[r])
    for c in cols: G.add_edge(('c',c),t,capacity=csum[c])
    for (r,c),u in cap.items():
        if u>0: G.add_edge(('r',r),('c',c),capacity=u)
    val,fl=nx.maximum_flow(G,s,t)
    if val!=sum(rsum.values()) or val!=sum(csum.values()): return None
    return {(r,c):fl[('r',r)].get(('c',c),0) for (r,c) in cap}
def ffactor_sat(edges, f):
    # choose subset of edges with deg = f(v)
    cnf=CNF(); var={e:i+1 for i,e in enumerate(edges)}; top=len(edges)
    inc={}
    for e in edges:
        for v in e: inc.setdefault(v,[]).append(var[e])
    for v,lits in inc.items():
        enc=CardEnc.equals(lits=lits,bound=f.get(v,0),top_id=top,encoding=EncType.seqcounter)
        top=max(top,enc.nv); cnf.extend(enc.clauses)
    for v in f:
        if v not in inc and f[v]!=0: return None
    with Cadical153(bootstrap_with=cnf.clauses) as S:
        if not S.solve(): return None
        m=set(x for x in S.get_model() if x>0)
    return [e for e in edges if var[e] in m]
def decompose_sat(Gedges, tris):
    cnf=CNF(); var={T:i+1 for i,T in enumerate(tris)}; top=len(tris)
    cover={}
    for T in tris:
        for e in itertools.combinations(T,2): cover.setdefault(frozenset(e),[]).append(var[T])
    for e in Gedges:
        lits=cover.get(frozenset(e),[])
        if not lits: return False
        enc=CardEnc.equals(lits=lits,bound=1,top_id=top,encoding=EncType.seqcounter); top=max(top,enc.nv); cnf.extend(enc.clauses)
    with Cadical153(bootstrap_with=cnf.clauses) as S: return S.solve()
def run(sizes, ntri, shift, seed):
    rng=random.Random(seed); k=len(sizes)
    cls=[]; [cls.extend([X]*s) for X,s in enumerate(sizes)]; n=len(cls); V=range(n)
    allowed=[T for T in itertools.combinations(V,3) if len({cls[v] for v in T})==2]
    rng.shuffle(allowed); used=set(); L=set(); q0={}
    for T in allowed:
        es=[frozenset(e) for e in itertools.combinations(T,2)]
        if any(e in used for e in es): continue
        used|=set(es); L|=set(es)
        cs=[cls[v] for v in T]; X=max(set(cs),key=cs.count); Y=[c for c in cs if c!=X][0]
        q0[(X,Y)]=q0.get((X,Y),0)+1
        if sum(q0.values())>=ntri: break
    q={(X,Y):q0.get((X,Y),0) for X in range(k) for Y in range(k) if X!=Y}
    if shift:   # cycle perturbation on classes 0->1->2->0
        for (X,Y) in [(0,1),(1,2),(2,0)]: q[(X,Y)]+=shift
        for (X,Y) in [(1,0),(2,1),(0,2)]: q[(X,Y)]-=shift
    if min(q.values())<0: return "neg-quota"
    dXX={v:0 for v in V}; dXY={(v,Y):0 for v in V for Y in range(k)}
    for e in L:
        u,w=tuple(e)
        if cls[u]==cls[w]: dXX[u]+=1; dXX[w]+=1
        else: dXY[(u,cls[w])]+=1; dXY[(w,cls[u])]+=1
    b={}
    for X in range(k):
        rows=[v for v in V if cls[v]==X]; cols=[Y for Y in range(k) if Y!=X]
        pi={(v,Y):dXY[(v,Y)]%2 for v in rows for Y in cols}
        rs={v:(dXX[v]-sum(pi[(v,Y)] for Y in cols)) for v in rows}
        cs={Y:(2*q[(X,Y)]-sum(pi[(v,Y)] for v in rows)) for Y in cols}
        if any(x%2 or x<0 for x in list(rs.values())+list(cs.values())): return "parity/neg in transport"
        rs={v:x//2 for v,x in rs.items()}; cs={Y:x//2 for Y,x in cs.items()}
        cap={(v,Y):(dXY[(v,Y)]-pi[(v,Y)])//2 for v in rows for Y in cols}
        m=flow_bipartite(rows,cols,cap,rs,cs)
        if m is None: return "transport infeasible"
        for (v,Y),x in m.items(): b[(v,Y)]=pi[(v,Y)]+2*x
    G={(X,Y):set() for X in range(k) for Y in range(k) if X!=Y}
    for X in range(k):
        for Y in range(X+1,k):
            EXY=[tuple(sorted(e)) for e in L if {cls[v] for v in e}=={X,Y}]
            Xs=[v for v in V if cls[v]==X]; Ys=[v for v in V if cls[v]==Y]
            # F: edges going to G_(X,Y): deg_F(x)=b[x,Y], deg_F(y)=dXY(y,X)-b[y,X]
            f={x:b[(x,Y)] for x in Xs}; f.update({y:dXY[(y,X)]-b[(y,X)] for y in Ys})
            F=ffactor_sat(EXY,f)
            if F is None: return "bipartite factor infeasible"
            Fs=set(F); G[(X,Y)]|={frozenset(e) for e in F}; G[(Y,X)]|={frozenset(e) for e in EXY if e not in Fs}
    for X in range(k):
        EXX=[tuple(sorted(e)) for e in L if {cls[v] for v in e}=={X}]
        cols=[Y for Y in range(k) if Y!=X]; rest=list(EXX)
        for Y in cols[:-1]:
            Fy=ffactor_sat(rest,{v:b[(v,Y)] for v in V if cls[v]==X})
            if Fy is None: return "XX colouring infeasible"
            G[(X,Y)]|={frozenset(e) for e in Fy}; s=set(Fy); rest=[e for e in rest if e not in s]
        G[(X,cols[-1])]|={frozenset(e) for e in rest}
    # verify divisibility and quotas exactly
    for (X,Y),E in G.items():
        nXX=sum(1 for e in E if {cls[v] for v in e}=={X}); nXY=len(E)-nXX
        if nXX!=q[(X,Y)] or nXY!=2*nXX: return f"quota mismatch {X,Y}"
        for v in V:
            dx=sum(1 for e in E if v in e and len({cls[u] for u in e})==1); dy=sum(1 for e in E if v in e and len({cls[u] for u in e})==2)
            if cls[v]==X and dx!=dy: return "div x"
            if cls[v]==Y and dy%2: return "div y"
    ok=all(decompose_sat(E,[T for T in itertools.combinations(sorted({v for e in E for v in e}),3)
              if sorted(cls[v] for v in T)==sorted([X,X,Y]) and all(frozenset(p) in E for p in itertools.combinations(T,2))])
           for (X,Y),E in G.items())
    return "split exact; SAT decomposition "+("OK" if ok else "FAILED (small n)")
for sizes,ntri in [((8,8,8),40),((10,10,10),60),((12,10,8),60)]:
    for shift in [0,1,-1,3]:
        print(sizes,ntri,"shift",shift,":",run(sizes,ntri,shift,seed=7))
