"""Do Pasch trades span all pair-preserving changes of block-type counts (all types allowed)?"""
import itertools, sympy
def run(k):
    types=list(itertools.combinations_with_replacement(range(k),3)); ti={t:i for i,t in enumerate(types)}
    pairs=list(itertools.combinations_with_replacement(range(k),2))
    # constraint matrix: pair-class counts of each type
    C=sympy.zeros(len(pairs),len(types))
    for j,t in enumerate(types):
        for a,b in itertools.combinations(t,2):
            C[pairs.index(tuple(sorted((a,b)))),j]+=1
    ker_dim=len(types)-C.rank()
    P1=[(0,1,2),(0,3,4),(1,3,5),(2,4,5)]; P2=[(0,1,3),(0,2,4),(1,2,5),(3,4,5)]
    rows=[]
    for col in itertools.product(range(k),repeat=6):
        v=[0]*len(types)
        for blk in P1: v[ti[tuple(sorted(col[x] for x in blk))]]+=1
        for blk in P2: v[ti[tuple(sorted(col[x] for x in blk))]]-=1
        if any(v): rows.append(tuple(v))
    rows=list(set(rows))
    M=sympy.Matrix(rows); r=M.rank()
    # integer span vs kernel lattice: compare Smith form torsion
    from sympy.matrices.normalforms import smith_normal_form
    D=smith_normal_form(M,domain=sympy.ZZ); d=[abs(D[i,i]) for i in range(min(D.shape)) if D[i,i]!=0]
    return len(types),ker_dim,r,sorted(set(d))
for k in [2,3,4]:
    print(k, run(k))
