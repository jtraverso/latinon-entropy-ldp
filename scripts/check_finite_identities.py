"""Deterministic regressions for the written finite identities, not proofs of the LDP."""
from pathlib import Path
from itertools import permutations,product,combinations
from fractions import Fraction as F
from math import log,exp,lgamma,sqrt,factorial,comb
import random,json,hashlib

root=Path(__file__).resolve().parents[1]
checks={}
count=0
for n in range(1,101):
    for m in range(13):
        lhs=sum(log((m+k)/n) for k in range(1,n+1))
        rhs=-n+(m+1)*log(n)+m*(m+1)+1
        assert lhs<=rhs+1e-10,(n,m,lhs,rhs)
        count+=1
checks['finite_label_logarithm_bound']=count

count=0
for q,m in product([F(0),F(1,4),F(1,2),F(1)],repeat=2):
    for a,b in product(range(5),repeat=2):
        if not a+b:continue
        delta=F(1,100)
        new=q+delta*(a-b)
        if q<m and new>m:continue
        if q>m and new<m:continue
        fc=-1 if q<m else 1
        bc=-1 if q>m else 1
        assert abs(new-m)-abs(q-m)<=delta*(a*fc+b*bc)
        count+=1
checks['repeated_arc_one_sided_cost']=count

rng=random.Random(20261115)
count=0
for n in range(1,31):
    for trial in range(20):
        cuts=sorted([0.0,1.0]+[rng.random() for _ in range(n-1)])
        masses=[cuts[i+1]-cuts[i] for i in range(n)]
        remaining=1.0
        total=0.0
        for p in masses:
            total+=p*log(remaining)
            remaining-=p
        assert total>=-1-1e-10,(n,total)
        count+=1
checks['fluid_right_endpoint_direction']=count

count=0
for n in range(1,7):
    ps=list(permutations(range(n)))
    weights=[rng.random()+0.1 for _ in range(7)]
    selected=[rng.choice(ps) for _ in weights]
    q=[[0.2/n for _ in range(n)] for _ in range(n)]
    for p,w in zip(selected,weights):
        for i,j in enumerate(p):q[i][j]+=0.8*w/sum(weights)
    raw=[]
    for p in ps:
        w=1.0
        for i,j in enumerate(p):w*=q[i][j]
        raw.append(w)
    per=sum(raw)
    mu=[w/per for w in raw]
    marginal=[[sum(w for p,w in zip(ps,mu) if p[i]==j) for j in range(n)] for i in range(n)]
    assert per+1e-12>=factorial(n)/n**n
    entropy=-sum(w*log(w) for w in mu if w)
    rhs=sum(marginal[i][j]*log(1/q[i][j]) for i in range(n) for j in range(n))+log(per)
    assert abs(entropy-rhs)<1e-10
    for trial in range(5):
        g=[[rng.uniform(-1,1) for _ in range(n)] for _ in range(n)]
        for s in [-1,-0.3,0.2,1]:
            direct=sum(w*exp(s*sum(g[i][p[i]] for i in range(n))) for p,w in zip(ps,mu))
            tilted=0.0
            for p in ps:
                w=1.0
                for i,j in enumerate(p):w*=q[i][j]*exp(s*g[i][j])
                tilted+=w
            assert abs(direct-tilted/per)<1e-9
            count+=1
checks['permanental_entropy_and_mgf_identity']=count

count=0;latin_counts={}
for n in range(1,5):
    ps=list(permutations(range(n)))
    squares=[]
    def extend(rows):
        if len(rows)==n:squares.append(tuple(rows));return
        for row in ps:
            if all(all(row[j]!=old[j] for j in range(n)) for old in rows):extend(rows+[row])
    extend([])
    latin_counts[n]=len(squares)
    assert len(squares)==[0,1,2,12,576][n]
    for square in squares:
        factors=[frozenset((i,j) for i in range(n) for j in range(n) if square[i][j]==z) for z in range(n)]
        recovered=tuple(tuple(next(z for z in range(n) if (i,j) in factors[z]) for j in range(n)) for i in range(n))
        assert square==recovered
        for k,l in [(1,1),(1,2),(2,1),(2,2)]:
            if max(k,l)>n:continue
            pattern_counts={}
            for xs,ys in product(combinations(range(n),k),combinations(range(n),l)):
                vals=[square[i][j] for i in xs for j in ys]
                if len(set(vals))!=k*l:continue
                pattern=tuple(sorted(vals).index(v) for v in vals)
                pattern_counts[pattern]=pattern_counts.get(pattern,0)+1
            for c in pattern_counts.values():
                direct=F(c,comb(n,k)*comb(n,l))
                aux=F(factorial(k)*factorial(l)*c,n**(k+l))
                beta=F(factorial(n)//factorial(n-k)*(factorial(n)//factorial(n-l)),n**(k+l))
                assert aux==beta*direct
                count+=1
checks['exact_binomial_bridge_instances']=count
checks['latin_square_enumeration']=latin_counts

# One oriented base group triple, nine Wilson slots, local order two.
tau=[[1,0,2],[0,2,1],[2,1,0]]
local=[((0,1),(1,0)),((1,0),(0,1))]
systems=set();footprint=None;types=None
for choices in product(range(2),repeat=9):
    blocks=set()
    for a,b in product(range(3),repeat=2):
        square=local[choices[3*a+b]]
        for i,j in product(range(2),repeat=2):
            blocks.add(frozenset([(0,a,i),(1,b,j),(2,tau[a][b],square[i][j])]))
    pairs=[frozenset(p) for block in blocks for p in combinations(block,2)]
    assert len(pairs)==len(set(pairs))==108
    vector={}
    for block in blocks:
        colors=tuple(sorted(v[1] for v in block))
        assert len(set(colors))==2
        vector[colors]=vector.get(colors,0)+1
    if footprint is None:footprint=set(pairs);types=vector
    assert footprint==set(pairs) and types==vector
    systems.add(frozenset(blocks))
assert len(systems)==2**9
checks['wilson_local_families_with_identical_pair_footprint']=len(systems)
checks['wilson_type_vector']={str(k):v for k,v in types.items()}
report={'status':'PASS','scope':'Finite regressions for written identities; not a numerical proof of asymptotic or analytic theorems',
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'checks':checks}
path=root/'preprints/LATINON/02_validation/FINITE_REGRESSIONS.json'
path.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(report,indent=2))
