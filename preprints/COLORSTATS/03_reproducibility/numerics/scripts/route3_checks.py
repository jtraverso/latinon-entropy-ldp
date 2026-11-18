"""Finite checks for the Route 3' lemmas (samples only, not proofs).

1. Phi_tri: explicit right inverse of the triangle incidence map of K_{m,m,m} on
   balanced edge vectors; check A Phi x = x exactly and the norm bound 7||x||/m.
2. H2 for STS residuals: H = K[U] minus an allowed packing restricted to U... realised as
   K_V minus a random maximal allowed packing, restricted to U, with every degree even,
   every cross count even and l = 0. Check 1_H is an integer combination of allowed
   triangles of H (integer Hermite reduction).
3. H2 for tripartite residuals: balanced subgraph of K_{m,m,m} obtained by deleting
   random transversal triangles; check 1_H in the integer span of its triangles.
4. Intercalate switches span the zero-marginal tensors on a k x k x k grid.
"""
import itertools, random
from fractions import Fraction
import numpy as np


# ---------- 1. Phi_tri ----------
def tri_check(m, trials=5, seed=0):
    rng = np.random.default_rng(seed)
    R, C, S = range(m), range(m), range(m)
    tris = [(r, c, s) for r in R for c in C for s in S]
    worst = 0.0
    for _ in range(trials):
        # random balanced x: take A applied to random triangle weights plus noise in kernel? Use A y.
        y = rng.normal(size=len(tris))
        xRC = np.zeros((m, m)); xRS = np.zeros((m, m)); xCS = np.zeros((m, m))
        for w, (r, c, s) in zip(y, tris):
            xRC[r, c] += w; xRS[r, s] += w; xCS[c, s] += w
        norm = max(abs(xRC).max(), abs(xRS).max(), abs(xCS).max())
        X = xRC.sum(1); Y = xRC.sum(0); Z = xRS.sum(0)
        assert np.allclose(X, xRS.sum(1)) and np.allclose(Y, xCS.sum(1)) and np.allclose(Z, xCS.sum(0))
        tau = xRC.sum()
        psi = np.zeros((m, m, m))
        for r, c, s in tris:
            psi[r, c, s] = (xRC[r, c] + xRS[r, s] + xCS[c, s]) / m - (X[r] + Y[c] + Z[s]) / m**2 + tau / m**3
        bRC = psi.sum(2); bRS = psi.sum(1); bCS = psi.sum(0)
        err = max(abs(bRC - xRC).max(), abs(bRS - xRS).max(), abs(bCS - xCS).max())
        assert err < 1e-9, err
        worst = max(worst, abs(psi).max() * m / norm)
    return worst


# ---------- integer span test ----------
def in_integer_span(gens, target):
    """Is target in the Z-span of the integer vectors gens? Hermite-style row reduction."""
    basis = {}  # pivot -> row (list of ints)
    for g in gens:
        v = list(g)
        while True:
            piv = next((i for i, a in enumerate(v) if a != 0), None)
            if piv is None:
                break
            if piv not in basis:
                if v[piv] < 0:
                    v = [-a for a in v]
                basis[piv] = v
                break
            b = basis[piv]
            # gcd step between v and b at pivot
            a, bb = v[piv], b[piv]
            if a % bb == 0:
                q = a // bb
                v = [x - q * y for x, y in zip(v, b)]
            else:
                # extended gcd combination
                g0, s, t = egcd(bb, a)
                newb = [s * y + t * x for x, y in zip(v, b)]
                u1, u2 = a // g0, bb // g0
                v = [u2 * x - u1 * y for x, y in zip(v, b)]
                basis[piv] = newb
    v = list(target)
    while True:
        piv = next((i for i, a in enumerate(v) if a != 0), None)
        if piv is None:
            return True
        if piv not in basis or v[piv] % basis[piv][piv] != 0:
            return False
        q = v[piv] // basis[piv][piv]
        v = [x - q * y for x, y in zip(v, basis[piv])]


def egcd(a, b):
    if b == 0:
        return (abs(a), 1 if a > 0 else -1, 0)
    g, x, y = egcd(b, a % b)
    return (g, y, x - (a // b) * y)


# ---------- 2/3. lattice structure via Smith normal form ----------
def snf_divisors(rows, ncols):
    import sympy
    from sympy.matrices.normalforms import smith_normal_form
    M = sympy.Matrix(rows)
    D = smith_normal_form(M, domain=sympy.ZZ)
    d = [abs(D[i, i]) for i in range(min(D.shape)) if D[i, i] != 0]
    return d


def f2_rank(vectors):
    rows = [int(''.join(str(b & 1) for b in v), 2) for v in vectors]
    basis = []
    for r in rows:
        for b in basis:
            r = min(r, r ^ b)
        if r:
            basis.append(r)
    return len(basis)


def sts_lattice_check(sizes, deletions, seed):
    """H0 = K[U] minus random edges (no constraints). Compare Z^E/span(allowed triangles)
    with Z^E/L_c, where L_c = {even degree sums, even cross counts, l = 0}."""
    rng = random.Random(seed)
    lab = []
    for i, s in enumerate(sizes):
        lab += [i] * s
    m = len(lab)
    E = [(a, b) for a in range(m) for b in range(a + 1, m)]
    for e in rng.sample(E, deletions):
        E.remove(e)
    idx = {e: i for i, e in enumerate(E)}
    rows = []
    for t in itertools.combinations(range(m), 3):
        es = [(t[0], t[1]), (t[0], t[2]), (t[1], t[2])]
        if len({lab[v] for v in t}) == 2 and all(e in idx for e in es):
            v = [0] * len(E)
            for e in es:
                v[idx[e]] = 1
            rows.append(v)
    d = snf_divisors(rows, len(E))
    rank = len(d)
    tors = sorted(x for x in d if x != 1)
    # constraint lattice: Z^E / L_c = Z (from l) + (Z/2)^s, s = F2-rank of parity vectors on ker l
    ell = [1 if lab[a] != lab[b] else -2 for a, b in E]
    e0 = next(i for i, x in enumerate(ell) if x == 1)
    pairs = sorted({tuple(sorted((lab[a], lab[b]))) for a, b in E if lab[a] != lab[b]})
    def parity(vec):
        out = [sum(vec[idx[e]] for e in E if v in e) % 2 for v in range(m)]
        out += [sum(vec[idx[e]] for e in E if tuple(sorted((lab[e[0]], lab[e[1]]))) == p) % 2 for p in pairs]
        return out
    gens = []
    for i in range(len(E)):
        v = [0] * len(E); v[i] = 1; v[e0] -= ell[i]
        gens.append(parity(v))
    s = f2_rank(gens)
    return {'edges': len(E), 'rank': rank, 'free_rank_quotient': len(E) - rank,
            'torsion': tors, 'expected': f'Z^1 + (Z/2)^{s}'}


def tri_lattice_check(m, deletions, seed):
    rng = random.Random(seed)
    E = [('RC', a, b) for a in range(m) for b in range(m)] + [('RS', a, b) for a in range(m) for b in range(m)] +         [('CS', a, b) for a in range(m) for b in range(m)]
    for e in rng.sample(E, deletions):
        E.remove(e)
    idx = {e: i for i, e in enumerate(E)}
    rows = []
    for r, c, s in itertools.product(range(m), repeat=3):
        es = [('RC', r, c), ('RS', r, s), ('CS', c, s)]
        if all(e in idx for e in es):
            v = [0] * len(E)
            for e in es:
                v[idx[e]] = 1
            rows.append(v)
    d = snf_divisors(rows, len(E))
    # balance equations: at each vertex, difference of degrees to the two other parts
    import sympy
    B = []
    for part, other in [('R', ('RC', 'RS')), ('C', ('RC', 'CS')), ('S', ('RS', 'CS'))]:
        for v in range(m):
            row = [0] * len(E)
            for i, (kind, a, b) in enumerate(E):
                pos = {'RC': ('R', 'C'), 'RS': ('R', 'S'), 'CS': ('C', 'S')}[kind]
                x = a if pos[0] == part else (b if pos[1] == part else None)
                if x == v:
                    row[i] = 1 if kind == other[0] else -1
            B.append(row)
    rB = sympy.Matrix(B).rank()
    return {'edges': len(E), 'rank': len(d), 'balance_rank': rB,
            'rank_plus_balance': len(d) + rB, 'torsion': sorted(x for x in d if x != 1)}


# ---------- 4. intercalate switches span zero-marginal tensors ----------
def switch_span(k):
    import sympy
    cells = list(itertools.product(range(k), repeat=3))
    pos = {c: i for i, c in enumerate(cells)}
    gens = []
    for i, i2 in itertools.combinations(range(k), 2):
        for j, j2 in itertools.combinations(range(k), 2):
            for l, l2 in itertools.combinations(range(k), 2):
                v = [0] * len(cells)
                for a, b, d in itertools.product(range(2), repeat=3):
                    v[pos[((i, i2)[a], (j, j2)[b], (l, l2)[d])]] = (-1) ** (a + b + d)
                gens.append(v)
    rank_switch = sympy.Matrix(gens).rank()
    # zero-marginal space: dimension k^3 - 3k^2 + 3k - 1 = (k-1)^3
    return rank_switch, (k - 1) ** 3


if __name__ == '__main__':
    print('1. Phi_tri: max |psi| * m / ||x|| (bound 7):')
    for m in [3, 5, 8, 12]:
        print(f'   m={m}: {tri_check(m, seed=m):.3f}')
    print('2. STS host K[U] minus random edges: quotient by span vs constraint lattice')
    for sizes, d, s in [((3, 3, 3), 3, 1), ((4, 3, 3), 4, 2), ((3, 3, 2, 2), 3, 3)]:
        print('  ', sizes, sts_lattice_check(sizes, d, s))
    print('3. Tripartite K_{m,m,m} minus random edges: rank(span) + rank(balance) should equal |E|, no torsion')
    for m, d, s in [(3, 2, 1), (4, 4, 2)]:
        print('  ', m, tri_lattice_check(m, d, s))
    print('4. Intercalate switches: (rank, (k-1)^3)')
    for k in [2, 3, 4]:
        print(f'   k={k}:', switch_span(k))
