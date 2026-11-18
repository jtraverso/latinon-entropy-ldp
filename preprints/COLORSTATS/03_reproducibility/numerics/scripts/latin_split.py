# Numerical test of the exact split (Lemma B') for Latin outlines.
import sys, random, itertools, math
import numpy as np, networkx as nx
def run(n, K, p, shift, seed):
    rng = random.Random(seed); npr = np.random.default_rng(seed)
    P = [list(range(n)) for _ in range(3)]
    for x in P: rng.shuffle(x)
    L = lambda r, c: P[2][(P[0][r] + P[1][c]) % n]          # Latin square
    cls = [ [ (v * K) // n for v in npr.permutation(n) ] for _ in range(3)]  # classes of rows, cols, syms
    R_, C_, S_ = cls
    kept = [(r, c, L(r, c)) for r in range(n) for c in range(n) if rng.random() < p]
    q = np.zeros((K, K, K), dtype=int)
    for r, c, s in kept: q[R_[r], C_[c], S_[s]] += 1
    f = np.zeros((K, K, K), dtype=int)
    for a, b, d in itertools.product(range(2), repeat=3): f[a, b, d] = (-1) ** (a + b + d)
    q = q + shift * f
    assert q.min() > 0
    RC = [(r, c) for r, c, s in kept]; RS = [(r, s) for r, c, s in kept]; CS = [(c, s) for r, c, s in kept]
    deg = {}
    def add(key): deg[key] = deg.get(key, 0) + 1
    for r, c, s in kept:
        add(('R', r, 'C', C_[c])); add(('R', r, 'S', S_[s])); add(('C', c, 'R', R_[r]))
        add(('C', c, 'S', S_[s])); add(('S', s, 'R', R_[r])); add(('S', s, 'C', C_[c]))
    def D(*k): return deg.get(k, 0)
    def round_margins(F, rows, cols):
        lo = np.floor(F).astype(int); rr = rows - lo.sum(1); cc = cols - lo.sum(0)
        G = nx.DiGraph()
        for a in range(K):
            G.add_edge('s', ('a', a), capacity=int(rr[a]))
            G.add_edge(('b', a), 't', capacity=int(cc[a]))
        for a, b in itertools.product(range(K), repeat=2):
            if F[a, b] > lo[a, b]: G.add_edge(('a', a), ('b', b), capacity=1)
        val, fl = nx.maximum_flow(G, 's', 't')
        assert val == rr.sum(), "rounding failed"
        X = lo.copy()
        for a, b in itertools.product(range(K), repeat=2):
            X[a, b] += fl.get(('a', a), {}).get(('b', b), 0)
        return X
    def targets(kind, o1, o2, members_of, cls_of, qslice):
        # per vertex v of class u: matrix over (classes of o1) x (classes of o2)
        out = {}
        for u in range(K):
            V = members_of[u]
            rows = np.array([[D(kind, v, o1, a) for a in range(K)] for v in V])
            cols = np.array([[D(kind, v, o2, b) for b in range(K)] for v in V])
            A = qslice(u) / len(V)
            mr, mc = rows.mean(0), cols.mean(0)
            w1, w2 = mr / mr.sum(), mc / mc.sum()
            X = {}
            for idx, v in enumerate(V):
                dr, dc = rows[idx] - mr, cols[idx] - mc; dd = dr.sum()
                Fr = A + np.outer(dr, w2) + np.outer(w1, dc) - dd * np.outer(w1, w2)
                assert Fr.min() > 0
                X[v] = round_margins(Fr, rows[idx], cols[idx])
            E = sum(X.values()) - qslice(u)
            Vl = list(V); ptr = 0
            for a, b in itertools.product(range(1, K), repeat=2):
                v_ = E[a, b]
                for _ in range(abs(v_)):
                    m = np.zeros((K, K), dtype=int); m[a, b] = m[0, 0] = 1; m[a, 0] = m[0, b] = -1
                    X[Vl[ptr % len(Vl)]] -= int(np.sign(v_)) * m; ptr += 1
            assert (sum(X.values()) == qslice(u)).all()
            assert min(x.min() for x in X.values()) >= 0
            out.update(X)
        return out
    mem = lambda arr: [[v for v in range(n) if arr[v] == u] for u in range(K)]
    a = targets('R', 'C', 'S', mem(R_), R_, lambda i: q[i, :, :])       # a[r][j,l]
    b = targets('C', 'R', 'S', mem(C_), C_, lambda j: q[:, j, :])       # b[c][i,l]
    e = targets('S', 'R', 'C', mem(S_), S_, lambda l: q[:, :, l])       # e[s][i,j]
    def peel(edges, tl, tr, ncol):
        rem = set(edges); colour = {}
        for col in range(ncol - 1):
            G = nx.DiGraph(); E = list(rem); rng.shuffle(E)
            for x, y in E: G.add_edge(('x', x), ('y', y), capacity=1)
            need = 0
            for x in {x for x, _ in E}:
                G.add_edge('s', ('x', x), capacity=tl(x, col)); need += tl(x, col)
            for y in {y for _, y in E}:
                G.add_edge(('y', y), 't', capacity=tr(y, col))
            val, fl = nx.maximum_flow(G, 's', 't')
            if val != need: return None
            for x, y in E:
                if fl[('x', x)][('y', y)]: colour[(x, y)] = col; rem.discard((x, y))
        for ed in rem: colour[ed] = ncol - 1
        return colour
    colRC, colRS, colCS = {}, {}, {}
    for i, j in itertools.product(range(K), repeat=2):
        ed = [(r, c) for r, c in RC if R_[r] == i and C_[c] == j]
        cc = peel(ed, lambda r, l: int(a[r][j, l]), lambda c, l: int(b[c][i, l]), K)
        if cc is None: return 'RC peel failed'
        colRC.update(cc)
    for i, l in itertools.product(range(K), repeat=2):
        ed = [(r, s) for r, s in RS if R_[r] == i and S_[s] == l]
        cc = peel(ed, lambda r, j: int(a[r][j, l]), lambda s, j: int(e[s][i, j]), K)
        if cc is None: return 'RS peel failed'
        colRS.update(cc)
    for j, l in itertools.product(range(K), repeat=2):
        ed = [(c, s) for c, s in CS if C_[c] == j and S_[s] == l]
        cc = peel(ed, lambda c, i: int(b[c][i, l]), lambda s, i: int(e[s][i, j]), K)
        if cc is None: return 'CS peel failed'
        colCS.update(cc)
    # verify D0, D1
    for i, j, l in itertools.product(range(K), repeat=3):
        Grc = [(r, c) for (r, c), x in colRC.items() if x == l and R_[r] == i and C_[c] == j]
        Grs = [(r, s) for (r, s), x in colRS.items() if x == j and R_[r] == i and S_[s] == l]
        Gcs = [(c, s) for (c, s), x in colCS.items() if x == i and C_[c] == j and S_[s] == l]
        if not (len(Grc) == len(Grs) == len(Gcs) == q[i, j, l]): return f'D0 fails {i,j,l}'
        from collections import Counter
        A1, A2 = Counter(r for r, _ in Grc), Counter(r for r, _ in Grs)
        B1, B2 = Counter(c for _, c in Grc), Counter(c for c, _ in Gcs)
        E1, E2 = Counter(s for _, s in Grs), Counter(s for _, s in Gcs)
        if A1 != A2 or B1 != B2 or E1 != E2: return f'D1 fails {i,j,l}'
    return 'ok'
for n, K, p, shift in [(60, 2, 0.5, 0), (60, 2, 0.5, 5), (90, 2, 0.3, 8), (90, 3, 0.5, 6), (120, 2, 0.3, 15), (120, 3, 0.4, 10)]:
    for seed in range(2):
        print(n, K, p, shift, seed, run(n, K, p, shift, seed), flush=True)
