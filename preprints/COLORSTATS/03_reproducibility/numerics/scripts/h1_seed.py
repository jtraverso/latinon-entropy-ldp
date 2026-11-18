"""Sanity checks for the H1 seed lemmas (existence on samples only; not a proof).

Test A (Lemma S): host K[U] with k classes minus a sparse deletion D chosen so that the
balance functional vanishes. LP: maximise the minimum triangle weight subject to exact
unit edge loads. Compare with the base weight a_ij/(u_i-1).

Test B (constant-density variant): a random graph with density p and #cross = 2 #internal.
Same LP; compare with a_ij/((u_i-1) p^2).
"""
import itertools, random, sys
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import lil_matrix


def classes_of(sizes):
    lab = []
    for i, s in enumerate(sizes):
        lab += [i] * s
    return lab


def solve(n, lab, edges, box=None):
    eidx = {e: i for i, e in enumerate(sorted(edges))}
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v); adj[v].add(u)
    tris = []
    for u, v in sorted(edges):
        for w in adj[u] & adj[v]:
            if w > v:
                if len({lab[u], lab[v], lab[w]}) == 2:
                    tris.append((u, v, w))
    T, E = len(tris), len(eidx)
    A = lil_matrix((E, T + 1))
    for j, (u, v, w) in enumerate(tris):
        for e in ((u, v), (u, w), (v, w)):
            A[eidx[e], j] = 1.0
    # variables: mu_T (T of them) and s; maximise s subject to mu_T >= s, A mu = 1
    c = np.zeros(T + 1); c[-1] = -1.0
    G = lil_matrix((T, T + 1))
    for j in range(T):
        G[j, j] = -1.0; G[j, T] = 1.0
    res = linprog(c, A_ub=G.tocsr(), b_ub=np.zeros(T), A_eq=A.tocsr(), b_eq=np.ones(E),
                  bounds=[((box[0] if box else 0), (box[1] if box else None))] * T + [(None, None)], method='highs')
    if res.status != 0:
        return None, T, E
    mu = res.x[:T]
    return (mu.min(), mu.max()), T, E


def balance(lab, edges):
    cross = sum(1 for u, v in edges if lab[u] != lab[v])
    return cross - 2 * (len(edges) - cross)


def test_A(u, k, extra_int, seed):
    random.seed(seed)
    sizes = [u] * k
    n = u * k
    lab = classes_of(sizes)
    full = {(a, b) for a in range(n) for b in range(a + 1, n)}
    need = balance(lab, full)  # l(K[U]); D must carry the same balance
    deg = [0] * n
    D = set()
    cap = 4
    def add(kind):
        for _ in range(100000):
            a, b = random.sample(range(n), 2)
            e = (min(a, b), max(a, b))
            if e in D or deg[a] >= cap or deg[b] >= cap:
                continue
            if (lab[a] == lab[b]) != (kind == 'int'):
                continue
            D.add(e); deg[a] += 1; deg[b] += 1
            return
        raise RuntimeError('cannot place')
    for _ in range(extra_int):
        add('int')
    for _ in range(need + 2 * extra_int):
        add('cross')
    edges = full - D
    assert balance(lab, edges) == 0
    base = 0.5 / (u - 1) if k == 3 else None
    out, T, E = solve(n, lab, edges, (base / 2, 2 * base))
    return n, max(deg), len(D), T, E, out, base


def test_B(u, p, seed):
    random.seed(seed)
    k = 3
    n = u * k
    lab = classes_of([u] * k)
    full = [(a, b) for a in range(n) for b in range(a + 1, n)]
    internal = [e for e in full if lab[e[0]] == lab[e[1]]]
    cross = [e for e in full if lab[e[0]] != lab[e[1]]]
    ni = int(round(p * len(internal)))
    edges = set(random.sample(internal, ni)) | set(random.sample(cross, 2 * ni))
    assert balance(lab, edges) == 0
    base = 0.5 / ((u - 1) * p * p)
    out, T, E = solve(n, lab, edges, (base / 2, 2 * base))
    return n, 2 * ni / len(cross), T, E, out, base


if __name__ == '__main__':
    print('Test A: K[U] minus sparse D, balance zero')
    for u, k, extra, seed in [(8, 3, 3, 1), (12, 3, 6, 2), (16, 3, 10, 3), (20, 3, 15, 4)]:
        n, dmax, dsize, T, E, out, base = test_A(u, k, extra, seed)
        if out is None:
            print(f'  m={n} k={k} |D|={dsize} maxdeg={dmax}: INFEASIBLE'); continue
        lo, hi = out
        tag = f' base={base:.4f} lo/base={lo/base:.3f} hi/base={hi/base:.3f}' if base else f' lo*m={lo*n:.3f} hi*m={hi*n:.3f}'
        print(f'  m={n} k={k} |D|={dsize} maxdeg={dmax} tri={T} edges={E}: min={lo:.4f} max={hi:.4f}{tag}')
    print('Test B: random density p, #cross = 2 #internal')
    for u, p, seed in [(14, 0.7, 1), (20, 0.7, 2), (20, 0.5, 3), (28, 0.5, 4)]:
        n, pc, T, E, out, base = test_B(u, p, seed)
        if out is None:
            print(f'  n={n} p={p}: INFEASIBLE (tri={T}, edges={E})'); continue
        lo, hi = out
        print(f'  n={n} p_int={p} p_cross={pc:.3f} tri={T} edges={E}: min={lo:.4f} max={hi:.4f} base={base:.4f} lo/base={lo/base:.3f} hi/base={hi/base:.3f}')
