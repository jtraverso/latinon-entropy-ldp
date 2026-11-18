# Numerical checks for "Counting Steiner triple systems and Latin squares with prescribed colour statistics"

Finite sanity checks cited in the draft and its claims ledger. They are evidence on samples,
not proofs. Moved here on 17 November 2026 from a temporary session folder (gate G6) and
rerun once; outputs are in `logs/`, hashes in `MANIFEST.json`.

Environment of the rerun: Python 3.12.10, numpy 2.5.1, scipy 1.16.1, sympy 1.14.0,
networkx 3.6.1, python-sat 1.9.dev15. Run each script from `scripts/`
(`colourfirst.py` loads `stsrate2.py` from the working directory).

| Ledger ID | Draft location | Script | Rerun result |
|---|---|---|---|
| X2 | Lemma 5.2 (identity of Lemma A) | `colourfirst.py` | both sides 750381.69514566 |
| X5 | §6.3, Lemma 6.1 (CF-L) | `latin_identity.py` | errors ≤ 1.9e−9 on 5 outlines |
| X6 | Corollary 1.4, Remark 7.2 | `stsrate2.py` | k = 3: min D = 0.405465 = log 1.5; k = 4: 0.6337 vs 0.5011 |
| X7 | Lemma 6.3 (exact split) | `latin_split.py` | 12/12 runs ok |
| E1-INV | Lemma 5.13 | `e1_checks.py` (1) | AΦx = x to 9e−16 |
| E1-PASCH | Lemma 5.14 | `pasch_span.py`, `e1_checks.py` (2) | SNF divisors [1] for k = 2, 3, 4; Pasch certificates |
| E1-ID | Lemma 5.12 | `e1_identity.py` | spread and identity error ≤ 2.2e−16, k = 1–5 |
| E2-INV, E2-LAT, E2-SWAP, E2-ID | Lemmas 5.16–5.18, §5.9 | `e2_checks.py` (a)–(d) | as in the ledger |
| E3-LAT, E3-SEED, E3-INV | Lemmas 5.19–5.20 | `e3_checks.py` (1)–(3) | ‖I − AΦ̃‖ ∈ [0.37, 0.64]; seed LP ≥ 0.65 × base; see note 2 |
| R3-B3′, R3-Stri, R3-B3tri, intercalates | Lemma 5.9, §6.5, Lemma 6.6 | `route3_checks.py` | ranks and torsion as stated; intercalate rank (k − 1)³ for k = 2, 3, 4 |
| H1 seed | working note RUTA3_TMAS_SEMILLA_H1 | `h1_seed.py` | Test A positive; Test B infeasible (not used) |
| X3, X4 | not cited in draft 7.12 | `lemmaB.py` | see note 1 |

Notes.
1. `lemmaB.py` checks the "Lemma B" exact split of draft 1, which draft 2 replaced. As it now
   stands it runs 40- and 60-vertex instances, all reported infeasible; it does not reproduce
   the ledger entry X3 ("90, 100, 132 vertices, 12/12 exact"). That entry is unverified and is
   not used by the current draft.
2. In `e3_checks.py` (1) the sample G(10, p) has rank 29 < |E| = 30 (an edge in no triangle,
   so the graph is not rich); the samples m = 8, 9 show the predicted torsion (Z/2)^{m−1} ⊕ Z/3.
3. Section (3) of `e1_checks.py` used type vectors that do not satisfy the pair identities and
   is superseded by `e1_identity.py`.
