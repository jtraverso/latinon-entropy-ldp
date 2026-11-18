# Audit round 4 — closure (independent agent, read-only, 17 Nov 2026)

Verdict: **PASS** — no open finding of MENOR or higher.

| Finding | Status | Evidence |
|---|---|---|
| F1 §1.7 | CLOSED | (a) "plus the loss O(ηn²) from typicality in Theorem 1.9(a)" matches `typed_upper_G`; (b) "in the form with Φ(t), not in the normalized form with D(Q‖P) of Theorems 1.5 and 1.7" matches MAPPING 2 and FREEZE; (c) scope "upper bounds of the main theorems and the finite algebra of Sections 5.8–5.10", non-formalized list includes Corollaries 1.4 and 1.11 and Lemmas 4.1–4.2. 89 queries with only the standard axioms; axiom-log hash equals FREEZE; dependence on [8]; T/T⁺ in [17], [18] in [19], [29] not formalized. ES identical in content. |
| F2 after Corollary 1.11 | CLOSED | [8, Theorem 1.1] (published text) completes sparse families of allowed (bicolored) blocks to bicolored systems with exact counts; Corollary 1.11 needs every type of order n², so it does not count those completions. |
| F3 companion | CLOSED | No "integer sum" / "suma entera" left; Lemmas 5.17 and 5.20 say "integer combination". |
| E1–E4 | CLOSED (E1 completed after this check) | |
| PARITY | OK | status PASS; hashes equal to the md files; TeX/PDF hashes match TYPESETTING records. |

## Editorial items raised by the closure (all applied by `editorial/fix_round4b.py`)
- N1 ES companion: "La conclusiones" → "Las conclusiones".
- N2 companions §1: scope sentence aligned with §1.7.
- N3 §1.7: Lemmas 3.1 and 5.21 added to the non-formalized list (EN and ES).
- N4 ES: one term for completion, "compleción" (the plural "completaciones" for third points in §5.8 kept).
- N5 mapping notes items 12 and 5 updated.
- Optional precision on Corollary 1.11 applied: "Instead of sparseness of $\mathcal Q$, it requires that the leftover graph be
  typical and that every block type … have order $n^2$".

Coverage: md EN/ES and companions read; TeX/PDF checked by hash and text extraction; no build run.
