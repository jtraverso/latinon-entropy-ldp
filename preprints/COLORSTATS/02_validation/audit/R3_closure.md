# Audit round 3 — closure (independent agent, read-only, 17 Nov 2026)

Verdict: **PASS** — no open finding of MENOR or higher.

## Round-2 findings
| Finding | Status | Evidence |
|---|---|---|
| N1 §5.4 Claim A, Freedman | CLOSED | Claim A matches the proof: (|A|−|B|)⁺ ≤ |ι|+|Bad|, plus s₂+s′; in step 2 the halves differ by O(√n log n) ≤ n^{1/2+γ′}. Freedman cited [32] at first use. |
| N2 §5.9 O(n) | CLOSED | Rounding mismatch O(k+ℓ)·o_X = O(n), so φ_X = 1+O(1/n). |
| N3 §5.11 Lemma 5.6 | CLOSED | nm^{−1/1000} = o(ρ²n) ⇔ δ′ < 4/2001; nm^{1−1/900} ≤ m^{2−1/1000} ⇔ δ′ < 4/9001 ≈ 4.444·10⁻⁴; δ′ = ε_G³/40 < 1/2560 ≈ 3.906·10⁻⁴. |
| ED-a, ED-d §5.10 | CLOSED | σ and s₀ with C_L consistent with R2, R3 (p d₀ s₀/4 − Δ_W ≥ σ, p d₀ σ/16 > Δ_W); the step-1 conditions are δ′ < 4/1801 and c₀ > δ′/2; the third condition δ′ < 4/9001 is sufficient (exact threshold 4/901). |
| ED-b, ED-c | CLOSED | m_τ = t′(1 ± O(n^{−ε_G³})); m = Σ⌊κc_X⌋ = (1+o(1))n^{1−δ′/4}. |
| ED-e Lemma 5.8 | CLOSED | Agψ = r₀, ‖ψ‖ ≤ 1/(2C₀m); no d₀ left in the lemma. |
| η_T | CLOSED | §5.1 item 2, Table 2, proof of Lemma 5.10: s_i/4 ≥ λ²m²/64 ≥ η_T m². |
| E5 renamings (5.16, 5.17, 5.20) | CLOSED | Proof of Lemma 5.16 recomputed with ξ and W_Σ: Σξ = 0, Y_C = 0, Z_y = ξ, AAᵀy = x. |
| C_L in §§5.10, 6.3 | CLOSED | No loose C in the role of C_L. |
| R2-4, R2-7 | CLOSED | Z_r defined at first use; Lemma 6.5 proof complete. |
| R2-1, E9 proportions | CLOSED | stsrate2.py rerun: (0.47, 0.288619, 0.120690, 0.120690) gives 0.6337 and 0.5011; rounded values sum to 1.0000, Σγ² = 0.333327. |
| R2-5 abstract | CLOSED | Existence implies admissibility, which implies classes n/3 + O(√n). |
| R2-6 DOIs | CLOSED | 27 doi.org links in the TeX and 53 URIs in the PDF; none ends in a period. |
| E1, E2, E4, E6, E7, E8 | CLOSED | Abbreviated locators only in Table 1; no GJKKL/EGJ acronyms; [22] arXiv version; Egorychev DOI; LDP spelling; [11] URL. |
| R2-2, R2-8, E_h | AUTHOR_DECISION | Not reopened. |

## Regression sweep
Cross-references (script): none dangling. Citations [1]–[36] in first-appearance order, all listed. No half-applied renaming except η in
Appendix A (E-2). British spelling only in the cited title "Coloured" and in E-3. Corrections present in TeX; PDF newer; page 20 rendered.

## New findings (all EDITORIAL, optional) — applied after this round
- E-1 §5.4 / Lemma 5.1 R3: R3 stated for |T| ≥ s₀/2 (its proof only uses t ≫ log n), and Claim A notes that each half has at least
  (1 − o(1))s₀ points.
- E-2 Appendix A, Theorem T⁺: tolerance η → η_T.
- E-3 "Afterwards" → "Afterward"; "towards" → "toward".

## Observations
- O-1 §5.10: δ′ < 4/9001 is stronger than needed (4/901) and holds; no change.
- O-2 front matter: the DOI 10.5281/zenodo.24308221 is reserved, so it resolves only after the deposit is published (as for the
  Latinon DOI). The Markdown front matter was updated to preprint 1.0 at the same time as the TeX.

## Coverage
VERIFIED: every listed fix, threshold arithmetic (4/1001, 4/2001, 4/1801, 4/9001, 3.91·10⁻⁴), Hall/σ/s₀ computations of §§5.4 and 5.10,
proofs of Lemmas 5.8, 5.16, 6.5, Remark 7.2 values (script rerun), DOIs in TeX and PDF, citation order, cross-references, symbol and
spelling sweeps. READ (not re-verified beyond round 2): the rest of §§5.1–5.11 and §6, Appendix B, bibliographic metadata. Black
boxes: T, T⁺, [18], [29], Freedman, [8].
