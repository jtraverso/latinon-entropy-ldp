# Review guide — preprint 1.0

Read the [English manuscript](../../01_manuscript/color_stats_en.pdf) (the
[Spanish edition](../../01_manuscript/color_stats_es.pdf) has the same statements,
formulas and numbering). The [edition audit](COLORSTATS_RELEASE_AUDIT.json) records internal preparation;
independent mathematical review remains separate. The points below are where a reviewer's time is best spent.

1. **Rates and the minimization.** Lemmas 2.1–2.2, Proposition 1.3 and Section 3: the normalized form of the
   rate, the minimum log 1.5 for three classes, the integral vector of Corollary 1.4 and the k ≥ 4 argument of
   Remark 7.2 (equality is impossible; the numerical comparison 0.634 against 0.501 is an illustration).
2. **Upper bounds.** Lemma 4.1 (factorization, after the proof of [Kwan–Sudakov, Proposition 15]) and Lemma 4.2 with
   Bregman's theorem for Latin squares; Section 4.2, the typed Linial–Luria bound, in particular Step 5
   (error O(n^{3/2})) and Step 7 (the divergence of the unordered type law).
3. **Color-first counting.** Lemma 5.2 and Corollary 5.3: the identity between the entropy of the random
   coloring plus the matching counts and the rate Φ(t), and the consistency factor φ before (5.1).
4. **Cleanup and cover-down.** Section 5.4 (Claims A and B, the thresholds σ and s₀ with C_L) and Lemma 5.6,
   steps 3–5: dispersion, the exclusions caused by E_X (both points counted, λ ≤ θ₀δ₀/200) and the repair.
5. **Completion and exact counts.** Lemmas 5.7–5.10: the exact seed, the exact masses, the lattice and the
   centered residual; Table 3 for the order of the constants, and Appendix A for the statements of T and T⁺
   used as black boxes.
6. **Extensions.** Section 5.8 (all block types, Pasch hub basis), Section 5.9 (1-factorizations, per-class
   factors φ_X), Section 5.10 (typical step graphs, Lemma 5.19 and its conditions on λ and c_ρ) and
   Section 5.11 (the constraints δ′ < 4/9001 and the error exponent c).
7. **Latin squares.** Section 6: the Latin color-first identity (Lemma 6.1), the explicit inverse (Lemma 6.3),
   the lattice of balanced vectors (Lemma 6.5) and the intercalate exchanges (Lemma 6.6).
8. **Formalization.** The section "Formal verification" and the [formal companion](../../05_formalization/formal_companion_en.pdf):
   compare each row of its table with the Lean statement in `ColorStats_Lean_v1.0.zip`; the
   [mapping notes](../../05_formalization/MAPPING_NOTES.md) list every difference of form (error
   O(n^{7/4}) in Lean against O(n^{3/2}) in the text, normalized forms of Theorems 1.5 and 1.7 not formalized, Lemma 5.18 at the
   level of type vectors). The lower bounds are not formalized.
9. **Priority and positioning.** Section 1.4 and the [bibliographic review](LITERATURE_REVIEW.md); its
   negative search is not an exhaustive priority certification (MathSciNet was not consulted).

The audit records of the review rounds are in
[`02_validation/audit`](../audit); the
[proof ledger](PROOF_LEDGER.json) maps each step to its records. Run `python scripts/verify_colorstats.py` from the repository root
before reviewing a modified package. Report objections by statement, equation and page.
