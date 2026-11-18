# Audit round 1 — §§1–4, Appendices A–B, Table 1, abstract (independent agent, read-only, 17 Nov 2026)

Verdict: **PASS WITH RESERVATIONS** (no BLOQUEANTE/SERIO; seven MENOR, text fixes only).
VERIFIED line by line: Lemmas 2.1, 2.2, 3.1, 4.1, 4.2, proof of (1.1), Remark 4.3; the new proof of Cor 1.4 (six equations,
integrality, the difference vanishing exactly by admissibility, entries n²/36 + O(n^{3/2})); §4.2 Steps 1–7 including the new
ordered/unordered sentence; proof of Cor 1.11; Φ ↔ D for Thms 1.5, 1.7; P ∈ ri F_γ; k = 1 case of 1.9(b); product form of the
maximiser; Ent = −TC and maximality of the step Latinon; Table 1 against the statements. READ: Appendix B cross-references,
Appendix A (T, T⁺ black boxes), attributions of [6], [7], [10], [5], [22]. Not reviewed: proofs of Thm 1.10, Cors 1.6, 1.8 (§5.11).

## Findings (fixes as reported)
- **M1 MENOR** §1.3 and Remark 7.2: four equal classes are never admissible (Σγ_X² = 1/3 + O(1/n)); for equal classes
  −log P₀(bic) = log(16/9) = 0.575. General claim true, with a short proof: "In the limit, equality would force Q proportional to
  P₀; the first identity of (1.3) then makes γ_X + γ_Y independent of X ≠ Y, so all classes would be equal, while admissibility gives
  Σ_X γ_X² = 1/3 + O(1/n), which for equal classes forces k = 3." [Assembler: use the admissible proportions of `stsrate2.py`,
  (0.47, 0.289, 0.121, 0.121), whose rerun gives 0.6337 and 0.5011.]
- **M2 MENOR** §4.2 Step 5 (closes B-6): the correction term is Θ(n^{−1/2}) per pair, Θ(n^{3/2}) in total, not O(n log n)
  (∫₀¹u² log(1 + 1/(Nu⁶))du = (π/3 + o(1))N^{−1/2}); §5.11 already says O(n^{3/2}). Fix from "By Jensen's inequality": "By Jensen's
  inequality, E log A_e(c) ≤ log(1 + γ_c n(1 − λ)⁶) = log(γ_c n) + 6 log(1 − λ) + log(1 + 1/(γ_c n(1 − λ)⁶)). Integrated against
  (1 − λ)² dλ, the last term is O((γ_c n)^{−1/2}), by the substitution 1 − λ = (γ_c n)^{−1/6}v; summed over pairs it contributes O(n^{3/2})."
- **M3 MENOR** after Prop 1.3: Q = 6t/n² has mass (n − 1)/n. Fix: "For a probability vector Q on the bicolored types,
  D(Q‖P₀) ≥ −log P₀(bicolored), with equality exactly when Q is proportional to P₀; the normalized matrix 6t/n² has mass (n − 1)/n,
  so for it this holds up to O(1/n)."
- **M4 MENOR** abstract: (a) hypotheses missing (classes of linear size, counts of order n²); (b) Cor 1.4 counts all bicolored
  systems; (c) "counts squares near a prescribed outline" attributes to [9] our deduction. Fixes: "partitioned into k ≥ 3 classes of
  linear size, prescribing the number of blocks of each bicolored type, each of order n², gives …"; "for three classes the total
  number of bicolored systems is ((2/3 + o(1))n/e²)^{n²/6}"; "the number of squares with a given outline, each entry of order n², is …";
  "unlike a recent large-deviation principle, which counts squares near a prescribed limit object, our count …".
- **M5 MENOR** §1.4: Simkin is not an author of [21] or [22]. Fix: "Kwan, Sah and Sawhney [21] and Kwan and Pham [22] study large
  deviations of substructure counts, such as intercalates in Latin squares and Pasch configurations in Steiner triple systems, respectively."
- **M6 MENOR** (A-12) §1.4 "Pattern densities, unlike the outline, do not depend on the labeling" is false. Fix: "The outline depends on
  a partition of the rows, columns and symbols, and the order-pattern densities of [9] on their order, so neither statistic determines the other."
- **M7 MENOR** Lemma 4.2 fails for d = 1. Fix: "Let d ≥ 2 and let G be a d-regular bipartite graph …" (only use: d = σ_l n).
- **E1** proof of (1.1): "We may assume #LS(M) > 0; then M satisfies the margin identities by Lemma 2.1."
- **E2** §4.2 Step 6: B is both the number of blocks and a class; use "b_n = n(n − 1)/6 blocks". Step 7: "which are (n/(n − 1))Q and P₀;
  the factor changes D by O(1/n)".
- **E3** §1.5: "inverse, seed and lattice lemmas (Lemmas 6.3–6.5), the hinge condition".
- **E4** Appendix B "Generalised" → "Generalized"; unify the reference for the residual ([5, (4.1)] in Lemma 5.10 vs [5, §§4.2–4.3]).

## Content queries
A-1 RESOLVED (arXiv 1611.02246 Thms 3.1, 3.2; PLMS numbering not checked). A-2 RESOLVED (step profile meets [9, Thm 3.1];
[9, Lemma 7.1] gives O(n^{3/2} log n)). A-3 RESOLVED ([FK20] Lemma 3.5). A-4 NOT-AN-ISSUE (MathSciNet a process step). A-5 NOT-AN-ISSUE.
A-6/Q2 RESOLVED. A-7/Q4 STILL-OPEN (non-blocking): add "Admissibility gives Σ_X(c_X − n/3)² = 2n/3, so every admissible partition into
three classes has sizes n/3 + O(√n). Such partitions exist for infinitely many n: for n = u² with u ≡ 3, 5 (mod 6), take sizes
(u² + u)/3, (u² + u)/3, (u² − 2u)/3." A-8 RESOLVED. A-9 STILL-OPEN: "Theorems T and T⁺ are formalized in Lean in [14], and the theorem of
[15] in [16]". A-10 STILL-OPEN: "and the count of Sudoku squares, with the upper bound of Berend [30] and the lower bound of Keevash
[31, Thm 2.8]". A-11 STILL-OPEN: rename the partial system of Cor 1.11 to S₀ (L_{S₀}, t(S₀)). A-12 see M6. A-13 STILL-OPEN: "(the
numbers of classes, δ₀, ζ and, where they occur, c₀, d₀ and r)". A-14 NOT-AN-ISSUE (arXiv 1108.5042 also bounds 1-factorizations).
B-6 closed by M2.
