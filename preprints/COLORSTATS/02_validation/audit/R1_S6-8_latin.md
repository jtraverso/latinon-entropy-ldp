# Audit round 1 — §§6–8 (independent agent, read-only, 17 Nov 2026)

Verdict: **PASS WITH RESERVATIONS** (no BLOQUEANTE/SERIO; four MENOR, all with text fixes).
Coverage VERIFIED: Lemma 6.1 (also numerically), Lemma 6.3 (AΦx = x, norm ≤ 7, numerically), Lemma 6.4, Lemma 6.5
(by hand and Smith normal form), Lemma 6.6 (12 edges, signs, basis, B ≤ J), H3/H4, consistency of M′, D′_τ, G3
expectations, G4 with ζ/2, 3c_ρm², Δ(D) ≤ 3ρn, Remark 6.7, Remark 7.2. READ: Lemma 5.1 analogue, Latin Claims A/B,
steps 1–5 of the Lemma 5.6 adaptation (own arithmetic: at least (1/2 − 2c_ρ − 6λ − (70/3)λ/δ₀)|Z_r| ≥ |Z_r|/3 blocks),
preimage count, line construction of [5, §4.1]. Black boxes: T, T⁺, [25], [15], Freedman, [5, §4.1], [30], [31].

## Findings and fixes (as reported)
- **S6-1 MENOR §6.6** residual outline "at least κ²M … plus at most (3ζ/100 + o(1))m²" impossible by counting and wrong sign; the
  free coordinates of M′ are not said to be fixed. Fix: "We fix the J free coordinates of M′ as in Section 5.7, so that the predicted
  residual M − M′ − M^{(1)}, where M^{(1)} is the expected outline of the step-1 cover-down blocks, is at least κ²M entrywise; it is
  κ²M(1 + O(c_ρ)). The actual residual r differs from it by the blocks with two points in U, of unknown type: each v ∈ O contributes
  ρm(1 + o(1)) of them, which gives (3c_ρ + o(1))m² ≤ (3ζ/100 + o(1))m² in all. The other blocks of unknown type and all error terms
  add o(m²), and the centering vector has entries at most (ζ/4)m². Since κ²M ≥ ζm² entrywise, r ≥ (ζ/2)m²."
- **S6-2 MENOR §6.3** degrees computed with π but the measure uses π′; with π′ the degrees are D′_τ = M′(i,j,l)²/(o^R_i o^C_j o^S_l)
  = (1 − Θ(κ))D_τ, so G1 as written is false. Fix: move the definition of π′ before "Degrees"; "The triangles of H_τ(χ) through rc
  correspond to the s ∈ O_S ∩ S_l with rs, cs available, rs of color j and cs of color i; by R1 their expected number is
  o^S_l ν^{RS}_{il} ν^{CS}_{jl} π′_{RS}(j|i,l) π′_{CS}(i|j,l)(1 ± n^{−1/3}) = D′_τ(1 ± n^{−1/3}), with D′_τ := M′(i,j,l)²/(o^R_i o^C_j o^S_l);
  the same holds for RS- and CS-edges, and log D′_τ = log D_τ + O(κ)." Use D′_τ in G1 and in the matching bound; returning to D_τ costs O(κn²).
- **S6-3 MENOR end of §6.3** "Δ(L) ≤ 2n^{1−δ′}, |L| ≤ n^{2−δ′}" false in the tripartite host (|R| ≈ 3pn², deg_R ≈ 2pn). Fix: "satisfy
  Δ(L) ≤ 3n^{1−δ′} and |L| ≤ 4n^{2−δ′}, since here deg_R(v) ≤ (2 + o(1))pn and |R| ≤ (3 + o(1))pn²." (Later steps need only
  Δ(L) ≪ ρ²m and |L| = o(m²).)
- **S6-4 MENOR Remark 7.2 and §1.3** "four equal classes" is not admissible (admissibility forces Σγ_X² = 1/3). The general claim is
  correct: Q ∝ P₀ is feasible only if all classes are equal, which admissibility allows only for k = 3. [Assembler: the numbers 0.634 and
  0.501 are those of the numerics script `stsrate2.py` for the admissible proportions (0.47, 0.289, 0.121, 0.121); fix the description.]
- **S6-5 EDITORIAL §6.3** state that the Latin marginals are consistent without correction (unlike (5.1)): Σ_j o^C_j ν^{RC}_{ij} equals
  (1 − p)[n − m − ((1 − ρ)/(1 − κ))(m − (1/(ρ_i n))Σ_{j,l} Q(i,j,l) u^C_j u^S_l/(γ_j σ_l))], symmetric in columns and symbols, hence
  equal to Σ_l o^S_l ν^{RS}_{il}; likewise for the other parts (uses Σ_l Q = ρ_iγ_j, Σ_j Q = ρ_iσ_l, |U_C| = |U_S| = m). Checked on 200
  random rounded instances (relative discrepancy ≤ 4·10⁻¹⁷).
- **S6-6 EDITORIAL** Latin cleanup: |B| ≤ 2Cn^{1−θ}; in the Latin Claim B replace 3(k − 1) by 2max{ab, bc, ca}.
- **S6-7 EDITORIAL §6.5** "G_U is balanced, because K_{n,n,n} is balanced, removing a triangle preserves balance, and E_X is an
  edge-disjoint union of triangles."
- **S6-8 EDITORIAL** §6.2 "(1 − ρ)|U_S ∩ S_l|(1 + O(1/n))"; §6.1 add "the terms of Section 5.1 involving k are not used."
- **S6-9 EDITORIAL** Remark 7.1 "the probability that the type matrix equals a given t with t_XY ≥ ζn² is"; Problem 1 "Theorems 1.1,
  1.2 and 1.5"; Problem 2 "other designs" (t clashes with the type matrix).

## Content queries
F-1 NOT-AN-ISSUE; F-2 NOT-AN-ISSUE (text fix S6-2, S6-5); F-3 RESOLVED (Q1 closed by G4; Q2 stated; Q3 covered by Remark 7.1 and
Cor 1.6). F-4 STILL-OPEN: the abstract of arXiv:1704.08136 does not give (1/e + o(1))^{n²}; fix "The number of Sudoku squares of order
n is ((1 + o(1))n/e³)^{n²}: Berend [30] proves the upper bound and Keevash [31, Thm 2.8] the lower bound. Hence the fraction … is
(1/e + o(1))^{n²}" (contents of [30], [31] unverified). F-5 STILL-OPEN (volumes/pages of [4], [10], [17], [21], [23]). F-6 STILL-OPEN
([LAT] DOI 404; give the GitHub release as locator, DOI "(reserved)"). F-7 STILL-OPEN (entries for Brégman, Egorychev, Falikman,
Hoeffding, Chernoff; Kim–Vu unused, remove). F-8 matching tuple → 𝒩. F-9 list threshold s → s₀; S_r → Z_r ("|Z_r|/4"). F-10 renamings
(H4 hinge J → E_h; residual r → r̄; total T → Σ; B_jl → A′_jl; χ in Lemma 6.5 → ψ; indices a, b, e of Lemma 6.6 → x, y, z; ρ vs ρ_i).
F-11 STILL-OPEN with exact fix: the proof of Lemma 6.5 gives the full lattice; "rich" is undefined. New statement: "Then an integer
vector on E(H) is an integer combination of triangles of H if and only if it is balanced. In particular, if H is balanced, then 1_{E(H)}
is." Add after the third point: "If rcs and r′cs are triangles then (g + g′)(r) = (g + g′)(r′), and any r, r′ have such c, s since
(1 − 3γ)m > 0." Replace the final paragraph: "Every triangle is balanced. Conversely, for balanced x write x(v) for its common sum at v;
the image of x is Σ_r x(r)ω_R + Σ_c x(c)ω_C + Σ_s x(s)ω_S = T(ω_R + ω_C + ω_S) = 0, where T is the common total of x on the three
bipartite parts." Delete "It follows that the lattice of a rich tripartite host …". (Checked by SNF saturation on K_{4,4,4} and
K_{5,5,5} minus 5 triangles.) F-12: "By [14], N₀ can be taken to be an explicit tower function of 1/α and C." (not checked in [14]).
