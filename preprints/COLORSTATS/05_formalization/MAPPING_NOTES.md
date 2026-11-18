# Mapping notes: Lean statements against the current manuscript

Manuscript: `01_manuscript/color_stats_en.md`, preprint 1.0 of 17 November 2026.
Lean source: `ColorStats_Lean_v1.0.zip` (project `colour_stats`, library `ColourStats`).
Date of the comparison: 2026-11-17.

The items below list every difference of statement found between a Lean declaration and the
manuscript statement it corresponds to. "Stronger" means that the statement implies the other
one. Items 1–5 matter for what the formalization paragraph of the paper may claim; items 6–14
are differences of form that do not affect such a claim; items 15–18 concern statements that
are only stated in Lean, not proved, or Lean comments that are now stale.

## Items that limit what the paper may claim

**1. Error term of the upper bounds: O(n^{7/4}) in Lean, O(n^{3/2}) in the paper.**
- Location: §4.2 Step 5 ("summed over pairs it contributes O(n^{3/2})"); §5.11, paragraph
  "The upper bounds of Theorems 1.2, 1.5 and 1.7 have error O(n^{3/2})"; §5.11, proof of the
  ball statement for the corollaries ("with error O(n^{3/2})").
- Lean: `ColourStats.TypedSTS.typed_upper` proves
  `log N^all_t ≤ Φ(t) + n²((5 log n + 16)/n + 8 c₁^{-1/4})` whenever every class has at least
  `c₁ + 2` points and `N^all_t > 0`. With `c₁ = δ₀n − 2` the error is `O(n^{7/4})`.
  `ColourStats.Typed1F.typed_upper_1F` gives `n²((log n + 4)/n + 7 h₁^{-1/4})`, also
  `O(n^{7/4})`. `ColourStats.TypedG.typed_upper_G` gives
  `n²((5 log n + 16)/n + 8 c₁^{-1/4} + η)`.
- The paper's claim is stronger. The Lean bounds do not establish `O(n^{3/2})`. They do give
  an error `O(n^{2−c})` with `c = 1/4` (and `c = min(1/4, c₀)` for Theorem 1.9), so the
  polynomial form of the upper halves in Theorem 1.10 can be read off them. No Lean
  declaration states that polynomial form.
- Consequence: the paper may say that Lean proves the upper halves with an explicit error
  `O(n^{7/4})`; it should not attribute the `O(n^{3/2})` error to the formalization.

**2. Normalized forms of Theorems 1.5 and 1.7 are not formalized.**
- Location: Theorem 1.5 (second equality, `(n²/6)(log n − 2 − D(Q‖P))`), Theorem 1.7
  (second equality, `C(n,2)(log n − 2 − D(Q‖P))`), (5.2), (5.3), §5.8 "Normalization", and
  the displayed identity `Φ(t) = (n²/6)(log n − 2 − D(Q‖P_n)) + O(n log n)` of §5.11.
- Lean: the upper bounds are proved in the form with `Φ(t)`. The normalization
  `Φ(t) ↔ D(Q‖P)` is formalized only for the bicolored rate (Proposition 1.3). The target
  statements `Theorem_1_5` and `Theorem_1_7` in Lean contain only the `Φ(t)` equality.
- The paper is stronger (it also states the normalized form). For the bicolored case, (4.3)
  in its normalized form follows from `typed_upper` and `prop_1_3_bicol` together, but no
  single declaration states it.

**3. Theorem 1.2: no separate declaration for the upper half.**
- Lean: the upper half of Theorem 1.2 is the instance `t := bicolTypes t` of
  `ColourStats.TypedSTS.theorem_1_5_upper_exp` (the count `countAll lab (bicolTypes t)` is the
  number of bicolored systems with type matrix `t`). This is stated in the module docstring of
  `TypedThm.lean`; there is no declaration with the exact shape of the upper half of
  `Theorem_1_2`.
- Not a difference of strength; the paper may describe it as a direct instance.

**4. Upper bound (1.1) of Theorem 1.1: different proof route.**
- Location: §4.1, Lemmas 4.1 and 4.2, Remark 4.3.
- Lean: `ColourStats.LatinUpper.theorem_1_1_upper` proves (1.1) exactly as stated, with
  explicit `K = 8c` (`c` the number of symbol classes) and `n₀ = max(3, ⌈e^{2+a+b}⌉)`, also
  when `#LS(M) = 0`. The proof is a single application of the corpus chain rule, with the class
  pattern revealed first and then the symbols one by one, each bounded by Brégman's theorem
  (`ColourStats.Bregman.bregman`, Radhakrishnan's entropy proof, proved in this project). The
  factorization identity of Lemma 4.1, the two-sided estimate of Lemma 4.2 (in particular its
  lower half, via Egorychev–Falikman) and Remark 4.3 are not formalized.
- Same statement as the paper; the paper may cite Lean for (1.1) but not for Lemmas 4.1–4.2.

**5. Lower bounds and large deviations.**
- Not formalized: the lower half (1.2) of Theorem 1.1, the lower bounds of Theorems 1.2, 1.5,
  1.7 and 1.9(a), Theorem 1.9(b), Theorem 1.10, Corollaries 1.4, 1.6, 1.8, and the unconditional
  form of Corollary 1.11. Lean contains only their statements (`Challenge.lean`,
  `Statements.lean`) and three conditional implications (Section 6 of the companion).

## Differences of form (no effect on what may be claimed)

**6. `log 0 = 0` (FQ7).** The Lean log-form upper statements (`Theorem_1_5_upper`,
`Theorem_1_7_upper`, `Theorem_1_9a_upper`, the upper conjunct of `Theorem_1_1`) are proved
also when the count is `0`. Because Lean sets `log 0 = 0`, in that case they assert
`Φ(t) + εn² ≥ 0` (resp. that the right side of (1.1) is nonnegative), which the paper does not
claim. The Lean statements are stronger; the extra content is proved (`UpperLog.Phi_nonneg`,
`TypedG.PhiG_nonneg`, `UpperLog.Phi1F_nonneg`, `LatinUpper.TC_le`). The exponential forms
(`N ≤ exp(Φ + εn²)`) are the faithful ones.

**7. Upper halves hold for every type vector.** `theorem_1_5_upper_exp`,
`theorem_1_7_upper_exp` and `theorem_1_9a_upper_exp` need neither the pair identities
(1.4)–(1.6) nor `n ≡ 1, 3 (mod 6)` or `n` even; `theorem_1_7_upper_exp` needs only the color
classes to have at least `δ₀n` elements. The paper says "for every `t` satisfying (1.4)"
(resp. (1.5), (1.6)). Lean is stronger, trivially so when the count is zero.

**8. Proposition 1.3.** `ColourStats.prop_1_3_bicol` gives the explicit error
`(n/6)|log n − 2| + n`, assuming only `c_X ≥ 2`, `t_XY > 0`, the row identities of (1.3) and
`3Σ c_X(c_X − 1) = n(n − 1)`. The paper states `O(n log n)` under the hypotheses of Theorem
1.2. Lean is stronger.

**9. Lemma 5.12.** Part (b) (`ColourFirst.entropy_identity`) is proved without the pair
identities `Σ_τ m_π(τ)t'_τ = ν_π e_π` (they only make `P(·|π)` a probability, `sum_P`), but
assumes every class of `O` has at least 3 points (2 for part (a)). The paper does not state a
lower bound on `o_X`. Neither statement implies the other; the extra hypothesis is harmless in
every use.

**10. Lemma 5.13.** `apply_inverse` holds for `m ≥ 5` (paper: `m ≥ 6`); the norm bound
`24‖x‖/m` for `m ≥ 8` is as in the paper. Edge vectors are encoded as symmetric functions with
zero diagonal. Lean is slightly stronger.

**11. Lemma 5.16.** Lean proves the statement with the absolute constant `K = 13`, for `m ≥ 3`,
`h ≥ 1`. The paper states "with `K` absolute"; its proof gives `9` for `m ≥ 4`. The constant `9`
is not formalized.

**12. Lemmas 5.17 and 5.20: "integer sum" (resolved: the manuscript now says "integer combination").** The conclusions in Lean are membership in the
ℤ-span of the triangle vectors (5.17) and in the corpus triangle lattice `TypedTriangle.lattice`
(5.20), that is, an integer *combination*. The paper said "integer sum of triangles" in both
statements; it now says "integer combination", as in §5.8 H2. The hypotheses now agree: the current Lemma 5.17 lists the three richness
conditions of Lean's `E2Lattice.Rich` (three colors with a common vertex neighbor; two
vertices, not necessarily distinct, adjacent to colors `c, c'` with a common vertex neighbor
adjacent to `c, c'`; every vertex edge in a triangle with a color), so FQ1 is resolved. The
current Lemma 5.20 matches `E3Lattice.Rich`, including "three vertices, not necessarily
distinct" and paths for two distinct vertices (FQ6).

**13. Lemma 5.18.** Lean works with type vectors: the type change of an alternating swap is
*defined* as `cycVec X₁ X₂ X₃ X₄ ⊗ (e_Γ' − e_Γ)` (`E2Swap.swapVec`), not derived from a swap in
an actual 1-factorization. Lean proves that every such vector lies in `Λ`, that the
`C(k,2)(ℓ − 1)` swaps on classes `(o, o, Y, Z)` form a basis with coefficients the free
coordinates, and `rank Λ = C(k,2)(ℓ − 1)`. The paper's first proof (via `L_even`) and the
counts "four triangles by four" and "at most eight signed units" are not in Lean.

**14. Lemma 5.19.** `Host519.lemma_5_19_exists` gives `η₀, m₀, K` depending only on
`δ₀, d₀` (paper: on `k, δ₀, d₀`), and assumes `δ₀ ≤ 1`, `d₀ ≤ d_XY ≤ 1`. Lean is (formally)
stronger. The right inverse is called `Ψ` in the paper and `Φ` in Lean; the first-order
inverse `Ψ₁` is `E3Gadget.Phi₁` / `Host519.Phiop`, and `𝒯` is `Tmap` / `Top`.

## Statements only, and stale Lean comments

**15. Theorem 1.10 (statement only).** `Statements.Theorem_1_10` covers the lower half of
Theorem 1.1 and the two-sided Theorems 1.2, 1.5, 1.7 and 1.9(a). It omits Theorem 1.9(b) and
the ball statement for Corollaries 1.6 and 1.8. Its docstring says the corollary claim "does
not say which neighbourhoods are meant"; the current paper now specifies closed balls of radius
`r` centred in `F_n` with all entries of `B ∩ F_n` at least `ζ` (FQ4 is resolved in the paper,
not in Lean). The Lean statement is weaker than the paper's theorem.

**16. Corollaries 1.6 and 1.8 (statements only).** Stated through counts (`CountLDP`), which is
equivalent to the two large-deviation bounds for a rate continuous on a compact feasible set.
Corollary 1.8 normalizes color classes by `n − 1`; the paper writes `h_Γ/n → η_Γ`. The limits
agree.

**17. Corollary 1.11 (statement only).** Lean writes `t − t(Q)` with truncated subtraction on
ℕ; since every entry is required to be at least `ζn² > 0`, this coincides with the paper.
Triangle-divisibility of `K_n − L_Q` is proved (`triDivisible_leave`), not assumed.

**18. Stale descriptions inside the archive.** `README.md`, the module docstrings of
`Challenge.lean` and `Statements.lean`, and `docs/ROADMAP_ES.md` refer to draft 6 of
14 November 2026, its title (with "1-factorizations" and British "colour") and to
`Φ` for the right inverses. The statement numbers they use coincide with the current
manuscript. `README.md` does not list `UpperLog.lean`, `Bregman.lean` and `LatinUpper.lean`,
and describes the Pasch switch as `{012, 034, 135, 245} → {013, 024, 125, 345}`; the docstring
of `hub_eq_pasch` likewise says "replacing `paschA` by `paschB`". The proved formula,
`hub o {a,b,c} = count(paschA) − count(paschB)` with `paschA = {012, 034, 135, 245}`, is the
paper's `b_σ` for the switch from `{013, 024, 125, 345}` to `{012, 034, 135, 245}`, so the
statement agrees with Lemma 5.14 and only the two descriptions have the direction reversed.
The sources were frozen unchanged.
