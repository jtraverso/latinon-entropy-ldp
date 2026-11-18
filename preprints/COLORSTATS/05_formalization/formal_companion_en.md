# Formal companion: counting Steiner triple systems and Latin squares with prescribed color statistics

Juan Pablo Traverso Gianini

Preprint 1.0 — 17 November 2026.

DOI: https://doi.org/10.5281/zenodo.24308221.

Repository: https://github.com/jtraverso/latinon-entropy-ldp.

## 1. Scope

This companion records which statements of the manuscript have Lean counterparts, what each
Lean declaration proves, and where its form differs from the written statement. It is a guide
to the delivered source `ColorStats_Lean_v1.0.zip` and its logs, not a substitute for the
written proofs. Statement numbers are those of the current manuscript.

The formalization covers the upper bounds of the main theorems and the finite algebra of Sections 5.8–5.10:

- the upper bound (1.1) of Theorem 1.1, with explicit constant;
- Proposition 1.3, with an explicit error;
- the typed Linial–Luria bound of Section 4.2 for all block types, which gives the upper
  halves of Theorems 1.2 and 1.5, and its analogues for 1-factorizations (upper half of
  Theorem 1.7) and for typical graphs (upper half of Theorem 1.9(a));
- Lemmas 5.12, 5.13, 5.14, 5.16, 5.17, 5.18, 5.19 and 5.20;
- three conditional implications between main results (Section 6 below).

It does not cover the lower bounds. In particular the following are **not** formalized: the
lower half (1.2) of Theorem 1.1; the lower bounds of Theorems 1.2, 1.5, 1.7 and 1.9(a);
Theorem 1.9(b); Theorem 1.10; Corollaries 1.4, 1.6 and 1.8; Corollary 1.11 except as a
consequence of Theorem 1.10. None of the machinery of Sections 5.1–5.7 and 6 (random
coloring, the matching theorem of Glock, Joos, Kim, Kühn and Lichev, cleanup, cover-down,
completion with T and T⁺, exchanges, bookkeeping) is formalized here, and neither are
Lemmas 2.1 (except as an internal step, see Section 3), 3.1, 4.1, 4.2, 5.1–5.11, 5.8′, 5.21,
Remarks 4.3, 5.15, 5.22, or the lemmas of Section 6. For those results the formalization
contains at most a Lean statement (Section 7).

Every proved declaration listed in Section 3 was checked with `#print axioms`; all reported
axiom sets are contained in `propext`, `Classical.choice` and `Quot.sound` (Section 8). This
says that the listed declarations are proved in Lean from those axioms; it says nothing about
results that are only stated.

## 2. Conventions and notation

**Names.** Lean identifiers keep the British spelling of the project (`ColourStats`,
`colour_first_Phi`, `colour_load`); the paper writes "color". In Lean, `Phi` denotes both the
rate and the right inverses:

| Paper | Lean |
|---|---|
| rate `Φ(t)` (all types) | `ColourStats.Phi lab t` (`Challenge.lean`) |
| rate `Φ(t)` (bicolored, Prop. 1.3) | `ColourStats.Prop13.Phi c t` |
| rate of Theorem 1.7 | `ColourStats.Statements.Phi1F lab col t` |
| rate `Φ_G(t)` | `ColourStats.Statements.PhiG G lab t` |
| right inverse `Ψ` of Lemma 5.13 | the triangle value `y x u v + y x u w + y x v w` (`TriangleInverse.y`) |
| right inverse `Ψ` of Lemma 5.16 | `ColourStats.E2Inverse.Phi xV xC` |
| `Ψ₁`, `𝒯` of Lemma 5.19 | `E3Gadget.Phi₁`, `E3Gadget.Tmap`; on the host, `Host519.Phiop`, `Host519.Top` |
| `Ψ̃`, `Ψ` of Lemma 5.19 | the operator built in `E3Assembly.right_inverse_of_estimates`; the `Φ` asserted by `lemma_5_19_exists` |
| `N_τ`, `e_π`, `c_X`, `m_π(τ)` | `numTriples`, `numPairs`, `classSize`, `mult` |
| `N^all_t`, `N^{1F}_t`, `#dec_t(G)`, `#LS(M)` | `countAll`, `count1F`, `countDecomp`, `numLS` |

**Logarithm of zero.** Lean sets `log 0 = 0`. A statement `log N ≤ Φ + εn²` with `N = 0` then
asserts `Φ + εn² ≥ 0`, which the paper does not claim. Each upper bound is therefore proved in
two forms: an exponential form `N ≤ exp(Φ + εn²)`, which is the faithful one, and the
logarithmic form of the paper's statement, proved for all `N ≥ 0` by showing separately that
the right side is nonnegative under the hypotheses.

**Asymptotic statements.** `o(n²)` is expressed as: for every `ε > 0` there is `n₀` such that
for all `n ≥ n₀`, all partitions and all type vectors satisfying the hypotheses, the bound holds
with `εn²`. Since `n₀` is chosen before the partition and `t`, the bounds are uniform as in the
paper.

**Draft numbering in the sources.** `README.md`, the docstrings of `Challenge.lean` and
`Statements.lean`, and `docs/ROADMAP_ES.md` refer to draft 6 (14 November 2026) and its former
title. The statement numbers used there coincide with the current manuscript. The sources were
frozen without edits.

## 3. Statement correspondence

All modules are under `lean/ColourStats/`; line numbers refer to the frozen source.

### 3.1 Main results (upper bounds)

| Paper | Lean declaration (module:line) | What is proved; difference of form |
|---|---|---|
| Theorem 1.1, upper bound (1.1) | `ColourStats.LatinUpper.theorem_1_1_upper` (`LatinUpper.lean:569`), proving `LatinUpper.Theorem_1_1_upper` | For fixed `a, b, c` and `δ₀, ζ > 0`: `log #LS(M) ≤ n²(log n − 2 − TC(Q)) + K n log² n` with `K = 8c`, `n ≥ max(3, ⌈e^{2+a+b}⌉)`, for all partitions with classes `≥ δ₀n` and outlines with `M/n² ≥ ζ`. Same as (1.1) and as the first conjunct of `Statements.Theorem_1_1`; holds also when `#LS(M) = 0` (right side shown nonnegative). |
| Proposition 1.3 | `ColourStats.prop_1_3_bicol` (`Prop13Bridge.lean:130`); `ColourStats.Prop13.prop_1_3` (`Prop13.lean:147`); exact identity `Prop13.prop_1_3_exact` (`Prop13.lean:100`); `ColourStats.Phi_bicolTypes` (`Prop13Bridge.lean:84`) | `|Φ(t) − (n²/6)(log n − 2 − D(Q‖P₀))| ≤ (n/6)|log n − 2| + n`, assuming `c_X ≥ 2`, `t_XY > 0`, the row identities of (1.3) and `3Σ c_X(c_X−1) = n(n−1)`. Explicit error instead of `O(n log n)`, under weaker hypotheses. |
| (4.3) and (5.2): typed Linial–Luria bound | `ColourStats.TypedSTS.typed_upper` (`TypedFinal.lean:137`) | If `N^all_t > 0` and every class has `≥ c₁ + 2` points (`c₁ ≥ 1`): `log N^all_t ≤ Φ(t) + n²((5 log n + 16)/n + 8 c₁^{−1/4})`, for every type vector `t`, all block types. Form `Φ(t)`, not the normalized `D(Q‖P)` form; error `O(n^{7/4})` (Section 4). |
| Theorem 1.5, upper half (and Theorem 1.2, upper half) | `ColourStats.TypedSTS.theorem_1_5_upper_exp` (`TypedThm.lean:90`); `ColourStats.UpperLog.theorem_1_5_upper` (`UpperLog.lean:104`), proving `Challenge.Theorem_1_5_upper`; `TypedSTS.upper_log` (`TypedThm.lean:123`) | Exponential form `N^all_t ≤ exp(Φ(t) + εn²)` for every `t` (no pair identities, no congruence on `n`), with explicit `n₀`; logarithmic form exactly as in `Theorem_1_5_upper`, including `N = 0`. Theorem 1.2: instance `t := bicolTypes t` (no separate declaration). |
| Theorem 1.7, upper half; (5.3) | `ColourStats.Typed1F.typed_upper_1F` (`Typed1FMain.lean:160`); `Typed1F.theorem_1_7_upper_exp` (`Typed1FMain.lean:315`); `ColourStats.UpperLog.theorem_1_7_upper` (`UpperLog.lean:135`), proving `Statements.Theorem_1_7_upper` | `log N^{1F}_t ≤ Φ(t) + n²((log n + 4)/n + 7 h₁^{−1/4})` when every color class has `≥ h₁ + 1` colors; exponential form for every `t` (only color classes `≥ δ₀n` needed); logarithmic form as stated. |
| Theorem 1.9(a), upper half; (5.4) | `ColourStats.TypedG.typed_upper_G` (`TypedGFinal.lean:140`); `TypedG.theorem_1_9a_upper_exp` (`TypedGThm.lean:47`); `ColourStats.TypedG.theorem_1_9a_upper` (`UpperLog.lean:193`), proving `Statements.Theorem_1_9a_upper` | For `(η, 5)`-typical `G` with `η ≤ 1/3` and every edge having `≥ c₁` common neighbors in every class: `log #dec_t(G) ≤ Φ_G(t) + n²((5 log n + 16)/n + 8 c₁^{−1/4} + η)`; exponential form under `TypHyp` (the hypotheses of Theorem 1.9) for every `t`; logarithmic form as stated. The pair identities (1.6) and triangle-divisibility are not used. |
| Nonnegativity of the rates (for `log 0`) | `UpperLog.Phi_nonneg` (`UpperLog.lean:69`), `UpperLog.Phi1F_nonneg` (`UpperLog.lean:120`), `TypedG.PhiG_nonneg` (`UpperLog.lean:159`), `LatinUpper.TC_le` (`LatinUpper.lean:133`) | `Φ ≥ 0` under the identities and class sizes `≥ 26` (resp. color classes `≥ 8`, `≥ 24` common neighbors); `TC(Q) ≤ a + b`. Not paper statements. |

Supporting declarations of Section 4.1: `Bregman.bregman` (`Bregman.lean:191`, Bregman's theorem
`log #PM(A) ≤ Σ_i log(|A_i|!)/|A_i|`, proved by Radhakrishnan's entropy argument), `Bregman.sum_rank`
(`Bregman.lean:107`), `LatinUpper.bregman_sum_le` (`:75`), `LatinUpper.log_card_Patt_le` (`:232`,
the pattern count), `LatinUpper.log_LSset_le` (`:368`, the chain-rule bound), `LatinUpper.TC_identity`
(`:162`). The margin identities of Lemma 2.1 for actual Latin squares are proved internally
(`LatinUpper.margin_rc`, `LatinUpper.margin_s`, lines 497 and 518).

Supporting declarations of Section 4.2: `TypedChain.chain_typed` (`TypedChain2.lean:160`, the chain rule
in counting form, with the class of the third point revealed separately), `TypedChain.cond_le`
(`TypedChain.lean:255`, conditioning reduces entropy), `TypedSTS.good_of_mem` (`TypedSTS.lean:293`,
the six pairs of Step 5), `TypedSTS.point_sum_le` (`TypedBox.lean:235`), `TypedSTS.pair_bound`
(`TypedPair.lean:212`), `TypedSTS.typed_raw_bound` (`TypedAssembly.lean:53`), `TypedSTS.typed_agg_bound`
(`TypedAggregate.lean:198`, Step 4), `TypedSTS.term_le` (`TypedAnalytic.lean:89`, Steps 5–6),
`TypedSTS.Mstat_eq` (`TypedStats.lean:69`); for 1-factorizations `Typed1F.good_of_mem`
(`Typed1F.lean:120`), `Typed1F.raw_bound` (`Typed1FAgg.lean:174`); for typical graphs
`TypedG.good_of_memG` (`TypedG.lean:208`), `TypedG.typed_agg_boundG` (`TypedGAgg.lean:207`),
`TypedG.MstatG_eq` (`TypedGStats.lean:146`), `TypedG.sum_cnb` (`TypedGStats.lean:268`). The random
order `λ_e ∈ [0, 1]` of the paper is replaced by labels in `Fin L` averaged uniformly; the
integrals of Steps 5–6 become finite sums, which is where the `log n / n` and `c₁^{−1/4}` terms
of the error come from.

### 3.2 Lemmas of Section 5

| Paper | Lean declaration (module:line) | What is proved; difference of form |
|---|---|---|
| Lemma 5.12 | `ColourFirst.compl_mul_typeNum` (`ColourFirst.lean:99`); `ColourFirst.apex_eq` (`:130`), `ColourFirst.apex_indep` (`:157`); `ColourFirst.sum_P` (`:168`); `ColourFirst.entropy_identity` (`:189`), `ColourFirst.entropy_identity_one` (`:274`); `ColourStats.card_type` (`TypeCount.lean:53`), `ColourStats.numTriples_eq` (`:96`), `ColourStats.colour_first_Phi` (`:109`) | The double count `w(τ,π)e_π = m_π(τ)N^O_τ`; (a) `D_τ` independent of the apex (classes of size `≥ 2`, `ν > 0`); (b) the entropy identity for positive `ν, t'` (classes of size `≥ 3`), without the pair identities, which only make `P(·|π)` a probability (`sum_P`); with `ν ≡ 1`, `t' = t`, the right side is `Φ(t)`. |
| Lemma 5.13 | `TriangleInverse.apply_inverse` (`TriangleInverse.lean:78`), `TriangleInverse.inverse_bound` (`:95`) | `AΨx = x` for symmetric `x` with zero diagonal and `m ≥ 5` (paper: `m ≥ 6`); `‖Ψx‖_∞ ≤ 24‖x‖_∞/m` for `m ≥ 8`. Same formulas `S`, `Y`, `y`. |
| Lemma 5.14 | `ColourStats.hub_pairPreserving` (`PaschHub.lean:237`), `ColourStats.hub_unique` (`:115`), `ColourStats.hub_basis` (`:266`); `ColourStats.finrank_Lam` (`PaschRank.lean:187`), `ColourStats.card_avoid` (`:84`), `ColourStats.hub_eq_pasch` (`:253`), `ColourStats.pasch_same_pairs` (`:211`) | The hub vectors lie in `Λ`; every `d ∈ Λ` equals `Σ_{σ ∌ o} d_σ b_σ`, and `d` vanishing off the types containing `o` is zero; `rank Λ = C(k+1, 3)`; `b_σ` is the type change of the Pasch switch from `{013, 024, 125, 345}` to `{012, 034, 135, 245}`, both families covering the same twelve pairs. As in the paper. |
| Lemma 5.16 | `E2Inverse.pair_load` (`E2Inverse.lean:101`), `E2Inverse.colour_load` (`:134`), `E2Inverse.inverse_bound` (`:154`) | `AΨx = x` for balanced `x` (pair loads use balance; color loads need only zero diagonal); `|Ψx| ≤ 13(1 + m/h)‖x‖/min(m, h)` for `m ≥ 3`, `h ≥ 1`. The paper's "`K` absolute" is `K = 13`; the value 9 obtained in the written proof for `m ≥ 4` is not formalized. |
| Lemma 5.17 | `E2Lattice.mem_span_of_rich` (`E2Lattice.lean:206`); dual form `E2Lattice.sum_eq_zero_of_rich` (`:58`) | For `H ⊂ K_m ∨ C_h` given by a graph `G` on the vertices and a set `EC` of vertex–color pairs, satisfying `Rich` (three colors have a common vertex neighbor; two vertices, not necessarily distinct, adjacent to colors `c, c'` have a common vertex neighbor adjacent to `c, c'`; every vertex edge lies in a triangle with a color), balanced at every vertex and with even color degrees: `1_{E(H)}` lies in the ℤ-span of the triangles `{u, v, c}` of `H`. The richness hypotheses are exactly those of the current Lemma 5.17. Lean's conclusion is an integer combination of triangles, as in the paper. |
| Lemma 5.18 | `E2Swap.swapVec_inLambda` (`E2Swap.lean:81`), `E2Swap.inLambda_unique` (`:111`), `E2Swap.inLambda_repr` (`:187`), `E2Swap.finrank_Lam2` (`E2SwapRank.lean:170`) | Swap vectors lie in `Λ`; the `C(k,2)(ℓ−1)` swaps on classes `(o, o, Y, Z)` between `ω` and `Γ` form a basis with coefficients the free coordinates `d(π, Γ)`, `π ∌ o`; `rank Λ = C(k,2)(ℓ−1)`. This is the explicit basis after the proof of Lemma 5.18. The type change of a swap is defined at the level of type vectors, not derived from a concrete 1-factorization; the first proof (via `L_even`) and the counts "four by four", "eight signed units" are not formalized. |
| Lemma 5.19 | `Host519.lemma_5_19_exists` (`Lemma519.lean:202`); explicit version `Host519.Hyp.lemma_5_19` (`Lemma519.lean:182`) | For every `δ₀ ∈ (0, 1]`, `d₀ > 0` there are `η₀ > 0`, `m₀`, `K` such that every `(η, 5)`-typical graph with `0 ≤ η ≤ η₀`, `m ≥ m₀` vertices, classes `≥ δ₀m` and densities in `[d₀, 1]` has a continuous linear right inverse `Φ` (paper: `Ψ`) of `A` with `‖Φ‖_{∞→∞} ≤ K/m`. Constants depend on `δ₀, d₀` only (paper: also on `k`). The explicit version gives `‖Φ‖ ≤ 2(108/p + 108/p² + 4/(δ₀³d₀³))/m` with `p = pconst δ₀ d₀`, under `eps1 + 4η/(δ₀²d₀) ≤ 1/2`. |
| Lemma 5.19, pieces | `E3Gadget.gadget_identity` (`E3Gadget.lean:56`), `E3Gadget.apply_Phi₁` (`:78`), `Host519.mulVec_gadget` (`Host519.lean:115`), `Host519.A_comp_Phi₁` (`:178`), `Host519.Hyp.norm_Phiop_le` (`Phi519.lean:142`), `Host519.Hyp.abs_K2_sub_disjoint` (`K2519.lean:139`), `Host519.Hyp.norm_E₁_le` (`Lemma519.lean:95`), `PairMap.pairMap_surjective` (`PairMap.lean:83`), `Weighting.idealLoad_weight` (`Weighting.lean:73`), `Weighting.load_weight_error` (`WeightingError.lean:46`), `Typical.load_estimate` (`Typical.lean:81`), `Counting.card_edgesIn_commonIn` (`Counting.lean:162`), `Neumann.exists_right_inverse` (`Neumann.lean:31`), `E3Assembly.right_inverse_of_estimates` (`E3Assembly.lean:39`), `E3Assembly.opNorm_le_of_rowSum` (`:90`) | The `K₄` gadget identity `Ag(e,f) = 1_e − 1_f`; `AΨ₁ = I − 𝒯`; `‖Ψ₁‖ ≤ 108/(pm)`; the two-step kernel `Π₂` is within `19η/M` of uniform on disjoint pairs; `‖𝒯² − σ ⊗ u‖ ≤ eps1`; the pair map is onto; the weighting `W` and its load error; the Neumann step; assembly from the four estimates. These follow the steps of the written proof. |
| Lemma 5.20 | `E3Lattice.isPhysical_of_rich` (`E3Lattice.lean:204`); dual form `E3Lattice.sum_eq_zero_of_rich` (`:65`) | If `G` is `Rich` (every two edges have a common `⊠`-partner; every three vertices, not necessarily distinct, have a common neighbor; two common neighbors of two distinct vertices are joined by a path inside their common neighborhood), all degrees are even and `3 ∣ e(G)`, then `1_{E(G)}` lies in the corpus triangle lattice (`TypedTriangle.IsPhysical`, all triangles allowed). Same hypotheses and conclusion (an integer combination of triangles) as the paper. |

## 4. Differences between the Lean results and the written statements

1. **Error of the upper bounds.** The Lean bounds have error
   `n²((5 log n + 16)/n + 8 c₁^{−1/4})` with `c₁ ≈ δ₀n`, that is `O(n^{7/4})` (and
   `n²((log n + 4)/n + 7 h₁^{−1/4})` for 1-factorizations). The manuscript proves `O(n^{3/2})` in
   writing (§4.2 Step 5; §5.11, used in Theorem 1.10). The formalization establishes the
   `o(n²)` statements of Theorems 1.2, 1.5, 1.7 and 1.9(a) (upper halves) with this explicit
   `O(n^{7/4})` error (plus `ηn²` for Theorem 1.9(a)), not the `O(n^{3/2})` error. An error `O(n^{2−c})` with `c = 1/4`
   (`c = min(1/4, c₀)` for Theorem 1.9) can be read off the explicit bounds, but no Lean
   declaration states the polynomial form.
2. **Lemma 5.17.** The current statement of Lemma 5.17 lists the richness conditions under which
   Lean proves the lemma, and they coincide with Lean's `E2Lattice.Rich`. The earlier
   discrepancy (a hypothesis that, read literally, forced `H = K_m ∨ C_h`) no longer exists. The
   conclusions of Lemmas 5.17 and 5.20 (integer combinations of triangles) also agree with Lean;
   no difference remains.
3. **`log 0 = 0`.** The logarithmic Lean statements are stronger than the paper when the count
   is zero (Section 2). The extra content is proved. The exponential forms carry exactly the
   paper's content.
4. **Exponential and logarithmic forms.** `theorem_1_5_upper_exp`, `theorem_1_7_upper_exp` and
   `theorem_1_9a_upper_exp` state `N ≤ exp(Φ + εn²)` for every type vector; `upper_log` and the
   three `UpperLog` theorems give `log N ≤ Φ + εn²`, the last three for all `N ≥ 0`.
5. **Proposition 1.3.** Lean gives the explicit error `(n/6)|log n − 2| + n` and needs only the
   row identities of (1.3) and the admissibility identity, not the full hypotheses of
   Theorem 1.2.
6. **Normalized forms.** The upper bounds are proved in the form `Φ(t)`. The normalized form
   `(n²/6)(log n − 2 − D(Q‖P))` of Theorem 1.5 and (5.2), and `C(n,2)(log n − 2 − D(Q‖P))` of
   Theorem 1.7 and (5.3), are not formalized; the normalization is formalized only for the
   bicolored rate (Proposition 1.3).
7. **Theorem 1.1.** The upper bound (1.1) is proved as stated, with `K = 8c`, but by a different
   route than Lemmas 4.1–4.2: one chain-rule argument over the class pattern and then the
   symbols, with Bregman's theorem proved in the project. Lemmas 4.1, 4.2 and Remark 4.3 are not
   formalized as statements.
8. **Minor differences of hypotheses** (Lemma 5.12 classes of size `≥ 3`; Lemma 5.13 `m ≥ 5`;
   Lemma 5.16 `K = 13`; Lemma 5.19 constants independent of `k`; Lemma 5.18 at the level of type
   vectors) are listed in Section 3 and in `MAPPING_NOTES.md`.

## 5. Theorem 1.2 and the bicolored count

`countAll lab (bicolTypes t)` counts Steiner triple systems with exactly `t_XY` blocks of type
`XXY` for `X ≠ Y` and no block of another type, that is, bicolored systems with type matrix
`t`. The upper half of Theorem 1.2 is the instance `t := bicolTypes t` of
`theorem_1_5_upper_exp`, and `Phi_bicolTypes` identifies `Φ(bicolTypes t)` with the bicolored
rate of Proposition 1.3. There is no separate declaration of the upper half of Theorem 1.2.

## 6. Conditional implications

| Implication | Lean declaration (module:line) | Content |
|---|---|---|
| Corollary 1.11 ⇐ Theorem 1.10 for Theorem 1.9(a) | `ColourStats.Statements.corollary_1_11_of` (`Cor111.lean:266`), with `Statements.completionEquiv` (`Cor111.lean:103`) and `Statements.triDivisible_leave` (`Cor111.lean:237`) | `Theorem_1_10_typical → Corollary_1_11`. Completions of a partial system `Q` with type vector `t` are in bijection with the triangle decompositions of `K_n − L_Q` with type vector `t − t(Q)`, and `K_n − L_Q` is triangle-divisible for `n ≡ 1, 3 (mod 6)`. |
| Theorem 1.5 ⇐ Theorem 1.9(a) | `ColourStats.Statements.theorem_1_5_of` (`Thm15From19.lean:113`) | `Theorem_1_9a → Theorem_1_5`, applying Theorem 1.9(a) to `G = K_n`. |
| Theorem 1.1 ⇐ its lower half | `ColourStats.LatinUpper.theorem_1_1_of_lower` (`LatinUpper.lean:704`) | The lower bound (1.2), as a hypothesis, together with `theorem_1_1_upper` gives `Statements.Theorem_1_1`. |

The hypotheses of these implications are not proved in Lean.

## 7. Statements only

Two files contain Lean statements (as `Prop` definitions) with no proof:

- `Challenge.lean`: `Theorem_1_2`, `Theorem_1_5`, `Theorem_1_5_upper` (the last is proved in
  `UpperLog.lean`).
- `Statements.lean`: `Theorem_1_1` (upper conjunct proved; full statement proved only from the
  lower half), `Corollary_1_4`, `Corollary_1_6`, `Theorem_1_7`, `Theorem_1_7_upper` (proved),
  `Corollary_1_8`, `Theorem_1_9a`, `Theorem_1_9a_upper` (proved), `Theorem_1_9b`, `Theorem_1_10`
  (with parts `Theorem_1_10_latin`, `_bicol`, `_all`, `_oneFact`, `_typical`) and
  `Corollary_1_11`.

They record the reading chosen for each statement: the lower half of Theorem 1.1 assumes the
margin identities (`OutlineMargins`), as in the current manuscript; the large-deviation
principles are stated through counts (`CountLDP`), which for a rate continuous on a compact
feasible set is the pair of standard bounds. Two of them differ from the current manuscript:

- `Theorem_1_10` covers the lower half of Theorem 1.1 and Theorems 1.2, 1.5, 1.7 and 1.9(a),
  but not Theorem 1.9(b) nor the ball statement for Corollaries 1.6 and 1.8. Its docstring says
  that the corollary claim does not specify the neighborhoods; the current manuscript does
  specify them (closed balls centered in `F_n`), so that comment is out of date.
- `Theorem_1_5` and `Theorem_1_7` state only the equality with `Φ(t)`, not the normalized form.

## 8. Build and axiom results

Toolchain `leanprover/lean4:v4.35.0-rc3`; Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`;
corpus `cdr_prescribed_bicolorings` 0.3.0, byte-identical in source to `CDRIII_Lean_v1.0.zip`
(details in `lean/DEPENDENCIES.md`). The library `ColourStats` has 57 modules (the root
`ColourStats.lean` and 56 modules under `ColourStats/`), with 63 source files in the archive.

**Build of the project directory (17 November 2026).** `lake build --no-build ColourStats`
reported all targets up to date (9030 jobs), so nothing upstream needed rebuilding.
`lake build ColourStats` then completed with exit code 0, "Build completed successfully (9030
jobs)", in 25 seconds. This run replayed the existing build outputs, whose traces match the
current sources; it did not recompile any module. Log: `logs/build_ColourStats.log`.

**Build from the archive (17 November 2026).** To check that the archive is complete and
compiles from source, `ColorStats_Lean_v1.0.zip` was extracted into a fresh directory placed so
that the relative corpus path resolves. There `lake build --no-build ColourStats` listed only
`ColourStats.*` modules as out of date. A first `lake build ColourStats` with Lake's default
parallelism ran out of memory (`std::bad_alloc` in eleven simultaneous Lean processes; log
`logs/rebuild_from_archive_attempt1_oom.log`). The second run, with `LEAN_NUM_THREADS=1`,
compiled all 57 `ColourStats` modules from source, replayed the corpus and Mathlib, and
finished with "Build completed successfully (9030 jobs)", exit code 0, in 2362 seconds. Log:
`logs/rebuild_from_archive.log`. The temporary directory was removed afterwards.

**Axioms.** `lake env lean checks/Axioms.lean` ran 89 `#print axioms` queries (455 seconds,
exit code 0). Every query reports exactly `[propext, Classical.choice, Quot.sound]`; no query
reports `sorryAx` and no source file contains `sorry`, `admit` or a user `axiom`. Log:
`logs/axioms.log`. The same 89 queries, run against the modules compiled from the archive,
gave the same result (exit code 0, 74 seconds; `logs/axioms_from_archive.log`).

**Archive.** `ColorStats_Lean_v1.0.zip`, SHA-256
`5091a807b3929336f74ea3cfb2d0f62a43c09ce44194c02cf9b78b71d907cd47`, 205061 bytes, 65 files
under `lean/` (63 source files, `DEPENDENCIES.md`, `source_manifest.json`).

The 89 queries cover every declaration named in Sections 3 and 6 except the internal lemmas
`LatinUpper.margin_rc`, `LatinUpper.margin_s`, `UpperLog.Phi1F_nonneg` and `LatinUpper.TC_le`,
which are used in the proofs of queried theorems (`theorem_1_1_upper`, `theorem_1_7_upper`) and
hence covered by their queries.

## 9. Rebuilding

1. Extract `ColorStats_Lean_v1.0.zip`; the project is the folder `lean/`. Check the files
   against `lean/source_manifest.json`.
2. Install `leanprover/lean4:v4.35.0-rc3`.
3. Obtain the corpus (the Lean source of `CDRIII_Lean_v1.0.zip`, DOI 10.5281/zenodo.24201563)
   and its Mathlib at the pinned revision. Either place the corpus at
   `../cdr-clean-20261113/snapshot/lean` relative to the project, or edit the corpus `path` and
   `packagesDir` in `lakefile.toml`. Neither the corpus nor Mathlib is bundled.
4. From `lean/`, run sequentially:

       lake build --no-build ColourStats   # only ColourStats.* should be out of date
       lake build ColourStats
       lake env lean checks/Axioms.lean

   On a machine with limited memory, set `LEAN_NUM_THREADS=1` for the build, so that Lake
   compiles one module at a time.

## 10. Provenance

The project directory `C:\nw\colour-stats-lean` is not under version control. The archive was
made from it on 17 November 2026 without editing any file. `FREEZE.json` binds the archive,
the hashes of its entries and the logs. The corpus snapshot was produced by the clean
reconstruction of CDR III from source commit `8756b2ef2dbe56002617a86e97e1b16a790ae069`; of its
1307 modules, 13 lie in the import closure of `ColourStats` (`lean/DEPENDENCIES.md`).
