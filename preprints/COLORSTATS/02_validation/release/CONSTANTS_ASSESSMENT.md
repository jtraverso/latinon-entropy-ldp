# Constants: order of choice, thresholds and effectivity

## Order of choice

Section 5.1 fixes the constants in five rows (Table 3): seeds and the vortex host bound γ_S; then θ₀, λ and the T⁺ tolerance η_T;
then the constants α, C, h of Theorem T; then the reserve density c_ρ; and last ε_G, θ and δ′. Each row depends only on the
hypotheses and the rows above it. The audit checked every term of the three minima (γ_S, λ, c_ρ) against the place where it is used:

| Constant | Term | Used in | Audit |
|---|---|---|---|
| γ_S | 1/(4K_cC₀(C₁+2C₀)) | Lemma 5.8 | VERIFIED |
| γ_S | ζ/(8B(K_cC₁+(K_c+1)C₀)) | Lemma 5.8′ | VERIFIED |
| γ_S | δ₀/8 | H3, H4 via [CDR III, Appendix B.4]; min degree 7m/8 − 1 in §5.8 | VERIFIED |
| γ_S | δ₀/(2(k+4)) | Lemma 5.9 | VERIFIED |
| γ_S | d₀⁵δ₀η₁/20 | §5.10, typicality of the vortex host | VERIFIED |
| λ | γ_S/36 | Δ(E_X) ≤ γ_S m/4 | VERIFIED |
| λ | δ₀/(18(J+1)) | vertex budget of exchange pools | VERIFIED |
| λ | θ₀δ₀/200 | exclusions by E_X in steps 4–5 of Lemma 5.6 (both points counted, 55/3) | VERIFIED (repaired in round 0) |
| λ | √(ζ/(40(J+B))) | centered residual of Lemma 5.10 | VERIFIED |
| η_T | λ²/256 | T⁺ tolerance in Lemma 5.10 (s_i/4 ≥ λ²m²/64) | VERIFIED |
| c_ρ | γ_S/12, ζ/100, θ₀/8 | Δ(D), §5.7, Lemma 5.6 | VERIFIED |
| §5.10 | c_ρ ≤ d₀³θ₀/32, λ ≤ min{d₀³θ₀/300, d₀⁵θ₀δ₀/100} | typical step graphs | VERIFIED (repaired in round 0) |
| §6.4 | λ ≤ δ₀/200 | Latin squares | VERIFIED |

No term is chosen to be optimal. Smaller values of any constant keep every proof valid and change only the threshold n₀.

## Vortex exponent

The vortex has m = (1+o(1))n^{1−δ′/4} points with δ′ = θ/20 = ε_G³/40 and ε_G < min{ε₀, 1/4}. Section 5.11 lists the constraints
on δ′ that the cover-down needs: δ′ < 4/1001, δ′ < 4/1801, δ′ < 4/2001 and δ′ < 4/9001 ≈ 4.44·10⁻⁴. The choice
δ′ < 3.91·10⁻⁴ satisfies all of them. The binding constraint comes from the exponent 1/900 in the pseudorandom matching theorem of
Ehard, Glock and Joos; a different constant there would change the bound. The audit rechecked each inequality with
m = (1+o(1))n^{1−δ′/4}.

## Error exponents

Theorem 1.10 gives error O(n^{2−c}) with c the smallest of δ′/4, θ, ε_G⁴ and c₀, less an arbitrarily small margin. The upper bounds
have error O(n^{3/2}) (Section 4.2, Step 5, checked by the substitution u = N^{−1/6}v) and O(n log² n) for Latin squares. No claim
is made that these exponents are sharp; the value of c is far from optimal and is not optimized.

## Effectivity

Remark 5.22: Theorem T has an explicit tower threshold [Triangle decompositions III]; the concentration inequalities are explicit; [Glock–Joos–Kim–Kühn–Lichev, Theorem 3.5] and
[Ehard–Glock–Joos, Theorem 1.2] are effective but do not state their thresholds. With explicit values for those two, n₀ is an explicit tower in
the fixed parameters. No arithmetic or Siegel-type input enters. Open problem 3 records the missing explicit constants.

## Numerical checks

The scripts in `03_reproducibility/numerics` (12 scripts, logs and manifest) check finite instances of the identities and of
the stated values: the color-first identity of Lemma 5.2, the Latin identity of Lemma 6.1, the three-class minimum log 1.5 and the
four-class comparison of Remark 7.2 (0.634 against 0.501 for proportions (0.47, 0.2886, 0.1207, 0.1207) with Σγ² = 1/3), the right
inverses and lattice ranks of Lemmas 5.12–5.20 and 6.3–6.6, and the torsion. They are evidence on samples, not part of any proof.
The constraints on δ′ above were checked by the auditors by hand, not by a script.
