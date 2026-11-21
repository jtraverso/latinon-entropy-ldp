/-
  R50.2: Finite expectation-to-weighted-count implication.
  Does not assert the Bernoulli expectation identity or GJKKL hypotheses.
-/
module
public import TypedClique.R50.Recovery
@[expose] public section

namespace TypedClique.R50

/-- Algebraic bridge:
 π*K ≤ E[#matchings] ≤ Fmax*Z/scale implies Z ≥ π*K*scale/Fmax. -/
theorem weighted_lower_bound
    (π K scale Fmax Z E : ℝ)
    (hScale : 0 < scale) (hF : 0 < Fmax)
    (hgood : π * K ≤ E)
    (hupper : E ≤ Fmax * Z / scale) :
    π * K * scale / Fmax ≤ Z := by
  apply (div_le_iff₀ hF).2
  have hb : E * scale ≤ Fmax * Z :=
    (le_div_iff₀ hScale).mp hupper
  have hc : π * K * scale ≤ E * scale :=
    mul_le_mul_of_nonneg_right hgood hScale.le
  calc
    π * K * scale ≤ E * scale := hc
    _ ≤ Fmax * Z := hb
    _ = Z * Fmax := by ring

end TypedClique.R50
