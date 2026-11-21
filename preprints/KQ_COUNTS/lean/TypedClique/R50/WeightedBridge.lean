/-
  R50.2: Finite expectation-to-weighted-count implication.
  Does not assert the Bernoulli expectation identity or GJKKL hypotheses.
-/
module
public import TypedClique.R50.Recovery
@[expose] public section

namespace TypedClique.R50

/-- Algebraic bridge:
 π*K ≤ E[#matchings] ≤ Fmax*Z/λpow implies Z ≥ π*K*λpow/Fmax. -/
theorem weighted_lower_bound
    (π K λpow Fmax Z E : ℝ)
    (hλ : 0 < λpow) (hF : 0 < Fmax)
    (hgood : π * K ≤ E)
    (hupper : E ≤ Fmax * Z / λpow) :
    π * K * λpow / Fmax ≤ Z := by
  apply (div_le_iff₀ hF).2
  have hb : E * λpow ≤ Fmax * Z :=
    (le_div_iff₀ hλ).mp hupper
  have hc : π * K * λpow ≤ E * λpow :=
    mul_le_mul_of_nonneg_right hgood hλ.le
  calc
    π * K * λpow ≤ E * λpow := hc
    _ ≤ Fmax * Z := hb
    _ = Z * Fmax := by ring

end TypedClique.R50
