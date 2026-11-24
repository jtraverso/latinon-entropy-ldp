module
public import KqCore

@[expose] public section

/-!
Algebraic scale program transcribed from specs/opt.py at encurso@5d5a95b.
This file does not state or prove the combinatorial counting theorem.
Reconstructed component; verified only by the GitHub workflow.
-/

namespace KqR75

/-- The complete continuous scale constraints, with c = 4r - 1. -/
def ScaleFeasible (c q a u v δ z : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ δ ∧ 0 ≤ z ∧
  c * a + 2 * δ ≤ 1 ∧ z ≤ δ ∧
  2 * u + (2 * q - 5) * z ≤ a ∧
  2 * z ≤ v ∧ v ≤ u ∧ u + v ≤ a ∧ z ≤ u

/-- Five of the constraints already give the claimed objective upper bound. -/
theorem scale_upper {c q a u v δ z : ℝ} (hc : 0 ≤ c)
    (he : c * a + 2 * δ ≤ 1) (ht : z ≤ δ)
    (hd : 2 * u + (2 * q - 5) * z ≤ a)
    (hg : 2 * z ≤ v) (hl : v ≤ u) :
    (c * (2 * q - 1) + 2) * z ≤ 1 := by
  have hu : 2 * z ≤ u := hg.trans hl
  have ha : (2 * q - 1) * z ≤ a := by nlinarith only [hu, hd]
  have hm := mul_le_mul_of_nonneg_left ha hc
  nlinarith only [hm, he, ht]

/-- The proposed primal point satisfies every constraint when normalized. -/
theorem scale_primal {c q z : ℝ} (hq : 3 ≤ q) (hz : 0 ≤ z)
    (hnorm : (c * (2 * q - 1) + 2) * z = 1) :
    ScaleFeasible c q ((2 * q - 1) * z) (2 * z) (2 * z) z z := by
  have hqz : 0 ≤ (q - 3) * z := mul_nonneg (sub_nonneg.mpr hq) hz
  have haz : 0 ≤ (2 * q - 1) * z :=
    mul_nonneg (by linarith) hz
  dsimp only [ScaleFeasible]
  refine ⟨haz, ?_, ?_, hz, hz, ?_, le_rfl, ?_, le_rfl, le_rfl, ?_, ?_⟩ <;>
    nlinarith only [hz, hqz, hnorm]

/-- The LP has its stated optimum for every real q >= 3 and c >= 0. -/
theorem scale_optimal (c q : ℝ) (hc : 0 ≤ c) (hq : 3 ≤ q) :
    let D := c * (2 * q - 1) + 2
    ScaleFeasible c q ((2 * q - 1) / D) (2 / D) (2 / D) (1 / D) (1 / D) ∧
    ∀ a u v δ z, ScaleFeasible c q a u v δ z → z ≤ 1 / D := by
  dsimp only
  let D := c * (2 * q - 1) + 2
  have hp : 0 ≤ 2 * q - 1 := by linarith
  have hD : 0 < D := by dsimp [D]; nlinarith [mul_nonneg hc hp]
  have hn : D * (1 / D) = 1 := by field_simp
  have hpr := scale_primal hq (le_of_lt (one_div_pos.mpr hD)) hn
  constructor
  · simpa only [div_eq_mul_inv, one_mul] using hpr
  · intro a u v δ z hf
    rcases hf with ⟨_, _, _, _, _, he, ht, hd, hg, hl, _, _⟩
    apply (le_div_iff₀ hD).mpr
    simpa only [D, mul_comm] using scale_upper hc he ht hd hg hl

end KqR75

#print axioms KqR75.scale_upper
#print axioms KqR75.scale_primal
#print axioms KqR75.scale_optimal
