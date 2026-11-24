module
public import KqCore

@[expose] public section
namespace KqR75.SignedBlock

def polynomial (r S T : ℝ) : ℝ :=
  (2 * r - 1) * T ^ 2 + (S ^ 2 - (2 * r - 1) * S - r * (2 * r - 1)) * T +
    r * (r - 1) * S

def coefficient (r S : ℝ) : ℝ :=
  S ^ 3 - (2 * r - 1) * S ^ 2 - r * (2 * r - 1) * S + 2 * (2 * r - 1) * r ^ 2

theorem coefficient_expansion (r S : ℝ) :
    coefficient r S = (S - (2 * r - 1)) ^ 3 + (4 * r - 2) * (S - (2 * r - 1)) ^ 2 +
      (2 * r - 1) * (r - 1) * (S - (2 * r - 1)) + r * (2 * r - 1) := by
  dsimp only [coefficient]
  ring

theorem certificate_identity (r S T : ℝ) :
    polynomial r S T * S ^ 2 = (2 * r - 1) * (S * T - r ^ 2) ^ 2 +
      coefficient r S * (S * T - r ^ 2) +
      r * (S - r) ^ 2 * ((2 * r - 1) * S + (2 * r - 1) * r) := by
  dsimp only [polynomial, coefficient]
  ring

theorem polynomial_nonnegative (r S T : ℝ) (hr : 1 ≤ r)
    (hS : 2 * r - 1 ≤ S) (hST : r ^ 2 ≤ S * T) : 0 ≤ polynomial r S T := by
  have hr0 : 0 ≤ r := by linarith
  have hS0 : 0 < S := by linarith
  have hU : 0 ≤ S - (2 * r - 1) := sub_nonneg.mpr hS
  have hV : 0 ≤ S * T - r ^ 2 := sub_nonneg.mpr hST
  have htwo : 0 ≤ 2 * r - 1 := by linarith
  have hr1 : 0 ≤ r - 1 := by linarith
  have hfour : 0 ≤ 4 * r - 2 := by linarith
  have hC : 0 ≤ coefficient r S := by
    rw [coefficient_expansion]
    positivity
  have hprod : 0 ≤ polynomial r S T * S ^ 2 := by
    rw [certificate_identity]
    positivity
  by_contra h
  have hneg : polynomial r S T < 0 := lt_of_not_ge h
  exact (not_lt_of_ge hprod) (mul_neg_of_neg_of_pos hneg (sq_pos_of_pos hS0))

end KqR75.SignedBlock

#print axioms KqR75.SignedBlock.certificate_identity
#print axioms KqR75.SignedBlock.polynomial_nonnegative
