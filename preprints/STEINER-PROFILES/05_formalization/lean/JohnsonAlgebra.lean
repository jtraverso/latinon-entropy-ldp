module
public import GeneralJohnson
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
noncomputable section
namespace KqR75.JohnsonAlgebra

open KqR75.GeneralJohnson

/-- Change from the three entry orbits to the basis I, vertex-incidence Gram, J. -/
theorem inverse_coefficients (q n : ℝ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) :
    (1 - 2 * s1 q n + s2 q n) * (u0 q n - 2 * u1 q n + u2 q n) = 1 ∧
    (1 - 2 * s1 q n + s2 q n) * (u1 q n - u2 q n) +
      (s1 q n - s2 q n) * (u0 q n - 2 * u1 q n + u2 q n) +
      (n - 2) * (s1 q n - s2 q n) * (u1 q n - u2 q n) = 0 ∧
    (1 - 2 * s1 q n + s2 q n) * u2 q n +
      s2 q n * (u0 q n - 2 * u1 q n + u2 q n) +
      4 * (s1 q n - s2 q n) * (u1 q n - u2 q n) +
      2 * (n - 1) * ((s1 q n - s2 q n) * u2 q n +
        s2 q n * (u1 q n - u2 q n)) +
      n * (n - 1) / 2 * s2 q n * u2 q n = 0 := by
  obtain ⟨h0, h1, h2⟩ := orbit_identities q n hq hn
  refine ⟨?_, ?_, ?_⟩
  · linear_combination h0 - 2 * h1 + h2
  · linear_combination h1 - h2
  · linear_combination h2

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Matrix multiplication in the three-dimensional incidence algebra.
The relations are to be supplied by the concrete vertex-edge incidence matrix. -/
theorem basis_product (K J : Matrix E E ℝ) (l d t N : ℝ)
    (hKK : K * K = l • K + d • J) (hKJ : K * J = t • J)
    (hJK : J * K = t • J) (hJJ : J * J = N • J)
    (a b c A B C : ℝ) :
    (a • (1 : Matrix E E ℝ) + b • K + c • J) * (A • 1 + B • K + C • J) =
      (a * A) • 1 + (a * B + b * A + l * b * B) • K +
        (a * C + c * A + d * b * B + t * (b * C + c * B) + N * c * C) • J := by
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one, hKK, hKJ, hJK, hJJ, smul_add, smul_smul]
  module

/-- The Johnson coefficients give an actual inverse as soon as the elementary
incidence-algebra relations have been proved. No invertibility is an input. -/
theorem inverse_of_relations (K J : Matrix E E ℝ) (q n : ℝ)
    (hq : 3 ≤ q) (hn : q + 2 ≤ n)
    (hKK : K * K = (n - 2) • K + (4 : ℝ) • J)
    (hKJ : K * J = (2 * (n - 1)) • J)
    (hJK : J * K = (2 * (n - 1)) • J)
    (hJJ : J * J = (n * (n - 1) / 2) • J) :
    ((1 - 2 * s1 q n + s2 q n) • (1 : Matrix E E ℝ) +
      (s1 q n - s2 q n) • K + s2 q n • J) *
    ((u0 q n - 2 * u1 q n + u2 q n) • 1 +
      (u1 q n - u2 q n) • K + u2 q n • J) = 1 := by
  rw [basis_product K J _ _ _ _ hKK hKJ hJK hJJ]
  obtain ⟨h0, h1, h2⟩ := inverse_coefficients q n hq hn
  rw [h0, h1, h2]
  simp

end KqR75.JohnsonAlgebra

#print axioms KqR75.JohnsonAlgebra.inverse_coefficients
#print axioms KqR75.JohnsonAlgebra.basis_product
#print axioms KqR75.JohnsonAlgebra.inverse_of_relations
