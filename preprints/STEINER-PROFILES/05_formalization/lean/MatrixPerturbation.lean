module
public import KqCore
public import Mathlib.LinearAlgebra.Matrix.Gershgorin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section
noncomputable section
namespace KqR75.MatrixPerturbation

open Finset

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- A matrix within row-sum distance one half of the identity is nonsingular. -/
theorem det_ne_zero_of_small_error (A : Matrix E E ℝ)
    (hnear : ∀ i, ∑ j, |((1 : Matrix E E ℝ) - A) i j| ≤ 1 / 2) : A.det ≠ 0 := by
  let R := (1 : Matrix E E ℝ) - A
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hoff : (∑ j ∈ univ.erase i, ‖A i j‖) = ∑ j ∈ univ.erase i, |R i j| := by
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    simp [R, Matrix.sub_apply, Matrix.one_apply, hij, Real.norm_eq_abs]
  have hsum : (∑ j ∈ univ.erase i, |R i j|) + |R i i| = ∑ j, |R i j| :=
    Finset.sum_erase_add _ _ (mem_univ i)
  have hn : (∑ j, |R i j|) ≤ 1 / 2 := hnear i
  have hd : 1 - |R i i| ≤ |A i i| := by
    have h1 := le_abs_self (R i i)
    have h2 := le_abs_self (A i i)
    have he : R i i = 1 - A i i := by simp [R, Matrix.sub_apply]
    linarith only [h1, h2, he]
  rw [hoff, Real.norm_eq_abs]
  linarith only [hsum, hn, hd]

/-- Quantitative finite-dimensional perturbation. Invertibility is proved,
and the inverse row bound is obtained from its resolvent identity. -/
theorem inverse_rows_le_eight (S U : Matrix E E ℝ)
    (hU : ∀ i, ∑ j, |U i j| ≤ 4)
    (hnear : ∀ i, ∑ j, |((1 : Matrix E E ℝ) - S * U) i j| ≤ 1 / 2) :
    S.det ≠ 0 ∧ ∀ i, ∑ j, |S⁻¹ i j| ≤ 8 := by
  have hp := det_ne_zero_of_small_error (S * U) hnear
  rw [Matrix.det_mul] at hp
  have hdet : S.det ≠ 0 := (mul_ne_zero_iff.mp hp).1
  have hSS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S (isUnit_iff_ne_zero.mpr hdet)
  let R := (1 : Matrix E E ℝ) - S * U
  let F (i : E) : ℝ := ∑ j, |S⁻¹ i j|
  have hidentity : U + S⁻¹ * R = S⁻¹ := by
    dsimp only [R]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hSS, Matrix.one_mul]
    module
  have hprod (i : E) : (∑ j, |(S⁻¹ * R) i j|) ≤ (1 / 2) * F i := by
    calc
      _ ≤ ∑ j, ∑ k, |S⁻¹ i k * R k j| := by
        apply Finset.sum_le_sum
        intro j _
        exact abs_sum_le_sum_abs _ _
      _ = ∑ k, |S⁻¹ i k| * ∑ j, |R k j| := by
        simp_rw [abs_mul]
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
      _ ≤ ∑ k, |S⁻¹ i k| * (1 / 2) :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hnear k) (abs_nonneg _))
      _ = _ := by rw [← Finset.sum_mul]; dsimp only [F]; ring
  refine ⟨hdet, ?_⟩
  intro i
  have hrow : F i ≤ 4 + (1 / 2) * F i := by
    have he (j : E) : S⁻¹ i j = U i j + (S⁻¹ * R) i j :=
      (congrArg (fun A : Matrix E E ℝ => A i j) hidentity).symm
    calc
      F i = ∑ j, |U i j + (S⁻¹ * R) i j| := by simp only [F, he]
      _ ≤ ∑ j, (|U i j| + |(S⁻¹ * R) i j|) :=
        Finset.sum_le_sum (fun j _ => abs_add_le _ _)
      _ = (∑ j, |U i j|) + ∑ j, |(S⁻¹ * R) i j| := Finset.sum_add_distrib
      _ ≤ _ := add_le_add (hU i) (hprod i)
  linarith only [hrow]

end KqR75.MatrixPerturbation

#print axioms KqR75.MatrixPerturbation.det_ne_zero_of_small_error
#print axioms KqR75.MatrixPerturbation.inverse_rows_le_eight
