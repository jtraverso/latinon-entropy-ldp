module
public import MatrixPerturbation

@[expose] public section
noncomputable section
namespace KqR75.RestrictedInverse

open Finset

variable {E F G : Type*} [Fintype E] [DecidableEq E]
    [Fintype F] [Fintype G]

theorem row_abs_mul (A : Matrix E F ℝ) (B : Matrix F G ℝ) (K : ℝ)
    (hB : ∀ k, ∑ j, |B k j| ≤ K) (i : E) :
    (∑ j, |(A * B) i j|) ≤ K * ∑ k, |A i k| := by
  calc
    _ ≤ ∑ j, ∑ k, |A i k * B k j| := by
      apply Finset.sum_le_sum
      intro j _
      exact abs_sum_le_sum_abs _ _
    _ = ∑ k, |A i k| * ∑ j, |B k j| := by
      simp_rw [abs_mul]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ k, |A i k| * K :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hB k) (abs_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem restricted_abs_row_le (U : Matrix E E ℝ) (J : Finset E) (K : ℝ)
    (hU : ∀ i, ∑ j, |U i j| ≤ K) (i : E) :
    (∑ j : J, |U i j|) ≤ K := by
  rw [Finset.sum_coe_sort J (fun j : E => |U i j|)]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
    (fun j _ _ => abs_nonneg (U i j))).trans (hU i)

theorem sum_restrict_add_compl (J : Finset E) (f : E → ℝ) :
    (∑ j : J, f j) + (∑ j : (Jᶜ : Finset E), f j) = ∑ j, f j := by
  rw [Finset.sum_coe_sort J f, Finset.sum_coe_sort (Jᶜ : Finset E) f]
  exact Finset.sum_add_sum_compl J f

/-- Restriction deletes two kinds of mass: intermediate resources outside J,
and blocks lost from the principal Gram. Both errors are measured explicitly. -/
theorem restricted_inverse_rows_le_eight (S₀ U : Matrix E E ℝ) (J : Finset E)
    (S : Matrix J J ℝ) (β δ : ℝ)
    (hinv : S₀ * U = 1) (hU : ∀ i, ∑ j, |U i j| ≤ 4)
    (hout_nonneg : ∀ (i : J) (j : (Jᶜ : Finset E)), 0 ≤ S₀ i j)
    (hout : ∀ i : J, ∑ j : (Jᶜ : Finset E), S₀ i j ≤ β)
    (hloss_nonneg : ∀ i j : J, 0 ≤ S₀ i j - S i j)
    (hloss : ∀ i : J, ∑ j : J, (S₀ i j - S i j) ≤ δ)
    (hsmall : 4 * (β + δ) ≤ 1 / 2) :
    S.det ≠ 0 ∧ ∀ i, ∑ j, |S⁻¹ i j| ≤ 8 := by
  let UJ : Matrix J J ℝ := fun i j => U i j
  let O : Matrix J (Jᶜ : Finset E) ℝ := fun i j => S₀ i j
  let V : Matrix (Jᶜ : Finset E) J ℝ := fun i j => U i j
  let D : Matrix J J ℝ := fun i j => S₀ i j - S i j
  have hUJ (i : J) : (∑ j, |UJ i j|) ≤ 4 := restricted_abs_row_le U J 4 hU i
  have hV (i : (Jᶜ : Finset E)) : (∑ j, |V i j|) ≤ 4 :=
    restricted_abs_row_le U J 4 hU i
  have hO (i : J) : (∑ j, |O i j|) ≤ β := by
    simpa only [O, abs_of_nonneg (hout_nonneg i _)] using hout i
  have hD (i : J) : (∑ j, |D i j|) ≤ δ := by
    simpa only [D, abs_of_nonneg (hloss_nonneg i _)] using hloss i
  have hidentity : (1 : Matrix J J ℝ) - S * UJ = O * V + D * UJ := by
    ext i j
    have hfull := congrArg (fun M : Matrix E E ℝ => M i j) hinv
    have hsplit := sum_restrict_add_compl J (fun k => S₀ i k * U k j)
    have hone : (1 : Matrix E E ℝ) i j = (1 : Matrix J J ℝ) i j := by
      simp only [Matrix.one_apply, Subtype.val_inj]
    rw [hone, Matrix.mul_apply] at hfull
    change (1 : Matrix J J ℝ) i j - (∑ k : J, S i k * U k j) =
      (∑ k : (Jᶜ : Finset E), S₀ i k * U k j) +
        ∑ k : J, (S₀ i k - S i k) * U k j
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    linarith only [hfull, hsplit]
  apply MatrixPerturbation.inverse_rows_le_eight S UJ hUJ
  intro i
  rw [hidentity]
  calc
    _ ≤ ∑ j, (|(O * V) i j| + |(D * UJ) i j|) :=
      Finset.sum_le_sum (fun j _ => abs_add_le _ _)
    _ = (∑ j, |(O * V) i j|) + ∑ j, |(D * UJ) i j| := Finset.sum_add_distrib
    _ ≤ 4 * (∑ k, |O i k|) + 4 * ∑ k, |D i k| :=
      add_le_add (row_abs_mul O V 4 hV i) (row_abs_mul D UJ 4 hUJ i)
    _ ≤ 4 * β + 4 * δ := add_le_add
      (mul_le_mul_of_nonneg_left (hO i) (by norm_num))
      (mul_le_mul_of_nonneg_left (hD i) (by norm_num))
    _ ≤ 1 / 2 := by linarith only [hsmall]

end KqR75.RestrictedInverse

#print axioms KqR75.RestrictedInverse.row_abs_mul
#print axioms KqR75.RestrictedInverse.restricted_inverse_rows_le_eight
