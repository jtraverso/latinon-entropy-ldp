module
public import JohnsonAlgebra

@[expose] public section
noncomputable section
namespace KqR75.IncidenceAlgebra

open Finset
open scoped Matrix

def ones {E V : Type*} : Matrix E V ℝ := fun _ _ => 1

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]

theorem mul_ones {F : Type*} (T : Matrix E V ℝ) (r : ℝ)
    (h : ∀ e, ∑ v, T e v = r) :
    T * (ones : Matrix V F ℝ) = r • (ones : Matrix E F ℝ) := by
  ext e f
  simpa [Matrix.mul_apply, ones] using h e

theorem ones_mul {F : Type*} (T : Matrix E V ℝ) (c : ℝ)
    (h : ∀ v, ∑ e, T e v = c) :
    (ones : Matrix F E ℝ) * T = c • (ones : Matrix F V ℝ) := by
  ext f v
  simpa [Matrix.mul_apply, ones] using h v

theorem ones_square : (ones : Matrix E E ℝ) * ones =
    (Fintype.card E : ℝ) • (ones : Matrix E E ℝ) := by
  ext e f
  simp [Matrix.mul_apply, ones]

theorem gram_row_sum (T : Matrix E V ℝ) (n : ℝ)
    (hrow : ∀ e, ∑ v, T e v = 2) (hcol : ∀ v, ∑ e, T e v = n - 1) (e : E) :
    (∑ f, (T * Tᵀ) e f) = 2 * (n - 1) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hcol]
  rw [← Finset.sum_mul, hrow]

theorem cardinality_of_incidence (T : Matrix E V ℝ) (n : ℝ)
    (hsize : (Fintype.card V : ℝ) = n)
    (hrow : ∀ e, ∑ v, T e v = 2) (hcol : ∀ v, ∑ e, T e v = n - 1) :
    (Fintype.card E : ℝ) = n * (n - 1) / 2 := by
  have hm1 : (∑ e, ∑ v, T e v) = (Fintype.card E : ℝ) * 2 := by simp [hrow]
  have hm2 : (∑ v, ∑ e, T e v) = n * (n - 1) := by simp [hcol, hsize] <;> ring
  have hm3 : (∑ e, ∑ v, T e v) = ∑ v, ∑ e, T e v := Finset.sum_comm
  linarith only [hm1, hm2, hm3]

/-- Vertex-edge incidence supplies all four algebra relations needed for the inverse. -/
theorem relations (T : Matrix E V ℝ) (n : ℝ)
    (hsize : (Fintype.card V : ℝ) = n)
    (hrow : ∀ e, ∑ v, T e v = 2)
    (hcol : ∀ v, ∑ e, T e v = n - 1)
    (hgram : Tᵀ * T = (n - 2) • (1 : Matrix V V ℝ) + ones) :
    let K := T * Tᵀ
    let J : Matrix E E ℝ := ones
    K * K = (n - 2) • K + (4 : ℝ) • J ∧
      K * J = (2 * (n - 1)) • J ∧ J * K = (2 * (n - 1)) • J ∧
      J * J = (n * (n - 1) / 2) • J := by
  let K := T * Tᵀ
  have hKr (e : E) : ∑ f, K e f = 2 * (n - 1) := gram_row_sum T n hrow hcol e
  have hKs (e f : E) : K e f = K f e := by
    dsimp only [K]
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hKc (e : E) : ∑ f, K f e = 2 * (n - 1) := by
    calc
      _ = ∑ f, K e f := Finset.sum_congr rfl (fun f _ => hKs f e)
      _ = _ := hKr e
  have hTJ : T * (ones : Matrix V V ℝ) = (2 : ℝ) • (ones : Matrix E V ℝ) :=
    mul_ones T 2 hrow
  have hJT : (ones : Matrix E V ℝ) * Tᵀ = (2 : ℝ) • (ones : Matrix E E ℝ) :=
    ones_mul Tᵀ 2 hrow
  have hKK : K * K = (n - 2) • K + (4 : ℝ) • (ones : Matrix E E ℝ) := by
    calc
      _ = T * (Tᵀ * T) * Tᵀ := by simp only [K, Matrix.mul_assoc]
      _ = T * ((n - 2) • (1 : Matrix V V ℝ) + ones) * Tᵀ := by rw [hgram]
      _ = (n - 2) • K + (T * (ones : Matrix V V ℝ)) * Tᵀ := by
        simp [K, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = (n - 2) • K + (2 : ℝ) • ((ones : Matrix E V ℝ) * Tᵀ) := by
        rw [hTJ, Matrix.smul_mul]
      _ = _ := by rw [hJT, smul_smul]; norm_num
  have hcount : (Fintype.card E : ℝ) = n * (n - 1) / 2 :=
    cardinality_of_incidence T n hsize hrow hcol
  refine ⟨hKK, mul_ones K _ hKr, ones_mul K _ hKc, ?_⟩
  rw [ones_square, hcount]

/-- An inverse of the incidence-algebra operator, with the concrete incidence
facts as inputs instead of an invertibility hypothesis. -/
theorem inverse_from_incidence (T : Matrix E V ℝ) (q n : ℝ)
    (hq : 3 ≤ q) (hn : q + 2 ≤ n) (hsize : (Fintype.card V : ℝ) = n)
    (hrow : ∀ e, ∑ v, T e v = 2) (hcol : ∀ v, ∑ e, T e v = n - 1)
    (hgram : Tᵀ * T = (n - 2) • (1 : Matrix V V ℝ) + ones) :
    let K := T * Tᵀ
    let J : Matrix E E ℝ := ones
    ((1 - 2 * GeneralJohnson.s1 q n + GeneralJohnson.s2 q n) • (1 : Matrix E E ℝ) +
      (GeneralJohnson.s1 q n - GeneralJohnson.s2 q n) • K + GeneralJohnson.s2 q n • J) *
      ((GeneralJohnson.u0 q n - 2 * GeneralJohnson.u1 q n + GeneralJohnson.u2 q n) • 1 +
        (GeneralJohnson.u1 q n - GeneralJohnson.u2 q n) • K + GeneralJohnson.u2 q n • J) = 1 := by
  obtain ⟨hKK, hKJ, hJK, hJJ⟩ := relations T n hsize hrow hcol hgram
  exact JohnsonAlgebra.inverse_of_relations _ _ q n hq hn hKK hKJ hJK hJJ

end KqR75.IncidenceAlgebra

#print axioms KqR75.IncidenceAlgebra.relations
#print axioms KqR75.IncidenceAlgebra.inverse_from_incidence
