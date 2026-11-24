module
public import RestrictedInverse

@[expose] public section
noncomputable section
namespace KqR75.LoadCorrection

open Finset
open scoped Matrix

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

def gram (A : Matrix E B ℝ) (α : ℝ) : Matrix E E ℝ := α • (A * Aᵀ)

def corrector (A : Matrix E B ℝ) (α : ℝ) : Matrix B E ℝ :=
  α • (Aᵀ * (gram A α)⁻¹)

theorem gram_symmetric (A : Matrix E B ℝ) (α : ℝ) : (gram A α)ᵀ = gram A α := by
  simp [gram, Matrix.transpose_smul, Matrix.transpose_mul]

theorem inverse_cols_le_eight (A : Matrix E B ℝ) (α : ℝ)
    (hrows : ∀ e, ∑ f, |(gram A α)⁻¹ e f| ≤ 8) :
    ∀ f, ∑ e, |(gram A α)⁻¹ e f| ≤ 8 := by
  have hs : ((gram A α)⁻¹)ᵀ = (gram A α)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, gram_symmetric]
  intro f
  have he (e : E) : (gram A α)⁻¹ e f = (gram A α)⁻¹ f e :=
    congrArg (fun M : Matrix E E ℝ => M f e) hs
  simp_rw [he]
  exact hrows f

/-- The correction solves the load equations; nonsingularity is not assumed
by the final host theorem, which obtains it from sparse deletion. -/
theorem right_inverse (A : Matrix E B ℝ) (α : ℝ) (hdet : (gram A α).det ≠ 0) :
    A * corrector A α = 1 := by
  calc
    _ = gram A α * (gram A α)⁻¹ := by
      simp only [corrector, gram, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)

theorem corrector_cols_le_eight (A : Matrix E B ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hA : ∀ e b, 0 ≤ A e b) (hcap : ∀ e, α * ∑ b, A e b ≤ 1)
    (hrows : ∀ e, ∑ f, |(gram A α)⁻¹ e f| ≤ 8) (f : E) :
    (∑ b, |corrector A α b f|) ≤ 8 := by
  have hcols := inverse_cols_le_eight A α hrows
  calc
    _ = α * ∑ b, |∑ e, A e b * (gram A α)⁻¹ e f| := by
      simp only [corrector, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hα]
      rw [← Finset.mul_sum]
      rfl
    _ ≤ α * ∑ b, ∑ e, |A e b * (gram A α)⁻¹ e f| := by
      apply mul_le_mul_of_nonneg_left _ hα
      exact Finset.sum_le_sum (fun b _ => abs_sum_le_sum_abs _ _)
    _ = ∑ e, (α * ∑ b, A e b) * |(gram A α)⁻¹ e f| := by
      simp_rw [abs_mul, abs_of_nonneg (hA _ _)]
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ ∑ e, |(gram A α)⁻¹ e f| := Finset.sum_le_sum (fun e _ => by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hcap e) (abs_nonneg _))
    _ ≤ 8 := hcols f

theorem corrector_rows_le (A : Matrix E B ℝ) (α r : ℝ) (hα : 0 ≤ α)
    (hA : ∀ e b, 0 ≤ A e b) (hsize : ∀ b, ∑ e, A e b ≤ r)
    (hrows : ∀ e, ∑ f, |(gram A α)⁻¹ e f| ≤ 8) (b : B) :
    (∑ e, |corrector A α b e|) ≤ 8 * r * α := by
  have hprod := RestrictedInverse.row_abs_mul Aᵀ (gram A α)⁻¹ 8 hrows b
  have hsize' : (∑ e, |Aᵀ b e|) ≤ r := by
    simpa only [Matrix.transpose_apply, abs_of_nonneg (hA _ _)] using hsize b
  calc
    _ = α * ∑ e, |(Aᵀ * (gram A α)⁻¹) b e| := by
      simp only [corrector, Matrix.smul_apply, smul_eq_mul, abs_mul,
        abs_of_nonneg hα, Finset.mul_sum]
    _ ≤ α * (8 * ∑ e, |Aᵀ b e|) := mul_le_mul_of_nonneg_left hprod hα
    _ ≤ α * (8 * r) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsize' (by norm_num)) hα
    _ = _ := by ring

theorem mulVec_l1_le (R : Matrix B E ℝ) (C : ℝ)
    (hcol : ∀ e, ∑ b, |R b e| ≤ C) (h : E → ℝ) :
    (∑ b, |(R *ᵥ h) b|) ≤ C * ∑ e, |h e| := by
  change (∑ b, |∑ e, R b e * h e|) ≤ _
  calc
    _ ≤ ∑ b, ∑ e, |R b e * h e| :=
      Finset.sum_le_sum (fun b _ => abs_sum_le_sum_abs _ _)
    _ = ∑ e, (∑ b, |R b e|) * |h e| := by
      simp_rw [abs_mul]
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ e, C * |h e| := Finset.sum_le_sum
      (fun e _ => mul_le_mul_of_nonneg_right (hcol e) (abs_nonneg _))
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem mulVec_pointwise_le (R : Matrix B E ℝ) (C u : ℝ) (hu : 0 ≤ u)
    (hrow : ∀ b, ∑ e, |R b e| ≤ C) (h : E → ℝ) (hh : ∀ e, |h e| ≤ u) (b : B) :
    |(R *ᵥ h) b| ≤ C * u := by
  change |∑ e, R b e * h e| ≤ _
  calc
    _ ≤ ∑ e, |R b e * h e| := abs_sum_le_sum_abs _ _
    _ = ∑ e, |R b e| * |h e| := by simp only [abs_mul]
    _ ≤ ∑ e, |R b e| * u := Finset.sum_le_sum
      (fun e _ => mul_le_mul_of_nonneg_left (hh e) (abs_nonneg _))
    _ = (∑ e, |R b e|) * u := (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (hrow b) hu

/-- Exact loads and positivity after a uniformly small correction. -/
theorem repair_positive (A : Matrix E B ℝ) (α r u δ : ℝ)
    (hα : 0 ≤ α) (hu : 0 ≤ u) (hδ : 0 < δ)
    (hA : ∀ e b, 0 ≤ A e b) (hsize : ∀ b, ∑ e, A e b ≤ r)
    (hdet : (gram A α).det ≠ 0)
    (hrows : ∀ e, ∑ f, |(gram A α)⁻¹ e f| ≤ 8)
    (μ : B → ℝ) (ν : E → ℝ) (hμ : ∀ b, δ ≤ μ b)
    (hdefect : ∀ e, |(ν - A *ᵥ μ) e| ≤ u) (hsmall : 8 * r * α * u ≤ δ / 2) :
    ∃ μ' : B → ℝ, A *ᵥ μ' = ν ∧
      (∀ b, 0 < μ' b) ∧ (∀ b, |μ' b - μ b| ≤ 8 * r * α * u) := by
  let h := ν - A *ᵥ μ
  let v := corrector A α *ᵥ h
  have hv (b : B) : |v b| ≤ 8 * r * α * u :=
    mulVec_pointwise_le _ _ u hu (corrector_rows_le A α r hα hA hsize hrows) h hdefect b
  refine ⟨μ + v, ?_, ?_, ?_⟩
  · dsimp only [v, h]
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, right_inverse A α hdet, Matrix.one_mulVec]
    module
  · intro b
    have hn := neg_abs_le (v b)
    change 0 < μ b + v b
    linarith only [hμ b, hv b, hsmall, hδ, hn]
  · intro b
    simpa only [Pi.add_apply, add_sub_cancel_left] using hv b

end KqR75.LoadCorrection

#print axioms KqR75.LoadCorrection.right_inverse
#print axioms KqR75.LoadCorrection.corrector_cols_le_eight
#print axioms KqR75.LoadCorrection.corrector_rows_le
#print axioms KqR75.LoadCorrection.repair_positive
