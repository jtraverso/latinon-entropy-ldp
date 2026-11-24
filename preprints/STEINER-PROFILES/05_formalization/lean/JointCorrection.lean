module
public import LoadCorrection

@[expose] public section
noncomputable section
namespace KqR75.JointCorrection

open Finset
open scoped Matrix
variable {E B D : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]
  [Fintype D] [DecidableEq D]

/-- Project the restricted lifts onto the load kernel using the physical
right inverse. The observed histogram changes by the correction term. -/
theorem restrict_lifts (A : Matrix E B ℝ) (R : Matrix B E ℝ)
    (H : Matrix D B ℝ) (L₀ : Matrix B D ℝ) (hR : A * R = 1) :
    let L := L₀ - R * (A * L₀)
    A * L = 0 ∧ H * L = H * L₀ - (H * R) * (A * L₀) := by
  dsimp only
  constructor
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc A R, hR, Matrix.one_mul, sub_self]
  · rw [Matrix.mul_sub, Matrix.mul_assoc H R]

/-- R repairs loads; L is a load-zero lift of independent histogram
coordinates. The finite Schur complement corrects both defects. -/
def delta (R : Matrix B E ℝ) (H : Matrix D B ℝ) (L : Matrix B D ℝ)
    (h : E → ℝ) (t : D → ℝ) : B → ℝ :=
  R *ᵥ h + L *ᵥ ((H * L)⁻¹ *ᵥ (t - H *ᵥ (R *ᵥ h)))

theorem equations (A : Matrix E B ℝ) (R : Matrix B E ℝ)
    (H : Matrix D B ℝ) (L : Matrix B D ℝ)
    (hR : A * R = 1) (hL : A * L = 0)
    (hdet : (H * L).det ≠ 0) (h : E → ℝ) (t : D → ℝ) :
    A *ᵥ delta R H L h t = h ∧ H *ᵥ delta R H L h t = t := by
  constructor
  · rw [delta, Matrix.mulVec_add, Matrix.mulVec_mulVec _ A R, Matrix.mulVec_mulVec _ A L,
      hR, hL, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
  · calc
      _ = H *ᵥ (R *ᵥ h) + (H * L) *ᵥ ((H * L)⁻¹ *ᵥ (t - H *ᵥ (R *ᵥ h))) := by
        rw [delta, Matrix.mulVec_add, Matrix.mulVec_mulVec _ H L]
      _ = H *ᵥ (R *ᵥ h) + (t - H *ᵥ (R *ᵥ h)) := by
        rw [Matrix.mulVec_mulVec _ (H * L) (H * L)⁻¹,
          Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
      _ = _ := by module

theorem inverse_bound (H : Matrix D B ℝ) (L : Matrix B D ℝ)
    (hnear : ∀ i, ∑ j, |((1 : Matrix D D ℝ) - H * L) i j| ≤ 1 / 2) :
    (H * L).det ≠ 0 ∧ ∀ i, ∑ j, |(H * L)⁻¹ i j| ≤ 8 := by
  apply MatrixPerturbation.inverse_rows_le_eight (H * L) 1
  · intro i
    have he : (∑ j, |(1 : Matrix D D ℝ) i j|) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp only [Matrix.one_apply, ite_true, abs_one]
      · intro j _ hji
        simp [Matrix.one_apply, Ne.symm hji]
      · simp
    rw [he]
    norm_num
  · simpa only [Matrix.mul_one] using hnear

/-- Quantitative positivity for simultaneous loads and independent type
coordinates. The near-identity condition proves the required invertibility. -/
theorem repair_positive (A : Matrix E B ℝ) (R : Matrix B E ℝ)
    (H : Matrix D B ℝ) (L : Matrix B D ℝ)
    (hR : A * R = 1) (hL : A * L = 0)
    (hnear : ∀ i, ∑ j, |((1 : Matrix D D ℝ) - H * L) i j| ≤ 1 / 2)
    (CR CL u w ε : ℝ) (hu : 0 ≤ u) (hw : 0 ≤ w) (hε : 0 < ε)
    (hrowsR : ∀ b, ∑ e, |R b e| ≤ CR) (hrowsL : ∀ b, ∑ i, |L b i| ≤ CL)
    (μ : B → ℝ) (ν : E → ℝ) (τ : D → ℝ) (hμ : ∀ b, ε ≤ μ b)
    (hdef : ∀ e, |(ν - A *ᵥ μ) e| ≤ u)
    (htype : ∀ i, |((τ - H *ᵥ μ) - H *ᵥ (R *ᵥ (ν - A *ᵥ μ))) i| ≤ w)
    (hsmall : CR * u + CL * (8 * w) ≤ ε / 2) :
    ∃ μ' : B → ℝ, A *ᵥ μ' = ν ∧ H *ᵥ μ' = τ ∧
      (∀ b, 0 < μ' b) ∧ (∀ b, |μ' b - μ b| ≤ CR * u + CL * (8 * w)) := by
  obtain ⟨hdet, hinv⟩ := inverse_bound H L hnear
  let h := ν - A *ᵥ μ
  let t := τ - H *ᵥ μ
  let z := (H * L)⁻¹ *ᵥ (t - H *ᵥ (R *ᵥ h))
  have hz (i : D) : |z i| ≤ 8 * w :=
    LoadCorrection.mulVec_pointwise_le _ 8 w hw hinv _ htype i
  have hfirst (b : B) : |(R *ᵥ h) b| ≤ CR * u :=
    LoadCorrection.mulVec_pointwise_le R CR u hu hrowsR h hdef b
  have hsecond (b : B) : |(L *ᵥ z) b| ≤ CL * (8 * w) :=
    LoadCorrection.mulVec_pointwise_le L CL (8 * w) (by positivity) hrowsL z hz b
  have hv (b : B) : |delta R H L h t b| ≤ CR * u + CL * (8 * w) := by
    change |(R *ᵥ h) b + (L *ᵥ z) b| ≤ CR * u + CL * (8 * w)
    exact (abs_add_le _ _).trans (add_le_add (hfirst b) (hsecond b))
  obtain ⟨ha, ht⟩ := equations A R H L hR hL hdet h t
  refine ⟨μ + delta R H L h t, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_add, ha]
    dsimp only [h]
    module
  · rw [Matrix.mulVec_add, ht]
    dsimp only [t]
    module
  · intro b
    have hn := neg_abs_le (delta R H L h t b)
    change 0 < μ b + delta R H L h t b
    linarith only [hμ b, hv b, hsmall, hε, hn]
  · intro b
    simpa only [Pi.add_apply, add_sub_cancel_left] using hv b

end KqR75.JointCorrection

#print axioms KqR75.JointCorrection.equations
#print axioms KqR75.JointCorrection.repair_positive
#print axioms KqR75.JointCorrection.restrict_lifts
