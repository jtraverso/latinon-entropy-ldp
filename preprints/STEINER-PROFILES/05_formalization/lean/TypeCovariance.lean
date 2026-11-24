module
public import TypeWeights

@[expose] public section
noncomputable section
namespace KqR75.TypeCovariance

open Finset
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

theorem difference_bound (a b p : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : |a - p * b| ≤ b := by
  have hb : 0 ≤ b := ha.trans hab
  have hpb0 := mul_nonneg hp0 hb
  have hpb1 := mul_le_mul_of_nonneg_right hp1 hb
  apply abs_le.mpr
  constructor <;> nlinarith only [ha, hab, hpb0, hpb1]

theorem load_mass (I : B → Finset E) (w : B → ℝ) (r : ℕ)
    (hsize : ∀ b, (I b).card = r) :
    (∑ e, WeightedEnergy.load I w e) = (r : ℝ) * ∑ b, w b := by
  have hi := WeightedEnergy.incidence_sum I w (fun _ => (1 : ℝ))
  have ht : (∑ e, WeightedEnergy.load I w e) = (∑ b, w b) * (r : ℝ) := by
    simpa only [Finset.sum_const, nsmul_eq_mul, hsize, mul_one, ← Finset.sum_mul] using hi.symm
  exact ht.trans (mul_comm _ _)

/-- Subtracting the type proportion cancels the constant load profile
exactly. This is the centering used in the type drift, before expectation. -/
theorem mean_identity (I : B → Finset E) (w v : B → ℝ) (r : ℕ)
    (hsize : ∀ b, (I b).card = r) (p k : ℝ)
    (hmass : (∑ b, v b) = p * ∑ b, w b) :
    (∑ c, w c * (p * TypeWeights.removed I w c - TypeWeights.removed I v c)) =
      -(∑ e, (WeightedEnergy.load I v e - p * WeightedEnergy.load I w e) *
        (WeightedEnergy.load I w e - k)) +
      ∑ b, (v b - p * w b) * OverlapDrift.overcount I w b := by
  have hz : (∑ e, (WeightedEnergy.load I v e - p * WeightedEnergy.load I w e)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, load_mass I v r hsize, load_mass I w r hsize, hmass]
    ring
  have he : (∑ e, (WeightedEnergy.load I v e - p * WeightedEnergy.load I w e) *
      (WeightedEnergy.load I w e - k)) =
      (∑ e, WeightedEnergy.load I v e * WeightedEnergy.load I w e) -
        p * ∑ e, WeightedEnergy.load I w e * WeightedEnergy.load I w e := by
    calc
      _ = (∑ e, (WeightedEnergy.load I v e * WeightedEnergy.load I w e -
          p * (WeightedEnergy.load I w e * WeightedEnergy.load I w e))) -
            k * ∑ e, (WeightedEnergy.load I v e - p * WeightedEnergy.load I w e) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = _ := by rw [hz, mul_zero, sub_zero, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hd : (∑ b, (v b - p * w b) * OverlapDrift.overcount I w b) =
      (∑ b, v b * OverlapDrift.overcount I w b) -
        p * ∑ b, w b * OverlapDrift.overcount I w b := by
    simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hl : (∑ c, w c * (p * TypeWeights.removed I w c - TypeWeights.removed I v c)) =
      p * (∑ c, w c * TypeWeights.removed I w c) -
        ∑ c, w c * TypeWeights.removed I v c := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hl, TypeWeights.mean_removed I w w, TypeWeights.mean_removed I w v, he, hd]
  ring

/-- Mean linearized type loss, controlled by the actual load error and
the multiple-intersection bound. The type may be any finite block family. -/
theorem mean_bound (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b)
    (S : Finset B) (r : ℕ) (hsize : ∀ b, (I b).card = r)
    (p k γ : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hγ : 0 ≤ γ)
    (hmass : (∑ b, TypeWeights.marked S w b) = p * ∑ b, w b)
    (hover : ∀ b, OverlapDrift.overcount I w b ≤ γ) :
    |∑ c, w c * (p * TypeWeights.removed I w c - TypeWeights.removed I (TypeWeights.marked S w) c)| ≤
      (∑ e, WeightedEnergy.load I w e * |WeightedEnergy.load I w e - k|) + γ * ∑ b, w b := by
  let v := TypeWeights.marked S w
  have hv (b : B) := TypeWeights.marked_bounds S w hw b
  have hload (e : E) : 0 ≤ WeightedEnergy.load I v e ∧ WeightedEnergy.load I v e ≤ WeightedEnergy.load I w e := by
    constructor
    · apply Finset.sum_nonneg
      intro b _
      split_ifs <;> first | exact (hv b).1 | exact le_rfl
    · apply Finset.sum_le_sum
      intro b _
      split_ifs <;> first | exact (hv b).2 | exact le_rfl
  have hc : |∑ e, (WeightedEnergy.load I v e - p * WeightedEnergy.load I w e) *
      (WeightedEnergy.load I w e - k)| ≤
      ∑ e, WeightedEnergy.load I w e * |WeightedEnergy.load I w e - k| := by
    calc
      _ ≤ ∑ e, |(WeightedEnergy.load I v e - p * WeightedEnergy.load I w e) *
          (WeightedEnergy.load I w e - k)| := abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro e _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (difference_bound _ _ p (hload e).1 (hload e).2 hp0 hp1) (abs_nonneg _)
  have hd : |∑ b, (v b - p * w b) * OverlapDrift.overcount I w b| ≤ γ * ∑ b, w b := by
    calc
      _ ≤ ∑ b, |(v b - p * w b) * OverlapDrift.overcount I w b| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ b, w b * γ := by
        apply Finset.sum_le_sum
        intro b _
        have hδ := CodegreeLoss.overcount_nonneg I w hw b
        rw [abs_mul, abs_of_nonneg hδ]
        exact mul_le_mul (difference_bound _ _ p (hv b).1 (hv b).2 hp0 hp1)
          (hover b) hδ (hw b)
      _ = _ := by rw [← Finset.sum_mul]; ring
  rw [mean_identity I w v r hsize p k hmass]
  exact (abs_add_le _ _).trans (by rw [abs_neg]; exact add_le_add hc hd)

end KqR75.TypeCovariance

#print axioms KqR75.TypeCovariance.mean_identity
#print axioms KqR75.TypeCovariance.mean_bound
