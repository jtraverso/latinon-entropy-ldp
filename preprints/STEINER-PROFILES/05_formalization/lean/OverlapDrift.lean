module
public import WeightedGreedy

@[expose] public section
noncomputable section
namespace KqR75.OverlapDrift

open Finset

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- The excess counts repeated resource intersections beyond the first. -/
def excess (I : B → Finset E) (b c : B) : ℝ :=
  if Disjoint (I b) (I c) then 0 else (((I b ∩ I c).card : ℝ) - 1)

def overcount (I : B → Finset E) (w : B → ℝ) (b : B) : ℝ :=
  ∑ c, w c * excess I b c

def correction (I : B → Finset E) (w : B → ℝ) (e : E) : ℝ :=
  WeightedEnergy.load I (fun b => w b * overcount I w b) e

def loss (I : B → Finset E) (w : B → ℝ) (c : B) (e : E) : ℝ :=
  WeightedEnergy.load I (fun b => if Disjoint (I b) (I c) then 0 else w b) e

theorem intersection_card (I : B → Finset E) (b c : B) :
    ((I b ∩ I c).card : ℝ) = (if Disjoint (I b) (I c) then 0 else 1) + excess I b c := by
  by_cases hd : Disjoint (I b) (I c)
  · have hi : I b ∩ I c = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd
    simp [excess, hd, hi]
  · simp only [excess, hd, ite_false]
    ring

theorem excess_nonneg (I : B → Finset E) (b c : B) : 0 ≤ excess I b c := by
  by_cases hd : Disjoint (I b) (I c)
  · simp [excess, hd]
  · have hn : (I b ∩ I c).Nonempty := Finset.nonempty_iff_ne_empty.mpr
      (fun hi => hd (Finset.disjoint_iff_inter_eq_empty.mpr hi))
    have hc : (1 : ℝ) ≤ (I b ∩ I c).card := by
      exact_mod_cast (show 1 ≤ (I b ∩ I c).card from Finset.card_pos.mpr hn)
    simpa only [excess, hd, ite_false] using sub_nonneg.mpr hc

theorem intersection_load (I : B → Finset E) (w : B → ℝ) (b : B) :
    (∑ e ∈ I b, WeightedEnergy.load I w e) = ∑ c, w c * ((I b ∩ I c).card : ℝ) := by
  dsimp only [WeightedEnergy.load]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul]
  ring

theorem overcount_identity (I : B → Finset E) (w : B → ℝ) (b : B) :
    (∑ e ∈ I b, WeightedEnergy.load I w e) =
      (∑ c, if Disjoint (I b) (I c) then 0 else w c) + overcount I w b := by
  rw [intersection_load]
  dsimp only [overcount]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [intersection_card]
  split_ifs <;> ring

theorem loss_eq_history (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (c : B) (e : E) :
    loss I (WeightedGreedy.availableWeight I μ J h) c e = WeightedGreedy.loss I μ J h c e := by
  apply Finset.sum_congr rfl
  intro b _
  by_cases he : e ∈ I b <;> by_cases hd : Disjoint (I b) (I c) <;>
    simp only [he, hd, not_true_eq_false, not_false_eq_true, false_and, true_and,
      ite_true, ite_false]

theorem loss_on_selected (I : B → Finset E) (w : B → ℝ) (c : B) (e : E)
    (he : e ∈ I c) : loss I w c e = WeightedEnergy.load I w e := by
  apply Finset.sum_congr rfl
  intro b _
  by_cases heb : e ∈ I b
  · have hn : ¬ Disjoint (I b) (I c) := fun hd => Finset.disjoint_left.mp hd heb he
    simp only [heb, hn, ite_true, ite_false]
  · simp only [heb, ite_false]

theorem weighted_loss (I : B → Finset E) (w : B → ℝ) (f : E → ℝ) :
    (∑ c, w c * ∑ e, loss I w c e * f e) =
      (∑ b, w b * (∑ e ∈ I b, f e) * (∑ e ∈ I b, WeightedEnergy.load I w e)) -
        ∑ e, correction I w e * f e := by
  have htest (c : B) : (∑ e, loss I w c e * f e) =
      ∑ b, (if Disjoint (I b) (I c) then 0 else w b) * ∑ e ∈ I b, f e :=
    (WeightedEnergy.incidence_sum I (fun b => if Disjoint (I b) (I c) then 0 else w b) f).symm
  have hb (b : B) :
      (∑ c, w c * ((if Disjoint (I b) (I c) then 0 else w b) * ∑ e ∈ I b, f e)) =
        w b * (∑ e ∈ I b, f e) *
          ((∑ e ∈ I b, WeightedEnergy.load I w e) - overcount I w b) := by
    have hi := overcount_identity I w b
    have hm : (∑ e ∈ I b, WeightedEnergy.load I w e) - overcount I w b =
        ∑ c, if Disjoint (I b) (I c) then 0 else w c := by linarith only [hi]
    conv_rhs => rw [hm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> ring
  have hi := WeightedEnergy.incidence_sum I (fun b => w b * overcount I w b) f
  calc
    _ = ∑ c, ∑ b, w c * ((if Disjoint (I b) (I c) then 0 else w b) * ∑ e ∈ I b, f e) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [htest, Finset.mul_sum]
    _ = ∑ b, ∑ c, w c * ((if Disjoint (I b) (I c) then 0 else w b) * ∑ e ∈ I b, f e) :=
      Finset.sum_comm
    _ = ∑ b, w b * (∑ e ∈ I b, f e) *
        ((∑ e ∈ I b, WeightedEnergy.load I w e) - overcount I w b) :=
      Finset.sum_congr rfl (fun b _ => hb b)
    _ = _ := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      congr 1
      calc
        _ = ∑ b, (w b * overcount I w b) * ∑ e ∈ I b, f e := by
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := hi

theorem weighted_outside_loss (I : B → Finset E) (w : B → ℝ) (e : E) :
    (∑ c, w c * (if e ∈ I c then 0 else loss I w c e)) =
      (∑ c, w c * loss I w c e) - (WeightedEnergy.load I w e) ^ 2 := by
  have hterm (c : B) : w c * (if e ∈ I c then 0 else loss I w c e) =
      w c * loss I w c e - (if e ∈ I c then w c else 0) * WeightedEnergy.load I w e := by
    by_cases he : e ∈ I c
    · rw [loss_on_selected I w c e he]
      simp [he]
    · simp [he]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  change (∑ c, w c * loss I w c e) - WeightedEnergy.load I w e * WeightedEnergy.load I w e = _
  ring

theorem correction_bounds (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b)
    (γ : ℝ) (hδ : ∀ b, overcount I w b ≤ γ) (e : E) :
    0 ≤ correction I w e ∧ correction I w e ≤ γ * WeightedEnergy.load I w e := by
  have hδ0 (b : B) : 0 ≤ overcount I w b :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (hw c) (excess_nonneg I b c))
  constructor
  · apply Finset.sum_nonneg
    intro b _
    split_ifs
    · exact mul_nonneg (hw b) (hδ0 b)
    · exact le_rfl
  · change (∑ b, if e ∈ I b then w b * overcount I w b else 0) ≤ _
    dsimp only [WeightedEnergy.load]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    by_cases he : e ∈ I b
    · simpa only [he, ite_true, mul_comm] using mul_le_mul_of_nonneg_left (hδ b) (hw b)
    · simp [he]

end KqR75.OverlapDrift

#print axioms KqR75.OverlapDrift.weighted_loss
#print axioms KqR75.OverlapDrift.weighted_outside_loss
#print axioms KqR75.OverlapDrift.correction_bounds
