module
public import TypeCovariance
public import RatioStep
public import GreedyMoments

@[expose] public section
noncomputable section
namespace KqR75.TypeDrift

open Finset
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- A finite bound for the full nonlinear type-ratio drift. It includes
the denominator remainder, rather than replacing a ratio by its derivative. -/
theorem mean_ratio (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b)
    (S : Finset B) (r : ℕ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hload : ∀ e, WeightedEnergy.load I w e ≤ 1) (k γ : ℝ) (hγ : 0 ≤ γ)
    (hover : ∀ b, OverlapDrift.overcount I w b ≤ γ)
    (hZ : 2 * (r : ℝ) ≤ ∑ b, w b) :
    let Z := ∑ b, w b
    let A := ∑ b, TypeWeights.marked S w b
    |∑ c, (w c / Z) * ((A - TypeWeights.removed I (TypeWeights.marked S w) c) /
        (Z - TypeWeights.removed I w c) - A / Z)| ≤
      (∑ e, WeightedEnergy.load I w e * |WeightedEnergy.load I w e - k|) / Z ^ 2 +
        γ / Z + 2 * (r : ℝ) ^ 2 / Z ^ 2 := by
  let Z := ∑ b, w b
  let v := TypeWeights.marked S w
  let A := ∑ b, v b
  let p := A / Z
  let F := ∑ e, WeightedEnergy.load I w e * |WeightedEnergy.load I w e - k|
  let D := fun c => (A - TypeWeights.removed I v c) / (Z - TypeWeights.removed I w c) - p
  let L := fun c => (p * TypeWeights.removed I w c - TypeWeights.removed I v c) / Z
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hZ0 : 0 < Z := by dsimp only [Z]; linarith only [hZ, hr0]
  have hv (b : B) := TypeWeights.marked_bounds S w hw b
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun b _ => (hv b).1)
  have hA : A ≤ Z := Finset.sum_le_sum (fun b _ => (hv b).2)
  have hp0 : 0 ≤ p := div_nonneg hA0 hZ0.le
  have hp1 : p ≤ 1 := (div_le_one hZ0).mpr hA
  have hmass : A = p * Z := by dsimp only [p]; field_simp [hZ0.ne']
  have hm := TypeCovariance.mean_bound I w hw S r hsize p k γ hp0 hp1 hγ hmass hover
  have hlinear : |∑ c, (w c / Z) * L c| ≤ F / Z ^ 2 + γ / Z := by
    have he : (∑ c, (w c / Z) * L c) =
        (∑ c, w c * (p * TypeWeights.removed I w c - TypeWeights.removed I v c)) / Z ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      dsimp only [L]
      ring
    rw [he, abs_div, abs_of_pos (sq_pos_of_pos hZ0)]
    have hs := div_le_div_of_nonneg_right hm (sq_nonneg Z)
    have ht : (F + γ * Z) / Z ^ 2 = F / Z ^ 2 + γ / Z := by
      field_simp [hZ0.ne']
      <;> ring
    exact hs.trans_eq ht
  have hprob : (∑ c, w c / Z) = 1 := by rw [← Finset.sum_div]; exact div_self hZ0.ne'
  have hrem (c : B) : |D c - L c| ≤ 2 * (r : ℝ) ^ 2 / Z ^ 2 := by
    exact (RatioStep.bounds Z A (TypeWeights.removed I w c) (TypeWeights.removed I v c)
      (r : ℝ) hr0 hZ hA0 hA (TypeWeights.removed_nonneg I w hw c)
      (TypeWeights.removed_le I w hw r hsize hload c)
      (TypeWeights.removed_nonneg I v (fun b => (hv b).1) c)
      (TypeWeights.removed_mono I v w (fun b => (hv b).2) c)).2
  have herror : |∑ c, (w c / Z) * (D c - L c)| ≤ 2 * (r : ℝ) ^ 2 / Z ^ 2 := by
    calc
      _ ≤ ∑ c, |(w c / Z) * (D c - L c)| := abs_sum_le_sum_abs _ _
      _ = ∑ c, (w c / Z) * |D c - L c| := by
        simp only [abs_mul, abs_of_nonneg (div_nonneg (hw _) hZ0.le)]
      _ ≤ ∑ c, (w c / Z) * (2 * (r : ℝ) ^ 2 / Z ^ 2) := Finset.sum_le_sum
        (fun c _ => mul_le_mul_of_nonneg_left (hrem c) (div_nonneg (hw c) hZ0.le))
      _ = _ := by rw [← Finset.sum_mul, hprob, one_mul]
  have he : (∑ c, (w c / Z) * D c) =
      (∑ c, (w c / Z) * L c) + ∑ c, (w c / Z) * (D c - L c) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  change |∑ c, (w c / Z) * D c| ≤ F / Z ^ 2 + γ / Z + 2 * (r : ℝ) ^ 2 / Z ^ 2
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add hlinear herror)

/-- Full conditional drift for a type in the actual physical greedy law.
The energy and absolute errors refer to the same current history. -/
theorem physical_mean (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (S : Finset B) (guard : List (Option B) → Prop)
    (h : List (Option B)) (hl : WeightedGreedy.live I μ J guard h)
    (r : ℕ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1) (k γ : ℝ) (hk : 0 ≤ k) (hγ : 0 ≤ γ)
    (hover : ∀ b, OverlapDrift.overcount I (WeightedGreedy.availableWeight I μ J h) b ≤ γ)
    (hZ : 2 * (r : ℝ) ≤ WeightedGreedy.totalWeight I μ J h) :
    |∑ a, (WeightedGreedy.kernel I μ hμ J guard).transition h a *
      (TypeWeights.proportion I μ J S (a :: h) - TypeWeights.proportion I μ J S h)| ≤
      (WeightedGreedy.energy I μ J h k + k * ∑ e, |WeightedGreedy.error I μ J h k e|) /
        WeightedGreedy.totalWeight I μ J h ^ 2 + γ / WeightedGreedy.totalWeight I μ J h +
        2 * (r : ℝ) ^ 2 / WeightedGreedy.totalWeight I μ J h ^ 2 := by
  let w := WeightedGreedy.availableWeight I μ J h
  have hw (b : B) : 0 ≤ w b := WeightedGreedy.availableWeight_nonneg I μ hμ J h b
  have hm := mean_ratio I w hw S r hr hsize
    (fun e => (WeightedGreedy.load_le_initial I μ hμ J h e).trans (hload e)) k γ hγ hover hZ
  have he : (∑ e, WeightedEnergy.load I w e * |WeightedEnergy.load I w e - k|) =
      ∑ e, WeightedGreedy.load I μ J h e * |WeightedGreedy.error I μ J h k e| := by
    apply Finset.sum_congr rfl
    intro e _
    by_cases ha : e ∈ WeightedGreedy.remaining I J h
    · simp only [w, WeightedGreedy.error, ha, ite_true, WeightedGreedy.load]
    · have hz := WeightedGreedy.load_zero_outside I μ J h e ha
      change WeightedGreedy.load I μ J h e * |WeightedGreedy.load I μ J h e - k| = _
      rw [hz, zero_mul, zero_mul]
  dsimp only at hm
  rw [he] at hm
  have hmoment := GreedyMoments.weighted_absolute_error I μ J h k
  have hbound := div_le_div_of_nonneg_right hmoment
    (sq_nonneg (WeightedGreedy.totalWeight I μ J h))
  have hmean : (∑ a, (WeightedGreedy.kernel I μ hμ J guard).transition h a *
      (TypeWeights.proportion I μ J S (a :: h) - TypeWeights.proportion I μ J S h)) =
      ∑ c, (w c / ∑ b, w b) *
        (((∑ b, TypeWeights.marked S w b) - TypeWeights.removed I (TypeWeights.marked S w) c) /
          ((∑ b, w b) - TypeWeights.removed I w c) - (∑ b, TypeWeights.marked S w b) / ∑ b, w b) := by
    simp only [WeightedGreedy.kernel, hl, ite_true, univ_option, Finset.sum_insertNone,
      zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro c _
    dsimp only [TypeWeights.proportion]
    rw [TypeWeights.total_after, TypeWeights.total_after, TypeWeights.available_marked,
      TypeWeights.total_marked]
    rfl
  rw [hmean]
  exact hm.trans (add_le_add (add_le_add hbound le_rfl) le_rfl)

end KqR75.TypeDrift

#print axioms KqR75.TypeDrift.mean_ratio
#print axioms KqR75.TypeDrift.physical_mean
