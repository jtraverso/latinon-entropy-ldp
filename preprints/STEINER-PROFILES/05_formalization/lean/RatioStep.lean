module
public import TypeWeights

@[expose] public section
noncomputable section
namespace KqR75.RatioStep

/-- Exact finite ratio update, including the step that crosses a guard. -/
theorem identity (Z A u v : ℝ) (hZ : Z ≠ 0) (hZu : Z - u ≠ 0) :
    (A - v) / (Z - u) - A / Z = (A / Z * u - v) / (Z - u) := by
  field_simp [hZ, hZu]
  <;> ring

theorem bounds (Z A u v R : ℝ) (hR : 0 < R) (hZ : 2 * R ≤ Z)
    (hA0 : 0 ≤ A) (hA : A ≤ Z) (hu0 : 0 ≤ u) (hu : u ≤ R) (hv0 : 0 ≤ v) (hv : v ≤ u) :
    |(A - v) / (Z - u) - A / Z| ≤ 2 * R / Z ∧
    |((A - v) / (Z - u) - A / Z) - (A / Z * u - v) / Z| ≤ 2 * R ^ 2 / Z ^ 2 := by
  have hZ0 : 0 < Z := by linarith
  have hZu : 0 < Z - u := by linarith
  have hf0 : 0 ≤ A / Z := div_nonneg hA0 hZ0.le
  have hf1 : A / Z ≤ 1 := (div_le_one hZ0).mpr hA
  have hN : |A / Z * u - v| ≤ R := by
    apply abs_le.mpr
    constructor
    · nlinarith only [mul_nonneg hf0 hu0, hv, hu]
    · have ht := mul_le_mul_of_nonneg_right hf1 hu0
      nlinarith only [ht, hu, hv0]
  have hd : |(A - v) / (Z - u) - A / Z| ≤ 2 * R / Z := by
    rw [identity Z A u v hZ0.ne' hZu.ne', abs_div, abs_of_pos hZu]
    calc
      _ ≤ R / (Z - u) := div_le_div_of_nonneg_right hN hZu.le
      _ ≤ R / (Z / 2) := div_le_div_of_nonneg_left hR.le (by linarith) (by linarith)
      _ = _ := by ring
  refine ⟨hd, ?_⟩
  have he : ((A - v) / (Z - u) - A / Z) - (A / Z * u - v) / Z =
      ((A - v) / (Z - u) - A / Z) * u / Z := by
    field_simp [hZ0.ne', hZu.ne']
    <;> ring
  rw [he, abs_div, abs_mul, abs_of_nonneg hu0, abs_of_pos hZ0]
  calc
    _ ≤ (2 * R / Z) * R / Z := div_le_div_of_nonneg_right
      (mul_le_mul hd hu hu0 (by positivity)) hZ0.le
    _ = _ := by ring

open Finset
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- Deterministic increments of the actual available type proportions.
The loss is bounded from the physical resource loads, not postulated. -/
theorem physical_bounds (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (S : Finset B) (h : List (Option B)) (c : B)
    (r : ℕ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (hZ : 2 * (r : ℝ) ≤ WeightedGreedy.totalWeight I μ J h) :
    |TypeWeights.proportion I μ J S (some c :: h) - TypeWeights.proportion I μ J S h| ≤
      2 * (r : ℝ) / WeightedGreedy.totalWeight I μ J h := by
  let w := WeightedGreedy.availableWeight I μ J h
  have hw (b : B) : 0 ≤ w b := WeightedGreedy.availableWeight_nonneg I μ hμ J h b
  have hmarked (b : B) := TypeWeights.marked_bounds S w hw b
  have hA0 : 0 ≤ WeightedGreedy.totalWeight I (TypeWeights.marked S μ) J h := by
    change 0 ≤ ∑ b, WeightedGreedy.availableWeight I (TypeWeights.marked S μ) J h b
    rw [TypeWeights.available_marked]
    exact Finset.sum_nonneg (fun b _ => (hmarked b).1)
  have hA : WeightedGreedy.totalWeight I (TypeWeights.marked S μ) J h ≤
      WeightedGreedy.totalWeight I μ J h := by
    change (∑ b, WeightedGreedy.availableWeight I (TypeWeights.marked S μ) J h b) ≤ ∑ b, w b
    rw [TypeWeights.available_marked]
    exact Finset.sum_le_sum (fun b _ => (hmarked b).2)
  have hu0 := TypeWeights.removed_nonneg I w hw c
  have hu := TypeWeights.removed_le I w hw r hsize
    (fun e => (WeightedGreedy.load_le_initial I μ hμ J h e).trans (hload e)) c
  have hv0 := TypeWeights.removed_nonneg I (TypeWeights.marked S w) (fun b => (hmarked b).1) c
  have hv := TypeWeights.removed_mono I (TypeWeights.marked S w) w (fun b => (hmarked b).2) c
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hs := (bounds _ _ _ _ (r : ℝ) hr0 hZ hA0 hA hu0 hu hv0 hv).1
  dsimp only [TypeWeights.proportion]
  rw [TypeWeights.total_after, TypeWeights.total_after, TypeWeights.available_marked]
  exact hs

end KqR75.RatioStep

#print axioms KqR75.RatioStep.bounds
#print axioms KqR75.RatioStep.physical_bounds
