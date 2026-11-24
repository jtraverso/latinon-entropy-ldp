module
public import RatioStep
public import FiniteAzuma

@[expose] public section
noncomputable section
namespace KqR75.TypeMartingale

open Finset LatinonEntropy
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- A predictable killing of the actual type-proportion increment. -/
def increment (I : B → Finset E) (μ : B → ℝ) (J : Finset E) (S : Finset B)
    (guard : List (Option B) → Prop) (h : List (Option B)) (a : Option B) : ℝ := by
  classical
  exact if WeightedGreedy.live I μ J guard h then
    match a with
    | none => 0
    | some c => TypeWeights.proportion I μ J S (some c :: h) - TypeWeights.proportion I μ J S h
  else 0

theorem increment_bound (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (S : Finset B) (guard : List (Option B) → Prop)
    (r : ℕ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (g : ℕ → ℝ) (hg : ∀ i, 0 < g i)
    (hregular : ∀ h, guard h → 2 * (r : ℝ) ≤ WeightedGreedy.totalWeight I μ J h)
    (hdenom : ∀ h, guard h → g h.length ≤ WeightedGreedy.totalWeight I μ J h)
    (h : List (Option B)) (a : Option B) :
    |increment I μ J S guard h a| ≤ 2 * (r : ℝ) / g h.length := by
  classical
  have hg0 : 0 < g h.length := hg h.length
  by_cases hl : WeightedGreedy.live I μ J guard h
  · cases a with
    | none => simp only [increment, hl, ite_true, abs_zero]; positivity
    | some c =>
      simp only [increment, hl, ite_true]
      exact (RatioStep.physical_bounds I μ hμ J S h c r hr hsize hload (hregular h hl.2.1)).trans
        (div_le_div_of_nonneg_left (by positivity) (hg _) (hdenom h hl.2.1))
  · simp only [increment, hl, ite_false, abs_zero]
    positivity

/-- Azuma for the martingale part of the actual stopped type proportions.
The step size is derived from physical losses and the denominator guard. -/
theorem tail (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (S : Finset B) (guard : List (Option B) → Prop)
    (r : ℕ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (g : ℕ → ℝ) (hg : ∀ i, 0 < g i)
    (hregular : ∀ h, guard h → 2 * (r : ℝ) ≤ WeightedGreedy.totalWeight I μ J h)
    (hdenom : ∀ h, guard h → g h.length ≤ WeightedGreedy.totalWeight I μ J h)
    (T : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hV : 0 < ∑ i ∈ range T, (4 * (r : ℝ) / g i) ^ 2) :
    let K := WeightedGreedy.kernel I μ hμ J guard
    let Z := FiniteAzuma.centered K (increment I μ J S guard)
    FiniteProcess.eventMass K T (fun h => u ≤ |pathSum Z h|) ≤
      2 * Real.exp (-(u ^ 2 / (2 * ∑ i ∈ range T, (4 * (r : ℝ) / g i) ^ 2))) := by
  let K := WeightedGreedy.kernel I μ hμ J guard
  let F := increment I μ J S guard
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hb (i : ℕ) : 0 < 4 * (r : ℝ) / g i := div_pos (by positivity) (hg i)
  have hc (h : List (Option B)) (a : Option B) :
      |FiniteAzuma.centered K F h a| ≤ 4 * (r : ℝ) / g h.length := by
    have hh := FiniteAzuma.centered_abs_le K F (fun i => 2 * (r : ℝ) / g i)
      (increment_bound I μ hμ J S guard r hr hsize hload g hg hregular hdenom) h a
    convert hh using 1 <;> ring
  exact FiniteAzuma.tail K (FiniteAzuma.centered K F) (fun i => 4 * (r : ℝ) / g i)
    hb (FiniteAzuma.centered_zero K F) hc T u hu hV

end KqR75.TypeMartingale

#print axioms KqR75.TypeMartingale.increment_bound
#print axioms KqR75.TypeMartingale.tail
