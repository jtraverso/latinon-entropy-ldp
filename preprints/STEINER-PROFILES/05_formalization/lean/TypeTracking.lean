module
public import TypeMartingale
public import TypeDrift

@[expose] public section
noncomputable section
namespace KqR75.TypeTracking

open Finset LatinonEntropy
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

theorem positive_increment (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (S : Finset B) (guard : List (Option B) → Prop)
    (h : List (Option B)) (a : Option B)
    (hp : 0 < (WeightedGreedy.kernel I μ hμ J guard).transition h a) :
    TypeMartingale.increment I μ J S guard h a =
      TypeWeights.proportion I μ J S (a :: h) - TypeWeights.proportion I μ J S h := by
  classical
  by_cases hl : WeightedGreedy.live I μ J guard h
  · cases a with
    | none => simp only [TypeMartingale.increment, hl, ite_true, TypeWeights.proportion_none, sub_self]
    | some c => simp only [TypeMartingale.increment, hl, ite_true]
  · cases a with
    | none => simp only [TypeMartingale.increment, hl, ite_false, TypeWeights.proportion_none, sub_self]
    | some c => simp [WeightedGreedy.kernel, hl] at hp

/-- On every positive-probability history the predictably killed increments
telescope to the actual type proportion, including after absorption. -/
theorem telescope (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (S : Finset B) (guard : List (Option B) → Prop)
    (h : List (Option B)) (hp : 0 < historyWeight (WeightedGreedy.kernel I μ hμ J guard) h) :
    pathSum (TypeMartingale.increment I μ J S guard) h =
      TypeWeights.proportion I μ J S h - TypeWeights.proportion I μ J S [] := by
  let K := WeightedGreedy.kernel I μ hμ J guard
  revert hp
  induction h with
  | nil => intro _; simp only [pathSum, sub_self]
  | cons a h ih =>
    intro hp
    change 0 < historyWeight K h * K.transition h a at hp
    have hh : 0 < historyWeight K h := by
      by_contra hn
      have hz : historyWeight K h = 0 := le_antisymm (le_of_not_gt hn) (historyWeight_nonneg K h)
      simp only [hz, zero_mul, lt_self_iff_false] at hp
    have ha : 0 < K.transition h a := by
      by_contra hn
      have hz : K.transition h a = 0 := le_antisymm (le_of_not_gt hn) (K.nonneg h a)
      simp only [hz, mul_zero, lt_self_iff_false] at hp
    rw [pathSum, ih hh, positive_increment I μ hμ J S guard h a ha]
    ring

theorem decomposition {Ω : Type*} [Fintype Ω] (K : FiniteKernel Ω)
    (F : List Ω → Ω → ℝ) (h : List Ω) :
    pathSum F h = pathSum (FiniteAzuma.centered K F) h +
      pathSum (fun h _ => ∑ a, K.transition h a * F h a) h := by
  induction h with
  | nil => simp only [pathSum]; ring
  | cons a h ih => simp only [pathSum, FiniteAzuma.centered]; rw [ih]; ring

theorem physical_decomposition (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (S : Finset B) (guard : List (Option B) → Prop)
    (h : List (Option B)) (hp : 0 < historyWeight (WeightedGreedy.kernel I μ hμ J guard) h) :
    let K := WeightedGreedy.kernel I μ hμ J guard
    let F := TypeMartingale.increment I μ J S guard
    TypeWeights.proportion I μ J S h - TypeWeights.proportion I μ J S [] =
      pathSum (FiniteAzuma.centered K F) h +
        pathSum (fun h _ => ∑ a, K.transition h a * F h a) h := by
  dsimp only
  rw [← telescope I μ hμ J S guard h hp]
  exact decomposition _ _ h

/-- The predictable drift in the decomposition is the full nonlinear
physical drift, with the same history's energy as its error control. -/
theorem active_mean_bound (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (S : Finset B) (guard : List (Option B) → Prop)
    (h : List (Option B)) (hl : WeightedGreedy.live I μ J guard h)
    (r : ℕ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1) (k γ : ℝ) (hk : 0 ≤ k) (hγ : 0 ≤ γ)
    (hover : ∀ b, OverlapDrift.overcount I (WeightedGreedy.availableWeight I μ J h) b ≤ γ)
    (hZ : 2 * (r : ℝ) ≤ WeightedGreedy.totalWeight I μ J h) :
    |∑ a, (WeightedGreedy.kernel I μ hμ J guard).transition h a *
      TypeMartingale.increment I μ J S guard h a| ≤
      (WeightedGreedy.energy I μ J h k + k * ∑ e, |WeightedGreedy.error I μ J h k e|) /
        WeightedGreedy.totalWeight I μ J h ^ 2 + γ / WeightedGreedy.totalWeight I μ J h +
        2 * (r : ℝ) ^ 2 / WeightedGreedy.totalWeight I μ J h ^ 2 := by
  classical
  have he : (∑ a, (WeightedGreedy.kernel I μ hμ J guard).transition h a *
      TypeMartingale.increment I μ J S guard h a) =
      ∑ a, (WeightedGreedy.kernel I μ hμ J guard).transition h a *
        (TypeWeights.proportion I μ J S (a :: h) - TypeWeights.proportion I μ J S h) := by
    apply Finset.sum_congr rfl
    intro a _
    cases a with
    | none => simp only [WeightedGreedy.kernel, hl, ite_true, zero_mul]
    | some c => simp only [TypeMartingale.increment, hl, ite_true]
  rw [he]
  exact TypeDrift.physical_mean I μ hμ J S guard h hl r hr hsize hload k γ hk hγ hover hZ

/-- Concentration stated for the observed proportion and its actual
predictable drift, rather than only for an auxiliary martingale. -/
theorem observed_tail (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (S : Finset B) (guard : List (Option B) → Prop)
    (r : ℕ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (g : ℕ → ℝ) (hg : ∀ i, 0 < g i)
    (hregular : ∀ h, guard h → 2 * (r : ℝ) ≤ WeightedGreedy.totalWeight I μ J h)
    (hdenom : ∀ h, guard h → g h.length ≤ WeightedGreedy.totalWeight I μ J h)
    (T : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hV : 0 < ∑ i ∈ range T, (4 * (r : ℝ) / g i) ^ 2) :
    let K := WeightedGreedy.kernel I μ hμ J guard
    let F := TypeMartingale.increment I μ J S guard
    let drift := pathSum (fun h _ => ∑ a, K.transition h a * F h a)
    FiniteProcess.eventMass K T (fun h => u ≤
      |TypeWeights.proportion I μ J S h - TypeWeights.proportion I μ J S [] - drift h|) ≤
      2 * Real.exp (-(u ^ 2 / (2 * ∑ i ∈ range T, (4 * (r : ℝ) / g i) ^ 2))) := by
  classical
  let K := WeightedGreedy.kernel I μ hμ J guard
  let F := TypeMartingale.increment I μ J S guard
  let drift := pathSum (fun h _ => ∑ a, K.transition h a * F h a)
  have he : FiniteProcess.eventMass K T (fun h => u ≤
      |TypeWeights.proportion I μ J S h - TypeWeights.proportion I μ J S [] - drift h|) =
      FiniteProcess.eventMass K T (fun h => u ≤ |pathSum (FiniteAzuma.centered K F) h|) := by
    dsimp only [FiniteProcess.eventMass]
    apply Finset.sum_congr rfl
    intro h _
    by_cases hp : 0 < historyWeight K h
    · have hd := physical_decomposition I μ hμ J S guard h hp
      change TypeWeights.proportion I μ J S h - TypeWeights.proportion I μ J S [] =
        pathSum (FiniteAzuma.centered K F) h + drift h at hd
      have hx : TypeWeights.proportion I μ J S h - TypeWeights.proportion I μ J S [] - drift h =
          pathSum (FiniteAzuma.centered K F) h := by rw [hd]; ring
      simp only [hx]
    · have hz : historyWeight K h = 0 := le_antisymm (le_of_not_gt hp) (historyWeight_nonneg K h)
      simp only [hz, ite_self]
  dsimp only
  rw [he]
  exact TypeMartingale.tail I μ hμ J S guard r hr hsize hload g hg hregular hdenom T u hu hV

end KqR75.TypeTracking

#print axioms KqR75.TypeTracking.physical_decomposition
#print axioms KqR75.TypeTracking.active_mean_bound
#print axioms KqR75.TypeTracking.observed_tail
