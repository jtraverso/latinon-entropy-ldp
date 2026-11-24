module
public import TypeTracking

@[expose] public section
noncomputable section
namespace KqR75.TypeCounts

open Finset LatinonEntropy
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

def indicator (S : Finset B) : Option B → ℝ
  | none => 0
  | some b => if b ∈ S then 1 else 0

def count (S : Finset B) : List (Option B) → ℕ
  | [] => 0
  | none :: h => count S h
  | some b :: h => count S h + if b ∈ S then 1 else 0

theorem indicator_bounds (S : Finset B) (a : Option B) :
    0 ≤ indicator S a ∧ indicator S a ≤ 1 := by
  cases a with
  | none => norm_num [indicator]
  | some b => dsimp only [indicator]; split_ifs <;> norm_num

theorem path_count (S : Finset B) (h : List (Option B)) :
    pathSum (fun _ a => indicator S a) h = (count S h : ℝ) := by
  induction h with
  | nil => simp only [pathSum, count, Nat.cast_zero]
  | cons a h ih =>
    cases a with
    | none => rw [pathSum, ih]; simp only [indicator, count, add_zero]
    | some b =>
      rw [pathSum, ih]
      by_cases hb : b ∈ S <;> simp [count, indicator, hb]

theorem live_mean (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (S : Finset B) (guard : List (Option B) → Prop)
    (h : List (Option B)) (hl : WeightedGreedy.live I μ J guard h) :
    (∑ a, (WeightedGreedy.kernel I μ hμ J guard).transition h a * indicator S a) =
      TypeWeights.proportion I μ J S h := by
  simp only [WeightedGreedy.kernel, hl, ite_true, univ_option, Finset.sum_insertNone,
    indicator, zero_mul, zero_add]
  have hterm (b : B) : WeightedGreedy.availableWeight I μ J h b / WeightedGreedy.totalWeight I μ J h *
      (if b ∈ S then (1 : ℝ) else 0) =
        TypeWeights.marked S (WeightedGreedy.availableWeight I μ J h) b / WeightedGreedy.totalWeight I μ J h := by
    dsimp only [TypeWeights.marked]
    split_ifs <;> simp
  simp_rw [hterm]
  rw [← Finset.sum_div]
  dsimp only [TypeWeights.proportion]
  rw [TypeWeights.total_marked]

theorem centered_bound (K : FiniteKernel (Option B)) (S : Finset B)
    (h : List (Option B)) (a : Option B) :
    |FiniteAzuma.centered K (fun _ a => indicator S a) h a| ≤ 1 := by
  have hm0 : 0 ≤ ∑ c, K.transition h c * indicator S c :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (K.nonneg h c) (indicator_bounds S c).1)
  have hm1 : (∑ c, K.transition h c * indicator S c) ≤ 1 := by
    calc
      _ ≤ ∑ c, K.transition h c * 1 := Finset.sum_le_sum
        (fun c _ => mul_le_mul_of_nonneg_left (indicator_bounds S c).2 (K.nonneg h c))
      _ = _ := by simp only [mul_one, K.total]
  dsimp only [FiniteAzuma.centered]
  apply abs_le.mpr
  constructor <;> linarith only [(indicator_bounds S a).1, (indicator_bounds S a).2, hm0, hm1]

/-- Concentration of the actual integer number of selected blocks of a
type about the sum of its conditional selection probabilities. -/
theorem tail (K : FiniteKernel (Option B)) (S : Finset B) (T : ℕ)
    (hT : 0 < T) (u : ℝ) (hu : 0 ≤ u) :
    FiniteProcess.eventMass K T (fun h => u ≤ |(count S h : ℝ) -
      pathSum (fun h _ => ∑ a, K.transition h a * indicator S a) h|) ≤
      2 * Real.exp (-(u ^ 2 / (2 * (T : ℝ)))) := by
  let F := fun (_ : List (Option B)) a => indicator S a
  have hpath (h : List (Option B)) : pathSum (FiniteAzuma.centered K F) h =
      (count S h : ℝ) - pathSum (fun h _ => ∑ a, K.transition h a * indicator S a) h := by
    have hd := TypeTracking.decomposition K F h
    rw [path_count] at hd
    linarith only [hd]
  have hV : 0 < ∑ _i ∈ range T, (1 : ℝ) ^ 2 := by
    simpa only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using
      (show (0 : ℝ) < T by exact_mod_cast hT)
  have ht := FiniteAzuma.tail K (FiniteAzuma.centered K F) (fun _ => 1)
    (fun _ => by norm_num) (FiniteAzuma.centered_zero K F) (centered_bound K S) T u hu hV
  simp_rw [hpath] at ht
  simpa only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] using ht

end KqR75.TypeCounts

#print axioms KqR75.TypeCounts.live_mean
#print axioms KqR75.TypeCounts.tail
