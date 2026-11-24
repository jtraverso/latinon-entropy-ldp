module
public import CumulativeTypeDrift
public import TypeCountHorizon
public import PrefixTypeTests

@[expose] public section
noncomputable section
namespace KqR75.HorizonConcentration

open Finset LatinonEntropy

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- Once predictable drift has been bounded, a single variance budget
controls the proportion of a type at every prefix of the horizon. -/
theorem prefix_tail (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ w, 0 ≤ μ w)
    (J : Finset E) (S : Finset B) (guard : List (Option B) → Prop)
    (r T : ℕ) (hr : 1 ≤ r) (hsize : ∀ w, (I w).card = r)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (g : ℕ → ℝ) (hg : ∀ i, 0 < g i)
    (hregular : ∀ h, guard h → 2 * (r : ℝ) ≤ WeightedGreedy.totalWeight I μ J h)
    (hdenom : ∀ h, guard h → g h.length ≤ WeightedGreedy.totalWeight I μ J h)
    (u L V : ℝ) (hu : 0 < u) (hL : 0 ≤ L) (hV : 0 < V)
    (hv : (∑ i ∈ range T, (4 * (r : ℝ) / g i) ^ 2) ≤ V) :
    let K := WeightedGreedy.kernel I μ hμ J guard
    let drift := fun h => pathSum
      (fun q _ => ∑ w, K.transition q w * TypeMartingale.increment I μ J S guard q w) h
    (∀ h : List (Option B), h.length ≤ T → |drift h| ≤ L) →
    ∀ t ≤ T, FiniteProcess.eventMass K t (fun h =>
      u + L < |TypeWeights.proportion I μ J S h - TypeWeights.proportion I μ J S []|) ≤
      2 * Real.exp (-(u ^ 2 / (2 * V))) := by
  classical
  dsimp only
  intro hbound t ht
  let K := WeightedGreedy.kernel I μ hμ J guard
  let drift := fun h => pathSum
    (fun q _ => ∑ w, K.transition q w * TypeMartingale.increment I μ J S guard q w) h
  by_cases ht0 : t = 0
  · subst t
    unfold FiniteProcess.eventMass
    refine le_trans (sum_nonpos ?_) (by positivity)
    intro h hh
    have hnil : h = [] := List.length_eq_zero_iff.mp (histories_length hh)
    subst h
    have hn : ¬ u + L < (0 : ℝ) := by linarith
    simp [hn]
  have hs : 0 < ∑ i ∈ range t, (4 * (r : ℝ) / g i) ^ 2 := by
    have h0 : 0 ∈ range t := mem_range.mpr (Nat.pos_of_ne_zero ht0)
    exact (show 0 < (4 * (r : ℝ) / g 0) ^ 2 by
      have h' : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
      exact pow_pos (div_pos (mul_pos (by norm_num) h') (hg 0)) _).trans_le
        (single_le_sum (f := fun i => (4 * (r : ℝ) / g i) ^ 2) (fun i _ => sq_nonneg _) h0)
  have htV : (∑ i ∈ range t, (4 * (r : ℝ) / g i) ^ 2) ≤ V :=
    (sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr ht) (fun i _ _ => sq_nonneg _)).trans hv
  have ht' := TypeTracking.observed_tail I μ hμ J S guard r hr hsize hload g hg hregular hdenom t u hu.le hs
  have hmono : FiniteProcess.eventMass K t (fun h =>
      u + L < |TypeWeights.proportion I μ J S h - TypeWeights.proportion I μ J S []|) ≤
      FiniteProcess.eventMass K t (fun h => u ≤
        |TypeWeights.proportion I μ J S h - TypeWeights.proportion I μ J S [] - drift h|) := by
    apply PrefixTypeTests.mono_support
    intro h hh _ hp
    have hd := hbound h (by rw [histories_length hh]; exact ht)
    let x := TypeWeights.proportion I μ J S h - TypeWeights.proportion I μ J S []
    have htriangle : |x| ≤ |x - drift h| + |drift h| := by
      simpa only [sub_add_cancel] using abs_add_le (x - drift h) (drift h)
    change u + L < |x| at hp
    change u ≤ |x - drift h|
    linarith only [htriangle, hp, hd]
  refine hmono.trans (ht'.trans ?_)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg
    (div_le_div_of_nonneg_left (sq_nonneg u) (by positivity)
      (mul_le_mul_of_nonneg_left htV (by norm_num))))) (by norm_num)

theorem proportion_rate (n : ℝ) (r : ℕ) (a z K : ℝ)
    (hn : 1 ≤ n) (ha : 0 ≤ a) (hK : 0 < K)
    (hs : a * (4 * (r : ℝ) - 1) = 1 - 2 * z) :
    2 * Real.exp (-((n ^ (-z)) ^ 2 / (2 * (K * n ^ (-2 + a * (2 * (r : ℝ) - 1)))))) ≤
      2 * Real.exp (-(1 / (2 * K)) * n) := by
  have hn₀ : 0 < n := by linarith
  have hu : (n ^ (-z)) ^ 2 = n ^ (-2 * z) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hn₀.le]
    congr 1
    ring
  have hp : n ^ (-2 * z) =
      n ^ (-2 + a * (2 * (r : ℝ) - 1)) * n ^ (1 + 2 * a * r) := by
    rw [← Real.rpow_add hn₀]
    congr 1
    linarith only [hs]
  have he : n ≤ n ^ (1 + 2 * a * r) := by
    calc
      n = n ^ (1 : ℝ) := (Real.rpow_one n).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn
        (le_add_of_nonneg_right (by positivity))
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
  rw [hu, hp]
  have hpn : 0 < n ^ (-2 + a * (2 * (r : ℝ) - 1)) := Real.rpow_pos_of_pos hn₀ _
  have hden : 0 < 2 * (K * n ^ (-2 + a * (2 * (r : ℝ) - 1))) := by positivity
  have hh : (1 / (2 * K)) * n ≤
      (n ^ (-2 + a * (2 * (r : ℝ) - 1)) * n ^ (1 + 2 * a * r)) /
        (2 * (K * n ^ (-2 + a * (2 * (r : ℝ) - 1)))) := by
    apply (le_div_iff₀ hden).2
    calc
      _ = n ^ (-2 + a * (2 * (r : ℝ) - 1)) * n := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left he hpn.le
  simpa only [neg_mul] using neg_le_neg hh

theorem count_rate (n C z : ℝ) (T : ℕ) (hn : 1 ≤ n) (hC : 0 < C)
    (hz : z ≤ 1 / 2) (hT : 0 < T) (hbound : (T : ℝ) ≤ C * n ^ 2) :
    2 * Real.exp (-((n ^ (2 - z)) ^ 2 / (2 * (T : ℝ)))) ≤
      2 * Real.exp (-(1 / (2 * C)) * n) := by
  have hn₀ : 0 < n := by linarith
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hp : n ^ (3 : ℕ) ≤ (n ^ (2 - z)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_two, ← Real.rpow_mul hn₀.le]
    exact Real.rpow_le_rpow_of_exponent_le hn (by push_cast; linarith)
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
  have hh : (1 / (2 * C)) * n ≤ (n ^ (2 - z)) ^ 2 / (2 * (T : ℝ)) := by
    apply (le_div_iff₀ (show 0 < 2 * (T : ℝ) by positivity)).2
    calc
      _ ≤ ((1 / (2 * C)) * n) * (2 * (C * n ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound (by norm_num)) (by positivity)
      _ = n ^ (3 : ℕ) := by field_simp
      _ ≤ _ := hp
  simpa only [neg_mul] using neg_le_neg hh

end KqR75.HorizonConcentration

#print axioms KqR75.HorizonConcentration.prefix_tail
#print axioms KqR75.HorizonConcentration.proportion_rate
#print axioms KqR75.HorizonConcentration.count_rate
