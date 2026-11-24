module
public import TypeDriftEnvelope

@[expose] public section
noncomputable section
namespace KqR75.CumulativeTypeDrift

open Finset LatinonEntropy

/-- A predictable envelope indexed by history length also bounds its
path sum, including histories on which some increments vanish. -/
theorem pathSum_abs_le {Ω : Type*} (f : List Ω → Ω → ℝ) (d : ℕ → ℝ)
    (T : ℕ) (hb : ∀ h a, h.length < T → |f h a| ≤ d h.length)
    (h : List Ω) (hh : h.length ≤ T) :
    |pathSum f h| ≤ ∑ i ∈ range h.length, d i := by
  induction h with
  | nil => simp [pathSum]
  | cons a h ih =>
    have ht : h.length < T := hh
    rw [pathSum, List.length_cons, sum_range_succ]
    calc
      _ ≤ |pathSum f h| + |f h a| := abs_add_le _ _
      _ ≤ _ := add_le_add (ih ht.le) (hb h a ht)

def envelope (r : ℕ) (M n c C A b : ℝ) (i : ℕ) : ℝ :=
  let p := (M - (i : ℝ)) / M
  (2 / c) ^ 2 * A * (n ^ (-3 : ℝ) * p ^ (-4 * (r : ℝ))) +
  (2 / c) ^ 2 * Real.sqrt ((r : ℝ) * C * A) * (n ^ (-5 / 2 : ℝ) * p ^ (-2 * (r : ℝ) - 1 / 2)) +
  (2 / c) * (r : ℝ) ^ 2 * b * (n ^ (-3 : ℝ) * p ^ (-(r : ℝ))) +
  (2 / c) ^ 2 * (2 * (r : ℝ) ^ 2) * (n ^ (-4 : ℝ) * p ^ (-2 * (r : ℝ)))

def driftConstant (r : ℕ) (c C A b : ℝ) : ℝ :=
  (2 / c) ^ 2 * A * (C / (4 * (r : ℝ) - 1)) +
  (2 / c) ^ 2 * Real.sqrt ((r : ℝ) * C * A) * (C / (2 * (r : ℝ) - 1 / 2)) +
  (2 / c) * (r : ℝ) ^ 2 * b * (C / ((r : ℝ) - 1)) +
  (2 / c) ^ 2 * (2 * (r : ℝ) ^ 2) * (C / (2 * (r : ℝ) - 1))

theorem sum_envelope (n T r : ℕ) (M c C A b a z : ℝ)
    (hn : 1 ≤ n) (hr : 2 ≤ r) (hc : 0 < c) (hC : 0 ≤ C) (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hM : 0 < M) (hMᵤ : M ≤ C * (n : ℝ) ^ 2) (ha : 0 ≤ a) (hz : 0 ≤ z)
    (hs : a * (4 * (r : ℝ) - 1) = 1 - 2 * z) (hT : T ≤ GreedyScales.horizon M n a) :
    (∑ i ∈ range T, envelope r M n c C A b i) ≤ driftConstant r c C A b * (n : ℝ) ^ (-z) := by
  obtain ⟨h₁, h₂, h₃, h₄, he⟩ := GreedyScales.type_drift_sums n T r M C a z
    hn hr hM hC hMᵤ ha hz hs hT
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have h₁' := h₁.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hn' (show -2 * z ≤ -z by linarith))
    (div_nonneg hC (by linarith : 0 ≤ 4 * (r : ℝ) - 1)))
  have h₄' := h₄.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hn' he)
    (div_nonneg hC (by linarith : 0 ≤ 2 * (r : ℝ) - 1)))
  have h₂' : (n : ℝ) ^ (-5 / 2 : ℝ) * (∑ i ∈ range T,
      ((M - (i : ℝ)) / M) ^ (-2 * (r : ℝ) - 1 / 2)) ≤
      C / (2 * (r : ℝ) - 1 / 2) * (n : ℝ) ^ (-z) := by
    simpa only [neg_add_rev, neg_mul, sub_eq_add_neg, add_comm] using h₂
  have htotal := add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left h₁' (show 0 ≤ (2 / c) ^ 2 * A by positivity))
    (mul_le_mul_of_nonneg_left h₂' (show 0 ≤ (2 / c) ^ 2 * Real.sqrt ((r : ℝ) * C * A) by positivity)))
    (mul_le_mul_of_nonneg_left h₃ (show 0 ≤ (2 / c) * (r : ℝ) ^ 2 * b by positivity)))
    (mul_le_mul_of_nonneg_left h₄' (show 0 ≤ (2 / c) ^ 2 * (2 * (r : ℝ) ^ 2) by positivity))
  simp only [envelope, sum_add_distrib, ← mul_sum]
  convert htotal using 1 <;> simp only [driftConstant, neg_mul] <;> ring

theorem physical_path_bound {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]
    (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ w, 0 ≤ μ w) (J : Finset E) (S : Finset B)
    (r T n : ℕ) (M β b c C A a z : ℝ) (hr : 2 ≤ r) (hn : 1 ≤ n)
    (hc : 0 < c) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hMₗ : c * (n : ℝ) ^ 2 ≤ M) (hMᵤ : M ≤ C * (n : ℝ) ^ 2)
    (ha : 0 ≤ a) (hz : 0 ≤ z) (hs : a * (4 * (r : ℝ) - 1) = 1 - 2 * z)
    (horizon : T ≤ GreedyScales.horizon M n a)
    (hsize : ∀ w, (I w).card = r) (hJ : (J.card : ℝ) = (r : ℝ) * M)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (hβ : 0 ≤ β) (hb : 0 ≤ b) (hβrate : β ≤ b / n)
    (hcodeg : ∀ e f, e ≠ f → CodegreeLoss.codegree I μ e f ≤ β)
    (guard : List (Option B) → Prop)
    (hguard : ∀ h, guard h → StoppedPhysical.regular I μ J r M n β h ∧
      WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
        (StoppedPhysical.profile (2 * r) M) h ≤ A * n ∧
      2 * (r : ℝ) ≤ WeightedGreedy.totalWeight I μ J h)
    (h : List (Option B)) (hlen : h.length ≤ T) :
    let K := WeightedGreedy.kernel I μ hμ J guard
    |pathSum (fun g _ => ∑ x, K.transition g x * TypeMartingale.increment I μ J S guard g x) h| ≤
      driftConstant r c C A b * (n : ℝ) ^ (-z) := by
  classical
  let K := WeightedGreedy.kernel I μ hμ J guard
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : 0 < M := (mul_pos hc (by positivity)).trans_le hMₗ
  have hTM : (T : ℝ) < M := (Nat.cast_le.mpr horizon).trans_lt
    (GreedyScales.horizon_bounds M n a hM hn ha).1
  refine (pathSum_abs_le (fun g _ => ∑ x, K.transition g x * TypeMartingale.increment I μ J S guard g x)
    (envelope r M n c C A b) T ?_ h hlen).trans
      (sum_envelope n h.length r M c C A b a z hn hr hc hC hA hb hM hMᵤ ha hz hs (hlen.trans horizon))
  intro g x ht
  by_cases hl : WeightedGreedy.live I μ J guard g
  · obtain ⟨hreg, hY, hZ⟩ := hguard g hl.2.1
    have hactive := TypeDriftEnvelope.active_bound I μ hμ J S guard r T M n β b c C A
      (by omega) hn' hc hC hA hMₗ hMᵤ hTM hsize hJ hload hβ hb hβrate hcodeg g hl ht.le hreg hY hZ
    have hcount := TypeDriftEnvelope.count_eq_length g hl.1
    simpa only [envelope, hcount] using hactive
  · have hp : 0 ≤ (M - (g.length : ℝ)) / M :=
      div_nonneg (sub_nonneg.mpr ((Nat.cast_le.mpr ht.le).trans hTM.le)) hM.le
    simp only [TypeMartingale.increment, ite_eq_right hl, mul_zero, sum_const_zero, abs_zero, envelope]
    positivity

end KqR75.CumulativeTypeDrift

#print axioms KqR75.CumulativeTypeDrift.pathSum_abs_le
#print axioms KqR75.CumulativeTypeDrift.sum_envelope
#print axioms KqR75.CumulativeTypeDrift.physical_path_bound
