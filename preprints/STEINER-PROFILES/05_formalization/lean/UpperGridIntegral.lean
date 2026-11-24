module
public import UpperGridBound
public import UpperEntropyIntegral

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset MeasureTheory Set
open scoped Interval

private theorem power_difference_le (k : ℕ) {x y : ℝ}
    (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x ≤ 1) :
    x ^ k - y ^ k ≤ (k : ℝ) * (x - y) := by
  have hx₀ := hy.trans hyx
  have h := abs_pow_sub_pow_le (a := x) (b := y) (n := k)
  rw [abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hy hyx _)),
    abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg hx₀, abs_of_nonneg hy, max_eq_left hyx] at h
  exact h.trans (by simpa only [mul_one, mul_comm (x - y)] using
    mul_le_mul_of_nonneg_left (pow_le_one₀ hx₀ hx (n := k - 1)) (by positivity : 0 ≤ (x - y) * k))

private theorem log_power_difference_le (k : ℕ) {x y δ : ℝ}
    (hδ : 0 < δ) (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x ≤ 1) :
    Real.log (δ + x ^ k) - Real.log (δ + y ^ k) ≤ ((k : ℝ) / δ) * (x - y) := by
  have h₁ : 0 < δ + x ^ k := add_pos_of_pos_of_nonneg hδ (pow_nonneg (hy.trans hyx) _)
  have h₂ : 0 < δ + y ^ k := add_pos_of_pos_of_nonneg hδ (pow_nonneg hy _)
  have h := Real.log_le_sub_one_of_pos (div_pos h₁ h₂)
  rw [Real.log_div h₁.ne' h₂.ne'] at h
  refine h.trans ?_
  rw [show (δ + x ^ k) / (δ + y ^ k) - 1 = (x ^ k - y ^ k) / (δ + y ^ k) by
    field_simp; ring]
  calc
    _ ≤ ((k : ℝ) * (x - y)) / (δ + y ^ k) :=
      div_le_div_of_nonneg_right (power_difference_le k hy hyx hx) h₂.le
    _ ≤ ((k : ℝ) * (x - y)) / δ := by
      apply div_le_div_of_nonneg_left (by positivity) hδ
      exact le_add_of_nonneg_right (pow_nonneg hy _)
    _ = _ := by ring

private theorem grid_cell_le (a k : ℕ) {δ x y t : ℝ}
    (hδ : 0 < δ) (hy : 0 ≤ y) (hyt : y ≤ t) (htx : t ≤ x) (hx : x ≤ 1) :
    y ^ a * Real.log (δ + x ^ k) ≤ t ^ a * Real.log (δ + t ^ k) +
      ((a : ℝ) * |Real.log δ| + (k : ℝ) / δ) * (x - y) := by
  have ht := hy.trans hyt
  have hp := sub_nonneg.mpr (pow_le_pow_left₀ hy hyt a)
  have hlog : -|Real.log δ| ≤ Real.log (δ + t ^ k) :=
    (neg_abs_le _).trans (Real.log_le_log hδ (le_add_of_nonneg_right (pow_nonneg ht _)))
  have hdiff₁ := mul_le_mul_of_nonneg_left (log_power_difference_le k hδ ht htx hx)
    (pow_nonneg hy a)
  have hdiff₂ : y ^ a * (((k : ℝ) / δ) * (x - t)) ≤ ((k : ℝ) / δ) * (x - t) :=
    mul_le_of_le_one_left (by positivity) (pow_le_one₀ hy (hyt.trans (htx.trans hx)) (n := a))
  have hdiff₃ := mul_le_mul_of_nonneg_left (show x - t ≤ x - y by linarith)
    (div_nonneg (Nat.cast_nonneg k) hδ.le)
  have hp₁ := mul_le_mul_of_nonneg_left hlog hp
  have hp₂ := mul_le_mul_of_nonneg_right (power_difference_le a hy hyt (htx.trans hx))
    (abs_nonneg (Real.log δ))
  have hp₃ := mul_le_mul_of_nonneg_left (show t - y ≤ x - y by linarith)
    (mul_nonneg (Nat.cast_nonneg a) (abs_nonneg (Real.log δ)))
  nlinarith only [hdiff₁, hdiff₂, hdiff₃, hp₁, hp₂, hp₃]

/-- A quantitative one-sided Riemann bound for mixed endpoints. It
allows the finite priorities to be taken arbitrarily fine at each
fixed host size. -/
theorem gridLog_le_integral (L a k : ℕ) (hL : 0 < L) (δ : ℝ) (hδ : 0 < δ) :
    gridLog L a k δ ≤
      (∫ x in (0 : ℝ)..1, x ^ a * Real.log (δ + x ^ k)) +
        ((a : ℝ) * |Real.log δ| + (k : ℝ) / δ) / L := by
  let p (i : ℕ) : ℝ := (i : ℝ) / L
  let f (t : ℝ) := t ^ a * Real.log (δ + t ^ k)
  let C : ℝ := (a : ℝ) * |Real.log δ| + (k : ℝ) / δ
  let v (i : ℕ) := p i ^ a * Real.log (δ + p (i + 1) ^ k)
  have hL' : 0 < (L : ℝ) := by exact_mod_cast hL
  have hint {i : ℕ} (hi : i < L) : IntervalIntegrable f volume (p i) (p (i + 1)) := by
    have hle : p i ≤ p (i + 1) := div_le_div_of_nonneg_right (by push_cast; linarith) hL'.le
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hle]
    refine (continuous_id.pow a).continuousOn.mul ?_
    apply (continuousOn_const.add (continuous_id.pow k).continuousOn).log
    intro t ht
    exact ne_of_gt (add_pos_of_pos_of_nonneg hδ (pow_nonneg ((by dsimp [p]; positivity : 0 ≤ p i).trans ht.1) _))
  have hcell (i : ℕ) (hi : i < L) :
      v i / L ≤ (∫ x in (p i)..(p (i + 1)), f x) + (1 / (L : ℝ)) * (C / L) := by
    have hle : p i ≤ p (i + 1) := div_le_div_of_nonneg_right (by push_cast; linarith) hL'.le
    have hy : 0 ≤ p i := by dsimp [p]; positivity
    have hx : p (i + 1) ≤ 1 := (div_le_one hL').mpr (by exact_mod_cast Nat.succ_le_of_lt hi)
    have hw : p (i + 1) - p i = 1 / (L : ℝ) := by dsimp [p]; push_cast; ring
    have hh := intervalIntegral.integral_mono_on hle
      (intervalIntegrable_const (c := v i)) ((hint hi).add (intervalIntegrable_const (c := C / L)))
      (fun t ht => by
        have hb := grid_cell_le a k hδ hy ht.1 ht.2 hx
        change v i ≤ f t + C * (p (i + 1) - p i) at hb
        rw [hw] at hb
        calc
          _ ≤ f t + C * (1 / (L : ℝ)) := hb
          _ = _ := by ring)
    rw [intervalIntegral.integral_add (hint hi) intervalIntegrable_const,
      intervalIntegral.integral_const, intervalIntegral.integral_const, hw, smul_eq_mul, smul_eq_mul] at hh
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm (v i)] using hh
  have hs := sum_le_sum (fun i hi => hcell i (mem_range.mp hi))
  rw [← sum_div, sum_add_distrib, intervalIntegral.sum_integral_adjacent_intervals (a := p) (n := L) (f := f) (fun i hi => hint hi),
    sum_const, card_range, nsmul_eq_mul] at hs
  have hp₀ : p 0 = 0 := by simp [p]
  have hpL : p L = 1 := div_self hL'.ne'
  rw [hp₀, hpL, show (L : ℝ) * (1 / (L : ℝ) * (C / L)) = C / L by field_simp] at hs
  unfold gridLog
  rw [show (∑ z : Fin L, ((z.val : ℝ) / L) ^ a *
    Real.log (δ + (((z.val : ℝ) + 1) / L) ^ k)) = ∑ i ∈ range L, v i by
      rw [← Fin.sum_univ_eq_sum_range v]
      simp only [v, p, Nat.cast_add, Nat.cast_one] ]
  exact hs

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.gridLog_le_integral
