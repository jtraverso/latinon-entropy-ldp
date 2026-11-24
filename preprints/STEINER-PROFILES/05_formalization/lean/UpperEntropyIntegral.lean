module
public import UpperLogCutoff
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open MeasureTheory Set intervalIntegral
open scoped Interval

/-- The integral from the weighted reveal argument, including its
leading negative term. -/
theorem weighted_entropy_integral (r : ℕ) (hr : 0 < r) (h s : ℝ)
    (hh : 0 < h) (hh₁ : h ≤ 1) (hs : 1 < s) :
    (∫ x in (0 : ℝ)..1, x ^ (r - 1) * Real.log ((x ^ r) ^ s + h ^ s)) ≤
      (-s + h * (Real.log 2 + s + 1 / (s - 1))) / (r : ℝ) := by
  let g (x : ℝ) := Real.log (|x| ^ s + h ^ s)
  have hgc : Continuous g := by
    dsimp only [g]
    have hpow : Continuous (fun x : ℝ => |x| ^ s) :=
      continuous_abs.rpow_const (fun _ => Or.inr (by linarith))
    exact (hpow.add continuous_const).log (fun x => ne_of_gt
      (add_pos_of_nonneg_of_pos (Real.rpow_nonneg (abs_nonneg x) s) (Real.rpow_pos_of_pos hh s)))
  have hpoint (x : ℝ) (hx : 0 < x) :
      g x = s * Real.log x + Real.log (1 + h ^ s * x ^ (-s)) := by
    have hxp : 0 < x ^ s := Real.rpow_pos_of_pos hx _
    have he : x ^ s * (1 + h ^ s * x ^ (-s)) = x ^ s + h ^ s := by
      rw [Real.rpow_neg hx.le]
      field_simp
    change Real.log (|x| ^ s + h ^ s) = _
    rw [abs_of_pos hx, ← he, Real.log_mul hxp.ne' (by positivity), Real.log_rpow hx]
  have hlog : IntervalIntegrable (fun x : ℝ => s * Real.log x) volume 0 1 :=
    intervalIntegrable_log'.const_mul _
  have hdiff : IntervalIntegrable (fun x : ℝ => Real.log (1 + h ^ s * x ^ (-s))) volume 0 1 := by
    apply ((hgc.intervalIntegrable 0 1).sub hlog).congr_ae
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    filter_upwards [ae_restrict_mem (μ := volume)
      (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1))] with x hx
    have hh := hpoint x hx.1
    linarith only [hh]
  have hsum : (∫ x in (0 : ℝ)..1, g x) =
      ∫ x in (0 : ℝ)..1, s * Real.log x + Real.log (1 + h ^ s * x ^ (-s)) := by
    rw [integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume)
      (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) 1))] with x hx
    exact hpoint x hx.1
  rw [integral_add hlog hdiff, intervalIntegral.integral_const_mul, integral_log_from_zero] at hsum
  simp only [Real.log_one, mul_zero, zero_sub, mul_neg, mul_one] at hsum
  have hb := cutoff_log_error h s hh hh₁ hs
  have hmain : (∫ x in (0 : ℝ)..1, g x) ≤ -s + h * (Real.log 2 + s + 1 / (s - 1)) := by
    linarith only [hsum, hb]
  have hsub := integral_comp_mul_deriv (a := (0 : ℝ)) (b := 1)
    (fun x _ => hasDerivAt_pow r x)
    ((continuous_const.mul (continuous_id.pow (r - 1))).continuousOn) hgc
  simp only [zero_pow hr.ne', one_pow] at hsub
  have hr₀ : 0 < (r : ℝ) := by exact_mod_cast hr
  apply (le_div_iff₀ hr₀).mpr
  rw [mul_comm, ← intervalIntegral.integral_const_mul]
  calc
    _ = ∫ x in (0 : ℝ)..1, (g ∘ fun x : ℝ => x ^ r) x * ((r : ℝ) * x ^ (r - 1)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      simp only [Function.comp_apply, g, abs_of_nonneg (pow_nonneg hx.1 _)]
      ring
    _ = _ := hsub
    _ ≤ _ := hmain

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.weighted_entropy_integral
