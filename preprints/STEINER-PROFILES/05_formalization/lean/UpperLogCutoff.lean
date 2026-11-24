module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open MeasureTheory Set intervalIntegral
open scoped Interval

private theorem log_near_zero {h s x : ℝ} (hx : 0 < x) (hxh : x ≤ h) (hs : 0 ≤ s) :
    Real.log (1 + h ^ s * x ^ (-s)) ≤ Real.log 2 + s * (Real.log h - Real.log x) := by
  have hh := hx.trans_le hxh
  have hy : 1 ≤ (h / x) ^ s :=
    Real.one_le_rpow ((one_le_div hx).mpr hxh) hs
  have he : h ^ s * x ^ (-s) = (h / x) ^ s := by
    rw [Real.div_rpow hh.le hx.le, Real.rpow_neg hx.le, div_eq_mul_inv]
  rw [he]
  calc
    _ ≤ Real.log (2 * (h / x) ^ s) := Real.log_le_log (by positivity) (by linarith)
    _ = _ := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity),
        Real.log_rpow (div_pos hh hx), Real.log_div hh.ne' hx.ne']

/-- The logarithmic error after substituting u = t^r in the weighted
entropy estimate. The cutoff h is the (r-1)-st root of the exceptional
mass and the bound keeps its full power. -/
theorem cutoff_log_error (h s : ℝ) (hh : 0 < h) (hh₁ : h ≤ 1) (hs : 1 < s) :
    (∫ x in (0 : ℝ)..1, Real.log (1 + h ^ s * x ^ (-s))) ≤
      h * (Real.log 2 + s + 1 / (s - 1)) := by
  let f (x : ℝ) := Real.log (1 + h ^ s * x ^ (-s))
  let lo (x : ℝ) := Real.log 2 + s * (Real.log h - Real.log x)
  let hi (x : ℝ) := h ^ s * x ^ (-s)
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hf₀ {x : ℝ} (hx : 0 ≤ x) : 0 ≤ f x :=
    Real.log_nonneg (le_add_of_nonneg_right (mul_nonneg (Real.rpow_nonneg hh.le _) (Real.rpow_nonneg hx _)))
  have hl : IntervalIntegrable lo volume 0 h :=
    intervalIntegrable_const.add ((intervalIntegrable_const.sub intervalIntegrable_log').const_mul s)
  have hz : (0 : ℝ) ∉ [[h, (1 : ℝ)]] := by rw [uIcc_of_le hh₁]; exact fun hx => hh.not_ge hx.1
  have hp : IntervalIntegrable (fun x : ℝ => x ^ (-s)) volume h 1 :=
    intervalIntegrable_rpow (Or.inr hz)
  have hu : IntervalIntegrable hi volume h 1 := hp.const_mul _
  have hlo (x : ℝ) (hx : x ∈ Ioc 0 h) : f x ≤ lo x :=
    log_near_zero hx.1 hx.2 (by linarith)
  have hhi (x : ℝ) (hx : x ∈ Ioc h 1) : f x ≤ hi x := by
    have hx₀ : 0 ≤ x := hh.le.trans hx.1.le
    have hp : 0 < 1 + hi x := by
      dsimp [hi]
      positivity
    have hl := Real.log_le_sub_one_of_pos hp
    change f x ≤ _
    simpa only [f, hi, add_sub_cancel_left] using hl
  have hflo : IntervalIntegrable f volume 0 h := by
    apply hl.mono_fun' hf.aestronglyMeasurable
    rw [uIoc_of_le hh.le]
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc (0 : ℝ) h))]
      with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hf₀ hx.1.le)]
    exact hlo x hx
  have hfhi : IntervalIntegrable f volume h 1 := by
    apply hu.mono_fun' hf.aestronglyMeasurable
    rw [uIoc_of_le hh₁]
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc : MeasurableSet (Ioc h (1 : ℝ)))]
      with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hf₀ (hh.le.trans hx.1.le))]
    exact hhi x hx
  have hloInt : (∫ x in 0..h, lo x) = h * (Real.log 2 + s) := by
    dsimp [lo]
    rw [integral_add intervalIntegrable_const
      ((intervalIntegrable_const.sub intervalIntegrable_log').const_mul s),
      intervalIntegral.integral_const_mul, integral_sub intervalIntegrable_const intervalIntegrable_log',
      integral_log_from_zero, intervalIntegral.integral_const, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hhiInt : (∫ x in h..1, hi x) ≤ h / (s - 1) := by
    dsimp [hi]
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, hz⟩),
      show -s + 1 = 1 - s by ring, Real.one_rpow]
    have hpower : h ^ s * h ^ (1 - s) = h := by
      rw [← Real.rpow_add hh, show s + (1 - s) = 1 by ring, Real.rpow_one]
    have hs₀ : 0 < s - 1 := sub_pos.mpr hs
    calc
      _ = (h - h ^ s) / (s - 1) := by
        rw [← mul_div_assoc, mul_sub, mul_one, hpower]
        have hneg : 1 - s = -(s - 1) := by ring
        rw [hneg, div_neg, ← neg_div, neg_sub]
      _ ≤ _ := div_le_div_of_nonneg_right (sub_le_self _ (Real.rpow_nonneg hh.le _)) hs₀.le
  have hlow := integral_mono_on_of_le_Ioo hh.le hflo hl
    (fun x hx => hlo x ⟨hx.1, hx.2.le⟩)
  have hhigh := integral_mono_on_of_le_Ioo hh₁ hfhi hu
    (fun x hx => hhi x ⟨hx.1, hx.2.le⟩)
  change (∫ x in (0 : ℝ)..1, f x) ≤ _
  rw [← integral_add_adjacent_intervals hflo hfhi]
  rw [hloInt] at hlow
  calc
    _ ≤ h * (Real.log 2 + s) + h / (s - 1) := add_le_add hlow (hhigh.trans hhiInt)
    _ = _ := by ring

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.cutoff_log_error
