module
public import SlotPairMargins
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section
noncomputable section
namespace KqR75.SlotPairMargins

open Finset ColouredCliques SlotProfiles

variable {C K : Type*} [Fintype C] [DecidableEq C]
  [Field K] [Fintype K] [DecidableEq K]

/-- Round a real quota vector in an affine fibre containing an integer
point. The coordinate error is bounded independently of the quotas. -/
theorem round_quotas {q : ℕ} (hq : 2 ≤ q)
    (s : Fin q → K) (hs : Function.Injective s) (ref : C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (m₀ : TypeProfile C q → ℤ) (x : TypeProfile C q → ℝ),
      (∀ i j, ∑ v, (x v - (m₀ v : ℝ)) * (orderedCount v i j : ℝ) = 0) →
      ∃ m : TypeProfile C q → ℤ,
        (∀ i j, ∑ v, (m v - m₀ v) * (orderedCount v i j : ℤ) = 0) ∧
        ∀ v, |(m v : ℝ) - x v| ≤ B := by
  classical
  obtain ⟨tag, r, _, hspan⟩ := affine_spans_kernel (R := ℝ) hq s hs ref
  let g (k : High C q ref) (v : TypeProfile C q) := cellDifference s ref (tag k) (r k) v
  let B : ℝ := ∑ k, ∑ v, |(g k v : ℝ)|
  refine ⟨B, sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => abs_nonneg _)), ?_⟩
  intro m₀ x hx
  obtain ⟨a, ha⟩ := hspan (fun v => x v - (m₀ v : ℝ)) hx
  let m (v : TypeProfile C q) : ℤ := m₀ v + ∑ k, ⌊a k⌋ * g k v
  refine ⟨m, ?_, ?_⟩
  · intro i j
    simp only [m, add_sub_cancel_left, sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum,
      show ∀ k : High C q ref, ∑ v, g k v * (orderedCount v i j : ℤ) = 0 from
        fun k => by exact_mod_cast cellDifference_margin_zero (R := ℤ) s hs ref (tag k) (r k) i j,
      mul_zero, sum_const_zero]
  · intro v
    have he : (m v : ℝ) - x v = ∑ k, ((⌊a k⌋ : ℝ) - a k) * (g k v : ℝ) := by
      simp only [m, Int.cast_add, Int.cast_sum, Int.cast_mul, sub_mul, sum_sub_distrib]
      have hv := ha v
      change x v - (m₀ v : ℝ) = ∑ k, a k * (g k v : ℝ) at hv
      rw [← hv]
      ring
    rw [he]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr (Int.floor_le (a k)))]
    have hround : -((⌊a k⌋ : ℝ) - a k) ≤ 1 := by linarith [Int.lt_floor_add_one (a k)]
    calc
      _ ≤ 1 * |(g k v : ℝ)| := mul_le_mul_of_nonneg_right hround (abs_nonneg _)
      _ = _ := one_mul _
      _ ≤ ∑ u, |(g k u : ℝ)| :=
        single_le_sum (f := fun u : TypeProfile C q => |(g k u : ℝ)|)
          (fun _ _ => abs_nonneg _) (mem_univ v)

end KqR75.SlotPairMargins

#print axioms KqR75.SlotPairMargins.round_quotas
