module
public import PrefixMassScales

@[expose] public section
noncomputable section
namespace KqR75.GreedySchedule

open Finset

private theorem log_step (x : ℝ) (hx : 0 < x) :
    Real.log x ≤ (x + 1) * Real.log (x + 1) - x * Real.log x - 1 ∧
    (x + 1) * Real.log (x + 1) - x * Real.log x - 1 ≤ Real.log (x + 1) := by
  have hy : 0 < x + 1 := by linarith
  have h₁ := Real.log_le_sub_one_of_pos (div_pos hx hy)
  have h₂ := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hx.ne' hy.ne', show x / (x + 1) - 1 = -1 / (x + 1) by
    field_simp; ring] at h₁
  rw [Real.log_div hy.ne' hx.ne', show (x + 1) / x - 1 = 1 / x by
    field_simp; ring] at h₂
  have hl := (le_div_iff₀ hy).mp h₁
  have hu := (le_div_iff₀ hx).mp h₂
  constructor <;> nlinarith only [hl, hu]

/-- The left-endpoint logarithms telescope against the primitive of log.
This bound applies to the fractional initial block mass of the host. -/
theorem sum_log_remaining_lower (M : ℝ) (T : ℕ) (hM : 0 < M) (hT : (T : ℝ) < M) :
    -(T : ℝ) - (M - (T : ℝ)) * Real.log ((M - (T : ℝ)) / M) ≤
      ∑ i ∈ range T, Real.log ((M - (i : ℝ)) / M) := by
  induction T with
  | zero => simp [div_self hM.ne']
  | succ T ih =>
    have hT' : (T : ℝ) < M := by rw [Nat.cast_succ] at hT; linarith
    have hx : 0 < M - (↑(T + 1) : ℝ) := sub_pos.mpr hT
    have hy : 0 < M - (T : ℝ) := sub_pos.mpr hT'
    have he : M - (↑(T + 1) : ℝ) + 1 = M - (T : ℝ) := by push_cast; ring
    have hb := (log_step _ hx).2
    rw [he] at hb
    have ht := ih hT'
    rw [sum_range_succ]
    rw [Real.log_div hx.ne' hM.ne']
    rw [Real.log_div hy.ne' hM.ne'] at ht
    rw [Real.log_div hy.ne' hM.ne']
    push_cast at hb ht ⊢
    nlinarith only [hb, ht]

/-- The weaker form sufficient for the probability cap. -/
theorem sum_log_remaining_ge_neg_mass (M : ℝ) (T : ℕ) (hM : 0 < M) (hT : (T : ℝ) < M) :
    -M ≤ ∑ i ∈ range T, Real.log ((M - (i : ℝ)) / M) := by
  have hx := sub_pos.mpr hT
  have hr : Real.log ((M - (T : ℝ)) / M) ≤ 0 :=
    Real.log_nonpos (by positivity) ((div_le_one hM).mpr (by linarith [Nat.cast_nonneg (α := ℝ) T]))
  exact le_trans (by nlinarith only [hT, mul_nonpos_of_nonneg_of_nonpos hx.le hr])
    (sum_log_remaining_lower M T hM hT)

/-- A one-sided factorial estimate with a logarithmic remainder, with
the direction used when dividing by the number of prefix orderings. -/
theorem log_factorial_upper (T : ℕ) (hT : 1 ≤ T) :
    Real.log (T.factorial : ℝ) ≤ (T : ℝ) * Real.log T - T + 1 + Real.log T := by
  induction T with
  | zero => omega
  | succ T ih =>
    by_cases hz : T = 0
    · subst T
      simp
    · have hpos : 0 < (T : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hz)
      have hb := (log_step T hpos).1
      have ht := ih (Nat.pos_of_ne_zero hz)
      rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity), Nat.cast_succ]
      linarith only [ht, hb]

/-- Evaluate the determinant-free part of the prefix probability cap
after paying the T! multiplicity. -/
theorem normalizer_minus_factorial_lower (M : ℝ) (r T : ℕ)
    (hT₁ : 1 ≤ T) (hT : (T : ℝ) < M) :
    -(r : ℝ) * M + T - 1 - Real.log T ≤
      (T : ℝ) * Real.log M +
        (r : ℝ) * (∑ i ∈ range T, Real.log ((M - (i : ℝ)) / M)) -
        Real.log (T.factorial : ℝ) := by
  have hT₀ : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hlog := Real.log_le_log hT₀ hT.le
  have hm := sum_log_remaining_ge_neg_mass M T (hT₀.trans hT) hT
  have hf := log_factorial_upper T hT₁
  linarith only [mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg r),
    mul_le_mul_of_nonneg_left hlog hT₀.le, hf]

end KqR75.GreedySchedule

#print axioms KqR75.GreedySchedule.normalizer_minus_factorial_lower
