module
public import KqCore

@[expose] public section
namespace KqR75.Energy

/-- The integrating factor for a raw drift coefficient equal to the exponent. -/
theorem factor_le_one (a : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) ^ a * (1 + (a : ℝ) * t) ≤ 1 := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hx : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hb : 0 ≤ 1 + (a : ℝ) * t := by positivity
    have hc : 1 + ((a + 1 : ℕ) : ℝ) * t ≤ (1 + (a : ℝ) * t) * (1 + t) := by
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a) (sq_nonneg t)]
    calc
      (1 - t) ^ (a + 1) * (1 + ((a + 1 : ℕ) : ℝ) * t)
          ≤ (1 - t) ^ (a + 1) * ((1 + (a : ℝ) * t) * (1 + t)) :=
        mul_le_mul_of_nonneg_left hc (pow_nonneg hx _)
      _ = ((1 - t) ^ a * (1 + (a : ℝ) * t)) * ((1 - t) * (1 + t)) := by
        rw [pow_succ]; ring
      _ ≤ 1 * ((1 - t) * (1 + t)) :=
        mul_le_mul_of_nonneg_right ih (mul_nonneg hx (by linarith))
      _ ≤ 1 := by nlinarith [sq_nonneg t]

/-- Multiplying a one-step energy bound by the next integrating factor.
This is a deterministic inequality; no martingale estimate is assumed here. -/
theorem weighted_step (a : ℕ) (m X X' b w : ℝ) (hm : 1 ≤ m)
    (hX : 0 ≤ X) (hw : 0 ≤ w)
    (hstep : X' ≤ (1 + (a : ℝ) / m) * X + b) :
    w * (1 - 1 / m) ^ a * X' ≤ w * X + w * (1 - 1 / m) ^ a * b := by
  have hm0 : 0 < m := by linarith
  have ht0 : 0 ≤ 1 / m := (one_div_pos.mpr hm0).le
  have ht1 : 1 / m ≤ 1 := (div_le_one hm0).mpr hm
  have hp : 0 ≤ (1 - 1 / m) ^ a := pow_nonneg (sub_nonneg.mpr ht1) _
  have hf := factor_le_one a (1 / m) ht0 ht1
  have hf' : (1 - 1 / m) ^ a * (1 + (a : ℝ) / m) ≤ 1 := by
    simpa only [div_eq_mul_inv, one_mul] using hf
  calc
    w * (1 - 1 / m) ^ a * X' ≤
        w * (1 - 1 / m) ^ a * ((1 + (a : ℝ) / m) * X + b) :=
      mul_le_mul_of_nonneg_left hstep (mul_nonneg hw hp)
    _ = w * ((1 - 1 / m) ^ a * (1 + (a : ℝ) / m)) * X +
        w * (1 - 1 / m) ^ a * b := by ring
    _ ≤ w * X + w * (1 - 1 / m) ^ a * b := by
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf' hw) hX
      simp only [mul_one] at hh
      linarith only [hh]

end KqR75.Energy

#print axioms KqR75.Energy.factor_le_one
#print axioms KqR75.Energy.weighted_step
