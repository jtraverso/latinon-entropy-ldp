module
public import EnergyFactor

@[expose] public section
noncomputable section
namespace KqR75.GreedyProfile

theorem bernoulli_lower (a : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    1 - (a : ℝ) * t ≤ (1 - t) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    have hx : 0 ≤ 1 - t := sub_nonneg.mpr ht1
    have hh := mul_le_mul_of_nonneg_right ih hx
    rw [pow_succ]
    push_cast
    nlinarith only [hh, mul_nonneg (Nat.cast_nonneg a : (0 : ℝ) ≤ a) (sq_nonneg t)]

theorem power_le_one (a : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) ^ a ≤ 1 := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr ht1)).trans
      (by simpa only [one_mul] using sub_le_self (1 : ℝ) ht)

/-- An algebraic second-order remainder; no differentiability or Taylor
expansion theorem is needed for the greedy schedule. -/
theorem remainder_bound (a : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    0 ≤ (a : ℝ) * t - (1 - (1 - t) ^ a) ∧
      (a : ℝ) * t - (1 - (1 - t) ^ a) ≤ ((a : ℝ) * t) ^ 2 := by
  have hl := bernoulli_lower a t ht ht1
  have hf := Energy.factor_le_one a t ht ht1
  let u := (a : ℝ) * t
  let v := (1 - t) ^ a
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpow : 0 ≤ u ^ 3 := pow_nonneg hu _
  have he : (1 + u) * (v - 1 + u - u ^ 2) = v * (1 + u) - 1 - u ^ 3 := by ring
  have hh : (1 + u) * (v - 1 + u - u ^ 2) ≤ 0 := by
    rw [he]
    change v * (1 + u) ≤ 1 at hf
    linarith only [hf, hpow]
  have hrem : v - 1 + u - u ^ 2 ≤ 0 := by
    by_contra hn
    have hp := mul_pos (show 0 < 1 + u by linarith) (lt_of_not_ge hn)
    linarith only [hh, hp]
  constructor
  · linarith only [hl]
  · change u - (1 - v) ≤ u ^ 2
    linarith only [hrem]

theorem schedule_bounds (a : ℕ) (m k : ℝ) (hm : 1 ≤ m) (hk : 0 ≤ k) :
    let η := k * (1 - (1 - 1 / m) ^ a)
    0 ≤ η ∧ η ≤ (a : ℝ) * k / m ∧
      0 ≤ (a : ℝ) * k / m - η ∧
      (a : ℝ) * k / m - η ≤ (a : ℝ) ^ 2 * k / m ^ 2 := by
  have hm0 : 0 < m := by linarith
  have ht : 0 ≤ 1 / m := by positivity
  have ht1 : 1 / m ≤ 1 := (div_le_one hm0).mpr hm
  have hp := power_le_one a (1 / m) ht ht1
  obtain ⟨hl, hu⟩ := remainder_bound a (1 / m) ht ht1
  dsimp only
  have hscaled : 0 ≤ (a : ℝ) * k / m - k * (1 - (1 - 1 / m) ^ a) := by
    calc
      _ ≤ k * ((a : ℝ) * (1 / m) - (1 - (1 - 1 / m) ^ a)) := mul_nonneg hk hl
      _ = _ := by ring
  refine ⟨mul_nonneg hk (sub_nonneg.mpr hp), ?_, ?_, ?_⟩
  · linarith only [hscaled]
  · exact hscaled
  · have hh := mul_le_mul_of_nonneg_left hu hk
    convert hh using 1 <;> field_simp [hm0.ne'] <;> ring

end KqR75.GreedyProfile

#print axioms KqR75.GreedyProfile.remainder_bound
#print axioms KqR75.GreedyProfile.schedule_bounds
