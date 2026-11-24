module
public import PrefixMass

@[expose] public section
noncomputable section
namespace KqR75.GreedySchedule

open WeightedGreedy

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- On the R75 horizon a linear bound on the stopped energy gives a
relative normalizer error of order n^(-z), uniformly over the host. -/
theorem relative_mass_at_horizon (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) (hsize : ∀ b, (I b).card = r)
    (M c A a z : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hscale : a * (4 * (r : ℝ) - 1) = 1 - 2 * z)
    (hM : c * (n : ℝ) ^ 2 ≤ M) (hJ : (J.card : ℝ) = (r : ℝ) * M)
    (h : List (Option B)) (hv : valid I J h)
    (hi : selectedCount h ≤ GreedyScales.horizon M n a) :
    let p := (M - (selectedCount h : ℝ)) / M
    stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
      (StoppedPhysical.profile (2 * r) M) h ≤ A * n →
    |totalWeight I μ J h - M * p ^ r| ≤
      (Real.sqrt (A / ((r : ℝ) * c)) * (n : ℝ) ^ (-z)) * (M * p ^ r) := by
  let i := selectedCount h
  let p := (M - (i : ℝ)) / M
  let ε := Real.sqrt (A / ((r : ℝ) * c)) * (n : ℝ) ^ (-z)
  dsimp only
  intro hY
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hM₀ : 0 < M := (mul_pos hc (by positivity)).trans_le hM
  have hr₀ : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  obtain ⟨hhi, _, hhp⟩ := GreedyScales.horizon_bounds M n a hM₀ hn ha
  have hiM : (i : ℝ) < M := (Nat.cast_le.mpr hi).trans_lt hhi
  have hp : (n : ℝ) ^ (-a) ≤ p := hhp i hi
  have hpPow : (n : ℝ) ^ (-a * (4 * r - 1 : ℕ)) ≤ p ^ (4 * r - 1) := by
    rw [Real.rpow_mul hn₀.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hp _
  have heq : -(a * (4 * r - 1 : ℕ)) + 2 = 1 + 2 * z := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_one]
    norm_num
    linarith only [hscale]
  apply relative_mass_error I μ J r hr hsize M hM₀ hJ h hv hiM ε (by dsimp [ε]; positivity)
  refine hY.trans ?_
  calc
    A * (n : ℝ) = ε ^ 2 * ((r : ℝ) * (c * (n : ℝ) ^ 2) *
        (n : ℝ) ^ (-a * (4 * r - 1 : ℕ))) := by
      have hrpow : ((n : ℝ) ^ (-z)) ^ 2 *
          ((n : ℝ) ^ 2 * (n : ℝ) ^ (-a * (4 * r - 1 : ℕ))) = n := by
        have hf₁ : ((n : ℝ) ^ (-z)) ^ 2 = (n : ℝ) ^ (-z * 2) := by
          rw [Real.rpow_mul hn₀.le]
          exact (Real.rpow_natCast _ 2).symm
        have hf₂ : (n : ℝ) ^ 2 * (n : ℝ) ^ (-a * (4 * r - 1 : ℕ)) =
            (n : ℝ) ^ (1 + 2 * z) := by
          rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hn₀, Nat.cast_ofNat]
          congr 1
          rw [← heq]
          ring
        rw [hf₁, hf₂, ← Real.rpow_add hn₀, show -z * 2 + (1 + 2 * z) = 1 by ring,
          Real.rpow_one]
      dsimp [ε]
      rw [mul_pow, Real.sq_sqrt (div_nonneg hA (by positivity))]
      symm
      calc
        _ = (A / ((r : ℝ) * c) * ((r : ℝ) * c)) *
            (((n : ℝ) ^ (-z)) ^ 2 *
              ((n : ℝ) ^ 2 * (n : ℝ) ^ (-a * (4 * r - 1 : ℕ)))) := by ring
        _ = _ := by rw [hrpow, div_mul_cancel₀ _ (mul_pos hr₀ hc).ne']
    _ ≤ _ := by
      gcongr

theorem log_difference_of_relative_error {x y ε : ℝ}
    (hx : 0 < x) (hε : 0 ≤ ε) (hhalf : ε ≤ 1 / 2) (h : |y - x| ≤ ε * x) :
    |Real.log y - Real.log x| ≤ 2 * ε := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  have hyHalf : x / 2 ≤ y := by
    nlinarith only [hl, mul_le_mul_of_nonneg_right hhalf hx.le]
  have hy : 0 < y := by linarith only [hyHalf, hx]
  have h₁ := Real.log_le_sub_one_of_pos (div_pos hx hy)
  have h₂ := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hx.ne' hy.ne'] at h₁
  rw [Real.log_div hy.ne' hx.ne'] at h₂
  have h₁' : x / y - 1 ≤ 2 * ε := by
    rw [sub_le_iff_le_add]
    apply (div_le_iff₀ hy).mpr
    nlinarith only [hl, mul_le_mul_of_nonneg_left hyHalf (by positivity : 0 ≤ 2 * ε)]
  have h₂' : y / x - 1 ≤ ε := by
    rw [sub_le_iff_le_add]
    apply (div_le_iff₀ hx).mpr
    nlinarith only [hu]
  exact abs_le.mpr ⟨by linarith only [h₁, h₁'], by linarith only [h₂, h₂', hε]⟩

end KqR75.GreedySchedule

#print axioms KqR75.GreedySchedule.relative_mass_at_horizon
#print axioms KqR75.GreedySchedule.log_difference_of_relative_error
