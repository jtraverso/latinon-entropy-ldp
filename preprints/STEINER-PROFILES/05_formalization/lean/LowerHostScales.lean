module
public import LowerFromHost

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Filter Finset ColouredCliques CompleteJohnson SparseGram WeightedGreedy
open scoped Topology

/-- Quantities controlling the horizon can be fixed before the
absorber and bank are placed. -/
theorem critical_completion_scales (q : ℕ) (hq : 3 ≤ q) :
    let r := q.choose 2
    let z := GreedyScales.criticalExponent q
    let a := (2 * (q : ℝ) - 1) * z
    0 < z ∧ z < 1 / 2 ∧ z ≤ a ∧ a ≤ 1 ∧
      a * (4 * (r : ℝ) - 1) = 1 - 2 * z ∧
      (2 * (q : ℝ) + 1) * z < 1 := by
  let r := q.choose 2
  let z := GreedyScales.criticalExponent q
  let a := (2 * (q : ℝ) - 1) * z
  obtain ⟨hz, _, ha, hscale⟩ := GreedyScales.criticalExponent_bounds q hq
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast Nat.choose_pos (show 2 ≤ q by omega)
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hgap := ReserveRandom.critical_cut_gap q hq
  have hz' : z < 1 / 2 := by
    nlinarith only [hgap, mul_nonneg (show 0 ≤ 2 * (q : ℝ) - 1 by linarith) hz.le]
  have hza : z ≤ a := by
    dsimp [a]
    nlinarith only [hq', mul_nonneg (show 0 ≤ (q : ℝ) - 1 by linarith) hz.le]
  have haup : a ≤ 1 := by
    nlinarith only [hscale, hz, mul_nonneg (show 0 ≤ 4 * (r : ℝ) - 2 by linarith) ha.le]
  exact ⟨hz, hz', hza, haup, hscale, hgap⟩

/-- The rounded horizon is positive uniformly whenever the initial
block mass has a quadratic lower bound. -/
theorem eventually_horizon_positive (c a : ℝ) (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ∀ M : ℝ, c * (n : ℝ) ^ 2 ≤ M → 1 ≤ GreedyScales.horizon M n a := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdec : Tendsto (fun n : ℕ => (n : ℝ) ^ (-a)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop ha).comp hn
  filter_upwards [hdec.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num),
    (tendsto_atTop.1 hn) (max 1 (2 / c))] with n hsmall hn'
  intro M hM
  have hn₁ : (1 : ℝ) ≤ n := (le_max_left _ _).trans hn'
  have hcn : 2 ≤ c * (n : ℝ) := by
    have h' := (div_le_iff₀ hc).mp ((le_max_right _ _).trans hn')
    simpa only [mul_comm] using h'
  have hn₀ : 0 ≤ (n : ℝ) := zero_le_one.trans hn₁
  have hs : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hn₁) hn₀]
  have hM' := hcn.trans ((mul_le_mul_of_nonneg_left hs hc.le).trans hM)
  have hM₀ : 0 ≤ M := by linarith only [hM']
  have hp : (1 : ℝ) / 2 ≤ 1 - (n : ℝ) ^ (-a) := by linarith only [hsmall]
  unfold GreedyScales.horizon
  apply (Nat.le_floor_iff' (by decide : (1 : ℕ) ≠ 0)).mpr
  push_cast
  nlinarith only [mul_le_mul_of_nonneg_left hp hM₀, hM']

/-- At every good horizon, the leave meets the cover-down budget
with coefficient 2r, independent of the deleted degree. -/
theorem horizon_leave_for_cover {n q : ℕ} (hn : 1 ≤ n) (a : ℝ)
    (ha : 0 ≤ a) (ha' : a ≤ 2) (J : Finset (Edge n)) (M : ℝ)
    (hM : 0 < M) (hMup : M ≤ (n : ℝ) ^ 2)
    (hcard : (J.card : ℝ) = (q.choose 2 : ℝ) * M)
    (h : List (Option (Clique n q))) (hlen : h.length = GreedyScales.horizon M n a)
    (hv : valid (resources n q) J h) (hstop : none ∉ h) :
    ((remaining (resources n q) J h).card : ℝ) ≤
      (2 * (q.choose 2 : ℝ)) * (n : ℝ) ^ (2 - a) := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have h := PhysicalHorizonCounts.leave_bound hn a ha J M hM hcard h hlen hv hstop
  have hpow : (n : ℝ) ^ 2 * (n : ℝ) ^ (-a) = (n : ℝ) ^ (2 - a) := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hn₀]
    rfl
  have hrem := mul_le_mul_of_nonneg_right hMup (Real.rpow_nonneg hn₀.le (-a))
  rw [hpow] at hrem
  have hone := Real.one_le_rpow hn₁ (show 0 ≤ 2 - a by linarith)
  refine h.trans ?_
  have hsum := add_le_add hrem hone
  rw [two_mul]
  nlinarith only [mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg (q.choose 2))]

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.critical_completion_scales
#print axioms KqR75.PhysicalCompletion.eventually_horizon_positive
#print axioms KqR75.PhysicalCompletion.horizon_leave_for_cover
