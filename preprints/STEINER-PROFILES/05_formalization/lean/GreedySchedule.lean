module
public import GreedyScales
public import EnergyExit

@[expose] public section
noncomputable section
namespace KqR75.GreedySchedule

open Filter Finset

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- Before the integrated-energy threshold, the other physical
regularity conditions follow from the asymptotic guards. -/
theorem eventually_regular (r : ℕ) (hr : 1 ≤ r) {a z c b A : ℝ}
    (ha : 0 < a) (hz : 0 < z) (hscale : a * (4 * (r : ℝ) - 1) = 1 - 2 * z) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (M β : ℝ), c * (n : ℝ) ^ 2 ≤ M → β ≤ b / (n : ℝ) →
      ∀ (I : B → Finset E) (μ : B → ℝ) (J : Finset E) (h : List (Option B)),
        WeightedGreedy.valid I J h →
        WeightedGreedy.selectedCount h ≤ GreedyScales.horizon M n a →
        WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
          (StoppedPhysical.profile (2 * r) M) h ≤ A * (n : ℝ) →
        StoppedPhysical.regular I μ J r M n β h := by
  filter_upwards [GreedyScales.eventually_guard_scales r hr ha hz hscale hc] with n hn
  intro M β hM hβ I μ J h hv hi henergy
  obtain ⟨hn, hguards⟩ := hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hM₀ : 0 < M := (mul_pos hc (by positivity)).trans_le hM
  obtain ⟨hm, hsmall, henergy_scale⟩ := hguards M β hM hβ _ hi
  exact StoppingGuard.regular_of_threshold I μ J r M hr hM₀ n β (A * n) hn' h hv
    hm hsmall henergy_scale henergy

omit [Fintype B] [DecidableEq B] in
theorem selectedCount_le_length (h : List (Option B)) : WeightedGreedy.selectedCount h ≤ h.length := by
  induction h with
  | nil => simp [WeightedGreedy.selectedCount]
  | cons x h ih => cases x <;> simp only [WeightedGreedy.selectedCount, List.length_cons] <;> omega

/-- Use the selected-block index for remaining mass, and the larger
history length for the deterministic denominator. The cutoff extends
the denominator positively beyond the active horizon. -/
def denominator (M : ℝ) (T r i : ℕ) : ℝ :=
  M / 2 * ((M - (↑(min i T) : ℝ)) / M) ^ r

theorem denominator_pos {M : ℝ} {T : ℕ} (hM : 0 < M) (hT : (T : ℝ) < M) (r i : ℕ) :
    0 < denominator M T r i := by
  have h : (↑(min i T) : ℝ) ≤ T := by exact_mod_cast min_le_right i T
  exact mul_pos (by positivity) (pow_pos (div_pos (sub_pos.mpr (h.trans_lt hT)) hM) _)

/-- The deterministic denominator bounds the actual available weight
on the whole regular part of the process. -/
theorem denominator_le_available (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (r T : ℕ) (M n β : ℝ) (hr : 1 ≤ r) (hn : 1 ≤ n) (hM : 0 < M)
    (hsize : ∀ b, (I b).card = r) (hJ : (J.card : ℝ) = (r : ℝ) * M)
    (h : List (Option B)) (hreg : StoppedPhysical.regular I μ J r M n β h)
    (hT : h.length ≤ T) (hTM : (T : ℝ) < M) :
    denominator M T r h.length ≤ WeightedGreedy.totalWeight I μ J h := by
  let i := WeightedGreedy.selectedCount h
  let m := StoppedPhysical.mass M i
  let p := m / M
  let k := StoppedPhysical.profile (r - 1) M i
  let X := WeightedGreedy.energy I μ J h k
  let Z := WeightedGreedy.totalWeight I μ J h
  obtain ⟨hv, hm, hk, _, hE⟩ := hreg
  change n ≤ m at hm
  have hm₀ : 0 < m := by linarith
  have hi : (i : ℝ) ≤ M := by dsimp [m, StoppedPhysical.mass] at hm₀; linarith
  have hc : (((WeightedGreedy.remaining I J h).card : ℕ) : ℝ) = (r : ℝ) * m := by
    have hcard := WeightedGreedy.resource_count I J r hsize h hv
    have hcard' : ((WeightedGreedy.remaining I J h).card : ℝ) + (r : ℝ) * i = J.card := by
      exact_mod_cast hcard
    rw [hJ] at hcard'
    dsimp [m, StoppedPhysical.mass]
    linarith only [hcard']
  have he := GreedyMoments.mass_error I μ J h r hsize k
  rw [hc] at he
  have hem : (∑ e, WeightedGreedy.error I μ J h k e) = (r : ℝ) * (Z - m * k) := by
    linarith only [he, show Z = WeightedGreedy.totalWeight I μ J h from rfl]
  have hvar := (GreedyMoments.error_variances I μ J h k).2
  rw [hc] at hvar
  have hz := (ScalarDrift.regularity r m k Z X (∑ e, WeightedGreedy.error I μ J h k e)
    (by exact_mod_cast hr) hm₀ hk hem hvar hE).1
  have hle : (M - (h.length : ℝ)) / M ≤ p := by
    have hh : (i : ℝ) ≤ h.length := by exact_mod_cast selectedCount_le_length h
    exact div_le_div_of_nonneg_right (by dsimp [m, StoppedPhysical.mass]; linarith) hM.le
  have hp₀ : 0 ≤ (M - (h.length : ℝ)) / M := by
    have hh : (h.length : ℝ) ≤ T := by exact_mod_cast hT
    exact div_nonneg (sub_nonneg.mpr (hh.trans hTM.le)) hM.le
  have hk_eq : k = p ^ (r - 1) := StoppedPhysical.profile_eq (r - 1) M i hM hi
  have hp_eq : M * p = m := by rw [mul_comm]; exact div_mul_cancel₀ _ hM.ne'
  have hr_eq : r = r - 1 + 1 := by omega
  calc
    _ ≤ M / 2 * p ^ r := by
      rw [denominator, min_eq_left hT]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp₀ hle _) (by positivity)
    _ = m * k / 2 := by
      have hp_pow : p ^ r = p ^ (r - 1) * p := (congrArg (fun j : ℕ => p ^ j) hr_eq).trans (pow_succ _ _)
      rw [hk_eq, hp_pow, ← hp_eq]
      ring
    _ ≤ _ := hz

/-- The deterministic denominators yield the required variance budget
even when the initial mass is fractional. -/
theorem variance_budget (n T r : ℕ) (M a c : ℝ) (hn : 1 ≤ n) (hr : 1 ≤ r)
    (ha : 0 ≤ a) (hc : 0 < c) (hM : c * (n : ℝ) ^ 2 ≤ M)
    (hT : T ≤ GreedyScales.horizon M n a) :
    (∑ i ∈ range T, (4 * (r : ℝ) / denominator M T r i) ^ 2) ≤
      ((8 * (r : ℝ)) ^ 2 / ((2 * (r : ℝ) - 1) * c)) *
        (n : ℝ) ^ (-2 + a * (2 * (r : ℝ) - 1)) := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hM₀ : 0 < M := (mul_pos hc (by positivity)).trans_le hM
  let p (i : ℕ) := (M - (i : ℝ)) / M
  let s := 2 * (r : ℝ)
  have hs : 1 < s := by dsimp [s]; linarith
  have hs' : 0 < s - 1 := by linarith
  obtain ⟨hH, _, htail⟩ := GreedyScales.horizon_bounds M n a hM₀ hn ha
  have hTM : (T : ℝ) < M := (Nat.cast_le.mpr hT).trans_lt hH
  have hp (i : ℕ) (hi : i ≤ T) : 0 < p i :=
    div_pos (sub_pos.mpr ((Nat.cast_le.mpr hi).trans_lt hTM)) hM₀
  have hpT : p T ^ (1 - s) ≤ (n : ℝ) ^ (a * (s - 1)) := by
    calc
      _ ≤ ((n : ℝ) ^ (-a)) ^ (1 - s) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hn₀ _) (htail T hT) (by linarith)
      _ = _ := by rw [← Real.rpow_mul hn₀.le]; congr 1; ring
  have hpow (i : ℕ) (hi : i ∈ range T) :
      (4 * (r : ℝ) / denominator M T r i) ^ 2 =
        (8 * (r : ℝ) / M) ^ 2 * p i ^ (-s) := by
    have hi' := (mem_range.mp hi).le
    have hp' := hp i hi'
    rw [show denominator M T r i = M / 2 * p i ^ r by simp [denominator, min_eq_left hi', p]]
    have hcast : s = (↑(r * 2) : ℝ) := by dsimp [s]; push_cast; ring
    rw [hcast, Real.rpow_neg hp'.le, Real.rpow_natCast, pow_mul]
    field_simp
    ring
  calc
    _ = (8 * (r : ℝ) / M) ^ 2 * ∑ i ∈ range T, p i ^ (-s) := by
      rw [mul_sum]
      exact sum_congr rfl hpow
    _ ≤ (8 * (r : ℝ) / M) ^ 2 * (M * p T ^ (1 - s) / (s - 1)) :=
      mul_le_mul_of_nonneg_left (GreedyScales.sum_inverse_remaining_power M s T hM₀ hTM hs) (sq_nonneg _)
    _ = ((8 * (r : ℝ)) ^ 2 / ((s - 1) * M)) * p T ^ (1 - s) := by field_simp
    _ ≤ ((8 * (r : ℝ)) ^ 2 / ((s - 1) * (c * (n : ℝ) ^ 2))) * (n : ℝ) ^ (a * (s - 1)) := by
      apply mul_le_mul _ hpT (by positivity) (by positivity)
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_left hM hs'.le)
    _ = _ := by
      rw [Real.rpow_add hn₀, show (n : ℝ) ^ (-2 : ℝ) = ((n : ℝ) ^ 2)⁻¹ by
        rw [Real.rpow_neg hn₀.le, Real.rpow_two]]
      dsimp [s]
      field_simp

end KqR75.GreedySchedule

#print axioms KqR75.GreedySchedule.eventually_regular
#print axioms KqR75.GreedySchedule.denominator_le_available
#print axioms KqR75.GreedySchedule.variance_budget
