module
public import HorizonConcentration

@[expose] public section
noncomputable section
namespace KqR75.HorizonCountTheorem

open Finset Filter LatinonEntropy

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

def energy (I : B → Finset E) (μ : B → ℝ) (J : Finset E) (r : ℕ) (M : ℝ) :
    List (Option B) → ℝ :=
  WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
    (StoppedPhysical.profile (2 * r) M)

def guard (I : B → Finset E) (μ : B → ℝ) (J : Finset E) (r T : ℕ)
    (M n β u : ℝ) (h : List (Option B)) : Prop :=
  StoppedPhysical.regular I μ J r M n β h ∧ (h.length < T ∧ energy I μ J r M h < u)

theorem denominator_ge_two (r T n : ℕ) (M a z c : ℝ) (hr : 1 ≤ r)
    (hn : 1 ≤ n) (ha : 0 ≤ a) (hz : 0 ≤ z) (hc : 0 < c)
    (hnc : 4 * (r : ℝ) / c ≤ n) (hs : a * (4 * (r : ℝ) - 1) = 1 - 2 * z)
    (hM : c * (n : ℝ) ^ 2 ≤ M) (hT : T ≤ GreedyScales.horizon M n a)
    (i : ℕ) (hi : i ≤ T) :
    2 * (r : ℝ) ≤ GreedySchedule.denominator M T r i := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hM₀ : 0 < M := (mul_pos hc (by positivity)).trans_le hM
  have hp := (GreedyScales.horizon_bounds M n a hM₀ hn ha).2.2 i (hi.trans hT)
  have hex : (1 : ℝ) ≤ 2 - a * r := by nlinarith [mul_nonneg ha (show 0 ≤ 3 * (r : ℝ) - 1 by linarith)]
  calc
    _ ≤ (c / 2) * n := by
      have hh := (div_le_iff₀ hc).mp hnc
      linarith only [hh, mul_comm (n : ℝ) c]
    _ ≤ (c / 2) * (n : ℝ) ^ (2 - a * r) := by
      rw [← Real.rpow_one (n : ℝ)] at ⊢
      rw [Real.rpow_one]
      exact mul_le_mul_of_nonneg_left ((Real.rpow_one (n : ℝ)).symm.le.trans
        (Real.rpow_le_rpow_of_exponent_le hn' hex)) (by positivity)
    _ = (c * (n : ℝ) ^ 2 / 2) * ((n : ℝ) ^ (-a)) ^ r := by
      rw [← Real.rpow_two, ← Real.rpow_natCast (((n : ℝ) ^ (-a))) r, ← Real.rpow_mul hn₀.le]
      rw [show 2 - a * r = 2 + (-a) * r by ring, Real.rpow_add hn₀]
      ring
    _ ≤ GreedySchedule.denominator M T r i := by
      rw [GreedySchedule.denominator, min_eq_left hi]
      exact mul_le_mul (div_le_div_of_nonneg_right hM (by norm_num))
        (pow_le_pow_left₀ (by positivity) hp _) (by positivity) (by positivity)

/-- The physical greedy procedure makes it to the horizon and all
type counts have the required error on the same event of mass 1/2. -/
theorem eventually_count (r : ℕ) (hr : 2 ≤ r) (k : ℕ) (c C A b a z : ℝ)
    (hc : 0 < c) (hC : 0 < C) (hA : 0 < A) (hb : 0 ≤ b) (ha : 0 < a)
    (hz : 0 < z) (hz₁ : z ≤ 1/2) (hs : a * (4 * (r : ℝ) - 1) = 1 - 2 * z)
    (hquota : 4 * C * PhysicalDrift.noiseConstant r b ≤ A) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ (E B : Type*) [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B],
    ∀ (M β : ℝ) (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ w, 0 ≤ μ w) (J : Finset E)
      (F : Fin k → Finset B),
      c * (n : ℝ) ^ 2 ≤ M → M ≤ C * (n : ℝ) ^ 2 → 0 ≤ β → β ≤ b / n →
      (∀ w, (I w).card = r) → (J.card : ℝ) = (r : ℝ) * M →
      (∀ w, ¬I w ⊆ J → μ w = 0) →
      (∀ e, WeightedEnergy.load I μ e = if e ∈ J then 1 else 0) →
      (∀ e f, e ≠ f → CodegreeLoss.codegree I μ e f ≤ β) →
      let T := GreedyScales.horizon M n a
      let Y := energy I μ J r M
      let K := WeightedGreedy.kernel I μ hμ J (guard I μ J r T M n β (A * n))
      1 / 2 ≤ FiniteProcess.eventMass K T (fun h =>
        none ∉ h ∧ WeightedGreedy.valid I J h ∧ ¬EnergyExit.crossed Y (A * n) h ∧
        ∀ d : Fin k, |(TypeCounts.count (F d) h : ℝ) -
          (T : ℝ) * TypeWeights.proportion I μ J (F d) []| ≤
            (1 + C * (1 + CumulativeTypeDrift.driftConstant r c C A b)) * (n : ℝ) ^ (2 - z)) := by
  classical
  let V := ((8 * (r : ℝ)) ^ 2 / ((2 * (r : ℝ) - 1) * c))
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hV : 0 < V := by dsimp [V]; exact div_pos (by positivity) (mul_pos (by linarith) hc)
  have hev := GreedyScales.eventually_guard_scales (b := b) (A := A)
    r (by omega : 1 ≤ r) ha hz hs hc
  have hnc : ∀ᶠ n : ℕ in Filter.atTop, 4 * (r : ℝ) / c ≤ n :=
    (tendsto_atTop.1 (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)) _
  have hpb := TypeTails.eventually_prefix_budget k (C := C) (η := 1)
    (div_pos (show 0 < (1 : ℝ) by norm_num) (show 0 < 2 * V by positivity)) (by norm_num) (by norm_num : 0 < (1 : ℝ) / 8)
  have hcb := TypeTails.eventually_prefix_budget k (C := C) (η := 1)
    (div_pos (show 0 < (1 : ℝ) by norm_num) (show 0 < 2 * C by positivity)) (by norm_num) (by norm_num : 0 < (1 : ℝ) / 8)
  filter_upwards [hev, hnc, hpb, hcb, eventually_ge_atTop (1 : ℕ)] with n he hnC hpbudget hcbudget hn
  intro E B _ _ _ _ M β I μ hμ J F hMₗ hMᵤ hβ hβrate hsize hJ hsupport hunit hcodeg
  dsimp only
  let T := GreedyScales.horizon M n a
  let Y := energy I μ J r M
  let G := guard I μ J r T M n β (A * n)
  let K := WeightedGreedy.kernel I μ hμ J G
  let L := CumulativeTypeDrift.driftConstant r c C A b
  let pErr := (1 + L) * (n : ℝ) ^ (-z)
  let countErr := (n : ℝ) ^ (2 - z)
  let δ := 2 * Real.exp (-(1 / (2 * V)) * (n : ℝ))
  let ε := 2 * Real.exp (-(1 / (2 * C)) * (n : ℝ))
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by linarith
  have hM : 0 < M := (mul_pos hc (by positivity)).trans_le hMₗ
  have hT := (GreedyScales.horizon_bounds M n a hM hn ha.le).1
  have hTC : (T : ℝ) ≤ C * (n : ℝ) ^ 2 := hT.le.trans hMᵤ
  have hr1 : 1 ≤ r := by omega
  have hload (e) : WeightedEnergy.load I μ e ≤ 1 := by rw [hunit]; split_ifs <;> norm_num
  have hguards (h : List (Option B)) (hh : h.length < T) (hv : WeightedGreedy.valid I J h)
      (hY : Y h < A * n) : StoppedPhysical.regular I μ J r M n β h := by
    obtain ⟨hm, hg, hu⟩ := he.2 M β hMₗ hβrate (WeightedGreedy.selectedCount h)
      ((GreedySchedule.selectedCount_le_length h).trans hh.le)
    exact StoppingGuard.regular_of_threshold I μ J r M hr1 hM n β (A * n) hn' h hv hm hg hu hY.le
  have hden (h) (hh : G h) : GreedySchedule.denominator M T r h.length ≤
      WeightedGreedy.totalWeight I μ J h :=
    GreedySchedule.denominator_le_available I μ J r T M n β hr1 hn' hM hsize hJ h hh.1 hh.2.1.le hT
  have hZ (h) (hh : G h) : 2 * (r : ℝ) ≤ WeightedGreedy.totalWeight I μ J h :=
    (denominator_ge_two r T n M a z c hr1 hn ha.le hz.le hc hnC hs hMₗ le_rfl h.length hh.2.1.le).trans (hden h hh)
  have hcross' := GreedyHorizon.horizon_failure_quarter I μ hμ J r T M n β b C A hr1
    hn' hM hT hMᵤ hsize hJ hsupport hunit hβ hb hβrate hcodeg hA hquota hguards
  have hcross : FiniteProcess.eventMass K T (EnergyExit.crossed Y (A * n)) ≤ 1 / 4 :=
    (PrefixTypeTests.mono_support _ _ _ _ (fun _ _ _ hp => Or.inr hp)).trans hcross'
  have hL : 0 ≤ L := by
    dsimp [L, CumulativeTypeDrift.driftConstant]
    have h1 : 0 ≤ (r : ℝ) - 1 := by linarith
    have h2 : 0 ≤ 2 * (r : ℝ) - 1 := by linarith
    have h3 : 0 ≤ 2 * (r : ℝ) - 1/2 := by linarith
    have h4 : 0 ≤ 4 * (r : ℝ) - 1 := by linarith
    positivity
  have hpTail (d : Fin k) (t : ℕ) (ht : t ≤ T) : FiniteProcess.eventMass K t (fun h =>
      pErr < |TypeWeights.proportion I μ J (F d) h - TypeWeights.proportion I μ J (F d) []|) ≤ δ := by
    have hh := HorizonConcentration.prefix_tail I μ hμ J (F d) G r T hr1 hsize hload
      (GreedySchedule.denominator M T r) (GreedySchedule.denominator_pos hM hT r)
      hZ hden ((n : ℝ) ^ (-z)) (L * (n : ℝ) ^ (-z)) (V * (n : ℝ) ^ (-2 + a * (2 * (r : ℝ) - 1)))
      (by positivity) (by positivity) (by positivity)
      (GreedySchedule.variance_budget n T r M a c hn hr1 ha.le hc hMₗ le_rfl)
    have hpath := CumulativeTypeDrift.physical_path_bound I μ hμ J (F d) r T n M β b c C A a z
      hr hn hc hC.le hA.le hMₗ hMᵤ ha.le hz.le hs le_rfl hsize hJ hload hβ hb hβrate hcodeg G
      (fun h hh => ⟨hh.1, hh.2.2.le, hZ h hh⟩)
    have htail := (hh hpath t ht).trans (HorizonConcentration.proportion_rate n r a z V hn' ha.le hV hs)
    simpa only [pErr, add_mul, one_mul] using htail
  have hcTail (d : Fin k) : FiniteProcess.eventMass K T (fun h => countErr < |(TypeCounts.count (F d) h : ℝ) -
      pathSum (fun g _ => ∑ w, K.transition g w * TypeCounts.indicator (F d) w) h|) ≤ ε := by
    by_cases ht : 0 < T
    · have ht' := TypeCounts.tail K (F d) T ht countErr (by positivity)
      exact (PrefixTypeTests.mono_support _ _ _ _ (fun _ _ _ hp => hp.le)).trans
        (ht'.trans (HorizonConcentration.count_rate n C z T hn' hC hz₁ ht hTC))
    · have hzero : T = 0 := by omega
      simp only [hzero, FiniteProcess.eventMass, histories, sum_singleton, TypeCounts.count,
        Nat.cast_zero, pathSum, sub_self, abs_zero, not_lt.mpr (show 0 ≤ countErr by positivity), ite_false]
      positivity
  have hbudget : ((univ : Finset (Fin k)).card : ℝ) * (T + 1) * δ +
      ((univ : Finset (Fin k)).card : ℝ) * ε ≤ 1 / 4 := by
    simp only [card_univ, Fintype.card_fin]
    have hpbudget' : (k : ℝ) * (C * (n : ℝ) ^ 2 + 1) * δ ≤ 1 / 8 := by
      simpa only [δ, Real.rpow_one] using hpbudget
    have hcbudget' : (k : ℝ) * (C * (n : ℝ) ^ 2 + 1) * ε ≤ 1 / 8 := by
      simpa only [ε, Real.rpow_one] using hcbudget
    have hp := (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (add_le_add hTC (le_refl (1 : ℝ))) (show (0 : ℝ) ≤ k by positivity))
      (show 0 ≤ δ by dsimp [δ]; positivity)).trans hpbudget'
    have hq : (k : ℝ) * ε ≤ 1 / 8 := by
      refine (le_trans ?_ hcbudget')
      exact mul_le_mul_of_nonneg_right (by
        calc (k : ℝ) = (k : ℝ) * 1 := by ring
             _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hC.le (sq_nonneg (n : ℝ))])
               (by positivity)) (by dsimp [ε]; positivity)
    linarith only [hp, hq]
  have hsim := TypeCountHorizon.simultaneous I μ hμ J (univ : Finset (Fin k)) F r T M n β (A * n)
    pErr countErr δ ε hr1 hn' hM hT hsize hJ hguards hcross
    (fun d _ t ht => hpTail d t ht) (fun d _ => hcTail d) hbudget
  refine hsim.trans (PrefixTypeTests.mono_support _ _ _ _ ?_)
  intro h _ _ ⟨hstop, hv, hx, hall⟩
  refine ⟨hstop, hv, hx, fun d => (hall d (mem_univ _)).trans ?_⟩
  calc
    _ ≤ countErr + (C * (n : ℝ) ^ 2) * pErr :=
      add_le_add (le_refl countErr) (mul_le_mul_of_nonneg_right hTC (show 0 ≤ pErr by dsimp [pErr]; positivity))
    _ = _ := by
      dsimp [countErr, pErr]
      have hnPow : (n : ℝ) ^ 2 * (n : ℝ) ^ (-z) = (n : ℝ) ^ (2 - z) := by
        rw [← Real.rpow_two, ← Real.rpow_add hn₀, sub_eq_add_neg]
      calc
        _ = (n : ℝ) ^ (2 - z) + C * (1 + L) * ((n : ℝ) ^ 2 * (n : ℝ) ^ (-z)) := by ring
        _ = _ := by rw [hnPow]; ring

end KqR75.HorizonCountTheorem

#print axioms KqR75.HorizonCountTheorem.eventually_count
