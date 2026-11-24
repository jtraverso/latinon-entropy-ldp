module
public import PhysicalDrift
public import EnergyFactor

@[expose] public section
noncomputable section
namespace KqR75.StoppedPhysical

open Finset LatinonEntropy
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

def mass (M : ℝ) (i : ℕ) : ℝ := M - i

/-- Clipping only defines the schedule beyond its useful horizon. -/
def ratio (M : ℝ) (i : ℕ) : ℝ := 1 - 1 / max 1 (mass M i)

def profile (a : ℕ) (M : ℝ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => profile a M i * ratio M i ^ a

theorem ratio_bounds (M : ℝ) (i : ℕ) : 0 ≤ ratio M i ∧ ratio M i ≤ 1 := by
  have hm : (1 : ℝ) ≤ max 1 (mass M i) := le_max_left _ _
  have hm0 : 0 < max 1 (mass M i) := by linarith
  have hi := (div_le_one hm0).mpr hm
  have hi0 := (one_div_pos.mpr hm0).le
  dsimp only [ratio]
  constructor <;> linarith

theorem profile_bounds (a : ℕ) (M : ℝ) (i : ℕ) : 0 ≤ profile a M i ∧ profile a M i ≤ 1 := by
  induction i with
  | zero => simp [profile]
  | succ i ih =>
    have hp0 := pow_nonneg (ratio_bounds M i).1 a
    have hp1 : ratio M i ^ a ≤ 1 := by
      have ht := GreedyProfile.power_le_one a (1 - ratio M i)
        (sub_nonneg.mpr (ratio_bounds M i).2) (by linarith [(ratio_bounds M i).1])
      simpa only [sub_sub_cancel] using ht
    constructor
    · exact mul_nonneg ih.1 hp0
    · exact (mul_le_mul ih.2 hp1 hp0 (by norm_num)).trans_eq (one_mul 1)

theorem profile_step (a : ℕ) (M : ℝ) (i : ℕ) (hm : 1 ≤ mass M i) :
    profile a M (i + 1) = profile a M i * (1 - 1 / mass M i) ^ a := by
  simp only [profile, ratio, max_eq_right hm]

theorem mass_succ (M : ℝ) (i : ℕ) : mass M (i + 1) = mass M i - 1 := by
  dsimp only [mass]
  push_cast
  ring

/-- On the physical horizon the recursive schedule is exactly the usual
power of the remaining resource proportion. -/
theorem profile_eq (a : ℕ) (M : ℝ) (i : ℕ) (hM : 0 < M) (hi : (i : ℝ) ≤ M) :
    profile a M i = (mass M i / M) ^ a := by
  revert hi
  induction i with
  | zero =>
    intro _
    simp only [profile, mass, Nat.cast_zero, sub_zero, div_self hM.ne', one_pow]
  | succ i ih =>
    intro hi
    have ht : (i : ℝ) + 1 ≤ M := by simpa only [Nat.cast_add, Nat.cast_one] using hi
    have hm : 1 ≤ mass M i := by
      dsimp only [mass]
      linarith only [ht]
    have hm0 : 0 < mass M i := by linarith
    rw [profile_step a M i hm, ih (by linarith only [ht]), ← mul_pow]
    congr 1
    rw [mass_succ]
    field_simp [hm0.ne', hM.ne']
    <;> ring

/-- All histories inherit the initial codegree bound, without a typicality
assumption or a bound on the number of deletions. -/
theorem codegree_le_initial (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (h : List (Option B)) (e f : E) :
    CodegreeLoss.codegree I (WeightedGreedy.availableWeight I μ J h) e f ≤
      CodegreeLoss.codegree I μ e f := by
  dsimp only [CodegreeLoss.codegree, WeightedEnergy.load]
  apply Finset.sum_le_sum
  intro b _
  dsimp only [WeightedGreedy.availableWeight]
  split_ifs <;> first | exact le_rfl | exact hμ b

/-- The regularity guard consists of state inequalities, not a drift hypothesis.
An additional predictable guard may stop for time or type constraints. -/
def regular (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (r : ℕ) (M n β : ℝ) (h : List (Option B)) : Prop :=
  WeightedGreedy.valid I J h ∧
  n ≤ mass M (WeightedGreedy.selectedCount h) ∧
  0 < profile (r - 1) M (WeightedGreedy.selectedCount h) ∧
  64 * (r : ℝ) ^ 2 * β ≤ profile (r - 1) M (WeightedGreedy.selectedCount h) ∧
  16 * (r : ℝ) * WeightedGreedy.energy I μ J h
    (profile (r - 1) M (WeightedGreedy.selectedCount h)) ≤
    mass M (WeightedGreedy.selectedCount h) *
      profile (r - 1) M (WeightedGreedy.selectedCount h) ^ 2

theorem live_stopped_mean (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop) (k factor : ℕ → ℝ)
    (h : List (Option B)) (hl : WeightedGreedy.live I μ J guard h) :
    (∑ a, (WeightedGreedy.kernel I μ hμ J guard).transition h a *
      WeightedGreedy.stoppedEnergy I μ J k factor (a :: h)) =
    factor (WeightedGreedy.selectedCount h + 1) *
      ∑ a, (WeightedGreedy.kernel I μ hμ J guard).transition h a *
        WeightedGreedy.energy I μ J (a :: h) (k (WeightedGreedy.selectedCount h + 1)) := by
  simp only [WeightedGreedy.kernel, hl, ite_true]
  simp only [univ_option, Finset.sum_insertNone, zero_mul, zero_add,
    WeightedGreedy.stoppedEnergy, WeightedGreedy.selectedCount]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Actual stopped-process drift with the coefficient 2r integrating factor.
The raw energy estimate is derived by PhysicalDrift, rather than assumed. -/
theorem active_step (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (r : ℕ) (M : ℝ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hcard : (J.card : ℝ) = (r : ℝ) * M)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (n β b : ℝ) (hn : 1 ≤ n) (hβ : 0 ≤ β) (hb : 0 ≤ b) (hβrate : β ≤ b / n)
    (hcodeg : ∀ e f, e ≠ f → CodegreeLoss.codegree I μ e f ≤ β)
    (extra : List (Option B) → Prop) (h : List (Option B))
    (hl : WeightedGreedy.live I μ J (fun h => regular I μ J r M n β h ∧ extra h) h) :
    let k := profile (r - 1) M
    let factor := profile (2 * r) M
    let K := WeightedGreedy.kernel I μ hμ J (fun h => regular I μ J r M n β h ∧ extra h)
    (∑ a, K.transition h a * WeightedGreedy.stoppedEnergy I μ J k factor (a :: h)) ≤
      WeightedGreedy.stoppedEnergy I μ J k factor h + PhysicalDrift.noiseConstant r b / n := by
  let i := WeightedGreedy.selectedCount h
  let m := mass M i
  let k := profile (r - 1) M
  let factor := profile (2 * r) M
  let K := WeightedGreedy.kernel I μ hμ J (fun h => regular I μ J r M n β h ∧ extra h)
  let X := WeightedGreedy.energy I μ J h (k i)
  let G := ∑ a, K.transition h a * WeightedGreedy.energy I μ J (a :: h) (k (i + 1))
  have hn0 : 0 < n := by linarith
  obtain ⟨hv, hm, hk, hsmall, henergy⟩ := hl.2.1.1
  have hm1 : 1 ≤ m := hn.trans hm
  have hc : ((WeightedGreedy.remaining I J h).card : ℝ) = (r : ℝ) * m := by
    have ht := WeightedGreedy.resource_count I J r hsize h hv
    have htR : ((WeightedGreedy.remaining I J h).card : ℝ) +
        (r : ℝ) * WeightedGreedy.selectedCount h = (J.card : ℝ) := by exact_mod_cast ht
    rw [hcard] at htR
    dsimp only [m, mass, i]
    nlinarith only [htR]
  have hcdeg (e f : E) (hef : e ≠ f) :=
    (codegree_le_initial I μ hμ J h e f).trans (hcodeg e f hef)
  have hd := PhysicalDrift.energy_drift_rate I μ hμ J _ h hl r hr hsize hload
    n m (k i) β b hn hm hk (profile_bounds (r - 1) M i).2 hβ hb hβrate hc hcdeg hsmall henergy
  have hkstep : k (i + 1) = k i - k i * (1 - (1 - 1 / m) ^ (r - 1)) := by
    dsimp only [k]
    rw [profile_step (r - 1) M i hm1]
    ring
  dsimp only at hd
  rw [← hkstep] at hd
  simp_rw [mul_sub] at hd
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, K.total, one_mul] at hd
  have hraw : G ≤ (1 + ((2 * r : ℕ) : ℝ) / m) * X + PhysicalDrift.noiseConstant r b / n := by
    change G - X ≤ 2 * (r : ℝ) * X / m + PhysicalDrift.noiseConstant r b / n at hd
    have he : (1 + ((2 * r : ℕ) : ℝ) / m) * X = X + 2 * (r : ℝ) * X / m := by
      push_cast
      ring
    rw [he]
    linarith only [hd]
  have hw := Energy.weighted_step (2 * r) m X G (PhysicalDrift.noiseConstant r b / n)
    (factor i) hm1 (Finset.sum_nonneg (fun e _ => sq_nonneg _))
    (profile_bounds (2 * r) M i).1 hraw
  have hfstep : factor (i + 1) = factor i * (1 - 1 / m) ^ (2 * r) :=
    profile_step (2 * r) M i hm1
  rw [← hfstep] at hw
  have hnoise : 0 ≤ PhysicalDrift.noiseConstant r b / n := by
    dsimp only [PhysicalDrift.noiseConstant]
    positivity
  have herr := mul_le_mul_of_nonneg_right (profile_bounds (2 * r) M (i + 1)).2 hnoise
  rw [one_mul] at herr
  have hmean := live_stopped_mean I μ hμ J _ k factor h hl
  dsimp only
  change (∑ a, K.transition h a * WeightedGreedy.stoppedEnergy I μ J k factor (a :: h)) ≤
    factor i * X + PhysicalDrift.noiseConstant r b / n
  rw [hmean]
  change factor (i + 1) * G ≤ factor i * X + PhysicalDrift.noiseConstant r b / n
  exact hw.trans (add_le_add le_rfl herr)

/-- Finite expectation bound for the physical stopped greedy chain. This
includes the crossing step and any further absorbing steps. -/
theorem expectation (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (r : ℕ) (M : ℝ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hcard : (J.card : ℝ) = (r : ℝ) * M)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (n β b : ℝ) (hn : 1 ≤ n) (hβ : 0 ≤ β) (hb : 0 ≤ b) (hβrate : β ≤ b / n)
    (hcodeg : ∀ e f, e ≠ f → CodegreeLoss.codegree I μ e f ≤ β)
    (extra : List (Option B) → Prop) (T : ℕ) :
    let k := profile (r - 1) M
    let factor := profile (2 * r) M
    let K := WeightedGreedy.kernel I μ hμ J (fun h => regular I μ J r M n β h ∧ extra h)
    historyExpectation K T (WeightedGreedy.stoppedEnergy I μ J k factor) ≤
      WeightedGreedy.energy I μ J [] 1 + (T : ℝ) * (PhysicalDrift.noiseConstant r b / n) := by
  have hn0 : 0 < n := by linarith
  have hnoise : 0 ≤ PhysicalDrift.noiseConstant r b / n := by
    dsimp only [PhysicalDrift.noiseConstant]
    positivity
  have he := WeightedGreedy.stoppedEnergy_drift_bound I μ hμ J
    (fun h => regular I μ J r M n β h ∧ extra h)
    (profile (r - 1) M) (profile (2 * r) M)
    (fun _ => PhysicalDrift.noiseConstant r b / n) (fun _ => hnoise)
    (fun h hl => active_step I μ hμ J r M hr hsize hcard hload n β b hn hβ hb hβrate hcodeg extra h hl) T
  simpa only [WeightedGreedy.stoppedEnergy, WeightedGreedy.selectedCount, profile,
    one_mul, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using he

theorem terminal_tail (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (r : ℕ) (M : ℝ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hcard : (J.card : ℝ) = (r : ℝ) * M)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (n β b : ℝ) (hn : 1 ≤ n) (hβ : 0 ≤ β) (hb : 0 ≤ b) (hβrate : β ≤ b / n)
    (hcodeg : ∀ e f, e ≠ f → CodegreeLoss.codegree I μ e f ≤ β)
    (extra : List (Option B) → Prop) (T : ℕ) (u : ℝ) (hu : 0 < u) :
    let Y := WeightedGreedy.stoppedEnergy I μ J (profile (r - 1) M) (profile (2 * r) M)
    let K := WeightedGreedy.kernel I μ hμ J (fun h => regular I μ J r M n β h ∧ extra h)
    FiniteProcess.eventMass K T (fun h => u ≤ Y h) ≤
      (WeightedGreedy.energy I μ J [] 1 + (T : ℝ) * (PhysicalDrift.noiseConstant r b / n)) / u := by
  dsimp only
  apply (le_div_iff₀ hu).mpr
  exact (FiniteProcess.event_markov _ T _ _ u
    (fun h _ => WeightedGreedy.stoppedEnergy_nonneg I μ J _ _ (fun i => (profile_bounds (2 * r) M i).1) h)
    (fun _ _ hp => hp)).trans
      (expectation I μ hμ J r M hr hsize hcard hload n β b hn hβ hb hβrate hcodeg extra T)

end KqR75.StoppedPhysical

#print axioms KqR75.StoppedPhysical.active_step
#print axioms KqR75.StoppedPhysical.profile_eq
#print axioms KqR75.StoppedPhysical.expectation
#print axioms KqR75.StoppedPhysical.terminal_tail
