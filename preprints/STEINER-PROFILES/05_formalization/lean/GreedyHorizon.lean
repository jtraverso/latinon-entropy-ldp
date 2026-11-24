module
public import GreedySchedule

@[expose] public section
noncomputable section
namespace KqR75.GreedyHorizon

open Finset LatinonEntropy

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- On positive-probability histories below the horizon, avoiding an
energy crossing also avoids the absorbing outcome. -/
theorem no_stop_without_exit (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (r T : ℕ) (M n β u : ℝ) (hr : 1 ≤ r) (hn : 1 ≤ n)
    (hM : 0 < M) (hT : (T : ℝ) < M) (hsize : ∀ b, (I b).card = r)
    (hJ : (J.card : ℝ) = (r : ℝ) * M)
    (hguards : ∀ h : List (Option B), h.length < T → WeightedGreedy.valid I J h →
      WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
        (StoppedPhysical.profile (2 * r) M) h < u →
      StoppedPhysical.regular I μ J r M n β h) :
    let Y := WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
      (StoppedPhysical.profile (2 * r) M)
    let K := WeightedGreedy.kernel I μ hμ J
      (fun h => StoppedPhysical.regular I μ J r M n β h ∧ (h.length < T ∧ Y h < u))
    ∀ h : List (Option B), h.length ≤ T → 0 < historyWeight K h →
      ¬EnergyExit.crossed Y u h → none ∉ h := by
  let Y := WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
    (StoppedPhysical.profile (2 * r) M)
  let guard := fun h : List (Option B) => StoppedPhysical.regular I μ J r M n β h ∧
    (h.length < T ∧ Y h < u)
  let K := WeightedGreedy.kernel I μ hμ J guard
  have hy (h : List (Option B)) (hh : ¬EnergyExit.crossed Y u h) : Y h < u := by
    apply lt_of_not_ge
    cases h with
    | nil => exact hh
    | cons a h => exact fun he => hh (Or.inl he)
  change ∀ h : List (Option B), h.length ≤ T → 0 < historyWeight K h →
    ¬EnergyExit.crossed Y u h → none ∉ h
  intro h
  induction h with
  | nil => simp
  | cons a h ih =>
    intro hlen hp he
    have hlen' : h.length < T := by simp only [List.length_cons] at hlen; omega
    have he' : ¬EnergyExit.crossed Y u h := fun hh => he (Or.inr hh)
    change 0 < historyWeight K h * K.transition h a at hp
    have hph : 0 < historyWeight K h := by
      by_contra hnp
      have hz : historyWeight K h = 0 :=
        le_antisymm (le_of_not_gt hnp) (historyWeight_nonneg K h)
      simp [hz] at hp
    have hnone := ih hlen'.le hph he'
    have hv := WeightedGreedy.positive_history_valid I μ hμ J guard h hph
    have hY := hy h he'
    have hreg := hguards h hlen' hv hY
    have hden := GreedySchedule.denominator_le_available I μ J r T M n β hr hn hM
      hsize hJ h hreg hlen'.le hT
    have hmass := (GreedySchedule.denominator_pos hM hT r h.length).trans_le hden
    have hl : WeightedGreedy.live I μ J guard h := ⟨hnone, ⟨hreg, hlen', hY⟩, hmass⟩
    cases a with
    | none =>
      have hz : K.transition h none = 0 := by simp [K, WeightedGreedy.kernel, hl]
      simp [hz] at hp
    | some b => simp [hnone]

/-- Unit initial loads give zero initial energy. A supported seed
has weight zero for blocks using an edge outside the starting host. -/
theorem initial_energy_zero (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (hsupport : ∀ b, ¬I b ⊆ J → μ b = 0)
    (hunit : ∀ e, WeightedEnergy.load I μ e = if e ∈ J then 1 else 0) :
    WeightedGreedy.energy I μ J [] 1 = 0 := by
  have havail : WeightedGreedy.availableWeight I μ J [] = μ := by
    funext b
    by_cases h : I b ⊆ J
    · simp [WeightedGreedy.availableWeight, WeightedGreedy.remaining, h]
    · simp [WeightedGreedy.availableWeight, WeightedGreedy.remaining, h, hsupport b h]
  simp [WeightedGreedy.energy, WeightedGreedy.error, WeightedGreedy.load, havail,
    hunit, WeightedGreedy.remaining]
  exact sum_eq_zero (fun e _ => by by_cases he : e ∈ J <;> simp [he])

/-- A quarter of the mass suffices for the energy failure budget, with
a constant independent of the bank capacity. This includes failure
to make a selection at an earlier step. -/
theorem horizon_failure_quarter (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ w, 0 ≤ μ w)
    (J : Finset E) (r T : ℕ) (M n β b C A : ℝ) (hr : 1 ≤ r)
    (hn : 1 ≤ n) (hM : 0 < M) (hT : (T : ℝ) < M) (hMb : M ≤ C * n ^ 2)
    (hsize : ∀ w, (I w).card = r) (hJ : (J.card : ℝ) = (r : ℝ) * M)
    (hsupport : ∀ w, ¬I w ⊆ J → μ w = 0)
    (hunit : ∀ e, WeightedEnergy.load I μ e = if e ∈ J then 1 else 0)
    (hβ : 0 ≤ β) (hb : 0 ≤ b) (hβrate : β ≤ b / n)
    (hcodeg : ∀ e f, e ≠ f → CodegreeLoss.codegree I μ e f ≤ β)
    (hA : 0 < A) (hquota : 4 * C * PhysicalDrift.noiseConstant r b ≤ A)
    (hguards : ∀ h : List (Option B), h.length < T → WeightedGreedy.valid I J h →
      WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
        (StoppedPhysical.profile (2 * r) M) h < A * n →
      StoppedPhysical.regular I μ J r M n β h) :
    let Y := WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
      (StoppedPhysical.profile (2 * r) M)
    let K := WeightedGreedy.kernel I μ hμ J
      (fun h => StoppedPhysical.regular I μ J r M n β h ∧ (h.length < T ∧ Y h < A * n))
    FiniteProcess.eventMass K T (fun h => none ∈ h ∨ EnergyExit.crossed Y (A * n) h) ≤ 1 / 4 := by
  classical
  let Y := WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
    (StoppedPhysical.profile (2 * r) M)
  let K := WeightedGreedy.kernel I μ hμ J
    (fun h => StoppedPhysical.regular I μ J r M n β h ∧ (h.length < T ∧ Y h < A * n))
  let bad := fun h => none ∈ h ∨ EnergyExit.crossed Y (A * n) h
  let cross := EnergyExit.crossed Y (A * n)
  have hn₀ : 0 < n := by linarith
  have hload (e : E) : WeightedEnergy.load I μ e ≤ 1 := by
    rw [hunit]
    split_ifs <;> norm_num
  have hbound := EnergyExit.first_exit_bound I μ hμ J r M hr hsize hJ hload
    n β b hn hβ hb hβrate hcodeg (fun h => h.length < T) T (A * n) (mul_pos hA hn₀)
  change FiniteProcess.eventMass K T cross ≤ _ at hbound
  rw [initial_energy_zero I μ J hsupport hunit, zero_add] at hbound
  have hmono : FiniteProcess.eventMass K T bad ≤ FiniteProcess.eventMass K T cross := by
    unfold FiniteProcess.eventMass
    apply sum_le_sum
    intro h hh
    by_cases he : cross h
    · simp only [he, ite_true]
      split_ifs <;> simp [historyWeight_nonneg]
    · by_cases hnone : none ∈ h
      · have hz : historyWeight K h = 0 := by
          by_contra hz
          have hpos := lt_of_le_of_ne (historyWeight_nonneg K h) (Ne.symm hz)
          exact (no_stop_without_exit I μ hμ J r T M n β (A * n) hr hn hM hT hsize hJ
            hguards h (le_of_eq (histories_length hh)) hpos he) hnone
        simp [hz]
      · change ¬EnergyExit.crossed Y (A * n) h at he
        simp [bad, cross, hnone, he]
  have hnoise : 0 ≤ PhysicalDrift.noiseConstant r b := by
    unfold PhysicalDrift.noiseConstant
    positivity
  calc
    _ ≤ FiniteProcess.eventMass K T cross := hmono
    _ ≤ (T : ℝ) * (PhysicalDrift.noiseConstant r b / n) / (A * n) := hbound
    _ ≤ (C * n ^ 2) * (PhysicalDrift.noiseConstant r b / n) / (A * n) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hT.le.trans hMb) (div_nonneg hnoise hn₀.le)) (by positivity)
    _ = C * PhysicalDrift.noiseConstant r b / A := by field_simp
    _ ≤ 1 / 4 := (div_le_iff₀ hA).2 (by linarith)

end KqR75.GreedyHorizon

#print axioms KqR75.GreedyHorizon.no_stop_without_exit
#print axioms KqR75.GreedyHorizon.initial_energy_zero
#print axioms KqR75.GreedyHorizon.horizon_failure_quarter
