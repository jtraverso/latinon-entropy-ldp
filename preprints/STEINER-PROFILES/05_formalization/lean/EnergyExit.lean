module
public import StoppedPhysical

@[expose] public section
noncomputable section
namespace KqR75.EnergyExit

open Finset LatinonEntropy
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

def crossed {Ω : Type*} (Y : List Ω → ℝ) (u : ℝ) : List Ω → Prop
  | [] => u ≤ Y []
  | a :: h => u ≤ Y (a :: h) ∨ crossed Y u h

/-- Once the threshold has been crossed, every positive transition is
the absorbing outcome, so the crossing value is retained. -/
theorem crossing_retained (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (k factor : ℕ → ℝ) (base : List (Option B) → Prop) (u : ℝ)
    (h : List (Option B))
    (hp : 0 < historyWeight (WeightedGreedy.kernel I μ hμ J
      (fun h => base h ∧ WeightedGreedy.stoppedEnergy I μ J k factor h < u)) h)
    (hc : crossed (WeightedGreedy.stoppedEnergy I μ J k factor) u h) :
    u ≤ WeightedGreedy.stoppedEnergy I μ J k factor h := by
  let Y := WeightedGreedy.stoppedEnergy I μ J k factor
  let guard := fun h => base h ∧ Y h < u
  let K := WeightedGreedy.kernel I μ hμ J guard
  revert hp hc
  induction h with
  | nil => intro _ hc; exact hc
  | cons a h ih =>
    intro hp hc
    change 0 < historyWeight K h * K.transition h a at hp
    have hh : 0 < historyWeight K h := by
      by_contra hn
      have hz : historyWeight K h = 0 := le_antisymm (le_of_not_gt hn) (historyWeight_nonneg K h)
      simp only [hz, zero_mul, lt_self_iff_false] at hp
    rcases hc with hc | hc
    · exact hc
    · have hy := ih hh hc
      have hl : ¬ WeightedGreedy.live I μ J guard h := by
        intro hl
        exact (not_lt_of_ge hy) hl.2.1.2
      cases a with
      | none => exact hy
      | some c => simp [K, WeightedGreedy.kernel, hl] at hp

/-- Markov on finite histories needs an event witness only on the support
of the actual law; zero-weight histories contribute nothing. -/
theorem support_markov {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (P : List Ω → Prop) (Y : List Ω → ℝ) (u : ℝ)
    (hY : ∀ h, 0 ≤ Y h)
    (hP : ∀ h, 0 < historyWeight K h → P h → u ≤ Y h) :
    FiniteProcess.eventMass K T P * u ≤ historyExpectation K T Y := by
  classical
  have hs : ∀ h ∈ histories Ω T,
      (if P h then historyWeight K h else 0) * u ≤ historyWeight K h * Y h := by
    intro h _
    by_cases hp : 0 < historyWeight K h
    · split_ifs with hPh
      · exact mul_le_mul_of_nonneg_left (hP h hp hPh) hp.le
      · simpa only [zero_mul] using mul_nonneg hp.le (hY h)
    · have hz : historyWeight K h = 0 := le_antisymm (le_of_not_gt hp) (historyWeight_nonneg K h)
      simp only [hz, ite_self, zero_mul, le_refl]
  have ht := Finset.sum_le_sum hs
  simpa only [FiniteProcess.eventMass, Finset.sum_mul, historyExpectation] using ht

/-- The first-exit probability, with the crossing step included. -/
theorem first_exit_bound (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (r : ℕ) (M : ℝ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hcard : (J.card : ℝ) = (r : ℝ) * M)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (n β b : ℝ) (hn : 1 ≤ n) (hβ : 0 ≤ β) (hb : 0 ≤ b) (hβrate : β ≤ b / n)
    (hcodeg : ∀ e f, e ≠ f → CodegreeLoss.codegree I μ e f ≤ β)
    (extra : List (Option B) → Prop) (T : ℕ) (u : ℝ) (hu : 0 < u) :
    let Y := WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
      (StoppedPhysical.profile (2 * r) M)
    let K := WeightedGreedy.kernel I μ hμ J
      (fun h => StoppedPhysical.regular I μ J r M n β h ∧ (extra h ∧ Y h < u))
    FiniteProcess.eventMass K T (crossed Y u) ≤
      (WeightedGreedy.energy I μ J [] 1 + (T : ℝ) * (PhysicalDrift.noiseConstant r b / n)) / u := by
  let k := StoppedPhysical.profile (r - 1) M
  let factor := StoppedPhysical.profile (2 * r) M
  let Y := WeightedGreedy.stoppedEnergy I μ J k factor
  let base := fun h => StoppedPhysical.regular I μ J r M n β h ∧ extra h
  let K := WeightedGreedy.kernel I μ hμ J
    (fun h => StoppedPhysical.regular I μ J r M n β h ∧ (extra h ∧ Y h < u))
  have hkernel : K = WeightedGreedy.kernel I μ hμ J (fun h => base h ∧ Y h < u) := by
    have hg : (fun h => StoppedPhysical.regular I μ J r M n β h ∧ (extra h ∧ Y h < u)) =
        (fun h => base h ∧ Y h < u) := by
      funext h
      exact propext and_assoc.symm
    exact congrArg (WeightedGreedy.kernel I μ hμ J) hg
  have hwitness (h : List (Option B)) (hp : 0 < historyWeight K h) (hc : crossed Y u h) : u ≤ Y h := by
    apply crossing_retained I μ hμ J k factor base u h
    · change 0 < historyWeight (WeightedGreedy.kernel I μ hμ J (fun h => base h ∧ Y h < u)) h
      rw [← hkernel]
      exact hp
    · exact hc
  have hm := support_markov K T (crossed Y u) Y u
    (WeightedGreedy.stoppedEnergy_nonneg I μ J k factor
      (fun i => (StoppedPhysical.profile_bounds (2 * r) M i).1))
    hwitness
  have he := StoppedPhysical.expectation I μ hμ J r M hr hsize hcard hload
    n β b hn hβ hb hβrate hcodeg (fun h => extra h ∧ Y h < u) T
  exact (le_div_iff₀ hu).mpr (hm.trans he)

end KqR75.EnergyExit

#print axioms KqR75.EnergyExit.crossing_retained
#print axioms KqR75.EnergyExit.first_exit_bound
