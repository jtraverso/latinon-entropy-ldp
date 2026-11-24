module
public import KqCore
public import FiniteHistory

@[expose] public section
noncomputable section
namespace KqR75.FiniteProcess

open Finset LatinonEntropy

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Sum a conditional drift inequality on the actual finite history law.
The kernel is the published finite-history construction, not a stochastic axiom. -/
theorem drift_bound (K : FiniteKernel Ω) (Y : List Ω → ℝ) (b : ℕ → ℝ)
    (hstep : ∀ h, (∑ a, K.transition h a * Y (a :: h)) ≤ Y h + b h.length)
    (T : ℕ) :
    historyExpectation K T Y ≤ Y [] + ∑ s ∈ range T, b s := by
  induction T with
  | zero => simp [historyExpectation, histories, historyWeight]
  | succ t ih =>
    rw [historyExpectation_tower]
    calc
      _ ≤ historyExpectation K t (fun h => Y h + b t) := by
        apply historyExpectation_mono
        intro h hh
        simpa only [histories_length hh] using hstep h
      _ = historyExpectation K t Y + b t := by
        rw [historyExpectation_add, historyExpectation_const]
      _ ≤ (Y [] + ∑ s ∈ range t, b s) + b t := add_le_add ih le_rfl
      _ = _ := by rw [sum_range_succ]; ring

def eventMass (K : FiniteKernel Ω) (T : ℕ) (P : List Ω → Prop) : ℝ := by
  classical
  exact ∑ h ∈ histories Ω T, if P h then historyWeight K h else 0

/-- Finite Markov bound for an event witnessed by a nonnegative stopped value. -/
theorem event_markov (K : FiniteKernel Ω) (T : ℕ) (P : List Ω → Prop)
    (Y : List Ω → ℝ) (u : ℝ)
    (hY : ∀ h ∈ histories Ω T, 0 ≤ Y h)
    (hP : ∀ h ∈ histories Ω T, P h → u ≤ Y h) :
    eventMass K T P * u ≤ historyExpectation K T Y := by
  classical
  have hp (h : List Ω) (hh : h ∈ histories Ω T) :
      (if P h then historyWeight K h else 0) * u ≤ historyWeight K h * Y h := by
    split_ifs with hPh
    · exact mul_le_mul_of_nonneg_left (hP h hh hPh) (historyWeight_nonneg K h)
    · simpa only [zero_mul] using mul_nonneg (historyWeight_nonneg K h) (hY h hh)
  have hs := Finset.sum_le_sum hp
  simpa only [eventMass, Finset.sum_mul, historyExpectation] using hs

theorem event_bound_of_drift (K : FiniteKernel Ω) (T : ℕ) (P : List Ω → Prop)
    (Y : List Ω → ℝ) (b u : ℝ) (hu : 0 < u) (hinit : Y [] = 0)
    (hstep : ∀ h, (∑ a, K.transition h a * Y (a :: h)) ≤ Y h + b)
    (hY : ∀ h ∈ histories Ω T, 0 ≤ Y h)
    (hP : ∀ h ∈ histories Ω T, P h → u ≤ Y h) :
    eventMass K T P ≤ (T : ℝ) * b / u := by
  have he := drift_bound K Y (fun _ => b) hstep T
  simp only [hinit, zero_add, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at he
  exact (le_div_iff₀ hu).mpr ((event_markov K T P Y u hY hP).trans he)

end KqR75.FiniteProcess

#print axioms KqR75.FiniteProcess.drift_bound
#print axioms KqR75.FiniteProcess.event_markov
#print axioms KqR75.FiniteProcess.event_bound_of_drift
