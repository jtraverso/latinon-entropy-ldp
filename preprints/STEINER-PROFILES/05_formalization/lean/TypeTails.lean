module
public import FiniteProcess
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
noncomputable section
namespace KqR75.TypeTails

open Filter Finset LatinonEntropy
open scoped Topology

/-- A polynomial number of prefix and type tests fits any positive
error budget when each tail is exponentially small in a positive
power of the order. -/
theorem eventually_prefix_budget (k : ℕ) {C κ η ε : ℝ} (hκ : 0 < κ)
    (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (k : ℝ) * (C * (n : ℝ) ^ 2 + 1) * (2 * Real.exp (-κ * (n : ℝ) ^ η)) ≤ ε := by
  have hp := (tendsto_rpow_atTop hη).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hx := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 / η) κ hκ).comp hp
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-κ * (n : ℝ) ^ η))
      atTop (𝓝 0) := by
    refine hx.congr' ?_
    filter_upwards with n
    change ((n : ℝ) ^ η) ^ (2 / η) * Real.exp (-κ * (n : ℝ) ^ η) = _
    rw [← Real.rpow_mul (by positivity), mul_comm η (2 / η), div_mul_cancel₀ _ hη.ne', Real.rpow_two]
  have hb : Tendsto
      (fun n : ℕ => (2 * (k : ℝ) * (C + 1)) * ((n : ℝ) ^ 2 * Real.exp (-κ * (n : ℝ) ^ η)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim.const_mul (2 * (k : ℝ) * (C + 1))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hb.eventually (gt_mem_nhds hε)] with n hn h
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    _ ≤ (k : ℝ) * ((C + 1) * (n : ℝ) ^ 2) * (2 * Real.exp (-κ * (n : ℝ) ^ η)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith only [hn', sq_nonneg ((n : ℝ) - 1)]
    _ = (2 * (k : ℝ) * (C + 1)) * ((n : ℝ) ^ 2 * Real.exp (-κ * (n : ℝ) ^ η)) := by ring
    _ ≤ _ := h.le

/-- A finite union bound for events on the same physical history
law, with the index set kept explicit. -/
theorem eventMass_exists_le {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (S : Finset I) (P : I → List Ω → Prop) :
    FiniteProcess.eventMass K T (fun h => ∃ j ∈ S, P j h) ≤
      ∑ j ∈ S, FiniteProcess.eventMass K T (P j) := by
  classical
  unfold FiniteProcess.eventMass
  rw [sum_comm]
  apply sum_le_sum
  intro h _
  by_cases he : ∃ j ∈ S, P j h
  · obtain ⟨j, hj, hp⟩ := he
    have hsum := single_le_sum (f := fun i => if P i h then historyWeight K h else 0)
      (fun i _ => by split_ifs; exacts [historyWeight_nonneg K h, le_rfl]) hj
    simpa only [ite_eq_left (show ∃ j ∈ S, P j h from ⟨j, hj, hp⟩), ite_eq_left hp] using hsum
  · rw [ite_eq_right he]
    exact sum_nonneg (fun i _ => by split_ifs; exacts [historyWeight_nonneg K h, le_rfl])

/-- Simultaneous good tests lose at most the sum of their failure
budgets on the common law. -/
theorem eventMass_all_ge {Ω I : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (S : Finset I) (P : I → List Ω → Prop) :
    1 - (∑ j ∈ S, FiniteProcess.eventMass K T (fun h => ¬P j h)) ≤
      FiniteProcess.eventMass K T (fun h => ∀ j ∈ S, P j h) := by
  classical
  have htot : FiniteProcess.eventMass K T (fun h => ∀ j ∈ S, P j h) +
      FiniteProcess.eventMass K T (fun h => ∃ j ∈ S, ¬P j h) = 1 := by
    unfold FiniteProcess.eventMass
    rw [← sum_add_distrib]
    calc
      _ = historyExpectation K T (fun _ => 1) := by
        unfold historyExpectation
        apply sum_congr rfl
        intro h _
        by_cases hh : ∀ j ∈ S, P j h
        · have hn : ¬∃ j ∈ S, ¬P j h := fun ⟨j, hj, hnj⟩ => hnj (hh j hj)
          simp [hn]
        · obtain ⟨j, hj⟩ := not_forall.mp hh
          obtain ⟨hjS, hjP⟩ := not_imp.mp hj
          have he : ∃ j ∈ S, ¬P j h := ⟨j, hjS, hjP⟩
          simp [hh, he]
      _ = 1 := historyExpectation_const K T 1
  have hbad := eventMass_exists_le K T S (fun j h => ¬P j h)
  linarith only [hbad, htot]

private theorem eventMass_indicator {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (P : List Ω → Prop) [DecidablePred P] :
    FiniteProcess.eventMass K T P =
      historyExpectation K T (fun h => if P h then 1 else 0) := by
  classical
  unfold FiniteProcess.eventMass historyExpectation
  apply sum_congr rfl
  intro h _
  by_cases hp : P h <;> simp [hp]

/-- A prefix read from a longer reverse history has exactly its original
law. This puts all prefix tests on the one terminal probability space. -/
theorem eventMass_drop {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T k : ℕ) (P : List Ω → Prop) :
    FiniteProcess.eventMass K (T + k) (fun h => P (h.drop k)) =
      FiniteProcess.eventMass K T P := by
  classical
  simp only [eventMass_indicator]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, historyExpectation_tower, ← ih]
    congr 1
    funext h
    simp only [List.drop_succ_cons]
    rw [← sum_mul, K.total, one_mul]

end KqR75.TypeTails

#print axioms KqR75.TypeTails.eventually_prefix_budget
#print axioms KqR75.TypeTails.eventMass_exists_le
#print axioms KqR75.TypeTails.eventMass_all_ge
#print axioms KqR75.TypeTails.eventMass_drop
