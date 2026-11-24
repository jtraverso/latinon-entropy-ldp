module
public import PrefixCountFromLog
public import CorrectedCompletion

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Finset LatinonEntropy CompleteJohnson ColouredCliques SparseGram WeightedGreedy

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Labelled clique decompositions with the specified integer counts
of each block type, in the same edge universe as the greedy process. -/
noncomputable def designFibre {n q : ℕ} (colour : Fin n → C) (m : TypeProfile C q → ℤ) :
    Finset (Finset (Clique n q)) := by
  classical
  exact univ.filter fun P => packs P univ ∧
    ∀ t, BankCapacity.integerHistogram colour P t = m t

theorem mem_designFibre {n q : ℕ} (colour : Fin n → C) (m : TypeProfile C q → ℤ)
    (P : Finset (Clique n q)) : P ∈ designFibre colour m ↔
      packs P univ ∧ ∀ t, BankCapacity.integerHistogram colour P t = m t := by
  classical
  simp only [designFibre, mem_filter, mem_univ, true_and]

/-- Convert the good-history exponent to a lower bound for the exact
physical design fibre. Each history may supply any recovering completion. -/
theorem log_designFibre_of_good_histories {n q : ℕ} (hq : 2 ≤ q)
    (colour : Fin n → C) (m : TypeProfile C q → ℤ) (J : Finset (Edge n))
    (K : FiniteKernel (Option (Clique n q))) (T : ℕ)
    (good : List (Option (Clique n q)) → Prop) (Q : ℝ)
    (hmass : (1 : ℝ) / 2 ≤ FiniteProcess.eventMass K T good)
    (hgood : ∀ h ∈ histories (Option (Clique n q)) T, good h → 0 < historyWeight K h →
      valid (resources n q) J h ∧ none ∉ h ∧
        (∃ P : Finset (Clique n q), packs P univ ∧
          (∀ t, BankCapacity.integerHistogram colour P t = m t) ∧
          P.filter (fun b => resources n q b ⊆ J) = picked h) ∧
        Real.log (historyWeight K h) + Real.log (T.factorial : ℝ) ≤ Q) :
    0 < (designFibre colour m).card ∧
      -Q - Real.log 2 ≤ Real.log ((designFibre colour m).card : ℝ) := by
  classical
  let A := fun h : List (Option (Clique n q)) => ∃ P : Finset (Clique n q),
    P ∈ designFibre colour m ∧ P.filter (fun b => resources n q b ⊆ J) = picked h
  let complete := fun h => if hs : A h then Classical.choose hs else ∅
  refine log_outputs_of_history_score (resources n q) J ?_ K T good _ complete Q hmass ?_
  · intro b
    apply card_pos.mp
    rw [resources_card]
    exact Nat.choose_pos hq
  · intro h hh hg hp
    obtain ⟨hv, hn, ⟨P, hP, hm, hrec⟩, hlog⟩ := hgood h hh hg hp
    have hs : A h := ⟨P, (mem_designFibre colour m P).mpr ⟨hP, hm⟩, hrec⟩
    have ht := Classical.choose_spec hs
    refine ⟨hv, hn, ?_, ?_, hlog⟩
    · simpa only [complete, dif_pos hs] using ht.1
    · simpa only [complete, dif_pos hs] using ht.2

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.log_designFibre_of_good_histories
