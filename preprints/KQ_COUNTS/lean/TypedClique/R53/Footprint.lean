/-
 R53.1: physical pair footprint of any finite set of >=2 vertices
 determines the vertex set. This is the missing "no parallel lifted
 hyperedges" input for Kq, q>=3.
-/
module
public import TypedClique.R52.Lift
@[expose] public section

namespace TypedClique.R53

open Finset

variable {V : Type*} [DecidableEq V]

def pairFootprint (Q : Finset V) : Finset (Finset V) :=
  Q.powersetCard 2

theorem pairFootprint_injective_of_two_le
    {Q₁ Q₂ : Finset V} (h₁ : 2 ≤ Q₁.card) (h₂ : 2 ≤ Q₂.card)
    (heq : pairFootprint Q₁ = pairFootprint Q₂) :
    Q₁ = Q₂ := by
  classical
  apply Finset.ext
  intro v
  constructor
  · intro hv
    have hcard : 1 < Fintype.card {u : V // u ∈ Q₁} := by
      simpa using h₁
    obtain ⟨w, hne⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨v, hv⟩
    have hvw : v ≠ w.1 := by
      intro h
      apply hne
      exact Subtype.ext h.symm
    have hp : ({v, w.1} : Finset V) ∈ pairFootprint Q₁ := by
      apply Finset.mem_powersetCard.mpr
      constructor
      · simp [hv, w.2]
      · exact Finset.card_pair hvw
    rw [heq] at hp
    exact ((Finset.mem_powersetCard.mp hp).1) (by simp)
  · intro hv
    have hcard : 1 < Fintype.card {u : V // u ∈ Q₂} := by
      simpa using h₂
    obtain ⟨w, hne⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨v, hv⟩
    have hvw : v ≠ w.1 := by
      intro h
      apply hne
      exact Subtype.ext h.symm
    have hp : ({v, w.1} : Finset V) ∈ pairFootprint Q₂ := by
      apply Finset.mem_powersetCard.mpr
      constructor
      · simp [hv, w.2]
      · exact Finset.card_pair hvw
    rw [← heq] at hp
    exact ((Finset.mem_powersetCard.mp hp).1) (by simp)

end TypedClique.R53
