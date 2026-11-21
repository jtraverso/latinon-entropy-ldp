/-
 R66: additivity of the physical edge-count and vertex-degree
 q-divisibility signatures for disjoint unions of resources.

 These are genuine edge-finset lemmas connecting the coverdown
 arithmetic to the omniabsorber contract. They do not assume
 existence of the reservoir, bank or absorber.
-/
module
public import TypedClique.R65.DivisibleRemainder
@[expose] public section

namespace TypedClique.R66

open Finset

variable {Vertex : Type*} [DecidableEq Vertex]

/-- The empty edge set is q-divisible for every q. -/
theorem empty_divisible (q : ℕ) :
    TypedClique.R65.IsPairDivisible q (∅ : Finset (Finset Vertex)) := by
  simp [TypedClique.R65.IsPairDivisible]

/-- q-divisibility is preserved by edge-disjoint unions. -/
theorem union_divisible (q : ℕ)
    (E F : Finset (Finset Vertex))
    (hdisjoint : Disjoint E F)
    (hE : TypedClique.R65.IsPairDivisible q E)
    (hF : TypedClique.R65.IsPairDivisible q F) :
    TypedClique.R65.IsPairDivisible q (E ∪ F) := by
  rcases hE with ⟨hcountE, hdegE⟩
  rcases hF with ⟨hcountF, hdegF⟩
  constructor
  · rw [Finset.sum_union hdisjoint, hcountE, hcountF]
    simp
  · intro v
    rw [Finset.sum_union hdisjoint, hdegE v, hdegF v]
    simp

end TypedClique.R66
