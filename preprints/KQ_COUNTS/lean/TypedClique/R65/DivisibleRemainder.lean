/-
 R65: the q-divisibility residue signature is additive under
 disjoint union. This is the finite graph-arithmetic adapter
 required to use an omniabsorber on X \\ Y after coverdown.

 It does not assert the existence of X, A, bank B or of a design.
-/
module
public import TypedClique.R64.Preallocation
@[expose] public section

namespace TypedClique.R65

open Finset

variable {Vertex : Type*} [DecidableEq Vertex]

/-- q-divisibility of an abstract graph (as a set of pairs):
  total edge count is 0 modulo choose(q,2), and every
  vertex degree is 0 modulo q-1. Every edge is understood
  to be a 2-subset, as in the clique setting. -/
def IsPairDivisible (q : ℕ) (E : Finset (Finset Vertex)) : Prop :=
  (∑ e ∈ E, (1 : ZMod (Nat.choose q 2))) = 0 ∧
  (∀ v : Vertex,
    (∑ e ∈ E, if v ∈ e then (1 : ZMod (q - 1)) else 0) = 0)

/-- With disjoint physical edge sets, if the complete graph and
 the already decomposed resources have q-divisible signatures,
 the remainder automatically has q-divisible signature.
 Neither the original reserve nor the greedy residual needs
 to satisfy divisibility separately. -/
theorem remainder_divisible_of_partition
    (q : ℕ) (used remainder : Finset (Finset Vertex))
    (hdisjoint : Disjoint used remainder)
    (hwhole : IsPairDivisible q (used ∪ remainder))
    (hused : IsPairDivisible q used) :
    IsPairDivisible q remainder := by
  rcases hwhole with ⟨hcount, hdeg⟩
  rcases hused with ⟨hcountUsed, hdegUsed⟩
  constructor
  · rw [Finset.sum_union hdisjoint, hcountUsed] at hcount
    simpa using hcount
  · intro v
    have hv := hdeg v
    rw [Finset.sum_union hdisjoint, hdegUsed v] at hv
    simpa using hv

end TypedClique.R65
