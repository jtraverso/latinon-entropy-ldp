/-
 R67: every physical K_q has q-divisible edge signature.

 This supplies the missing 'resources are divisible because they
 decompose into cliques' premise behind R65/R66 and the DP
 omniabsorber interface. The pair-edge footprint uses powersetCard 2.
-/
module
public import TypedClique.R66.DivisibleUnion
@[expose] public section

namespace TypedClique.R67

open Finset

variable {Vertex : Type*} [DecidableEq Vertex]

/-- A physical Kq block has total edge count divisible by choose(q,2)
 and every vertex degree divisible by q-1. -/
theorem clique_divisible
    (q : ℕ) (Q : Finset Vertex) (hQ : Q.card = q) :
    TypedClique.R65.IsPairDivisible q (Q.powersetCard 2) := by
  classical
  have hcount : (Q.powersetCard 2).card = Nat.choose q 2 := by
    simp [hQ]
  constructor
  · simp [Finset.sum_const, hcount]
  · intro v
    by_cases hv : v ∈ Q
    · have hs : ({v} : Finset Vertex) ⊆ Q := by
        simpa using hv
      have hct := Finset.card_filter_powersetCard_subset
        ({v} : Finset Vertex) Q 2 hs (by simp)
      have hcard :
          ((Q.powersetCard 2).filter (fun e => v ∈ e)).card = q - 1 := by
        simpa [hQ] using hct
      have hsum :
          (∑ e ∈ Q.powersetCard 2,
            if v ∈ e then (1 : ZMod (q - 1)) else 0) =
          ((Q.powersetCard 2).filter (fun e => v ∈ e)).card := by
        simp [Finset.sum_filter]
      rw [hsum, hcard]
      simp
    · have hnot : ∀ e ∈ Q.powersetCard 2, v ∉ e := by
        intro e he heV
        exact hv ((Finset.mem_powersetCard.mp he).1 heV)
      have hzero :
          ((Q.powersetCard 2).filter (fun e => v ∈ e)) = ∅ := by
        ext e
        constructor
        · intro he
          exact False.elim ((hnot e (Finset.mem_filter.mp he).1)
            (Finset.mem_filter.mp he).2)
        · intro he
          exact False.elim (Finset.not_mem_empty e he)
      simp [hzero]

end TypedClique.R67
