/-
 R68: every edge-disjoint packing of physical Kq cliques is q-divisible.
 This transports the individual-clique theorem R67 to arbitrary packings,
 via disjoint union additivity R66, without postulating divisibility.

 Finite arithmetic result; no universal asymptotic existence claim.
-/
module
public import TypedClique.R67.CliqueDivisible
@[expose] public section

namespace TypedClique.R68

open Finset

variable {Vertex : Type*} [DecidableEq Vertex]

/-- A finite family of q-cliques with pairwise disjoint edge footprints
 has q-divisible total physical footprint. -/
theorem packing_divisible
    (q : ℕ) (P : Finset (Finset Vertex))
    (hsize : ∀ Q ∈ P, Q.card = q)
    (hpair : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' →
      Disjoint (Q.powersetCard 2) (Q'.powersetCard 2)) :
    TypedClique.R65.IsPairDivisible q
      (P.biUnion fun Q => Q.powersetCard 2) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      simpa using (TypedClique.R66.empty_divisible (Vertex := Vertex) q)
  | @insert Q P hQ ih =>
      have hsizeP : ∀ B ∈ P, B.card = q := by
        intro B hB
        exact hsize B (Finset.mem_insert_of_mem hB)
      have hpairP : ∀ B ∈ P, ∀ C ∈ P, B ≠ C →
          Disjoint (B.powersetCard 2) (C.powersetCard 2) := by
        intro B hB C hC hBC
        exact hpair B (Finset.mem_insert_of_mem hB)
          C (Finset.mem_insert_of_mem hC) hBC
      have hQdiff : ∀ B ∈ P, Disjoint (Q.powersetCard 2) (B.powersetCard 2) := by
        intro B hB
        have hne : Q ≠ B := by
          intro h
          exact hQ (h ▸ hB)
        exact hpair Q (Finset.mem_insert_self Q P)
          B (Finset.mem_insert_of_mem hB) hne
      have hdisjoint :
          Disjoint (Q.powersetCard 2)
            (P.biUnion fun B => B.powersetCard 2) := by
        apply (Finset.disjoint_biUnion_right _ _ _).2
        exact hQdiff
      rw [Finset.biUnion_insert]
      apply TypedClique.R66.union_divisible q
        (Q.powersetCard 2)
        (P.biUnion fun B => B.powersetCard 2)
        hdisjoint
      · exact TypedClique.R67.clique_divisible q Q (hsize Q (Finset.mem_insert_self Q P))
      · exact ih hsizeP hpairP

end TypedClique.R68
