/-
 R72 — P3 universal physical composition, still conditional on
 the actual coverdown/omniabsorber existence contracts.

 No asymptotic bank, reservoir or seed existence is assumed as an axiom.
-/
module
public import TypedClique.R69.SubsetsDivisible
@[expose] public section

namespace TypedClique.R72

open Finset

variable {Vertex : Type*} [DecidableEq Vertex]

/-- The edge footprint of a family of physical q-vertex cliques. -/
def footprint (P : Finset (Finset Vertex)) : Finset (Finset Vertex) :=
  P.biUnion fun Q => Q.powersetCard 2

/-- The full q-divisible remainder is obtained from an actual physical
 packing of q-cliques and a disjoint edge partition. This bridges R68
 to the R69 subset-divisibility predicate of the absorber. -/
theorem remnant_is_subset_divisible
    (q : ℕ) (used : Finset (Finset Vertex))
    (X Y full : Finset (Finset Vertex))
    (hsize : ∀ Q ∈ used, Q.card = q)
    (hpair : ∀ Q ∈ used, ∀ Q' ∈ used, Q ≠ Q' →
      Disjoint (Q.powersetCard 2) (Q'.powersetCard 2))
    (hpartition : footprint used ∪ (X \ Y) = full)
    (hdisjoint : Disjoint (footprint used) (X \ Y))
    (hwhole : TypedClique.R65.IsPairDivisible q full) :
    TypedClique.R69.IsPairSubsetDivisible q (X \ Y) := by
  have hused : TypedClique.R65.IsPairDivisible q (footprint used) :=
    TypedClique.R68.packing_divisible q used hsize hpair
  have hwhole' : TypedClique.R65.IsPairDivisible q
      (footprint used ∪ (X \ Y)) := by
    simpa only [hpartition] using hwhole
  have hrem : TypedClique.R65.IsPairDivisible q (X \ Y) :=
    TypedClique.R65.remainder_divisible_of_partition
      q (footprint used) (X \ Y) hdisjoint hwhole' hused
  exact (TypedClique.R69.subset_divisible_iff_signature q (X \ Y)).2 hrem

/-- A SINGLE preselected reserve X and omniabsorber A work for EVERY
 admissible packing P whenever the coverdown contract covers every P.
 The quantified conclusion does not choose X or A after P.
 This is an exact logical bridge, not an assertion of the coverdown
 or the absorber's asymptotic existence. -/
theorem universal_absorber_activated
    (q : ℕ)
    (Ps : Finset (Finset (Finset Vertex)))
    (full X A : Finset (Finset Vertex))
    (hwhole : TypedClique.R65.IsPairDivisible q full)
    (hcover : ∀ P ∈ Ps,
      ∃ (used : Finset (Finset Vertex)) (Y : Finset (Finset Vertex)),
        Y ⊆ X ∧
        (∀ Q ∈ used, Q.card = q) ∧
        (∀ Q ∈ used, ∀ Q' ∈ used, Q ≠ Q' →
          Disjoint (Q.powersetCard 2) (Q'.powersetCard 2)) ∧
        (footprint used ∪ (X \ Y) = full) ∧
        Disjoint (footprint used) (X \ Y))
    (hOmni : ∀ rem : Finset (Finset Vertex), rem ⊆ X →
      TypedClique.R69.IsPairSubsetDivisible q rem →
        ∃ QA : Finset (Finset Vertex), footprint QA = A ∪ rem) :
    ∀ P ∈ Ps,
      ∃ (used : Finset (Finset Vertex))
        (Y : Finset (Finset Vertex))
        (QA : Finset (Finset Vertex)),
        Y ⊆ X ∧ footprint QA = A ∪ (X \ Y) := by
  intro P hP
  obtain ⟨used, Y, hYX, hsize, hpair, hpartition, hdisjoint⟩ :=
    hcover P hP
  have hrem := remnant_is_subset_divisible q used X Y full
    hsize hpair hpartition hdisjoint hwhole
  obtain ⟨QA, hQA⟩ := hOmni (X \ Y) (Finset.sdiff_subset) hrem
  exact ⟨used, Y, QA, hYX, hQA⟩



/-- Physical recovery retains exactly the input prefix: every block in P
 is fully contained in J, whereas each new block has an edge outside J.
 This condition is guaranteed by coverdown (touches X), absorber (touches
 A or X), and bank swaps (touch B), when X,A,B are outside J. -/
theorem recover_prefix_of_external_blocks
    (J : Finset (Finset Vertex))
    (P Out : Finset (Finset Vertex))
    (hP : ∀ Q ∈ P, Q.powersetCard 2 ⊆ J)
    (hOut : ∀ Q ∈ Out, ¬ Q.powersetCard 2 ⊆ J) :
    ((P ∪ Out).filter fun Q => Q.powersetCard 2 ⊆ J) = P := by
  ext Q
  constructor
  · intro h
    have h' := Finset.mem_filter.mp h
    rcases Finset.mem_union.mp h'.1 with hP' | hOut'
    · exact hP'
    · exact False.elim ((hOut Q hOut') h'.2)
  · intro h
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_union.mpr (Or.inl h), hP Q h⟩

/-- Once every packing has an actual FULL design completed by only
 external-footprint blocks, its physical recovery left inverse exists
 uniformly over the entire family. No counting assumption is needed. -/
theorem universal_physical_completion_recovers
    (Ps Ds : Finset (Finset (Finset Vertex)))
    (J : Finset (Finset Vertex))
    (hcomplete : ∀ P ∈ Ps,
      ∃ Out : Finset (Finset Vertex),
        (P ∪ Out) ∈ Ds ∧
        (∀ Q ∈ P, Q.powersetCard 2 ⊆ J) ∧
        (∀ Q ∈ Out, ¬ Q.powersetCard 2 ⊆ J)) :
    ∀ P ∈ Ps, ∃ D ∈ Ds,
      (D.filter fun Q => Q.powersetCard 2 ⊆ J) = P := by
  intro P hP
  obtain ⟨Out, hD, hPin, hOut⟩ := hcomplete P hP
  exact ⟨P ∪ Out, hD, recover_prefix_of_external_blocks J P Out hPin hOut⟩

/-- The physical recovery supplied by P3 is exactly the precondition
 of the finite cardinal transfer theorem R63. -/
theorem universal_physical_completion_card
    (Ps Ds : Finset (Finset (Finset Vertex)))
    (J : Finset (Finset Vertex))
    (hcomplete : ∀ P ∈ Ps,
      ∃ Out : Finset (Finset Vertex),
        (P ∪ Out) ∈ Ds ∧
        (∀ Q ∈ P, Q.powersetCard 2 ⊆ J) ∧
        (∀ Q ∈ Out, ¬ Q.powersetCard 2 ⊆ J)) :
    Ps.card ≤ Ds.card := by
  apply TypedClique.R63.universal_completion_card_bound
    Ps Ds (fun D => D.filter fun Q => Q.powersetCard 2 ⊆ J)
  exact universal_physical_completion_recovers Ps Ds J hcomplete

end TypedClique.R72
