/-
 R52: a physical block plus one labeled token is a hyperedge whose
 vertices are tagged physical pairs or a typed token.
 Proves the geometric projection obligations of R46.A.
 This does NOT assert a bijection/counting formula or GJKKL regularity.
-/
module
public import TypedClique.R51.TokenFibres
@[expose] public section

namespace TypedClique.R52

open Finset

variable {Block Pair Color : Type*}
variable [DecidableEq Block] [DecidableEq Pair] [DecidableEq Color]
variable (footprint : Block → Finset Pair) (color : Block → Color)
variable (capacity : Color → ℕ)

/-- One physical block with an allowed labeled token of its type. -/
abbrev Candidate := Σ b : Block, Fin (capacity (color b))

/-- The lifted hyperedge uses all physical pairs plus one typed token. -/
def liftedSupport (c : Candidate color capacity) :
    Finset (Sum Pair (Σ i : Color, Fin (capacity i))) :=
  (footprint c.1).image Sum.inl ∪ {Sum.inr ⟨color c.1, c.2⟩}

theorem physical_pair_mem (c : Candidate color capacity) (e : Pair)
    (he : e ∈ footprint c.1) :
    (Sum.inl e : Sum Pair (Σ i : Color, Fin (capacity i))) ∈
      liftedSupport footprint color capacity c := by
  simp [liftedSupport, he]

theorem typed_token_mem (c : Candidate color capacity) :
    (Sum.inr ⟨color c.1, c.2⟩ :
      Sum Pair (Σ i : Color, Fin (capacity i))) ∈
      liftedSupport footprint color capacity c := by
  simp [liftedSupport]

/-- Disjoint lifted edges cannot reuse any physical pair. -/
theorem disjoint_implies_footprints {c d : Candidate color capacity}
    (h : Disjoint (liftedSupport footprint color capacity c)
      (liftedSupport footprint color capacity d)) :
    Disjoint (footprint c.1) (footprint d.1) := by
  apply Finset.disjoint_left.mpr
  intro e hce hde
  exact (Finset.disjoint_left.mp h)
    (physical_pair_mem footprint color capacity c e hce)
    (physical_pair_mem footprint color capacity d e hde)

/-- Disjoint lifted edges cannot reuse the same typed token. -/
theorem disjoint_implies_distinct_tokens {c d : Candidate color capacity}
    (h : Disjoint (liftedSupport footprint color capacity c)
      (liftedSupport footprint color capacity d)) :
    (⟨color c.1, c.2⟩ : Σ i : Color, Fin (capacity i)) ≠
      ⟨color d.1, d.2⟩ := by
  intro ht
  have htc := typed_token_mem footprint color capacity c
  have htd := typed_token_mem footprint color capacity d
  rw [← ht] at htd
  exact (Finset.disjoint_left.mp h) htc htd

/-- In a matching of lifted edges, no two candidates may use the
same physical block when every block has at least one physical pair. -/
theorem matching_unique_block
    (S : Finset (Candidate color capacity))
    (hMatch : ∀ c ∈ S, ∀ d ∈ S, c ≠ d →
      Disjoint (liftedSupport footprint color capacity c)
        (liftedSupport footprint color capacity d))
    (hNonempty : ∀ b, (footprint b).Nonempty)
    {c d : Candidate color capacity} (hc : c ∈ S) (hd : d ∈ S)
    (hBlock : c.1 = d.1) : c = d := by
  by_contra hneq
  have hfp := disjoint_implies_footprints footprint color capacity
    (hMatch c hc d hd hneq)
  rw [hBlock] at hfp
  obtain ⟨e, he⟩ := hNonempty d.1
  exact (Finset.disjoint_left.mp hfp) he he

/-- Projection of a lifted matching is a genuine physical pair-packing. -/
theorem matching_projects_to_packing
    (S : Finset (Candidate color capacity))
    (hMatch : ∀ c ∈ S, ∀ d ∈ S, c ≠ d →
      Disjoint (liftedSupport footprint color capacity c)
        (liftedSupport footprint color capacity d))
    {c d : Candidate color capacity} (hc : c ∈ S) (hd : d ∈ S)
    (hBlock : c.1 ≠ d.1) :
    Disjoint (footprint c.1) (footprint d.1) := by
  have hcd : c ≠ d := by
    intro h
    exact hBlock (congrArg Sigma.fst h)
  exact disjoint_implies_footprints footprint color capacity
    (hMatch c hc d hd hcd)

end TypedClique.R52
