/-
 R54.1: exact criterion for two lifted hyperedges to be disjoint.
 This supplies the converse to R52, making the token construction
 a finite combinatorial equivalence (not yet full geometric fiber count).
-/
module
public import TypedClique.R53.InjectiveLift
@[expose] public section

namespace TypedClique.R54

open Finset

variable {Block Pair Color : Type*}
variable [DecidableEq Block] [DecidableEq Pair] [DecidableEq Color]
variable (footprint : Block → Finset Pair) (color : Block → Color)
variable (capacity : Color → ℕ)

/-- Lifted hyperedges are disjoint precisely when their physical footprints
are disjoint AND their typed tokens differ. -/
theorem liftedSupport_disjoint_iff
    {c d : TypedClique.R52.Candidate color capacity} :
    Disjoint (TypedClique.R52.liftedSupport footprint color capacity c)
      (TypedClique.R52.liftedSupport footprint color capacity d) ↔
    Disjoint (footprint c.1) (footprint d.1) ∧
      (⟨color c.1, c.2⟩ : Σ i : Color, Fin (capacity i)) ≠
        ⟨color d.1, d.2⟩ := by
  constructor
  · intro h
    exact ⟨TypedClique.R52.disjoint_implies_footprints footprint color capacity h,
      TypedClique.R52.disjoint_implies_distinct_tokens footprint color capacity h⟩
  · rintro ⟨hphysical, htoken⟩
    apply Finset.disjoint_left.mpr
    intro x hx hy
    cases x with
    | inl e =>
      have hc : e ∈ footprint c.1 := by
        simpa [TypedClique.R52.liftedSupport] using hx
      have hd : e ∈ footprint d.1 := by
        simpa [TypedClique.R52.liftedSupport] using hy
      exact (Finset.disjoint_left.mp hphysical) hc hd
    | inr tok =>
      have hc : tok = (⟨color c.1, c.2⟩ :
          Σ i : Color, Fin (capacity i)) := by
        simpa [TypedClique.R52.liftedSupport] using hx
      have hd : tok = (⟨color d.1, d.2⟩ :
          Σ i : Color, Fin (capacity i)) := by
        simpa [TypedClique.R52.liftedSupport] using hy
      exact htoken (hc.symm.trans hd)

end TypedClique.R54
