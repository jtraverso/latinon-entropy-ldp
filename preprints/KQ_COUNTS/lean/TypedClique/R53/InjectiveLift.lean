/-
 R53.2: no parallel lifted hyperedges whenever the physical footprint
 distinguishes blocks. The q-clique condition gives this from pairFootprint.
-/
module
public import TypedClique.R53.Footprint
@[expose] public section

namespace TypedClique.R53

open Finset

variable {Block Pair Color : Type*}
variable [DecidableEq Block] [DecidableEq Pair] [DecidableEq Color]
variable (footprint : Block → Finset Pair) (color : Block → Color)
variable (capacity : Color → ℕ)

/-- Physical block injectivity transfers to the tagged (pair + token) hyperedges. -/
theorem liftedSupport_injective_of_footprint
    (hfp : Function.Injective footprint) :
    Function.Injective (TypedClique.R52.liftedSupport footprint color capacity) := by
  intro c d hsup
  have hphys : footprint c.1 = footprint d.1 := by
    apply Finset.ext
    intro e
    constructor
    · intro he
      have hh := TypedClique.R52.physical_pair_mem footprint color capacity c e he
      rw [hsup] at hh
      simpa [TypedClique.R52.liftedSupport] using hh
    · intro he
      have hh := TypedClique.R52.physical_pair_mem footprint color capacity d e he
      rw [← hsup] at hh
      simpa [TypedClique.R52.liftedSupport] using hh
  have hblocks : c.1 = d.1 := hfp hphys
  cases c with
  | mk b i =>
    cases d with
    | mk b' j =>
      change b = b' at hblocks
      cases hblocks
      have htoken := TypedClique.R52.typed_token_mem footprint color capacity
        (⟨b, i⟩ : TypedClique.R52.Candidate color capacity)
      rw [hsup] at htoken
      have hj : i = j := by
        simpa [TypedClique.R52.liftedSupport] using htoken
      cases hj
      rfl

end TypedClique.R53
