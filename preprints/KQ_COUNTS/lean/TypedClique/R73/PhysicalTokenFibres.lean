/- R73: physical type token fibres are falling factorials. -/
module
public import TypedClique.R73.ExpectedDegrees
@[expose] public section
namespace TypedClique.R73
open Finset
variable {Block Color : Type*} [DecidableEq Block]

theorem physical_type_fibre_card (P : Finset Block) (a : ℕ) :
    Fintype.card ({b : Block // b ∈ P} ↪ Fin a) =
      a.descFactorial P.card := by
  classical
  simpa using
    (Fintype.card_embedding_eq (α := {b : Block // b ∈ P}) (β := Fin a))

theorem physical_typewise_fibre_card
    [Fintype Color] (byType : Color → Finset Block) (capacity : Color → ℕ) :
    (∏ i : Color, Fintype.card
        ({b : Block // b ∈ byType i} ↪ Fin (capacity i))) =
      (∏ i : Color, (capacity i).descFactorial (byType i).card) := by
  classical
  apply Finset.prod_congr rfl
  intro i _
  exact physical_type_fibre_card (byType i) (capacity i)
end TypedClique.R73
