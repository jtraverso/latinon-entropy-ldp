/-
 R51.2: finite typewise token assignment counts.
 Mathlib already proves that injective choices from Fin t to Fin a
 are the falling factorial a.descFactorial t. The combined product is
 a product of cardinalities, without asserting a geometric fiber equivalence.
-/
module
public import TypedClique.R51.Bernoulli
@[expose] public section

namespace TypedClique.R51

open Finset

/-- Number of injective assignments of t labeled blocks to a labeled tokens. -/
theorem token_fibre_card (t a : ℕ) :
    Fintype.card (Fin t ↪ Fin a) = a.descFactorial t := by
  classical
  simp

/-- Fiber cardinalities multiply when tokens are separated by a finite
family of types. This is the multiplicative factor needed in R46.A. -/
theorem typewise_token_fibre_card
    {I : Type*} [Fintype I] (t a : I → ℕ) :
    (∏ i : I, Fintype.card (Fin (t i) ↪ Fin (a i))) =
    ∏ i : I, (a i).descFactorial (t i) := by
  classical
  simp

end TypedClique.R51
