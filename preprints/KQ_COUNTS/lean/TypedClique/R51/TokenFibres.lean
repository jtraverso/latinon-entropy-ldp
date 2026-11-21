/-
 R51.2: number of token assignments of each type.
 The R46.A fibers are injections from the blocks of a given type to
 its available labeled tokens. No probability is involved in this count.
-/
module
public import TypedClique.R51.Bernoulli
@[expose] public section

namespace TypedClique.R51

open Finset

/-- For t blocks and a labeled tokens, the number of injective assignments
is the descending factorial (a)_t, also when t > a (both sides zero). -/
theorem token_fibre_card (t a : ℕ) :
    Fintype.card (Fin t ↪ Fin a) = a.descFactorial t := by
  classical
  simp

/-- Independent token choices in finitely many types multiply their fiber counts. -/
theorem typewise_token_fibre_card
    {I : Type*} [Fintype I] (t a : I → ℕ) :
    Fintype.card (∀ i : I, Fin (t i) ↪ Fin (a i)) =
    ∏ i : I, (a i).descFactorial (t i) := by
  classical
  simp

end TypedClique.R51
