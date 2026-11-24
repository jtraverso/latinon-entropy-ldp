module
public import SlotPairMargins

@[expose] public section

namespace KqR75.PhysicalCompletion

open Finset ColouredCliques CompleteJohnson SlotPairMargins

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The matrix equation on two-colour multisets. The component indexed by
`i, j` counts pairs of that type in the requested block histogram. -/
def ExactPairMargins {n q : ℕ} (colour : Fin n → C) (m : TypeProfile C q → ℤ) : Prop :=
  ∀ i j : C, (∑ t : TypeProfile C q,
    ((∏ c, (t.val c : ℕ).choose (demand i j c) : ℕ) : ℤ) * m t) =
    (cliques colour univ (demand i j) : ℤ)

/-- A component of the matrix equation applies to every physical edge of
the corresponding type. Conversely, each component is tested when every
colour class has at least two vertices. -/
theorem exactPairMargins_iff {n q : ℕ} (colour : Fin n → C)
    (m : TypeProfile C q → ℤ) (hclasses : ∀ c, 2 ≤ profile colour univ c) :
    ExactPairMargins colour m ↔
      ∀ e : Edge n, pairMargin colour (fun t => (m t : ℝ)) e =
        (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ) := by
  constructor
  · intro hm e
    obtain ⟨i, j, he⟩ := edge_profile_demand colour e
    have h := congrArg (fun a : ℤ => (a : ℝ)) (hm i j)
    simpa only [pairMargin, he, Int.cast_sum, Int.cast_mul, Int.cast_natCast] using h
  · intro hm i j
    obtain ⟨e, he⟩ := exists_edge_demand colour hclasses i j
    have h := hm e
    rw [pairMargin, he] at h
    exact_mod_cast h

end KqR75.PhysicalCompletion
