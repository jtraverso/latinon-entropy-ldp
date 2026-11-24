module
public import UpperOwners

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset ColouredCliques CompleteJohnson SparseGram PhysicalCompletion

/-- A test edge is active if its true block has not been revealed at an
earlier edge in the fixed order. -/
def active {n q : ℕ} {P : Finset (Clique n q)} (hP : packs P univ)
    (key : Edge n → ℕ) (e : Edge n) : Prop :=
  ∀ f ∈ resources n q (owner hP e), key e ≤ key f

theorem inactive_owner_fixed {n q : ℕ} {P Q : Finset (Clique n q)}
    (hP : packs P univ) (hQ : packs Q univ) (key : Edge n → ℕ) (e : Edge n)
    (hag : ∀ g, key g < key e → owner hQ g = owner hP g)
    (hact : ¬ active hP key e) : owner hQ e = owner hP e := by
  have hex : ∃ f ∈ resources n q (owner hP e), key f < key e := by
    by_contra! hn
    exact hact hn
  obtain ⟨f, hf, hlt⟩ := hex
  have heq := (hag f hlt).trans (owner_eq hP f _ (owner_spec hP e).1 hf)
  have hm := (owner_spec hQ f).1
  rw [heq] at hm
  exact owner_eq hQ e _ hm (owner_spec hP e).2

private theorem true_candidate_is_exceptional {n q : ℕ} (hq : 3 ≤ q)
    {P : Finset (Clique n q)} {e : Edge n} {b : Clique n q}
    (hP : b ∈ P) (he : e ∈ resources n q b) : b ∈ exceptional P e := by
  apply mem_biUnion.mpr
  refine ⟨b, hP, mem_filter.mpr ⟨mem_univ _, he, ?_⟩⟩
  rwa [inter_self, (mem_powersetCard.mp b.property).2]

/-- For an available nonexceptional candidate, every edge in the true
owner of each candidate resource is still at or after the test edge. -/
theorem available_owner_late {n q : ℕ} (hq : 3 ≤ q) {P Q : Finset (Clique n q)}
    (hP : packs P univ) (hQ : packs Q univ) (key : Edge n → ℕ) (e : Edge n)
    (hag : ∀ g, key g < key e → owner hQ g = owner hP g)
    (hc : owner hQ e ∉ exceptional P e)
    {f g : Edge n} (hf : f ∈ resources n q (owner hQ e))
    (hg : g ∈ resources n q (owner hP f)) : key e ≤ key g := by
  by_contra! hlt
  have heq := (hag g hlt).trans (owner_eq hP g _ (owner_spec hP f).1 hg)
  have hm := (owner_spec hQ g).1
  rw [heq] at hm
  have htrue : owner hQ e = owner hP f :=
    (owner_eq hQ f _ (owner_spec hQ e).1 hf).symm.trans
      (owner_eq hQ f _ hm (owner_spec hP f).2)
  exact hc (true_candidate_is_exceptional hq (htrue.symm ▸ (owner_spec hP f).1)
    (owner_spec hQ e).2)

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.inactive_owner_fixed
#print axioms KqR75.UpperCounting.available_owner_late
