module
public import UpperExceptional

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset ColouredCliques CompleteJohnson SparseGram PhysicalCompletion

/-- A nonexceptional candidate through the test edge meets each true
block in at most one resource. In particular its other resources
have pairwise distinct owners and none has the test edge's owner. -/
theorem resources_inter_card_le_one {n q : ℕ} {P : Finset (Clique n q)}
    {e : Edge n} {c : Clique n q} (he : e ∈ resources n q c)
    (hc : c ∉ exceptional P e) {b : Clique n q} (hb : b ∈ P) :
    (resources n q b ∩ resources n q c).card ≤ 1 := by
  have hcnt : (b.val ∩ c.val).card ≤ 2 := by
    by_contra! h
    exact hc (mem_biUnion.mpr ⟨b, hb, mem_filter.mpr ⟨mem_univ _, he, h⟩⟩)
  apply card_le_one.mpr
  intro x hx y hy
  have hfix (u : Edge n) (hu : u ∈ resources n q b ∩ resources n q c) :
      u.val = b.val ∩ c.val := by
    refine eq_of_subset_of_card_le (subset_inter (mem_filter.mp (mem_inter.mp hu).1).2
      (mem_filter.mp (mem_inter.mp hu).2).2) ?_
    rwa [(mem_powersetCard.mp u.property).2]
  exact Subtype.ext ((hfix x hx).trans (hfix y hy).symm)

theorem exists_owner {n q : ℕ} {P : Finset (Clique n q)} (hP : packs P univ)
    (e : Edge n) : ∃ b, b ∈ P ∧ e ∈ resources n q b := by
  have h := hP e
  change (P.filter fun b => e ∈ resources n q b).card = _ at h
  simp only [mem_univ, ite_true] at h
  obtain ⟨b, hb⟩ := card_pos.mp (by omega :
    0 < (P.filter fun b => e ∈ resources n q b).card)
  exact ⟨b, mem_filter.mp hb⟩

/-- The owner of each physical edge in an exact packing. -/
noncomputable def owner {n q : ℕ} {P : Finset (Clique n q)} (hP : packs P univ)
    (e : Edge n) : Clique n q := Classical.choose (exists_owner hP e)

theorem owner_spec {n q : ℕ} {P : Finset (Clique n q)} (hP : packs P univ) (e : Edge n) :
    owner hP e ∈ P ∧ e ∈ resources n q (owner hP e) :=
  Classical.choose_spec (exists_owner hP e)

theorem owner_eq {n q : ℕ} {P : Finset (Clique n q)} (hP : packs P univ)
    (e : Edge n) (b : Clique n q) (hb : b ∈ P) (he : e ∈ resources n q b) :
    owner hP e = b := by
  have h := hP e
  change (P.filter fun b => e ∈ resources n q b).card = _ at h
  simp only [mem_univ, ite_true] at h
  exact card_le_one.mp h.le _ (mem_filter.mpr (owner_spec hP e)) _ (mem_filter.mpr ⟨hb, he⟩)

theorem injective_owners_of_nonexceptional {n q : ℕ} {P : Finset (Clique n q)}
    (hP : packs P univ) {e : Edge n} {c : Clique n q} (he : e ∈ resources n q c)
    (hc : c ∉ exceptional P e) : Set.InjOn (owner hP) (resources n q c : Set (Edge n)) := by
  intro x hx y hy hxy
  have hb := owner_spec hP x
  have hby := (owner_spec hP y).2
  rw [← hxy] at hby
  exact card_le_one.mp (resources_inter_card_le_one he hc hb.1) _
    (mem_inter.mpr ⟨hb.2, hx⟩) _ (mem_inter.mpr ⟨hby, hy⟩)

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.injective_owners_of_nonexceptional
