module
public import UpperWeightedReveal

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset ColouredCliques CompleteJohnson SparseGram PhysicalCompletion

private theorem disjoint_owners {n q : ℕ} (P : FullPacking n q) {e f : Edge n}
    (h : owner P.property e ≠ owner P.property f) :
    Disjoint (resources n q (owner P.property e)) (resources n q (owner P.property f)) := by
  apply disjoint_left.mpr
  intro g hg hg'
  exact h ((owner_eq P.property g _ (owner_spec P.property e).1 hg).symm.trans
    (owner_eq P.property g _ (owner_spec P.property f).1 hg'))

open scoped Classical

/-- The activity test uses r-1 other edges and the availability test
of an ordinary candidate uses r(r-1) edges disjoint from the entire
true block of the test edge. -/
theorem required_edges_of_nonexceptional {n q : ℕ} (P : FullPacking n q)
    (e : Edge n) (c : Clique n q) (he : e ∈ resources n q c) (hc : c ∉ exceptional P.val e) :
    (requiredEdges P e c).card = (q.choose 2 - 1) * q.choose 2 ∧
      Disjoint (requiredEdges P e c) (resources n q (owner P.property e)) := by
  classical
  let I := (resources n q c).erase e
  let R (f : Edge n) := resources n q (owner P.property f)
  have hi := injective_owners_of_nonexceptional P.property he hc
  have hd : Set.PairwiseDisjoint (I : Set (Edge n)) R := by
    intro f hf g hg hne
    exact disjoint_owners P (fun h => hne (hi (mem_of_mem_erase hf) (mem_of_mem_erase hg) h))
  constructor
  · change (I.biUnion R).card = _
    rw [card_biUnion hd]
    simp only [R, resources_card, sum_const, Nat.nsmul_eq_mul, I, card_erase_of_mem he]
  · apply disjoint_left.mpr
    intro g hg hge
    obtain ⟨f, hf, hgf⟩ := mem_biUnion.mp hg
    have hd' := disjoint_owners P
      (fun heq => (ne_of_mem_erase hf) (hi (mem_of_mem_erase hf) he heq))
    exact disjoint_left.mp hd' hgf hge

/-- Every block contributes precisely one active coordinate, so the
reference score can be summed over the blocks of the design. -/
theorem active_reference_score {n q : ℕ} (hq : 2 ≤ q) (P : FullPacking n q)
    (key : Edge n → ℕ) (hkey : Function.Injective key) (w : Clique n q → ℝ) :
    (∑ e : Edge n, if active P.property key e then Real.log (w (owner P.property e)) else 0) =
      ∑ b ∈ P.val, Real.log (w b) := by
  classical
  rw [← sum_filter]
  apply sum_bij (fun e _ => owner P.property e)
  · intro e _
    exact (owner_spec P.property e).1
  · intro e he f hf heq
    have hae := (mem_filter.mp he).2
    have haf := (mem_filter.mp hf).2
    apply hkey
    have h₁ := (owner_spec P.property f).2
    have h₂ := (owner_spec P.property e).2
    rw [← heq] at h₁
    rw [heq] at h₂
    exact le_antisymm (hae f h₁) (haf e h₂)
  · intro b hb
    have hne : (resources n q b).Nonempty := by
      apply card_pos.mp
      rw [resources_card]
      exact Nat.choose_pos hq
    obtain ⟨e, he, hmin⟩ := (resources n q b).exists_min_image key hne
    have heq := owner_eq P.property e b hb he
    refine ⟨e, mem_filter.mpr ⟨mem_univ _, ?_⟩, heq⟩
    simpa only [active, heq] using hmin
  · intro e _
    rfl

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.required_edges_of_nonexceptional
#print axioms KqR75.UpperCounting.active_reference_score
