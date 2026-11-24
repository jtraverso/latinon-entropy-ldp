module
public import UpperReveal
public import WeightedChain

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset ColouredCliques CompleteJohnson SparseGram PhysicalCompletion LatinonEntropy

open scoped Classical

/-- Vertices of the entropy encoding are exact packings of all edges. -/
abbrev FullPacking (n q : ℕ) := {P : Finset (Clique n q) // packs P univ}

/-- Edges of the true owner blocks of the candidate resources other
than the test edge. -/
def requiredEdges {n q : ℕ} (P : FullPacking n q) (e : Edge n) (c : Clique n q) :
    Finset (Edge n) :=
  ((resources n q c).erase e).biUnion (fun f => resources n q (owner P.property f))

/-- A superset of the values that are still available at an active
coordinate. Exceptional candidates are retained without restrictions. -/
noncomputable def availableCandidates {n q : ℕ} (P : FullPacking n q) (key : Edge n → ℕ)
    (e : Edge n) : Finset (Clique n q) := by
  classical
  exact univ.filter fun c => e ∈ resources n q c ∧
    (c ∈ exceptional P.val e ∨ ∀ g ∈ requiredEdges P e c, key e ≤ key g)

private theorem owner_code_injective {n q : ℕ} (hq : 2 ≤ q) {P Q : FullPacking n q}
    (heq : ∀ e : Edge n, owner P.property e = owner Q.property e) : P = Q := by
  have hsub (A B : FullPacking n q)
      (h : ∀ e : Edge n, owner A.property e = owner B.property e) : A.val ⊆ B.val := by
    intro b hb
    have hp : 0 < (resources n q b).card := by rw [resources_card]; exact Nat.choose_pos hq
    obtain ⟨e, he⟩ := card_pos.mp hp
    rw [← owner_eq A.property e b hb he, h e]
    exact (owner_spec B.property e).1
  exact Subtype.ext (Subset.antisymm (hsub P Q heq) (hsub Q P (fun e => (heq e).symm)))

/-- Weighted chain rule for one order of the physical edges. An already
determined coordinate contributes zero, and the available reference
mass is bounded by the candidates and owner constraints above. -/
theorem weighted_reveal_bound {n q : ℕ} (hq : 3 ≤ q) (S : Finset (FullPacking n q))
    (hS : S.Nonempty) (key : Edge n → ℕ) (hkey : Function.Injective key)
    (w : Clique n q → ℝ) (hw : ∀ b, 0 ≤ w b)
    (hwpos : ∀ P ∈ S, ∀ b ∈ P.val, 0 < w b) :
    (S.card : ℝ) * Real.log S.card ≤ ∑ P ∈ S, ∑ e : Edge n,
      if active P.property key e then
        Real.log (∑ b ∈ availableCandidates P key e, w b) - Real.log (w (owner P.property e))
      else 0 := by
  classical
  let f (e : Edge n) (P : FullPacking n q) := owner P.property e
  let a (e : Edge n) (P : FullPacking n q) := availableReference S univ key f (fun _ => w) e P
  have hchain := weighted_chain_bound key f (fun _ => (1 : ℝ)) (fun _ => w) univ S
    (fun _ _ _ _ h => hkey h)
    (fun P _ Q _ h => owner_code_injective (by omega) (fun e => h e (mem_univ _)))
    hS (fun _ _ => zero_lt_one) (fun e _ P hP => hwpos P hP _ (owner_spec P.property e).1)
  simp only [weightedFamilyEntropy, sum_const, nsmul_eq_mul, mul_one, Real.log_one,
    one_mul, mul_zero, sub_zero] at hchain
  refine hchain.trans (sum_le_sum (fun P hP => sum_le_sum (fun e _ => ?_)))
  change Real.log (a e P) - Real.log (w (f e P)) ≤ _
  have hself : f e P ∈ (revealFibre S univ key f e P).image (f e) := by
    apply mem_image_of_mem
    simp [revealFibre, hP]
  have ha : 0 < a e P :=
    (hwpos P hP _ (owner_spec P.property e).1).trans_le
      (single_le_sum (fun b _ => hw b) hself)
  by_cases hact : active P.property key e
  · rw [ite_eq_left hact]
    apply sub_le_sub_right (Real.log_le_log ha ?_)
    apply sum_le_sum_of_subset_of_nonneg _ (fun b _ _ => hw b)
    intro b hb
    obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hb
    simp only [revealFibre, mem_filter] at hQ
    have hag : ∀ g, key g < key e → owner Q.property g = owner P.property g :=
      fun g hg => hQ.2 g (mem_univ _) hg
    simp only [availableCandidates, mem_filter, mem_univ, true_and]
    refine ⟨(owner_spec Q.property e).2, ?_⟩
    by_cases hex : owner Q.property e ∈ exceptional P.val e
    · exact Or.inl hex
    · apply Or.inr
      intro g hg
      obtain ⟨u, hu, hgu⟩ := mem_biUnion.mp hg
      exact available_owner_late hq P.property Q.property key e hag hex (mem_of_mem_erase hu) hgu
  · rw [ite_eq_right hact]
    have hs : (revealFibre S univ key f e P).image (f e) = {f e P} := by
      ext b
      constructor
      · intro hb
        obtain ⟨Q, hQ, rfl⟩ := mem_image.mp hb
        simp only [revealFibre, mem_filter] at hQ
        apply mem_singleton.mpr
        exact inactive_owner_fixed P.property Q.property key e
          (fun g hg => hQ.2 g (mem_univ _) hg) hact
      · intro hb
        simpa only [mem_singleton.mp hb] using hself
    simp only [a, availableReference, hs, sum_singleton, sub_self, le_refl]

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.weighted_reveal_bound
