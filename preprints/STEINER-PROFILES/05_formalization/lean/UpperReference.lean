module
public import UpperWeightedReveal
public import DesignFibre

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset ColouredCliques CompleteJohnson SparseGram PhysicalCompletion

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Reference weights may vanish on absent types. On every realized
block the weight is positive, and the weighted candidates through a
given physical edge have total mass one. -/
theorem profile_reference_properties {n q : ℕ} (colour : Fin n → C)
    (hclasses : ∀ i, q ≤ profile colour univ i)
    (m : TypeProfile C q → ℤ)
    (hmargin : ∀ e : Edge n, pairMargin colour (fun t => (m t : ℝ)) e =
      (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ))
    (P : Finset (Clique n q)) (hP : P ∈ designFibre colour m) :
    let w := ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ))
    (∀ b, 0 ≤ w b) ∧ (∀ b ∈ P, 0 < w b) ∧
      ∀ e : Edge n, WeightedEnergy.load (resources n q) w e = 1 := by
  have ht := ((mem_designFibre colour m P).mp hP).2
  refine ⟨?_, ?_, seed_load colour hclasses _ hmargin⟩
  · intro b
    rw [ProfileWeights.weight, ← ht]
    simp only [BankCapacity.integerHistogram, Int.cast_natCast]
    positivity
  · intro b hb
    rw [ProfileWeights.weight, ← ht]
    simp only [BankCapacity.integerHistogram, Int.cast_natCast]
    apply div_pos
    · have hpos : 0 < (P.filter (fun l => cliqueType colour l = cliqueType colour b)).card :=
        card_pos.mpr ⟨b, mem_filter.mpr ⟨hb, rfl⟩⟩
      exact_mod_cast hpos
    · exact_mod_cast fibre_pos colour hclasses (cliqueType colour b)

/-- Every fixed-order candidate sum is bounded by one. This sign is
needed when replacing the actual activity indicator by a strict
priority event before averaging. -/
theorem available_reference_le_one {n q : ℕ} (P : FullPacking n q)
    (key : Edge n → ℕ) (w : Clique n q → ℝ) (hw : ∀ b, 0 ≤ w b)
    (hload : ∀ e : Edge n, WeightedEnergy.load (resources n q) w e = 1)
    (e : Edge n) : (∑ b ∈ availableCandidates P key e, w b) ≤ 1 := by
  rw [← hload e, WeightedEnergy.load, ← sum_filter]
  apply sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => hw b)
  intro b hb
  simp only [availableCandidates, mem_filter, mem_univ, true_and] at hb ⊢
  exact hb.1

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.profile_reference_properties
#print axioms KqR75.UpperCounting.available_reference_le_one
