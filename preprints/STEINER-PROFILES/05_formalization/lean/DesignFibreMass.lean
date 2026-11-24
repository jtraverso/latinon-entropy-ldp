module
public import DesignFibre
public import TypeScore

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Finset ColouredCliques CompleteJohnson SparseGram

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Every nonempty exact fibre prescribes a total mass of one block
per r edges of the complete graph. -/
theorem profile_mass_of_designFibre {n q : ℕ} (hq : 2 ≤ q)
    (colour : Fin n → C) (m : TypeProfile C q → ℤ)
    (P : Finset (Clique n q)) (hP : P ∈ designFibre colour m) :
    (∑ t, (m t : ℝ)) = (Fintype.card (Edge n) : ℝ) / (q.choose 2 : ℝ) := by
  classical
  obtain ⟨hp, hm⟩ := (mem_designFibre colour m P).mp hP
  let w : Clique n q → ℝ := fun b => if b ∈ P then 1 else 0
  have hsum : (∑ t, (m t : ℝ)) = ∑ b, w b := by
    rw [← sum_fiberwise univ (cliqueType colour) w]
    apply sum_congr rfl
    intro t _
    have h := BankCapacity.histogram_indicator colour P t
    rw [hm t] at h
    exact h.symm
  have he (e : Edge n) : WeightedEnergy.load (resources n q) w e = 1 := by
    have hh := hp e
    change (P.filter (fun b => e ∈ resources n q b)).card = _ at hh
    simp only [mem_univ, ite_true] at hh
    exact (BankCapacity.load_indicator P e).trans (by exact_mod_cast hh)
  have hr : (0 : ℝ) < q.choose 2 := by exact_mod_cast Nat.choose_pos hq
  have hinc := WeightedEnergy.incidence_sum (resources n q) w (fun _ => (1 : ℝ))
  simp only [he, mul_one, sum_const, nsmul_eq_mul, card_univ, resources_card, ← sum_mul] at hinc
  rw [hsum]
  exact (eq_div_iff hr.ne').mpr hinc

/-- The clique total is the product of the block mass and the number
of extensions of a fixed edge. -/
theorem complete_clique_mass {n q : ℕ} (hq : 2 ≤ q) :
    (Fintype.card (Edge n) : ℝ) / (q.choose 2 : ℝ) * ((n - 2).choose (q - 2) : ℝ)
      = (n.choose q : ℝ) := by
  have hb : Fintype.card (Edge n) = n.choose 2 := by
    rw [Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]
  rw [hb, div_mul_eq_mul_div]
  have hr : (0 : ℝ) < q.choose 2 := by exact_mod_cast Nat.choose_pos hq
  apply (div_eq_iff hr.ne').mpr
  have he := ProfileWeights.choose_completion n q 2
  rw [ProfileWeights.completionChoices, ite_eq_left hq] at he
  exact_mod_cast he

theorem designFibre_type_score_as_entropy {n q : ℕ} (hq : 2 ≤ q) (hnq : q ≤ n)
    (colour : Fin n → C) (hclasses : ∀ i, q ≤ profile colour univ i)
    (m : TypeProfile C q → ℤ)
    (P : Finset (Clique n q)) (hP : P ∈ designFibre colour m) :
    let b := (Fintype.card (Edge n) : ℝ) / (q.choose 2 : ℝ)
    let N := fun t : TypeProfile C q => ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ)
    let K := ∑ t, ((m t : ℝ) / b) * Real.log (((m t : ℝ) / b) / (N t / (n.choose q : ℝ)));
    -(∑ t, (m t : ℝ) * Real.log ((m t : ℝ) / N t)) =
      b * (Real.log ((n - 2).choose (q - 2)) - K) := by
  let b := (Fintype.card (Edge n) : ℝ) / (q.choose 2 : ℝ)
  let d : ℝ := (n - 2).choose (q - 2)
  let N := fun t : TypeProfile C q => ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ)
  have hr : (0 : ℝ) < q.choose 2 := by exact_mod_cast Nat.choose_pos hq
  have hEdge : Fintype.card (Edge n) = n.choose 2 := by
    rw [Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]
  have hb : 0 < b := by
    dsimp only [b]
    rw [hEdge]
    exact div_pos (by exact_mod_cast Nat.choose_pos (hq.trans hnq)) hr
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast Nat.choose_pos (by omega : q - 2 ≤ n - 2)
  have hN (t : TypeProfile C q) : 0 < N t := by
    dsimp only [N]
    exact_mod_cast fibre_pos colour hclasses t
  have he := type_score_as_relative_entropy (fun t => (m t : ℝ)) N b d hb hd
    hN (profile_mass_of_designFibre hq colour m P hP)
  have hd' : b * d = (n.choose q : ℝ) := complete_clique_mass hq
  rw [hd'] at he
  exact he

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.profile_mass_of_designFibre
#print axioms KqR75.PhysicalCompletion.complete_clique_mass
#print axioms KqR75.PhysicalCompletion.designFibre_type_score_as_entropy
