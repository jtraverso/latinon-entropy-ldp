module
public import UpperUniform
public import DesignFibreMass

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Filter Finset ColouredCliques CompleteJohnson PhysicalCompletion

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Uniform upper bound on the exact count, expressed multiplicatively
so that empty fibres and zero-count types are included. -/
theorem eventually_card_designFibre_upper (q : ℕ) (hq : 3 ≤ q) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ err : ℝ, 0 ≤ err ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (colour : Fin n → C) (m : TypeProfile C q → ℤ),
      (∀ c, ρ * (n : ℝ) ≤ (profile colour univ c : ℝ)) →
      (∀ e : Edge n, pairMargin colour (fun t => (m t : ℝ)) e =
        (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ)) →
      let r := q.choose 2
      let s : ℝ := (r - 1 : ℕ)
      let B := (Fintype.card (Edge n) : ℝ) / (r : ℝ)
      ((designFibre colour m).card : ℝ) ≤ Real.exp (
        -(∑ t, (m t : ℝ) * Real.log ((m t : ℝ) /
          ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ))) -
        s * B + err * (n : ℝ) ^ (2 - 1 / s)) := by
  obtain ⟨err, he, hb⟩ := eventually_log_designFibre_upper (C := C) q hq ρ hρ
  refine ⟨err, he, ?_⟩
  filter_upwards [hb] with n hn
  intro colour m hcol hmarg
  rcases (designFibre colour m).eq_empty_or_nonempty with he | hh
  · simp only [he, card_empty, Nat.cast_zero]
    exact (Real.exp_pos _).le
  · dsimp only
    have hcard : 0 < ((designFibre colour m).card : ℝ) := by exact_mod_cast hh.card_pos
    apply (Real.log_le_iff_le_exp hcard).mp
    have ht := hn colour m hcol hmarg hh
    dsimp only at ht
    linarith only [ht]

/-- The upper half of the quantitative R75 formula in the stated
relative-entropy normalization, including zero quotas. -/
theorem eventually_card_designFibre_upper_entropy (q : ℕ) (hq : 3 ≤ q)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ err : ℝ, 0 ≤ err ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (colour : Fin n → C) (m : TypeProfile C q → ℤ),
      (∀ c, ρ * (n : ℝ) ≤ (profile colour univ c : ℝ)) →
      (∀ e : Edge n, pairMargin colour (fun t => (m t : ℝ)) e =
        (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ)) →
      let r := q.choose 2
      let s : ℝ := (r - 1 : ℕ)
      let B := (Fintype.card (Edge n) : ℝ) / (r : ℝ)
      let N := fun t : TypeProfile C q => ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ)
      let K := ∑ t, ((m t : ℝ) / B) * Real.log (((m t : ℝ) / B) / (N t / (n.choose q : ℝ)))
      ((designFibre colour m).card : ℝ) ≤ Real.exp (
        B * (Real.log ((n - 2).choose (q - 2)) - s - K) +
        err * (n : ℝ) ^ (2 - 1 / s)) := by
  obtain ⟨err, he, hb⟩ := eventually_card_designFibre_upper (C := C) q hq ρ hρ
  refine ⟨err, he, ?_⟩
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hb, eventually_ge_atTop q, (tendsto_atTop.1 hnat) ((q : ℝ) / ρ)]
    with n hn hnq hlarge
  intro colour m hcol hmarg
  rcases (designFibre colour m).eq_empty_or_nonempty with he | ⟨P, hP⟩
  · simp only [he, card_empty, Nat.cast_zero]
    exact (Real.exp_pos _).le
  · have hclasses (c : C) : q ≤ profile colour univ c := by
      have hh := (div_le_iff₀ hρ).mp hlarge
      rw [mul_comm] at hh
      exact_mod_cast hh.trans (hcol c)
    have hs := designFibre_type_score_as_entropy (by omega : 2 ≤ q) hnq colour hclasses m P hP
    have ht := hn colour m hcol hmarg
    dsimp only at hs ht ⊢
    rw [hs] at ht
    refine ht.trans_eq ?_
    congr 1
    ring

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.eventually_card_designFibre_upper
#print axioms KqR75.UpperCounting.eventually_card_designFibre_upper_entropy
