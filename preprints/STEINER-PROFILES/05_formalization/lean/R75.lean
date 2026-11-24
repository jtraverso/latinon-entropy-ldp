module
public import Bilateral
public import ExactPairMargins
public import OmniBridge

@[expose] public section

namespace KqR75.PhysicalCompletion

open Filter Finset ColouredCliques CompleteJohnson

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Quantitative enumeration of labelled `K_q`-decompositions with an
exact interior colour profile, uniformly over all sufficiently large
admissible orders, colourings and integer quotas. -/
theorem eventually_designFibre_bilateral (q : ℕ) (hq : 3 ≤ q) (ρ κ : ℝ)
    (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ err : ℝ, 0 ≤ err ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (colour : Fin n → C) (m : TypeProfile C q → ℤ),
      (∀ c, ρ * (n : ℝ) ≤ (profile colour univ c : ℝ)) →
      ExactPairMargins colour m →
      (∀ t, κ * ((Fintype.card (Edge n) : ℝ) / (q.choose 2 : ℝ)) ≤ (m t : ℝ)) →
      q.choose 2 ∣ n.choose 2 → q - 1 ∣ n - 1 →
      let r := q.choose 2
      let z := GreedyScales.criticalExponent q
      let s : ℝ := (r - 1 : ℕ)
      let B := (Fintype.card (Edge n) : ℝ) / (r : ℝ)
      let N := fun t : TypeProfile C q => ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ)
      let K := ∑ t, ((m t : ℝ) / B) * Real.log (((m t : ℝ) / B) / (N t / (n.choose q : ℝ)))
      let main := B * (Real.log ((n - 2).choose (q - 2)) - s - K)
      0 < (designFibre colour m).card ∧
        main - err * ((n : ℝ) ^ (2 - z) * Real.log n) ≤
          Real.log ((designFibre colour m).card : ℝ) ∧
        Real.log ((designFibre colour m).card : ℝ) ≤
          main + err * (n : ℝ) ^ (2 - 1 / s) := by
  have hz := critical_completion_scales q hq
  have homni := OmniBridge.physicalOmniPlacement_of_omni q hq
    (GreedyScales.criticalExponent q) hz.1 hz.2.1
  obtain ⟨L, U, hL, _, hcount⟩ :=
    eventually_designFibre_bilateral_of_omni (C := C) q hq ρ κ hρ hκ homni
  refine ⟨max L U, hL.trans (le_max_left L U), ?_⟩
  have hnlim : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcount, eventually_ge_atTop (1 : ℕ), (tendsto_atTop.1 hnlim) (2 / ρ)]
    with n hn hn₁ hnρ
  intro colour m hclasses hm hκm hsize hdegree
  have hclasses' (c : C) : 2 ≤ profile colour univ c := by
    have h := (div_le_iff₀ hρ).mp hnρ
    rw [mul_comm] at h
    exact_mod_cast h.trans (hclasses c)
  have hmargin := (exactPairMargins_iff colour m hclasses').mp hm
  obtain ⟨hp, hl, hu⟩ := hn colour m hclasses hmargin hκm hsize hdegree
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn₁)
  refine ⟨hp, le_trans ?_ hl, hu.trans ?_⟩
  · exact sub_le_sub_left (mul_le_mul_of_nonneg_right (le_max_left L U)
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) hlog)) _
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (le_max_right L U)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.eventually_designFibre_bilateral
