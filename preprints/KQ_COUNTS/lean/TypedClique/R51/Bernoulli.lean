/-
 R51.1: finite independent Bernoulli expectation for candidate sets.
 A sample H is the set of retained edges, weighted by the Bernoulli product.
 No near-regularity or GJKKL assertion is made.
-/
module
public import TypedClique.R50.WeightedBridge
@[expose] public section

namespace TypedClique.R51

open Finset

variable {Edge : Type*} [Fintype Edge] [DecidableEq Edge]

/-- Product probability of a Bernoulli-selected subset. -/
noncomputable def bernoulliWeight (p : Edge → ℝ) (H : Finset Edge) : ℝ :=
  (∏ e ∈ H, p e) *
    ∏ e ∈ ((Finset.univ : Finset Edge) \ H), (1 - p e)

/-- Total mass of retained subsets containing M equals the product over M. -/
theorem sum_containing_eq_prod (p : Edge → ℝ) (M : Finset Edge) :
    (∑ H ∈ (Finset.univ : Finset Edge).powerset,
      if M ⊆ H then bernoulliWeight p H else 0) =
      ∏ e ∈ M, p e := by
  classical
  let g : Edge → ℝ := fun e => if e ∈ M then 0 else 1 - p e
  have hterm (H : Finset Edge) :
      (if M ⊆ H then bernoulliWeight p H else 0) =
      (∏ e ∈ H, p e) * ∏ e ∈ ((Finset.univ : Finset Edge) \ H), g e := by
    by_cases hMH : M ⊆ H
    · simp only [if_pos hMH, bernoulliWeight]
      congr 1
      apply Finset.prod_congr rfl
      intro e he
      have heM : e ∉ M := fun hem => (Finset.mem_sdiff.mp he).2 (hMH hem)
      simp [g, heM]
    · simp only [if_neg hMH]
      obtain ⟨e, heM, heNotH⟩ := Finset.not_subset.mp hMH
      have heComp : e ∈ ((Finset.univ : Finset Edge) \ H) :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, heNotH⟩
      have hzero : (∏ x ∈ ((Finset.univ : Finset Edge) \ H), g x) = 0 := by
        apply Finset.prod_eq_zero heComp
        simp [g, heM]
      simp [hzero]
  have hprod :
      (∏ e ∈ (Finset.univ : Finset Edge), (p e + g e)) =
      ∏ e ∈ M, p e := by
    have hfun (e : Edge) : p e + g e = if e ∈ M then p e else 1 := by
      simp only [g]
      split_ifs <;> ring
    simp_rw [hfun]
    have hsubset :
        (∏ e ∈ (Finset.univ : Finset Edge),
          if e ∈ M then p e else 1) =
        ∏ e ∈ M, if e ∈ M then p e else 1 := by
      apply Finset.prod_subset (Finset.subset_univ M)
      intro e he heM
      simp [heM]
    rw [hsubset]
    simp
  calc
    (∑ H ∈ (Finset.univ : Finset Edge).powerset,
      if M ⊆ H then bernoulliWeight p H else 0) =
      ∑ H ∈ (Finset.univ : Finset Edge).powerset,
        (∏ e ∈ H, p e) *
          ∏ e ∈ ((Finset.univ : Finset Edge) \ H), g e := by
            apply Finset.sum_congr rfl
            intro H _
            exact hterm H
    _ = ∏ e ∈ (Finset.univ : Finset Edge), (p e + g e) :=
      (Finset.prod_add p g (Finset.univ : Finset Edge)).symm
    _ = ∏ e ∈ M, p e := hprod

/-- Expected number of candidate subsets retained by Bernoulli sampling. -/
theorem expected_contained_count (p : Edge → ℝ)
    (C : Finset (Finset Edge)) :
    (∑ H ∈ (Finset.univ : Finset Edge).powerset,
      bernoulliWeight p H *
        (∑ M ∈ C, if M ⊆ H then (1 : ℝ) else 0)) =
    ∑ M ∈ C, ∏ e ∈ M, p e := by
  classical
  calc
    (∑ H ∈ (Finset.univ : Finset Edge).powerset,
      bernoulliWeight p H *
        (∑ M ∈ C, if M ⊆ H then (1 : ℝ) else 0)) =
      ∑ H ∈ (Finset.univ : Finset Edge).powerset,
        ∑ M ∈ C, if M ⊆ H then bernoulliWeight p H else 0 := by
          apply Finset.sum_congr rfl
          intro H _
          simp only [mul_sum, mul_ite, mul_one, mul_zero]
    _ = ∑ M ∈ C, ∑ H ∈ (Finset.univ : Finset Edge).powerset,
          if M ⊆ H then bernoulliWeight p H else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ M ∈ C, ∏ e ∈ M, p e := by
      apply Finset.sum_congr rfl
      intro M _
      exact sum_containing_eq_prod p M

end TypedClique.R51
