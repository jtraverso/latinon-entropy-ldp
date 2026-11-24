module
public import RestrictedInverse

@[expose] public section
noncomputable section
namespace KqR75.DeletedGram

open Finset

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

def gram (I : B → Finset E) (w : B → ℝ) : Matrix E E ℝ :=
  fun e f => ∑ b, if e ∈ I b ∧ f ∈ I b then w b else 0

def prunedGram (I : B → Finset E) (w : B → ℝ) (J : Finset E) : Matrix E E ℝ :=
  fun e f => ∑ b, if I b ⊆ J then
    (if e ∈ I b ∧ f ∈ I b then w b else 0) else 0

theorem gram_nonneg (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b)
    (e f : E) : 0 ≤ gram I w e f := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact hw b
  · exact le_rfl

theorem loss_nonneg (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b)
    (J : Finset E) (e f : E) : 0 ≤ gram I w e f - prunedGram I w J e f := by
  dsimp only [gram, prunedGram]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_nonneg
  intro b _
  split_ifs <;> simp_all

/-- Losing a block costs at most r row entries, and every lost block has
an outside resource. This is a finite weighted union bound, with no randomness. -/
theorem loss_row_le_outside (I : B → Finset E) (w : B → ℝ)
    (hw : ∀ b, 0 ≤ w b) (r : ℝ) (hr : 0 ≤ r)
    (hsize : ∀ b, ((I b).card : ℝ) ≤ r) (J : Finset E) (e : E) :
    (∑ f : J, (gram I w e f - prunedGram I w J e f)) ≤
      r * ∑ g : (Jᶜ : Finset E), gram I w e g := by
  have hblock (b : B) :
      (∑ f : J, ((if e ∈ I b ∧ (f : E) ∈ I b then w b else 0) -
        if I b ⊆ J then (if e ∈ I b ∧ (f : E) ∈ I b then w b else 0) else 0)) ≤
        r * ∑ g : (Jᶜ : Finset E), if e ∈ I b ∧ (g : E) ∈ I b then w b else 0 := by
    by_cases hgood : I b ⊆ J
    · simp only [hgood, ite_true, sub_self, Finset.sum_const_zero]
      exact mul_nonneg hr (Finset.sum_nonneg (fun g _ => by
        split_ifs
        · exact hw b
        · exact le_rfl))
    by_cases he : e ∈ I b
    · obtain ⟨g, hg, hgJ⟩ := Finset.not_subset.mp hgood
      let g' : (Jᶜ : Finset E) := ⟨g, Finset.mem_compl.mpr hgJ⟩
      have hs : w b ≤ ∑ g : (Jᶜ : Finset E), if (g : E) ∈ I b then w b else 0 := by
        have h := Finset.single_le_sum
          (s := (univ : Finset (Jᶜ : Finset E)))
          (f := fun g : (Jᶜ : Finset E) => if (g : E) ∈ I b then w b else 0)
          (fun g _ => by split_ifs; exact hw b; exact le_rfl) (mem_univ g')
        simpa only [g', hg, ite_true] using h
      have hfull : (∑ f : E, if f ∈ I b then w b else 0) = ((I b).card : ℝ) * w b := by
        rw [← Finset.sum_filter]
        simp
      have hj : (∑ f : J, if (f : E) ∈ I b then w b else 0) ≤
          ((I b).card : ℝ) * w b := by
        rw [Finset.sum_coe_sort J (fun f : E => if f ∈ I b then w b else 0)]
        rw [← hfull]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
          (fun f _ _ => by split_ifs; exact hw b; exact le_rfl)
      simp only [hgood, ite_false, he, true_and, sub_zero]
      exact hj.trans ((mul_le_mul_of_nonneg_right (hsize b) (hw b)).trans
        (mul_le_mul_of_nonneg_left hs hr))
    · simp only [hgood, he, false_and, ite_false, sub_zero, Finset.sum_const_zero, mul_zero]
      exact le_rfl
  dsimp only [gram, prunedGram]
  simp_rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (s := (univ : Finset (Jᶜ : Finset E))),
    Finset.mul_sum]
  exact Finset.sum_le_sum (fun b _ => hblock b)

/-- Actual weighted block deletion satisfies the inverse perturbation theorem.
Only the outside Gram mass remains to be bounded from geometric degree data. -/
theorem pruned_inverse_rows_le_eight (I : B → Finset E) (w : B → ℝ)
    (hw : ∀ b, 0 ≤ w b) (r : ℝ) (hr : 0 ≤ r)
    (hsize : ∀ b, ((I b).card : ℝ) ≤ r) (J : Finset E)
    (U : Matrix E E ℝ) (hinv : gram I w * U = 1)
    (hU : ∀ i, ∑ j, |U i j| ≤ 4) (β : ℝ)
    (hout : ∀ i : J, ∑ g : (Jᶜ : Finset E), gram I w i g ≤ β)
    (hsmall : 4 * (1 + r) * β ≤ 1 / 2) :
    let S : Matrix J J ℝ := fun e f => prunedGram I w J e f
    S.det ≠ 0 ∧ ∀ i, ∑ j, |S⁻¹ i j| ≤ 8 := by
  apply RestrictedInverse.restricted_inverse_rows_le_eight (gram I w) U J _ β (r * β)
    hinv hU
  · intro i g
    exact gram_nonneg I w hw i g
  · exact hout
  · intro i j
    exact loss_nonneg I w hw J i j
  · intro i
    exact (loss_row_le_outside I w hw r hr hsize J i).trans
      (mul_le_mul_of_nonneg_left (hout i) hr)
  · nlinarith only [hsmall]

end KqR75.DeletedGram

#print axioms KqR75.DeletedGram.loss_row_le_outside
#print axioms KqR75.DeletedGram.pruned_inverse_rows_le_eight
