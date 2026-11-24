module
public import UpperPriorityJensen

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset ColouredCliques CompleteJohnson SparseGram
open scoped Classical

/-- The available-reference part of the contribution at a test edge. -/
noncomputable def activeLogReference {n q L : ℕ} (P : FullPacking n q)
    (lab : Edge n → Fin L) (e : Edge n) (w : Clique n q → ℝ) : ℝ :=
  if active P.property (priorityKey lab) e then
    Real.log (∑ b ∈ availableCandidates P (priorityKey lab) e, w b)
  else 0

/-- Conditional averaging for one test edge, summed over all priorities.
For a nonstrict activity event the log contribution is nonpositive,
which justifies restricting to the strict boxes. -/
theorem sum_activeLogReference_le {n q L : ℕ} (hq : 3 ≤ q)
    (P : FullPacking n q) (e : Edge n)
    (w : Clique n q → ℝ) (hw : ∀ b, 0 ≤ w b) (hwpos : ∀ b ∈ P.val, 0 < w b)
    (hload : ∀ f : Edge n, WeightedEnergy.load (resources n q) w f = 1)
    (δ : ℝ) (hδ : 0 < δ) (hmass : (∑ b ∈ exceptional P.val e, w b) ≤ δ) :
    (∑ lab : Edge n → Fin L, activeLogReference P lab e w) ≤
      (L : ℝ) ^ (Fintype.card (Edge n) - q.choose 2) *
        ∑ z : Fin L, (z.val : ℝ) ^ (q.choose 2 - 1) *
          Real.log (δ + (((z.val : ℝ) + 1) / L) ^ ((q.choose 2 - 1) * q.choose 2)) := by
  classical
  let A (z : Fin L) : Finset (Edge n → Fin L) := univ.filter fun lab => lab e = z
  let R (lab : Edge n → Fin L) : ℝ := ∑ b ∈ availableCandidates P (priorityKey lab) e, w b
  have hlog (lab : Edge n → Fin L) : Real.log (R lab) ≤ 0 := by
    apply Real.log_nonpos
    · exact sum_nonneg (fun b _ => hw b)
    · exact available_reference_le_one P (priorityKey lab) w hw hload e
  have hbox (z : Fin L) : strictBox P e z ⊆ A z :=
    fun lab hl => mem_filter.mpr ⟨mem_univ _, ((mem_strictBox P e z lab).mp hl).1⟩
  have hsum (z : Fin L) :
      (∑ lab ∈ A z, activeLogReference P lab e w) ≤
        ∑ lab ∈ strictBox P e z, Real.log (R lab) := by
    calc
      _ ≤ ∑ lab ∈ A z, if lab ∈ strictBox P e z then Real.log (R lab) else 0 := by
        apply sum_le_sum
        intro lab _
        by_cases hb : lab ∈ strictBox P e z
        · have ha := (mem_strictBox P e z lab).mp hb
          have hactive : active P.property (priorityKey lab) e :=
            strict_labels_active P lab e (by rw [ha.1]; exact ha.2)
          simp only [activeLogReference, ite_eq_left hactive, ite_eq_left hb, R, le_refl]
        · rw [ite_eq_right hb, activeLogReference]
          split_ifs
          · exact hlog lab
          · exact le_rfl
      _ = _ := by rw [← sum_filter, filter_mem_eq_of_subset (hbox z)]
  rw [← sum_fiberwise univ (fun lab : Edge n → Fin L => lab e)
    (fun lab => activeLogReference P lab e w), mul_sum]
  apply sum_le_sum
  intro z _
  have hJ := log_reference_on_strictBox hq P e z w hw hwpos (hload e) δ hδ hmass
  simp only [strictBox_card, Nat.cast_mul, Nat.cast_pow] at hJ
  exact (hsum z).trans (hJ.trans_eq (by ring))

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.sum_activeLogReference_le
