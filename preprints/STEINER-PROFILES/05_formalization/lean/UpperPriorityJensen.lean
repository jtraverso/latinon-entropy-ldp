module
public import UpperPriorityCounts
public import UpperReference

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset ColouredCliques CompleteJohnson SparseGram
open scoped Classical

private theorem sum_log_le_of_mean {T : Type*} (B : Finset T) (u : T → ℝ) (M : ℝ)
    (hM : 0 < M) (hpos : ∀ t ∈ B, 0 < u t)
    (hmean : ∑ t ∈ B, u t ≤ (B.card : ℝ) * M) :
    ∑ t ∈ B, Real.log (u t) ≤ (B.card : ℝ) * Real.log M := by
  have hineq (t : T) (ht : t ∈ B) : Real.log (u t) - Real.log M ≤ u t / M - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos (hpos t ht) hM)
    rwa [Real.log_div (hpos t ht).ne' hM.ne'] at h
  have hs := sum_le_sum hineq
  rw [sum_sub_distrib, sum_sub_distrib, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul,
    ← sum_div, mul_one] at hs
  have hmean' : (∑ t ∈ B, u t) / M ≤ (B.card : ℝ) :=
    (div_le_iff₀ hM).mpr hmean
  linarith only [hs, hmean']

/-- Total reference weight available under the strict activity event,
averaged over a box with a fixed test label. -/
theorem sum_reference_on_strictBox {n q L : ℕ} (P : FullPacking n q) (e : Edge n) (z : Fin L)
    (w : Clique n q → ℝ) (hw : ∀ b, 0 ≤ w b)
    (hload : WeightedEnergy.load (resources n q) w e = 1)
    (δ : ℝ) (hδ : (∑ b ∈ exceptional P.val e, w b) ≤ δ) :
    let x := ((z.val : ℝ) + 1) / L
    ∑ lab ∈ strictBox P e z, ∑ b ∈ availableCandidates P (priorityKey lab) e, w b ≤
      ((strictBox P e z).card : ℝ) * (δ + x ^ ((q.choose 2 - 1) * q.choose 2)) := by
  let B := strictBox P e z
  let x := ((z.val : ℝ) + 1) / L
  let k := (q.choose 2 - 1) * q.choose 2
  let count (b : Clique n q) := (B.filter fun lab =>
    b ∈ availableCandidates P (priorityKey lab) e).card
  have hL : 0 < (L : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt z.isLt)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hbound (b : Clique n q) :
      (count b : ℝ) * w b ≤
        (if b ∈ exceptional P.val e then (B.card : ℝ) * w b else 0) +
          (if e ∈ resources n q b then ((B.card : ℝ) * x ^ k) * w b else 0) := by
    by_cases hb : b ∈ exceptional P.val e
    · rw [ite_eq_left hb]
      have hle : (count b : ℝ) ≤ B.card := by exact_mod_cast card_filter_le _ _
      refine (mul_le_mul_of_nonneg_right hle (hw b)).trans (le_add_of_nonneg_right ?_)
      split_ifs
      · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx _)) (hw b)
      · exact le_rfl
    · rw [ite_eq_right hb, zero_add]
      by_cases he : e ∈ resources n q b
      · rw [ite_eq_left he]
        apply mul_le_mul_of_nonneg_right _ (hw b)
        have hh : (count b : ℝ) * (L : ℝ) ^ k ≤ (B.card : ℝ) * ((z.val : ℝ) + 1) ^ k := by
          exact_mod_cast ordinary_availability_card P e z b he hb
        apply le_of_mul_le_mul_right _ (pow_pos hL k)
        calc
          _ ≤ (B.card : ℝ) * ((z.val : ℝ) + 1) ^ k := hh
          _ = _ := by
            dsimp [x]
            rw [div_pow, mul_assoc, div_mul_cancel₀ _ (pow_pos hL k).ne']
      · rw [ite_eq_right he]
        have hz : count b = 0 := by
          change (B.filter (fun lab => b ∈ availableCandidates P (priorityKey lab) e)).card = 0
          rw [card_eq_zero, filter_eq_empty_iff]
          intro lab _ h
          simp only [availableCandidates, mem_filter, mem_univ, true_and] at h
          exact he h.1
        simp [hz]
  change ∑ lab ∈ B, ∑ b ∈ availableCandidates P (priorityKey lab) e, w b ≤ _
  calc
    _ = ∑ b : Clique n q, (count b : ℝ) * w b := by
      have hsum (lab : Edge n → Fin L) :
          ∑ b ∈ availableCandidates P (priorityKey lab) e, w b =
            ∑ b : Clique n q, if b ∈ availableCandidates P (priorityKey lab) e then w b else 0 := by
        rw [← sum_filter]
        congr 1
        exact (filter_mem_eq_of_subset (subset_univ _)).symm
      simp_rw [hsum]
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      rw [← sum_filter, sum_const, nsmul_eq_mul]
    _ ≤ ∑ b : Clique n q,
        ((if b ∈ exceptional P.val e then (B.card : ℝ) * w b else 0) +
          (if e ∈ resources n q b then ((B.card : ℝ) * x ^ k) * w b else 0)) :=
      sum_le_sum (fun b _ => hbound b)
    _ = (B.card : ℝ) * (∑ b ∈ exceptional P.val e, w b) + (B.card : ℝ) * x ^ k := by
      rw [sum_add_distrib, ← sum_filter, ← sum_filter, ← mul_sum, ← mul_sum]
      rw [filter_mem_eq_of_subset (subset_univ (exceptional P.val e))]
      have h := hload
      rw [WeightedEnergy.load, ← sum_filter] at h
      rw [h, mul_one]
    _ ≤ _ := by
      dsimp only [B, x, k] at *
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg _)) le_rfl

/-- Jensen conditional on the test label and strict activity. -/
theorem log_reference_on_strictBox {n q L : ℕ} (hq : 3 ≤ q)
    (P : FullPacking n q) (e : Edge n) (z : Fin L)
    (w : Clique n q → ℝ) (hw : ∀ b, 0 ≤ w b) (hwpos : ∀ b ∈ P.val, 0 < w b)
    (hload : WeightedEnergy.load (resources n q) w e = 1)
    (δ : ℝ) (hδ : 0 < δ) (hmass : (∑ b ∈ exceptional P.val e, w b) ≤ δ) :
    let x := ((z.val : ℝ) + 1) / L
    ∑ lab ∈ strictBox P e z, Real.log (∑ b ∈ availableCandidates P (priorityKey lab) e, w b) ≤
      ((strictBox P e z).card : ℝ) * Real.log (δ + x ^ ((q.choose 2 - 1) * q.choose 2)) := by
  dsimp only
  apply sum_log_le_of_mean
  · positivity
  · intro lab _
    have howner : owner P.property e ∈ availableCandidates P (priorityKey lab) e := by
      have he := owner_spec P.property e
      have hb : owner P.property e ∈ exceptional P.val e := by
        apply mem_biUnion.mpr
        refine ⟨_, he.1, mem_filter.mpr ⟨mem_univ _, he.2, ?_⟩⟩
        rwa [inter_self, (mem_powersetCard.mp (owner P.property e).property).2]
      simp only [availableCandidates, mem_filter, mem_univ, true_and]
      exact ⟨he.2, Or.inl hb⟩
    exact (hwpos _ (owner_spec P.property e).1).trans_le (single_le_sum (fun b _ => hw b) howner)
  · exact sum_reference_on_strictBox P e z w hw hload δ hmass

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.log_reference_on_strictBox
