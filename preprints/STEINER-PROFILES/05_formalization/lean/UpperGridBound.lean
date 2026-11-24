module
public import UpperPriorityAverage

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset ColouredCliques CompleteJohnson SparseGram
open scoped Classical

def gridLog (L a k : ℕ) (δ : ℝ) : ℝ :=
  (∑ z : Fin L, ((z.val : ℝ) / L) ^ a *
    Real.log (δ + (((z.val : ℝ) + 1) / L) ^ k)) / L

/-- Average all fixed orders produced by the finite priorities. The
weighted score of the blocks is separated from the available masses. -/
theorem weighted_grid_upper {n q L : ℕ} (hq : 3 ≤ q) (hnq : q ≤ n) (hL : 0 < L)
    (S : Finset (FullPacking n q)) (hS : S.Nonempty)
    (w : Clique n q → ℝ) (hw : ∀ b, 0 ≤ w b)
    (hwpos : ∀ P ∈ S, ∀ b ∈ P.val, 0 < w b)
    (hload : ∀ e : Edge n, WeightedEnergy.load (resources n q) w e = 1)
    (δ v : ℝ) (hδ : 0 < δ)
    (hmass : ∀ P ∈ S, ∀ e : Edge n, (∑ b ∈ exceptional P.val e, w b) ≤ δ)
    (hscore : ∀ P ∈ S, v ≤ ∑ b ∈ P.val, Real.log (w b)) :
    Real.log S.card + v ≤ (Fintype.card (Edge n) : ℝ) *
      gridLog L (q.choose 2 - 1) ((q.choose 2 - 1) * q.choose 2) δ := by
  classical
  let N := Fintype.card (Edge n)
  let r := q.choose 2
  let H := gridLog L (r - 1) ((r - 1) * r) δ
  let F (P : FullPacking n q) (lab : Edge n → Fin L) (e : Edge n) :=
    activeLogReference P lab e w
  have hSc : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  have hL' : 0 < (L : ℝ) := by exact_mod_cast hL
  have hN : r ≤ N := by
    have he : N = n.choose 2 := by
      dsimp only [N, Edge]
      rw [Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]
    exact (Nat.choose_le_choose 2 hnq).trans_eq he.symm
  have hpoint (lab : Edge n → Fin L) :
      (S.card : ℝ) * (Real.log S.card + v) ≤ ∑ P ∈ S, ∑ e : Edge n, F P lab e := by
    have ho := weighted_reveal_bound hq S hS (priorityKey lab) (priorityKey_injective lab)
      w hw hwpos
    have hterm (P : FullPacking n q) :
        (∑ e : Edge n, if active P.property (priorityKey lab) e then
          Real.log (∑ b ∈ availableCandidates P (priorityKey lab) e, w b) -
            Real.log (w (owner P.property e)) else 0) =
          (∑ e : Edge n, F P lab e) - ∑ b ∈ P.val, Real.log (w b) := by
      rw [← active_reference_score (by omega : 2 ≤ q) P (priorityKey lab)
        (priorityKey_injective lab)]
      rw [← sum_sub_distrib]
      apply sum_congr rfl
      intro e _
      by_cases ha : active P.property (priorityKey lab) e <;> simp [F, activeLogReference, ha]
    rw [sum_congr rfl (fun P _ => hterm P), sum_sub_distrib] at ho
    have hs := sum_le_sum hscore
    rw [sum_const, nsmul_eq_mul] at hs
    nlinarith only [ho, hs]
  have hmass' (P : FullPacking n q) (hP : P ∈ S) (e : Edge n) :
      (∑ lab : Edge n → Fin L, F P lab e) ≤ (L : ℝ) ^ N * H := by
    have hh := sum_activeLogReference_le (L := L) hq P e w hw (hwpos P hP) hload δ hδ (hmass P hP e)
    refine hh.trans_eq ?_
    let a := r - 1
    let g (z : Fin L) := Real.log (δ + (((z.val : ℝ) + 1) / L) ^ (a * r))
    have hsumdiv : (∑ z : Fin L, ((z.val : ℝ) / L) ^ a * g z) =
        (∑ z : Fin L, (z.val : ℝ) ^ a * g z) / (L : ℝ) ^ a := by
      rw [sum_div]
      apply sum_congr rfl
      intro z _
      rw [div_pow, div_mul_eq_mul_div]
    change (L : ℝ) ^ (N - r) * (∑ z : Fin L, (z.val : ℝ) ^ a * g z) =
      (L : ℝ) ^ N * ((∑ z : Fin L, ((z.val : ℝ) / L) ^ a * g z) / L)
    have hr : a + 1 = r := Nat.sub_add_cancel (Nat.choose_pos (by omega : 2 ≤ q))
    rw [hsumdiv, div_div, ← pow_succ, hr]
    have he : (L : ℝ) ^ N = (L : ℝ) ^ (N - r) * (L : ℝ) ^ r := by
      rw [← pow_add, Nat.sub_add_cancel hN]
    rw [he]
    field_simp
  have hsum := sum_le_sum (fun lab (_ : lab ∈ (univ : Finset (Edge n → Fin L))) => hpoint lab)
  rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    sum_comm] at hsum
  have hb : (∑ P ∈ S, ∑ lab : Edge n → Fin L, ∑ e : Edge n, F P lab e) ≤
      (S.card : ℝ) * ((N : ℝ) * ((L : ℝ) ^ N * H)) := by
    have he (P : FullPacking n q) (hP : P ∈ S) :
        (∑ lab : Edge n → Fin L, ∑ e : Edge n, F P lab e) ≤ (N : ℝ) * ((L : ℝ) ^ N * H) := by
      rw [sum_comm]
      exact (sum_le_sum (fun e _ => hmass' P hP e)).trans_eq (by simp [N, nsmul_eq_mul])
    exact (sum_le_sum he).trans_eq (by rw [sum_const, nsmul_eq_mul])
  have ht := hsum.trans hb
  apply le_of_mul_le_mul_left _ (mul_pos (pow_pos hL' N) hSc)
  calc
    _ = (L : ℝ) ^ N * ((S.card : ℝ) * (Real.log S.card + v)) := by ring
    _ ≤ (S.card : ℝ) * ((N : ℝ) * ((L : ℝ) ^ N * H)) := ht
    _ = _ := by ring

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.weighted_grid_upper
