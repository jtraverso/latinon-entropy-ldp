module
public import UpperGridIntegral

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset ColouredCliques CompleteJohnson SparseGram
open MeasureTheory Set
open scoped Interval

/-- The grid error can be made arbitrarily small for each design size. -/
theorem weighted_integral_upper {n q : ℕ} (hq : 3 ≤ q) (hnq : q ≤ n)
    (S : Finset (FullPacking n q)) (hS : S.Nonempty)
    (w : Clique n q → ℝ) (hw : ∀ b, 0 ≤ w b)
    (hwpos : ∀ P ∈ S, ∀ b ∈ P.val, 0 < w b)
    (hload : ∀ e : Edge n, WeightedEnergy.load (resources n q) w e = 1)
    (δ v : ℝ) (hδ : 0 < δ)
    (hmass : ∀ P ∈ S, ∀ e : Edge n, (∑ b ∈ exceptional P.val e, w b) ≤ δ)
    (hscore : ∀ P ∈ S, v ≤ ∑ b ∈ P.val, Real.log (w b)) :
    Real.log S.card + v ≤ (Fintype.card (Edge n) : ℝ) *
      ∫ x in (0 : ℝ)..1, x ^ (q.choose 2 - 1) * Real.log (δ + x ^ ((q.choose 2 - 1) * q.choose 2)) := by
  let N : ℝ := Fintype.card (Edge n)
  let a := q.choose 2 - 1
  let k := a * q.choose 2
  let C : ℝ := (a : ℝ) * |Real.log δ| + (k : ℝ) / δ
  let I := ∫ x in (0 : ℝ)..1, x ^ a * Real.log (δ + x ^ k)
  change Real.log S.card + v ≤ N * I
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨L, hL⟩ := exists_nat_gt (max 0 (N * C / ε))
  have hL₀ : 0 < L := by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hL)
  have hL' : 0 < (L : ℝ) := by exact_mod_cast hL₀
  have hC : N * C / (L : ℝ) ≤ ε :=
    (div_le_iff₀ hL').mpr (by
      have h := (div_lt_iff₀ hε).mp ((le_max_right _ _).trans_lt hL)
      linarith only [h, mul_comm ε (L : ℝ)])
  calc
    _ ≤ N * gridLog L a k δ :=
      weighted_grid_upper hq hnq hL₀ S hS w hw hwpos hload δ v hδ hmass hscore
    _ ≤ N * (I + C / L) :=
      mul_le_mul_of_nonneg_left (gridLog_le_integral L a k hL₀ δ hδ) (Nat.cast_nonneg _)
    _ ≤ N * I + ε := by
      rw [mul_add, ← mul_div_assoc]
      exact add_le_add le_rfl hC

/-- Evaluate the design-wide entropy bound at the root of the
exceptional mass, retaining its power in the error. -/
theorem weighted_upper_of_exceptional_mass {n q : ℕ} (hq : 3 ≤ q) (hnq : q ≤ n)
    (S : Finset (FullPacking n q)) (hS : S.Nonempty)
    (w : Clique n q → ℝ) (hw : ∀ b, 0 ≤ w b)
    (hwpos : ∀ P ∈ S, ∀ b ∈ P.val, 0 < w b)
    (hload : ∀ e : Edge n, WeightedEnergy.load (resources n q) w e = 1)
    (δ v : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hmass : ∀ P ∈ S, ∀ e : Edge n, (∑ b ∈ exceptional P.val e, w b) ≤ δ)
    (hscore : ∀ P ∈ S, v ≤ ∑ b ∈ P.val, Real.log (w b)) :
    let r := q.choose 2
    let s : ℝ := (r - 1 : ℕ)
    Real.log S.card + v ≤ (Fintype.card (Edge n) : ℝ) / (r : ℝ) *
      (-s + δ ^ (1 / s) * (Real.log 2 + s + 1 / (s - 1))) := by
  let r := q.choose 2
  let s : ℝ := (r - 1 : ℕ)
  let h := δ ^ (1 / s)
  have hr : 3 ≤ r := (show 3 ≤ (3 : ℕ).choose 2 by decide).trans (Nat.choose_le_choose 2 hq)
  have hs : 1 < s := by
    dsimp only [s]
    exact_mod_cast (by omega : 1 < r - 1)
  have hs₀ : 0 < s := by linarith
  have hh : 0 < h := Real.rpow_pos_of_pos hδ _
  have hh₁ : h ≤ 1 := by dsimp [h]; exact Real.rpow_le_one hδ.le hδ₁ (by positivity)
  have hpow : h ^ s = δ := by
    dsimp [h]
    rw [← Real.rpow_mul hδ.le, one_div_mul_cancel hs₀.ne', Real.rpow_one]
  have hsame :
      (∫ x in (0 : ℝ)..1, x ^ (r - 1) * Real.log (δ + x ^ ((r - 1) * r))) =
        ∫ x in (0 : ℝ)..1, x ^ (r - 1) * Real.log ((x ^ r) ^ s + h ^ s) := by
    apply intervalIntegral.integral_congr
    intro x _
    rw [hpow]
    simp only [s, Real.rpow_natCast, ← pow_mul, Nat.mul_comm r, add_comm δ]
  have hb := weighted_integral_upper hq hnq S hS w hw hwpos hload δ v hδ hmass hscore
  change _ ≤ (Fintype.card (Edge n) : ℝ) * _ at hb
  rw [hsame] at hb
  refine hb.trans ?_
  have hi := weighted_entropy_integral r (by omega) h s hh hh₁ hs
  exact (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)).trans_eq (by dsimp [h]; ring)

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.weighted_integral_upper
#print axioms KqR75.UpperCounting.weighted_upper_of_exceptional_mass
