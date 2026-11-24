module
public import SlotPairMargins

@[expose] public section
noncomputable section
namespace KqR75.BankCapacity

open Finset ColouredCliques SlotProfiles SlotPairMargins

variable {C K : Type*} [Fintype C] [DecidableEq C]
  [Field K] [Fintype K] [DecidableEq K]

/-- A fixed number of cell copies per unit of defect suffices for each
generator. The coefficient bound uses only the high coordinates of the
defect, and the resulting correction agrees in all coordinates. -/
theorem bounded_integer_correction {q : ℕ} (hq : 2 ≤ q)
    (s : Fin q → K) (hs : Function.Injective s) (ref : C) :
    ∃ (tag : High C q ref → Fin q → C) (r : High C q ref → Fin q) (B : ℤ),
      (∀ j, slotType (tag j) = j.val) ∧ 0 ≤ B ∧
      ∀ (w : TypeProfile C q → ℤ) (D : ℤ),
        (∀ i : High C q ref, |w i.val| ≤ D) →
        (∀ i j, ∑ v, w v * (orderedCount v i j : ℤ) = 0) →
        ∃ a : High C q ref → ℤ, (∀ j, |a j| ≤ B * D) ∧
          ∀ v, w v = ∑ k, a k * cellDifference s ref (tag k) (r k) v := by
  classical
  obtain ⟨tag, r, L, htag, hL⟩ := cell_high_coordinates s hs ref
  let B : ℤ := ∑ j, ∑ k, |L j k|
  refine ⟨tag, r, B, htag, sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => abs_nonneg _)), ?_⟩
  intro w D hw hmargin
  let a (k : High C q ref) := ∑ j : High C q ref, w j.val * L j k
  let z (v : TypeProfile C q) := ∑ k, a k * cellDifference s ref (tag k) (r k) v
  have ha (k : High C q ref) : |a k| ≤ B * D := by
    calc
      _ ≤ ∑ j : High C q ref, |w j.val * L j k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (∑ l, |L j l|) * D := by
        apply sum_le_sum
        intro j _
        rw [abs_mul, mul_comm]
        exact mul_le_mul (single_le_sum (fun l _ => abs_nonneg (L j l)) (mem_univ k))
          (hw j) (abs_nonneg _) (sum_nonneg fun l _ => abs_nonneg (L j l))
      _ = _ := (sum_mul _ _ _).symm
  have hh (v : TypeProfile C q) (hv : 2 < degree ref v) : w v - z v = 0 := by
    let i : High C q ref := ⟨v, hv⟩
    have he : z v = w v := by
      calc
        _ = ∑ j : High C q ref, w j.val *
            ∑ k, L j k * cellDifference s ref (tag k) (r k) v := by
          simp only [z, a, sum_mul, mul_sum, mul_assoc]
          rw [sum_comm]
        _ = ∑ j : High C q ref, w j.val * (if i = j then 1 else 0) := by
          apply sum_congr rfl
          intro j _
          exact congrArg (fun x : ℤ => w j.val * x) (hL i j)
        _ = _ := by
          rw [sum_eq_single i]
          · simp [i]
          · intro j _ hji
            simp [Ne.symm hji]
          · simp
    exact sub_eq_zero.mpr he.symm
  have hz (i j : C) : ∑ v, (w v - z v) * (orderedCount v i j : ℤ) = 0 := by
    simp only [sub_mul, sum_sub_distrib, hmargin, zero_sub, neg_eq_zero, z, sum_mul]
    rw [sum_comm]
    apply sum_eq_zero
    intro k _
    simp only [mul_assoc, ← mul_sum]
    have h0 : (∑ v, cellDifference s ref (tag k) (r k) v * (orderedCount v i j : ℤ)) = 0 :=
      cellDifference_margin_zero (R := ℤ) s hs ref (tag k) (r k) i j
    rw [h0, mul_zero]
  have h := low_eq_zero hq ref (fun v => w v - z v) hh hz
  exact ⟨a, ha, fun v => sub_eq_zero.mp (congrFun h v)⟩

/-- An integer coefficient can be implemented using copies from two
independently reserved orientations, each of capacity M. -/
theorem select_signed_copies {M : ℕ} (a : ℤ) (ha : |a| ≤ (M : ℤ)) :
    ∃ plus minus : Finset (Fin M),
      (plus.card : ℤ) - (minus.card : ℤ) = a ∧
      (plus = ∅ ∨ minus = ∅) := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp ha
  have hp : a.toNat ≤ M := by omega
  have hm : (-a).toNat ≤ M := by omega
  let plus : Finset (Fin M) := univ.map (Fin.castLEEmb hp)
  let minus : Finset (Fin M) := univ.map (Fin.castLEEmb hm)
  have hc₁ : plus.card = a.toNat := by simp [plus]
  have hc₂ : minus.card = (-a).toNat := by simp [minus]
  refine ⟨plus, minus, ?_, ?_⟩
  · rw [hc₁, hc₂]
    omega
  · rw [← card_eq_zero, ← card_eq_zero, hc₁, hc₂]
    omega

end KqR75.BankCapacity

#print axioms KqR75.BankCapacity.bounded_integer_correction
#print axioms KqR75.BankCapacity.select_signed_copies
