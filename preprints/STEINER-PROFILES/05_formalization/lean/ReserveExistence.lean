module
public import ReserveRootLaws
public import Mathlib.Data.Nat.Choose.Bounds

@[expose] public section
noncomputable section
namespace KqR75.ReserveRandom

open Finset MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]

private def roots (V : Type*) [Fintype V] [DecidableEq V] (d : ℕ) : Finset (Finset V) :=
  (range (d + 1)).biUnion (fun h => (univ : Finset V).powersetCard h)

private theorem mem_roots (H : Finset V) (d : ℕ) : H ∈ roots V d ↔ H.card ≤ d := by
  simp only [roots, mem_biUnion, mem_range, mem_powersetCard, subset_univ, true_and]
  exact ⟨fun ⟨j, hj, hc⟩ => by omega, fun h => ⟨H.card, by omega, rfl⟩⟩

private theorem roots_card (d : ℕ) :
    (roots V d).card ≤ (d + 1) * (Fintype.card V + 1) ^ d := by
  unfold roots
  refine (card_biUnion_le_card_mul _ _ _ (fun h hh => ?_)).trans_eq (by rw [card_range])

  rw [card_powersetCard, card_univ]
  refine (Nat.choose_le_pow _ _).trans ?_
  exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
    (Nat.pow_le_pow_right (by omega) (by have := mem_range.mp hh; omega))

/-- The two common-neighbour tests needed by the cover-down argument. -/
def RootGood (p : unitInterval) (ω : Sym2 V → Bool) (d : ℕ) : Prop :=
  ∀ H : Finset V, H.card ≤ d →
    let N := ((ReserveCuts.common (adj ω) univ H).card : ℝ)
    N ≤ 2 * (Fintype.card V : ℝ) * (p : ℝ) ^ H.card ∧
      (H.card ≤ 2 → ((Fintype.card V : ℝ) * (p : ℝ) ^ H.card) / 2 ≤ N)

theorem roots_failure (p : unitInterval) (d : ℕ) (hn : 4 * d ≤ Fintype.card V) :
    (law V p).real {ω | ¬ RootGood p ω d} ≤
      ((d + 1 : ℕ) : ℝ) * ((Fintype.card V : ℝ) + 1) ^ d *
        (2 * Real.exp (-((Fintype.card V : ℝ) * (p : ℝ) ^ d) / 72)) := by
  classical
  let n : ℝ := Fintype.card V
  let N := fun (H : Finset V) (ω : Sym2 V → Bool) =>
    ((ReserveCuts.common (adj ω) univ H).card : ℝ)
  let bad := fun H : ↥(roots V d) =>
    {ω | ¬ (N H ω ≤ 2 * n * (p : ℝ) ^ H.val.card ∧
      (H.val.card ≤ 2 → n * (p : ℝ) ^ H.val.card / 2 ≤ N H ω))}
  let e := 2 * Real.exp (-(n * (p : ℝ) ^ d) / 72)
  have he : 0 ≤ e := by unfold e; positivity
  have hcover : {ω | ¬ RootGood p ω d} ⊆ ⋃ i, bad i := by
    intro ω hw
    change ¬ RootGood p ω d at hw
    unfold RootGood at hw
    simp only [not_forall] at hw
    obtain ⟨H, hHd, hw⟩ := hw
    exact Set.mem_iUnion.mpr ⟨⟨H, (mem_roots H d).mpr hHd⟩, hw⟩
  have htest (H : ↥(roots V d)) : (law V p).real (bad H) ≤ e := by
    let b : ℝ := (p : ℝ) ^ H.val.card
    let m := (n - H.val.card) * b
    have hb : 0 ≤ b := pow_nonneg p.2.1 _
    have hHd := (mem_roots H.val d).mp H.property
    have h4H : (4 : ℝ) * H.val.card ≤ n := by
      dsimp [n]
      exact_mod_cast (Nat.mul_le_mul_left 4 hHd).trans hn
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    have hpow : (p : ℝ) ^ d ≤ b := by
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hHd
      rw [(congrArg (fun k : ℕ => (p : ℝ) ^ k) hj).trans (pow_add _ _ _)]
      exact mul_le_of_le_one_right hb (pow_le_one₀ p.2.1 p.2.2)
    have hmlo : n * (p : ℝ) ^ d / 2 ≤ m := by
      calc
        _ = (n / 2) * (p : ℝ) ^ d := by ring
        _ ≤ (n / 2) * b := mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hb
    have hlo : n * b / 2 ≤ (2 / 3) * m := by
      have h := mul_le_mul_of_nonneg_right h4H hb
      dsimp [m]
      nlinarith only [h]
    have hup : 2 * m ≤ 2 * n * b := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (sub_le_self _ (Nat.cast_nonneg _)) hb) (by norm_num)
    let low := {ω | N H ω ≤ (2 / 3) * m}
    let high := {ω | 2 * m ≤ N H ω}
    have hsub : bad H ⊆ low ∪ high := by
      intro ω hw
      by_cases hu : N H ω ≤ 2 * n * b
      · apply Or.inl
        apply le_trans _ hlo
        exact le_of_not_ge (fun hh => hw ⟨hu, fun _ => hh⟩)
      · exact Or.inr (hup.trans (lt_of_not_ge hu).le)
    have htail := common_tails p (univ : Finset V) H.val (subset_univ _)
    simp only [card_univ] at htail
    change (law V p).real low ≤ Real.exp (-m / 36) ∧
      (law V p).real high ≤ Real.exp (-m / 6) at htail
    calc
      _ ≤ (law V p).real (low ∪ high) := measureReal_mono hsub
      _ ≤ (law V p).real low + (law V p).real high := measureReal_union_le _ _
      _ ≤ Real.exp (-m / 36) + Real.exp (-m / 6) := add_le_add htail.1 htail.2
      _ ≤ e := by
        have hnP : 0 ≤ n * (p : ℝ) ^ d := mul_nonneg hn0 (pow_nonneg p.2.1 _)
        dsimp [e]
        rw [two_mul]
        exact add_le_add (Real.exp_le_exp.mpr (by linarith)) (Real.exp_le_exp.mpr (by linarith))
  calc
    _ ≤ (law V p).real (⋃ i, bad i) := measureReal_mono hcover
    _ ≤ ∑ i, (law V p).real (bad i) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _i : ↥(roots V d), e := sum_le_sum (fun i _ => htest i)
    _ = ((roots V d).card : ℝ) * e := by simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have h := roots_card (V := V) d
      apply mul_le_mul_of_nonneg_right _ he
      exact_mod_cast h

/-- A reserve exists when the two explicit failure budgets sum to less than one. -/
theorem exists_reserve (p : unitInterval) (t d : ℕ) (hn : 4 * d ≤ Fintype.card V)
    (hbudget : (4 : ℝ) ^ Fintype.card V * Real.exp (-((p : ℝ) * t ^ 2) / 36) +
      ((d + 1 : ℕ) : ℝ) * ((Fintype.card V : ℝ) + 1) ^ d *
        (2 * Real.exp (-((Fintype.card V : ℝ) * (p : ℝ) ^ d) / 72)) < 1) :
    ∃ ω : Sym2 V → Bool, ReserveCuts.cutLower (adj ω) (p : ℝ) t ∧ RootGood p ω d := by
  classical
  by_contra! h
  let A : Set (Sym2 V → Bool) := {ω | ¬ ReserveCuts.cutLower (adj ω) (p : ℝ) t}
  let B : Set (Sym2 V → Bool) := {ω | ¬ RootGood p ω d}
  have he : A ∪ B = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    by_cases hA : ω ∈ A
    · exact Or.inl hA
    · exact Or.inr (h ω (not_not.mp hA))
  have hl := (measureReal_union_le (μ := law V p) A B).trans
    (add_le_add (cut_failure (V := V) p t) (roots_failure (V := V) p d hn))
  simp [he] at hl
  exact (not_le_of_gt hbudget) (by simpa using hl)

end KqR75.ReserveRandom

#print axioms KqR75.ReserveRandom.roots_failure
#print axioms KqR75.ReserveRandom.exists_reserve
