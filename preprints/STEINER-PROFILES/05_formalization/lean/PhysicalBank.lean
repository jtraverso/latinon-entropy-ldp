module
public import BankPlacement
public import BankCapacity
public import PhysicalAffineCell

@[expose] public section
noncomputable section
namespace KqR75.PhysicalBank

open Finset ColouredCliques SlotProfiles

variable {C K : Type*} [Fintype C] [DecidableEq C]
  [Field K] [Fintype K] [DecidableEq K]

abbrev Copy (q : ℕ) (ref : C) (M : ℕ) := High C q ref × Bool × Fin M

/-- Reserve M copies per generator in each orientation on the physical
vertex set. The degree bound counts even the unused within-group pairs. -/
theorem place_copies {n q M : ℕ} (ref : C) (tag : High C q ref → Fin q → C)
    (colour : Fin n → C) (forbidden : Fin n → Finset (Fin n))
    (degree cap budget : ℕ) (hcap : 0 < cap)
    (hforbid : ∀ v, (forbidden v).card ≤ degree)
    (hsym : ∀ a b, a ∈ forbidden b ↔ b ∈ forbidden a)
    (htotal : (Fintype.card (High C q ref) * (2 * M)) * (q * Fintype.card K) ≤ budget * cap)
    (hspace : ∀ c, budget + (q * Fintype.card K) * (degree + (q * Fintype.card K) * cap + 1) <
      profile colour univ c) :
    ∃ f : Copy q ref M → (Fin q × K) ↪ Fin n,
      (∀ j i x, colour (f j (i, x)) = if x = 0 then tag j.1 i else ref) ∧
      (∀ j x y, x ≠ y → f j x ∉ forbidden (f j y)) ∧
      (∀ i j, i ≠ j → ((univ.map (f i)) ∩ (univ.map (f j))).card ≤ 1) ∧
      ∀ v, ((univ : Finset (Copy q ref M)).biUnion fun j =>
        if v ∈ univ.map (f j) then univ.map (f j) else ∅).card ≤ (q * Fintype.card K) * cap := by
  classical
  let labels (j : Copy q ref M) (x : Fin q × K) := if x.2 = 0 then tag j.1 x.1 else ref
  have hcount : Fintype.card (Copy q ref M) * Fintype.card (Fin q × K) ≤ budget * cap := by
    simpa only [Copy, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using htotal
  obtain ⟨f, hf, havoid, hsep, hdegree⟩ := BankPlacement.place_indexed_bank labels
    (part colour univ) forbidden degree cap budget hcap hforbid hsym hcount
    (by simpa only [Fintype.card_prod, Fintype.card_fin, profile] using hspace)
  refine ⟨f, ?_, havoid, hsep, ?_⟩
  · intro j i x
    exact (mem_filter.mp (hf j (i, x))).2
  · simpa only [Fintype.card_prod, Fintype.card_fin] using hdegree

/-- Select actual copies for an integer correction. The resulting switches
preserve every edge load and add the whole requested type histogram. -/
theorem switch_copies {n q M : ℕ} (hq : 2 ≤ q) (ref : C)
    (tag : High C q ref → Fin q → C) (r : High C q ref → Fin q)
    (s : Fin q → K) (hs : Function.Injective s) (colour : Fin n → C)
    (f : Copy q ref M → (Fin q × K) ↪ Fin n)
    (hcolour : ∀ j i x, colour (f j (i, x)) = if x = 0 then tag j.1 i else ref)
    (hsep : ∀ i j, i ≠ j → ((univ.map (f i)) ∩ (univ.map (f j))).card ≤ 1)
    (w : TypeProfile C q → ℤ) (a : High C q ref → ℤ)
    (ha : ∀ j, |a j| ≤ (M : ℤ))
    (hw : ∀ t, w t = ∑ j, a j * SlotPairMargins.cellDifference s ref (tag j) (r j) t) :
    ∃ selected : Finset (Copy q ref M),
      let after := selected.biUnion fun j => PhysicalAffineCell.blocks hq (f j) s hs
        (fun i => if j.2.1 ∧ i = r j.1 then Equiv.swap 0 1 else Equiv.refl K)
      let before := selected.biUnion fun j => PhysicalAffineCell.blocks hq (f j) s hs
        (fun i => if ¬j.2.1 ∧ i = r j.1 then Equiv.swap 0 1 else Equiv.refl K)
      (∀ e : CompleteJohnson.Edge n,
        (after.filter fun b => e ∈ SparseGram.resources n q b).card =
        (before.filter fun b => e ∈ SparseGram.resources n q b).card) ∧
      ∀ t, ((after.filter (fun b => cliqueType colour b = t)).card : ℤ) -
        ((before.filter (fun b => cliqueType colour b = t)).card : ℤ) = w t := by
  classical
  choose plus minus hcount _hsign using fun j => BankCapacity.select_signed_copies (a j) (ha j)
  let selected : Finset (Copy q ref M) := univ.filter fun j =>
    if j.2.1 then j.2.2 ∈ minus j.1 else j.2.2 ∈ plus j.1
  have hsum (t : TypeProfile C q) :
      (∑ j ∈ selected, (if j.2.1 then -1 else 1) *
        SlotPairMargins.cellDifference s ref (tag j.1) (r j.1) t) = w t := by
    dsimp only [selected]
    rw [hw, sum_filter, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro j _
    let col := SlotPairMargins.cellDifference s ref (tag j) (r j) t
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    change (∑ k : Fin M, if k ∈ minus j then -1 * col else 0) +
        (∑ k : Fin M, if k ∈ plus j then 1 * col else 0) = a j * col
    rw [← sum_filter, ← sum_filter, filter_mem_eq_of_subset (subset_univ (minus j)),
      filter_mem_eq_of_subset (subset_univ (plus j))]
    simp only [sum_const, nsmul_eq_mul]
    rw [← hcount j]
    ring
  obtain ⟨hload, hhist⟩ := PhysicalAffineCell.switch_disjoint_cells selected hq f s hs
    (fun j => r j.1) (fun j => tag j.1) (fun j => j.2.1) ref colour
    (fun j _ => hcolour j) (fun i _ j _ => hsep i j)
  exact ⟨selected, hload, fun t => (hhist t).trans (hsum t)⟩

end KqR75.PhysicalBank

#print axioms KqR75.PhysicalBank.place_copies
#print axioms KqR75.PhysicalBank.switch_copies
