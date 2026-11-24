module
public import PhysicalBank
public import BasalBank

@[expose] public section
noncomputable section
namespace KqR75.PhysicalBank

open Finset ColouredCliques SlotProfiles CompleteJohnson

variable {C K : Type*} [Fintype C] [DecidableEq C]
  [Field K] [Fintype K] [DecidableEq K]

/-- The decomposition placed on the bank before the greedy process starts. -/
def basalBlocks {n q M : ℕ} {ref : C} (hq : 2 ≤ q)
    (r : High C q ref → Fin q) (s : Fin q → K) (hs : Function.Injective s)
    (f : Copy q ref M → (Fin q × K) ↪ Fin n) : Finset (Clique n q) :=
  univ.biUnion fun j => PhysicalAffineCell.blocks hq (f j) s hs
    (fun i => if ¬j.2.1 ∧ i = r j.1 then Equiv.swap 0 1 else Equiv.refl K)

/-- Implement a signed correction in the whole basal bank. Each unselected
cell retains its original decomposition and every edge has its original load. -/
theorem switch_whole_bank {n q M : ℕ} (hq : 2 ≤ q) (ref : C)
    (tag : High C q ref → Fin q → C) (r : High C q ref → Fin q)
    (s : Fin q → K) (hs : Function.Injective s) (colour : Fin n → C)
    (f : Copy q ref M → (Fin q × K) ↪ Fin n)
    (hcolour : ∀ j i x, colour (f j (i, x)) = if x = 0 then tag j.1 i else ref)
    (hsep : ∀ i j, i ≠ j → ((univ.map (f i)) ∩ (univ.map (f j))).card ≤ 1)
    (w : TypeProfile C q → ℤ) (a : High C q ref → ℤ)
    (ha : ∀ j, |a j| ≤ (M : ℤ))
    (hw : ∀ t, w t = ∑ j, a j * SlotPairMargins.cellDifference s ref (tag j) (r j) t) :
    ∃ P : Finset (Clique n q),
      (∀ e : Edge n,
        (P.filter (fun b => e ∈ SparseGram.resources n q b)).card =
          ((basalBlocks hq r s hs f).filter (fun b => e ∈ SparseGram.resources n q b)).card) ∧
      ∀ t, ((P.filter (fun b => cliqueType colour b = t)).card : ℤ) -
        (((basalBlocks hq r s hs f).filter (fun b => cliqueType colour b = t)).card : ℤ) = w t := by
  classical
  obtain ⟨selected, hload, hhist⟩ := switch_copies hq ref tag r s hs colour f hcolour hsep w a ha hw
  let I := Copy q ref M
  let oldσ (j : I) (i : Fin q) :=
    if ¬j.2.1 ∧ i = r j.1 then Equiv.swap (0 : K) 1 else Equiv.refl K
  let newσ (j : I) (i : Fin q) :=
    if j.2.1 ∧ i = r j.1 then Equiv.swap (0 : K) 1 else Equiv.refl K
  let afterσ (j : I) := if j ∈ selected then newσ j else oldσ j
  let old (j : I) := PhysicalAffineCell.blocks hq (f j) s hs (oldσ j)
  let new (j : I) := PhysicalAffineCell.blocks hq (f j) s hs (newσ j)
  let after (j : I) := PhysicalAffineCell.blocks hq (f j) s hs (afterσ j)
  let P := (univ : Finset I).biUnion after
  have hOld := PhysicalAffineCell.disjoint_blocks (univ : Finset I) hq f s hs oldσ
    (fun i _ j _ hij => hsep i j hij)
  have hAfter := PhysicalAffineCell.disjoint_blocks (univ : Finset I) hq f s hs afterσ
    (fun i _ j _ hij => hsep i j hij)
  have hNew := PhysicalAffineCell.disjoint_blocks selected hq f s hs newσ
    (fun i _ j _ hij => hsep i j hij)
  have hOldSel := PhysicalAffineCell.disjoint_blocks selected hq f s hs oldσ
    (fun i _ j _ hij => hsep i j hij)
  have hcount (A : Clique n q → Prop) [DecidablePred A] :
      ((P.filter A).card : ℤ) - (((basalBlocks hq r s hs f).filter A).card : ℤ) =
        (((selected.biUnion new).filter A).card : ℤ) -
          (((selected.biUnion old).filter A).card : ℤ) := by
    change (((univ.biUnion after).filter A).card : ℤ) -
        (((univ.biUnion old).filter A).card : ℤ) = _
    simp only [filter_biUnion]
    change ((univ.biUnion fun j => (after j).filter A).card : ℤ) -
        ((univ.biUnion fun j => (old j).filter A).card : ℤ) =
          ((selected.biUnion fun j => (new j).filter A).card : ℤ) -
          ((selected.biUnion fun j => (old j).filter A).card : ℤ)
    rw [card_biUnion (pairwiseDisjoint_filter hAfter A),
      card_biUnion (pairwiseDisjoint_filter hOld A),
      card_biUnion (pairwiseDisjoint_filter hNew A),
      card_biUnion (pairwiseDisjoint_filter hOldSel A)]
    simp only [Nat.cast_sum, ← sum_sub_distrib]
    rw [← sum_subset (subset_univ selected) (fun j _ hj => ?_)]
    · apply sum_congr rfl
      intro j hj
      simp [after, afterσ, hj, new]
    · simp [after, afterσ, hj, old]
  refine ⟨P, ?_, ?_⟩
  · intro e
    have h := hcount (fun b => e ∈ SparseGram.resources n q b)
    change ((P.filter (fun b => e ∈ SparseGram.resources n q b)).card : ℤ) -
        (((basalBlocks hq r s hs f).filter (fun b => e ∈ SparseGram.resources n q b)).card : ℤ) =
      (((selected.biUnion new).filter (fun b => e ∈ SparseGram.resources n q b)).card : ℤ) -
      (((selected.biUnion old).filter (fun b => e ∈ SparseGram.resources n q b)).card : ℤ) at h
    have he := hload e
    change ((selected.biUnion new).filter _).card = ((selected.biUnion old).filter _).card at he
    rw [he, sub_self] at h
    exact_mod_cast sub_eq_zero.mp h
  · intro t
    exact (hcount (fun b => cliqueType colour b = t)).trans (hhist t)

end KqR75.PhysicalBank

#print axioms KqR75.PhysicalBank.switch_whole_bank
