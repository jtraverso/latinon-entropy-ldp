module
public import ColouredCliques
public import AffineCellCounts
public import Mathlib.Data.Fintype.Sigma
public import GradedColumns

@[expose] public section
noncomputable section
namespace KqR75.SlotProfiles

open Finset ColouredCliques

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Treat the set of group indices as one complete block to use the same
type profiles as the physical clique incidence. -/
def slotType {q : ℕ} (tag : Fin q → C) : TypeProfile C q :=
  cliqueType tag ⟨univ, mem_powersetCard.mpr ⟨subset_rfl, by simp⟩⟩

def degree {q : ℕ} (ref : C) (u : TypeProfile C q) : ℕ :=
  ∑ i ∈ univ.erase ref, (u.val i : ℕ)

theorem degree_slotType {q : ℕ} (ref : C) (tag : Fin q → C) :
    degree ref (slotType tag) = (AffineCellCounts.active tag ref).card := by
  simpa [degree, slotType, cliqueType, profile, part, AffineCellCounts.active] using
    (sum_card_fiberwise_eq_card_filter (univ : Finset (Fin q)) (univ.erase ref) tag)

private def sigmaFibre {q : ℕ} (u : TypeProfile C q) (i : C) :
    {x : (Σ j : C, Fin (u.val j : ℕ)) // x.1 = i} ≃ Fin (u.val i : ℕ) where
  toFun x := x.property ▸ x.val.2
  invFun x := ⟨⟨i, x⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨j, x⟩, h⟩
    change j = i at h
    subst j
    rfl
  right_inv := by intro x; rfl

theorem slotType_surjective (q : ℕ) : Function.Surjective (slotType (C := C) (q := q)) := by
  classical
  intro u
  have hc : Fintype.card (Fin q) = Fintype.card (Σ i : C, Fin (u.val i : ℕ)) := by
    simp only [Fintype.card_fin, Fintype.card_sigma, u.property]
  let E := Fintype.equivOfCardEq hc
  let tag : Fin q → C := fun x => (E x).1
  have he (i : C) :
      {x : Fin q // tag x = i} ≃ {x : (Σ j : C, Fin (u.val j : ℕ)) // x.1 = i} :=
    E.subtypeEquiv (fun _ => Iff.rfl)
  refine ⟨tag, ?_⟩
  apply Subtype.ext
  funext i
  apply Fin.ext
  change ((univ : Finset (Fin q)).filter (fun x => tag x = i)).card = _
  have hf := Fintype.card_congr ((he i).trans (sigmaFibre u i))
  let S := (univ : Finset (Fin q)).filter (fun x => tag x = i)
  have hsub : ↥S ≃ {x : Fin q // tag x = i} :=
    Equiv.subtypeEquivRight (fun x => by simp [S])
  calc
    _ = Fintype.card S := (Fintype.card_coe S).symm
    _ = Fintype.card {x : Fin q // tag x = i} := Fintype.card_congr hsub
    _ = (u.val i : ℕ) := by simpa only [Fintype.card_fin] using hf

abbrev High (C : Type*) [Fintype C] [DecidableEq C] (q : ℕ) (ref : C) :=
  {u : TypeProfile C q // 2 < degree ref u}

/-- Each high profile has a column realised by the indicated group swap.
It preserves every statistic given by a sum over distinct pairs of slots. -/
theorem cell_column {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {q : ℕ} (s : Fin q → K) (hs : Function.Injective s)
    (ref : C) (u : High C q ref) :
    ∃ tag : Fin q → C, ∃ r : Fin q, slotType tag = (u : TypeProfile C q) ∧
      let z : TypeProfile C q → ℤ := fun v =>
        AffineCellCounts.histogram slotType s (fun _ => Equiv.refl K) tag ref v -
          AffineCellCounts.histogram slotType s
            (fun i => if i = r then Equiv.swap 0 1 else Equiv.refl K) tag ref v
      (∀ v, degree ref u.val ≤ degree ref v → z v = if u.val = v then 1 else 0) ∧
      ∀ (a : TypeProfile C q → ℤ) (P : Finset (Fin q × Fin q))
        (hP : ∀ ij ∈ P, ij.1 ≠ ij.2) (f : C → C → ℤ),
        (∀ labels, a (slotType labels) = ∑ ij ∈ P, f (labels ij.1) (labels ij.2)) →
        ∑ v, z v * a v = 0 := by
  classical
  obtain ⟨tag, htag⟩ := slotType_surjective q u.val
  have hd : 2 < (AffineCellCounts.active tag ref).card := by
    rw [← degree_slotType, htag]
    exact u.property
  obtain ⟨i, hi, j, hj, r, hr, hij, hir, hjr⟩ := two_lt_card.mp hd
  have htag' {i : Fin q} (hi : i ∈ AffineCellCounts.active tag ref) : tag i ≠ ref :=
    (mem_filter.mp hi).2
  refine ⟨tag, r, htag, ?_, ?_⟩
  · intro v hv
    have hv' : degree ref (slotType tag) ≤ degree ref v := by simpa only [htag] using hv
    have ht := AffineCellCounts.top_difference slotType (degree ref) ref (degree_slotType ref)
      s tag (fun h => hij (hs h)) hir hjr (htag' hi) (htag' hj) (htag' hr)
      (Equiv.swap 0 1 : Equiv.Perm K) (by simp) v hv'
    rw [htag] at ht
    exact ht
  · intro a P hP f ha
    simp only [sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (AffineCellCounts.histogram_pair_invariant slotType a P s
      (fun ij hij h => hP ij hij (hs h)) f ha tag ref
      (fun i => if i = r then Equiv.swap 0 1 else Equiv.refl K)).symm

/-- Choose one affine cell per high type. The integer matrix on high
coordinates has a fixed right inverse. -/
theorem cell_high_coordinates {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {q : ℕ} (s : Fin q → K) (hs : Function.Injective s) (ref : C) :
    ∃ (tag : High C q ref → Fin q → C) (r : High C q ref → Fin q)
      (L : High C q ref → High C q ref → ℤ),
      (∀ j, slotType (tag j) = j.val) ∧
      ∀ i j : High C q ref,
        (∑ k, L j k *
          (AffineCellCounts.histogram slotType s (fun _ => Equiv.refl K) (tag k) ref i.val -
           AffineCellCounts.histogram slotType s
             (fun a => if a = r k then Equiv.swap 0 1 else Equiv.refl K) (tag k) ref i.val)) =
          if i = j then 1 else 0 := by
  classical
  choose tag r htag htop hpair using fun u : High C q ref => cell_column s hs ref u
  let col (j i : High C q ref) :=
    AffineCellCounts.histogram slotType s (fun _ => Equiv.refl K) (tag j) ref i.val -
      AffineCellCounts.histogram slotType s
        (fun a => if a = r j then Equiv.swap 0 1 else Equiv.refl K) (tag j) ref i.val
  have hdiag (i : High C q ref) : col i i = 1 := by
    have h := htop i i.val le_rfl
    change col i i = (if i.val = i.val then (1 : ℤ) else 0) at h
    simpa using h
  have htri (i j : High C q ref) (hle : degree ref j.val ≤ degree ref i.val) (hne : j ≠ i) :
      col j i = 0 := by
    have hv : j.val ≠ i.val := fun h => hne (Subtype.ext h)
    simpa only [hv, ite_false] using htop j i.val hle
  obtain ⟨L, hL⟩ := GradedColumns.right_inverse (fun j : High C q ref => degree ref j.val)
    col hdiag htri
  exact ⟨tag, r, L, htag, hL⟩

end KqR75.SlotProfiles

#print axioms KqR75.SlotProfiles.degree_slotType
#print axioms KqR75.SlotProfiles.slotType_surjective
#print axioms KqR75.SlotProfiles.cell_column
#print axioms KqR75.SlotProfiles.cell_high_coordinates
