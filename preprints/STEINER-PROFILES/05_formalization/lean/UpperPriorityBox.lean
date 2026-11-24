module
public import UpperFootprint
public import Mathlib.Data.Fin.Rev

/-! The finite box count follows the argument in Juan Pablo Traverso
Gianini's CountingCone.LL.Order (Apache-2.0). -/

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset CompleteJohnson

variable {V β : Type*} [Fintype V] [DecidableEq V] [Fintype β] [DecidableEq β]

/-- Assign one of the allowed labels at each constrained coordinate. -/
def priorityBox (D : Finset V) (A : V → Finset β) : Finset (V → β) :=
  univ.filter fun lab => ∀ v ∈ D, lab v ∈ A v

theorem mem_priorityBox {D : Finset V} {A : V → Finset β} {lab : V → β} :
    lab ∈ priorityBox D A ↔ ∀ v ∈ D, lab v ∈ A v := by
  simp only [priorityBox, mem_filter, mem_univ, true_and]

theorem priorityBox_card (D : Finset V) (A : V → Finset β) :
    (priorityBox D A).card = (∏ v ∈ D, (A v).card) *
      (Fintype.card β) ^ (Fintype.card V - D.card) := by
  have h : priorityBox D A = Fintype.piFinset (fun v => if v ∈ D then A v else univ) := by
    ext lab
    rw [mem_priorityBox, Fintype.mem_piFinset]
    constructor
    · intro hl v
      by_cases hv : v ∈ D
      · simpa only [ite_eq_left hv] using hl v hv
      · simp [hv]
    · intro hl v hv
      simpa only [ite_eq_left hv] using hl v
  rw [h, Fintype.card_piFinset, ← prod_mul_prod_compl D]
  have h₁ : ∏ v ∈ D, (if v ∈ D then A v else univ).card = ∏ v ∈ D, (A v).card :=
    prod_congr rfl (fun v hv => by rw [ite_eq_left hv])
  have h₂ : ∏ v ∈ Dᶜ, (if v ∈ D then A v else (univ : Finset β)).card =
      (Fintype.card β) ^ Dᶜ.card := by
    rw [prod_congr rfl (fun v hv => by rw [ite_eq_right (mem_compl.mp hv)]), prod_const, card_univ]
  rw [h₁, h₂, card_compl]

/-- Conditioning on a box of priority assignments leaves the labels in
a disjoint set independent and uniform. This identity works even for
empty conditioning boxes. -/
theorem priorityBox_disjoint_ratio (D E : Finset V) (hDE : Disjoint D E)
    (A : V → Finset β) :
    (priorityBox (D ∪ E) A).card * (Fintype.card β) ^ E.card =
      (priorityBox D A).card * ∏ v ∈ E, (A v).card := by
  have hcard := (D ∪ E).card_le_univ
  rw [card_union_of_disjoint hDE] at hcard
  rw [priorityBox_card, priorityBox_card D, card_union_of_disjoint hDE, prod_union hDE]
  have he : Fintype.card V - (D.card + E.card) + E.card = Fintype.card V - D.card := by omega
  rw [← he, pow_add]
  ac_rfl

variable {L : ℕ}

/-- Larger labels appear first. The fixed vertex index breaks ties. -/
def priorityKey (lab : V → Fin L) (v : V) : ℕ :=
  (lab v).rev.val * Fintype.card V + (Fintype.equivFin V v).val

omit [DecidableEq V] in
private theorem priorityKey_lt_of_label_lt (lab : V → Fin L) {u v : V}
    (h : lab v < lab u) : priorityKey lab u < priorityKey lab v := by
  have hrev : (lab u).rev.val < (lab v).rev.val := by
    exact Fin.rev_lt_rev.mpr h
  have hui := (Fintype.equivFin V u).isLt
  have hmul := Nat.mul_le_mul_right (Fintype.card V) (Nat.succ_le_of_lt hrev)
  dsimp only [priorityKey]
  rw [Nat.succ_mul] at hmul
  omega

theorem priorityKey_label_le (lab : V → Fin L) {u v : V} (h : priorityKey lab u ≤ priorityKey lab v) :
    lab v ≤ lab u :=
  le_of_not_gt (fun hv => not_lt_of_ge h (priorityKey_lt_of_label_lt lab hv))

theorem priorityKey_injective (lab : V → Fin L) : Function.Injective (priorityKey lab) := by
  intro u v he
  have hl := le_antisymm (priorityKey_label_le lab he.ge) (priorityKey_label_le lab he.le)
  have hidx : (Fintype.equivFin V u).val = (Fintype.equivFin V v).val := by
    dsimp only [priorityKey] at he
    rw [hl] at he
    omega
  exact (Fintype.equivFin V).injective (Fin.ext hidx)

theorem strict_labels_active {n q : ℕ} (P : FullPacking n q)
    (lab : Edge n → Fin L) (e : Edge n)
    (h : ∀ f ∈ (SparseGram.resources n q (owner P.property e)).erase e, lab f < lab e) :
    active P.property (priorityKey lab) e := by
  intro f hf
  by_cases he : f = e
  · simp [he]
  · exact (priorityKey_lt_of_label_lt lab (h f (mem_erase.mpr ⟨he, hf⟩))).le

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.priorityBox_disjoint_ratio
#print axioms KqR75.UpperCounting.priorityKey_injective
