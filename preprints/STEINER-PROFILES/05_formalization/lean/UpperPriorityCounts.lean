module
public import UpperPriorityBox
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset ColouredCliques CompleteJohnson SparseGram

/-- The test edge has label z and the other edges of its true block
have strictly smaller labels. -/
def strictBox {n q L : ℕ} (P : FullPacking n q) (e : Edge n) (z : Fin L) :
    Finset (Edge n → Fin L) :=
  priorityBox (resources n q (owner P.property e)) (fun v => if v = e then {z} else Iio z)

theorem mem_strictBox {n q L : ℕ} (P : FullPacking n q) (e : Edge n) (z : Fin L)
    (lab : Edge n → Fin L) : lab ∈ strictBox P e z ↔
      lab e = z ∧ ∀ f ∈ (resources n q (owner P.property e)).erase e, lab f < z := by
  rw [strictBox, mem_priorityBox]
  constructor
  · intro h
    refine ⟨by simpa using h e (owner_spec P.property e).2, ?_⟩
    intro f hf
    simpa only [ite_eq_right (ne_of_mem_erase hf), mem_Iio] using h f (mem_of_mem_erase hf)
  · rintro ⟨he, h⟩ f hf
    by_cases hf₀ : f = e
    · subst f
      simp [he]
    · simpa only [ite_eq_right hf₀, mem_Iio] using h f (mem_erase.mpr ⟨hf₀, hf⟩)

theorem strictBox_card {n q L : ℕ} (P : FullPacking n q) (e : Edge n) (z : Fin L) :
    (strictBox P e z).card = (z.val) ^ (q.choose 2 - 1) *
      L ^ (Fintype.card (Edge n) - q.choose 2) := by
  let D := resources n q (owner P.property e)
  have he : e ∈ D := (owner_spec P.property e).2
  have heq : ∏ v ∈ D, (if v = e then {z} else Iio z).card = z.val ^ (q.choose 2 - 1) := by
    rw [← mul_prod_erase D _ he]
    simp only [ite_true, card_singleton, one_mul]
    rw [prod_congr rfl (fun v hv => by rw [ite_eq_right (ne_of_mem_erase hv)]), prod_const,
      Fin.card_Iio, card_erase_of_mem he, show D.card = q.choose 2 from resources_card n q _]
  rw [strictBox, priorityBox_card, heq, Fintype.card_fin, resources_card]

/-- Within the strict box, an ordinary available candidate requires
r(r-1) further independent labels to be at most the test label. -/
theorem ordinary_availability_card {n q L : ℕ} (P : FullPacking n q) (e : Edge n) (z : Fin L)
    (b : Clique n q) (he : e ∈ resources n q b) (hb : b ∉ exceptional P.val e) :
    let k := (q.choose 2 - 1) * q.choose 2
    ((strictBox P e z).filter (fun lab => b ∈ availableCandidates P (priorityKey lab) e)).card *
      L ^ k ≤ (strictBox P e z).card * (z.val + 1) ^ k := by
  classical
  let D := resources n q (owner P.property e)
  let E := requiredEdges P e b
  obtain ⟨hE, hdis⟩ := required_edges_of_nonexceptional P e b he hb
  let A (v : Edge n) := if v ∈ D then (if v = e then {z} else Iio z) else Iic z
  have hD : priorityBox D A = strictBox P e z := by
    ext lab
    rw [strictBox, mem_priorityBox, mem_priorityBox]
    constructor
    · intro h v hv
      have h' := h v hv
      change lab v ∈ (if v ∈ D then (if v = e then {z} else Iio z) else Iic z) at h'
      rwa [ite_eq_left hv] at h'
    · intro h v hv
      change lab v ∈ (if v ∈ D then (if v = e then {z} else Iio z) else Iic z)
      rw [ite_eq_left hv]
      exact h v hv
  have hproduct : ∏ v ∈ E, (A v).card = (z.val + 1) ^ ((q.choose 2 - 1) * q.choose 2) := by
    have hval (v : Edge n) (hv : v ∈ E) : (A v).card = z.val + 1 := by
      change (if v ∈ D then (if v = e then {z} else Iio z) else Iic z).card = _
      rw [ite_eq_right (fun hv' => disjoint_left.mp hdis hv hv'), Fin.card_Iic]
    rw [prod_congr rfl hval, prod_const]
    rw [show E.card = (q.choose 2 - 1) * q.choose 2 from hE]
  have hratio := priorityBox_disjoint_ratio D E hdis.symm A
  rw [hD, hproduct, Fintype.card_fin, show E.card = (q.choose 2 - 1) * q.choose 2 from hE] at hratio
  have hsub : (strictBox P e z).filter (fun lab => b ∈ availableCandidates P (priorityKey lab) e)
      ⊆ priorityBox (D ∪ E) A := by
    intro lab hl
    obtain ⟨hbox, hcan⟩ := mem_filter.mp hl
    have hbox' := (mem_priorityBox.mp (hD.symm ▸ hbox))
    have hz := ((mem_strictBox P e z lab).mp hbox).1
    simp only [availableCandidates, mem_filter, mem_univ, true_and] at hcan
    have hlate := hcan.2.resolve_left hb
    apply mem_priorityBox.mpr
    intro v hv
    rcases mem_union.mp hv with hd | he'
    · exact hbox' v hd
    · change lab v ∈ (if v ∈ D then (if v = e then {z} else Iio z) else Iic z)
      rw [ite_eq_right (fun hv' => disjoint_left.mp hdis he' hv'), mem_Iic, ← hz]
      exact priorityKey_label_le lab (hlate v he')
  change _ * L ^ ((q.choose 2 - 1) * q.choose 2) ≤ _
  exact (Nat.mul_le_mul_right _ (card_le_card hsub)).trans_eq hratio

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.strictBox_card
#print axioms KqR75.UpperCounting.ordinary_availability_card
