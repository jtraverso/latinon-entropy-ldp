module
public import CoverDown

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Finset
open ReserveCuts

variable {V : Type*} [DecidableEq V]

private theorem extension_mem (R : V → V → Prop) [DecidableRel R]
    (S H : Finset V) (k : ℕ) (C : Finset V) :
    C ∈ extensions R S H k ↔
      C ⊆ common R S H ∧ C.card = k ∧ (C : Set V).Pairwise R := by
  rw [extensions, cliquesIn, mem_filter, mem_powersetCard, and_assoc]

/-- A specified set of auxiliary vertices consumes that many places
in the extension and joins the original roots. -/
theorem extension_fibre_density (R : V → V → Prop) [DecidableRel R]
    (hirr : ∀ v, ¬ R v v) (S : Finset V) (p : ℝ) (hp : 0 ≤ p) (d : ℕ)
    (hcommon : ∀ H ⊆ S, H.card < d →
      ((common R S H).card : ℝ) ≤ 2 * (S.card : ℝ) * p ^ H.card)
    (H A : Finset V) (k : ℕ) (hH : H ⊆ S) (hk : H.card + k ≤ d) :
    (((extensions R S H k).filter (A ⊆ ·)).card : ℝ) ≤
      (2 * (S.card : ℝ)) ^ (k - A.card) *
        p ^ ((H.card + A.card) * (k - A.card) + (k - A.card).choose 2) := by
  by_cases hex : ((extensions R S H k).filter (A ⊆ ·)).Nonempty
  · obtain ⟨C, hC⟩ := hex
    obtain ⟨hm, hAC⟩ := mem_filter.mp hC
    obtain ⟨hc, hcard, _⟩ := (extension_mem R S H k C).mp hm
    have hA : A ⊆ S := hAC.trans (hc.trans (filter_subset _ _))
    have hAk : A.card ≤ k := hcard ▸ card_le_card hAC
    have hd : Disjoint H A := by
      refine disjoint_left.mpr fun v hvH hvA => hirr v ?_
      exact (mem_filter.mp (hc (hAC hvA))).2 v hvH
    have hsize : (H ∪ A).card + (k - A.card) ≤ d := by
      rw [card_union_of_disjoint hd]
      omega
    have hf := extension_fibre_le R S H A k
    have hu := extensions_card_le_density R hirr S p hp d hcommon
      (H ∪ A) (union_subset hH hA) (k - A.card) hsize
    rw [card_union_of_disjoint hd] at hu
    exact (by exact_mod_cast hf : (_ : ℝ) ≤ _).trans hu
  · rw [not_nonempty_iff_eq_empty.mp hex, card_empty, Nat.cast_zero]
    positivity

/-- The forbidden objects used by cover-down are auxiliary vertices
and unordered pairs contained in the auxiliary clique. -/
theorem exists_clean_extension (R : V → V → Prop) [DecidableRel R]
    (S H Z : Finset V) (Y : Finset (Finset V)) (k : ℕ)
    (bf : V → ℕ) (be : Finset V → ℕ)
    (hv : ∀ v ∈ Z, ((extensions R S H k).filter (fun C => v ∈ C)).card ≤ bf v)
    (he : ∀ e ∈ Y, ((extensions R S H k).filter (e ⊆ ·)).card ≤ be e)
    (hroom : (∑ v ∈ Z, bf v) + (∑ e ∈ Y, be e) < (extensions R S H k).card) :
    ∃ C ∈ extensions R S H k, Disjoint C Z ∧ Disjoint (C.powersetCard 2) Y := by
  classical
  let F : Finset (V ⊕ Finset V) := Z.disjSum Y
  let bad : (V ⊕ Finset V) → Finset V → Prop := Sum.elim (fun v C => v ∈ C) (fun e C => e ⊆ C)
  let b := Sum.elim bf be
  have hbad (i : V ⊕ Finset V) (hi : i ∈ F) : ((extensions R S H k).filter (bad i)).card ≤ b i := by
    cases i with
    | inl v =>
      have hf : (extensions R S H k).filter (bad (.inl v)) =
          (extensions R S H k).filter (fun C => v ∈ C) := by
        exact Finset.filter_congr (fun _ _ => Iff.rfl)
      rw [hf]
      exact hv v (by simpa [F] using hi)
    | inr e =>
      have hf : (extensions R S H k).filter (bad (.inr e)) =
          (extensions R S H k).filter (e ⊆ ·) := by
        exact Finset.filter_congr (fun _ _ => Iff.rfl)
      rw [hf]
      exact he e (by simpa [F] using hi)
  have hs : ∑ i ∈ F, b i < (extensions R S H k).card := by
    simpa [F, b] using hroom
  obtain ⟨C, hC, hn⟩ := exists_avoiding (extensions R S H k) F bad b hbad hs
  refine ⟨C, hC, disjoint_left.mpr ?_, disjoint_left.mpr ?_⟩
  · intro v hcv hz
    exact hn (.inl v) (by simpa [F] using hz) hcv
  · intro e hce hy
    exact hn (.inr e) (by simpa [F] using hy) (mem_powersetCard.mp hce).1

/-- The real-valued obstruction budgets can be used directly in the
selection rule without rounding the asymptotic estimates upward. -/
theorem exists_clean_extension_of_bounds (R : V → V → Prop) [DecidableRel R]
    (S H Z : Finset V) (Y : Finset (Finset V)) (k : ℕ)
    (bv be : ℝ) (hv₀ : 0 ≤ bv) (he₀ : 0 ≤ be)
    (hv : ∀ v ∈ Z, (((extensions R S H k).filter (fun C => v ∈ C)).card : ℝ) ≤ bv)
    (he : ∀ e ∈ Y, (((extensions R S H k).filter (e ⊆ ·)).card : ℝ) ≤ be)
    (hroom : (Z.card : ℝ) * bv + (Y.card : ℝ) * be < (extensions R S H k).card) :
    ∃ C ∈ extensions R S H k, Disjoint C Z ∧ Disjoint (C.powersetCard 2) Y := by
  refine exists_clean_extension R S H Z Y k (fun _ => ⌊bv⌋₊) (fun _ => ⌊be⌋₊)
    (fun v hz => Nat.le_floor (hv v hz)) (fun e hy => Nat.le_floor (he e hy)) ?_
  have hV : (Z.card : ℝ) * (⌊bv⌋₊ : ℝ) ≤ (Z.card : ℝ) * bv :=
    mul_le_mul_of_nonneg_left (Nat.floor_le hv₀) (Nat.cast_nonneg _)
  have hE : (Y.card : ℝ) * (⌊be⌋₊ : ℝ) ≤ (Y.card : ℝ) * be :=
    mul_le_mul_of_nonneg_left (Nat.floor_le he₀) (Nat.cast_nonneg _)
  rw [sum_const, sum_const, Nat.nsmul_eq_mul, Nat.nsmul_eq_mul]
  exact_mod_cast (add_le_add hV hE).trans_lt hroom

end KqR75.CoverDown

#print axioms KqR75.CoverDown.extension_fibre_density
#print axioms KqR75.CoverDown.exists_clean_extension
#print axioms KqR75.CoverDown.exists_clean_extension_of_bounds
