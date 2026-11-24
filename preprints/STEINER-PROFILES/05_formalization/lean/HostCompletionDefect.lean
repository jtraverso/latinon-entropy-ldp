module
public import CompletionBudget

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Finset ColouredCliques CompleteJohnson SparseGram WeightedGreedy
open BankCapacity (integerHistogram)

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Bound the defect of the actual assembled baseline design. Its
reserve and absorber losses determine the coefficient before the
number of bank cells is chosen. -/
theorem defect_of_assembled_history {n q : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n)
    (colour : Fin n → C) (m : TypeProfile C q → ℤ)
    (A X F Y : Finset (Edge n)) (hAX : Disjoint A X) (hAF : Disjoint A F)
    (hXF : Disjoint X F) (hY : Y ⊆ X)
    (h : List (Option (Clique n q))) (PB P₀ PC PA : Finset (Clique n q))
    (hv : valid (resources n q) (A ∪ X ∪ F)ᶜ h)
    (hbank : packs PB F) (hbasal : packs P₀ A)
    (hcover : packs PC (remaining (resources n q) (A ∪ X ∪ F)ᶜ h ∪ Y))
    (hmark : ∀ b ∈ PC, ((resources n q b) ∩ X).Nonempty)
    (habs : packs PA (A ∪ (X \ Y)))
    (G U z E₁ E₂ : ℝ)
    (hdegA : ∀ v : Fin n, ∑ e : A, CliqueGram.incidence 2 e v ≤ G * (n : ℝ) ^ (1 - z))
    (hdegX : ∀ v : Fin n, ∑ e : X, CliqueGram.incidence 2 e v ≤ U * (n : ℝ) ^ (1 - z))
    (repaired : TypeProfile C q → ℝ)
    (hrepair : ∀ t, |(m t : ℝ) - (integerHistogram colour (PB ∪ P₀) t : ℝ) - repaired t| ≤
      E₁ * (n : ℝ) ^ (2 - z))
    (hprefix : ∀ t, |repaired t - (integerHistogram colour (picked h) t : ℝ)| ≤
      E₂ * (n : ℝ) ^ (2 - z)) :
    ∀ t, |(m t : ℝ) - (integerHistogram colour (PB ∪ (picked h ∪ PC ∪ PA)) t : ℝ)| ≤
      (E₁ + E₂ + G + U) * (n : ℝ) ^ (2 - z) := by
  let J := (A ∪ X ∪ F)ᶜ
  let L := remaining (resources n q) J h
  have hJ : Disjoint J (A ∪ X ∪ F) := disjoint_compl_left
  have hJF : Disjoint J F := hJ.mono_right subset_union_right
  have hJX : Disjoint J X := hJ.mono_right
    ((subset_union_right : X ⊆ A ∪ X).trans subset_union_left)
  have hJA : Disjoint J A := hJ.mono_right
    ((subset_union_left : A ⊆ A ∪ X).trans subset_union_left)
  have hp := prefix_packs hq J h hv
  have hpc := prefix_cover_packs hq J Y h PC hv hcover (hJX.mono_right hY)
  have hpL : Disjoint (J \ L) L := sdiff_disjoint
  have hpc' : Disjoint (J \ L) (L ∪ Y) := disjoint_union_right.mpr
    ⟨hpL, (hJX.mono_right hY).mono_left sdiff_subset⟩
  have hprefixCover := packs_disjoint hq hp hcover hpc'
  have hpcA : Disjoint (J ∪ Y) (A ∪ (X \ Y)) := by
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨hJA, hJX.mono_right sdiff_subset⟩,
      ⟨hAX.symm.mono_left hY, sdiff_disjoint.symm⟩⟩
  have hcoverAbs := packs_disjoint hq hpc habs hpcA
  have hfull := packs_outside_bank hq A X F Y hAX hAF hXF hY h PC PA hv hcover habs
  have hbfull := packs_disjoint hq hbank hfull disjoint_compl_right
  have hb₀ := packs_disjoint hq hbank hbasal hAF.symm
  have h₁ : Disjoint PB (picked h) := hbfull.mono_right (subset_union_left.trans subset_union_left)
  have h₂ : Disjoint (PB ∪ picked h) PC := disjoint_union_left.mpr
    ⟨hbfull.mono_right (subset_union_right.trans subset_union_left), hprefixCover⟩
  have h₃ : Disjoint (PB ∪ picked h ∪ PC) PA := by
    rw [union_assoc, disjoint_union_left]
    exact ⟨hbfull.mono_right subset_union_right, hcoverAbs⟩
  have hbgt := completion_block_budget hq hn hbasal hcover habs hmark G U z hdegA hdegX
  intro t
  have hbt : (integerHistogram colour (PB ∪ P₀) t : ℝ) =
      (integerHistogram colour PB t : ℝ) + (integerHistogram colour P₀ t : ℝ) := by
    simp only [integerHistogram, Int.cast_natCast, filter_union]
    rw [card_union_of_disjoint (hb₀.mono (filter_subset _ _) (filter_subset _ _)), Nat.cast_add]
  have hh₁ := hrepair t
  rw [hbt, ← sub_sub] at hh₁
  have ht := completion_type_budget colour PB P₀ (picked h) PC PA t hh₁ (hprefix t)
    hbgt h₁ h₂ h₃
  rw [← union_assoc, ← union_assoc]
  exact ht.trans_eq (by ring)

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.defect_of_assembled_history
