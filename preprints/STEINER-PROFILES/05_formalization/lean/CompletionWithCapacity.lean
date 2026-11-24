module
public import HostCompletionDefect
public import PhysicalDivisibility
public import CorrectedCompletion

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Finset ColouredCliques SlotProfiles CompleteJohnson SparseGram WeightedGreedy
open PhysicalBank (Copy basalBlocks)
open BankCapacity (integerHistogram)

variable {C K : Type*} [Fintype C] [DecidableEq C] [Field K] [Fintype K] [DecidableEq K]

/-- One number of cell copies suffices for all admissible prefixes.
The coefficient uses the reserve, the absorber and the process
errors, independent of the degree of the placed bank. -/
theorem complete_with_capacity {q : ℕ} (hq : 3 ≤ q)
    (s : Fin q → K) (hs : Function.Injective s) (ref : C) :
    ∃ (tag : High C q ref → Fin q → C) (r : High C q ref → Fin q) (B : ℤ),
      (∀ j, slotType (tag j) = j.val) ∧ 0 ≤ B ∧
      ∀ {n M : ℕ} (hn : 1 ≤ n) (colour : Fin n → C) (f : Copy q ref M → (Fin q × K) ↪ Fin n),
        (∀ j i x, colour (f j (i, x)) = if x = 0 then tag j.1 i else ref) →
        (∀ i j, i ≠ j → ((univ.map (f i)) ∩ (univ.map (f j))).card ≤ 1) →
        (∀ i, 2 ≤ profile colour univ i) →
      ∀ (A X F : Finset (Edge n)),
        Disjoint A X → Disjoint A F → Disjoint X F →
        packs (basalBlocks (by omega : 2 ≤ q) r s hs f) F →
        (∀ S ⊆ X, Divisible q S → ∃ P : Finset (Clique n q), packs P (A ∪ S)) →
        Divisible q (univ : Finset (Edge n)) →
      ∀ (G U z E₁ E₂ : ℝ), z ≤ 2 → 0 ≤ E₁ + E₂ + G + U →
        B.toNat * ⌈(E₁ + E₂ + G + U) * (n : ℝ) ^ (2 - z)⌉₊ ≤ M →
        (∀ v : Fin n, ∑ e : A, CliqueGram.incidence 2 e v ≤ G * (n : ℝ) ^ (1 - z)) →
        (∀ v : Fin n, ∑ e : X, CliqueGram.incidence 2 e v ≤ U * (n : ℝ) ^ (1 - z)) →
      ∀ (m : TypeProfile C q → ℤ),
        (∀ e : Edge n, pairMargin colour (fun t => (m t : ℝ)) e =
          ∑ g : Edge n, if profile colour (g : Finset (Fin n)) =
            profile colour (e : Finset (Fin n)) then 1 else 0) →
      ∀ (P₀ : Finset (Clique n q)), packs P₀ A →
      ∀ (h : List (Option (Clique n q))) (repaired : TypeProfile C q → ℝ),
        valid (resources n q) (A ∪ X ∪ F)ᶜ h →
        (∀ t, |repaired t - (integerHistogram colour (picked h) t : ℝ)| ≤
          E₂ * (n : ℝ) ^ (2 - z)) →
        (∀ t, |(m t : ℝ) -
            (integerHistogram colour (basalBlocks (by omega : 2 ≤ q) r s hs f ∪ P₀) t : ℝ) -
            repaired t| ≤ E₁ * (n : ℝ) ^ (2 - z)) →
        (∃ (PC : Finset (Clique n q)) (Y : Finset (Edge n)), Y ⊆ X ∧
          packs PC (remaining (resources n q) (A ∪ X ∪ F)ᶜ h ∪ Y) ∧
          ∀ b ∈ PC, ((resources n q b) ∩ X).Nonempty) →
        ∃ P : Finset (Clique n q), packs P univ ∧
          (∀ t, integerHistogram colour P t = m t) ∧
          P.filter (fun b => resources n q b ⊆ (A ∪ X ∪ F)ᶜ) = picked h := by
  have hq' : 2 ≤ q := by omega
  obtain ⟨tag, r, B, htag, hB, hcorr⟩ := corrected_completion hq' s hs ref
  refine ⟨tag, r, B, htag, hB, ?_⟩
  intro n M hn colour f hcolour hsep hclasses A X F hAX hAF hXF hbank habs hK
    G U z E₁ E₂ hz hD hcap hdegA hdegX m hmargin P₀ hP₀ h repaired hv hprefix hrepair hcover
  obtain ⟨PC, Y, hY, hPC, hmark⟩ := hcover
  have hdiv := divisible_after_cover hq' A X F Y hAX hAF hXF hY h P₀
    (basalBlocks hq' r s hs f) PC hv hP₀ hbank hPC hK
  obtain ⟨PA, hPA⟩ := habs (X \ Y) sdiff_subset hdiv
  have hdef := defect_of_assembled_history hq' hn colour m A X F Y hAX hAF hXF hY h
    (basalBlocks hq' r s hs f) P₀ PC PA hv hbank hP₀ hPC hmark hPA
    G U z E₁ E₂ hdegA hdegX repaired hrepair hprefix
  let ε := ⌈(E₁ + E₂ + G + U) * (n : ℝ) ^ (2 - z)⌉₊
  obtain ⟨hε, _, hround⟩ := BankCapacity.capacity_rounding (B := B) hn hB hD hz
  have hcapacity : B * (ε : ℤ) ≤ M := hε.trans (by exact_mod_cast hcap)
  refine hcorr colour f hcolour hsep hclasses A X F Y hAX hAF hXF hY h PC PA hv
    hPC hmark hPA hbank m ε hcapacity hmargin ?_
  intro t
  apply hround
  push_cast
  exact hdef t

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.complete_with_capacity
