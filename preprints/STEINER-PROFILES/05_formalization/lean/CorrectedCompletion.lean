module
public import PackingJoin

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Finset ColouredCliques SlotProfiles CompleteJohnson SparseGram WeightedGreedy
open PhysicalBank (Copy basalBlocks edgeMultiplicity)
open BankCapacity (integerHistogram)

variable {C K : Type*} [Fintype C] [DecidableEq C] [Field K] [Fintype K] [DecidableEq K]

/-- With the physical cover and absorber completions supplied, the bank
can correct all type counts at once. The resulting design still
recovers its greedy prefix by restriction to the original host. -/
theorem corrected_completion {q : ℕ} (hq : 2 ≤ q)
    (s : Fin q → K) (hs : Function.Injective s) (ref : C) :
    ∃ (tag : High C q ref → Fin q → C) (r : High C q ref → Fin q) (B : ℤ),
      (∀ j, slotType (tag j) = j.val) ∧ 0 ≤ B ∧
      ∀ {n M : ℕ} (colour : Fin n → C) (f : Copy q ref M → (Fin q × K) ↪ Fin n)
        (hcolour : ∀ j i x, colour (f j (i, x)) = if x = 0 then tag j.1 i else ref)
        (hsep : ∀ i j, i ≠ j → ((univ.map (f i)) ∩ (univ.map (f j))).card ≤ 1)
        (hclasses : ∀ i, 2 ≤ profile colour univ i)
        (A X F Y : Finset (Edge n))
        (hAX : Disjoint A X) (hAF : Disjoint A F) (hXF : Disjoint X F) (hY : Y ⊆ X)
        (h : List (Option (Clique n q))) (PC PA : Finset (Clique n q))
        (hv : valid (resources n q) (A ∪ X ∪ F)ᶜ h)
        (hcover : packs PC (remaining (resources n q) (A ∪ X ∪ F)ᶜ h ∪ Y))
        (hmark : ∀ b ∈ PC, ((resources n q b) ∩ X).Nonempty)
        (habs : packs PA (A ∪ (X \ Y)))
        (hbank : packs (basalBlocks hq r s hs f) F)
        (m : TypeProfile C q → ℤ) (ε : ℤ),
        B * ε ≤ M →
        (∀ e : Edge n, pairMargin colour (fun t => (m t : ℝ)) e =
          ∑ g : Edge n,
            if profile colour (g : Finset (Fin n)) = profile colour (e : Finset (Fin n)) then 1 else 0) →
        (∀ t, |m t - integerHistogram colour (basalBlocks hq r s hs f ∪ (picked h ∪ PC ∪ PA)) t|
          ≤ ε) →
        ∃ P : Finset (Clique n q), packs P univ ∧
          (∀ t, integerHistogram colour P t = m t) ∧
          P.filter (fun b => resources n q b ⊆ (A ∪ X ∪ F)ᶜ) = picked h := by
  obtain ⟨tag, r, B, htag, hB, hcorr⟩ := PhysicalBank.correct_design_with_bank hq s hs ref
  refine ⟨tag, r, B, htag, hB, ?_⟩
  intro n M colour f hcolour hsep hclasses A X F Y hAX hAF hXF hY h PC PA hv hcover hmark habs
    hbank m ε hcapacity hmargin hdef
  let Q := picked h ∪ PC ∪ PA
  let bank := basalBlocks hq r s hs f
  have hQ : packs Q Fᶜ := packs_outside_bank hq A X F Y hAX hAF hXF hY h PC PA hv hcover habs
  have hd : Disjoint bank Q := packs_disjoint hq hbank hQ disjoint_compl_right
  have hbase := (assemble hq A X F Y hAX hAF hXF hY h PC PA bank hv hcover hmark habs hbank).1
  have hmult (e : Edge n) : edgeMultiplicity (bank ∪ Q) e = 1 := by
    rw [union_comm bank Q]
    simpa only [mem_univ, ite_true] using hbase e
  obtain ⟨PB, _, hPB, _, hhist⟩ :=
    hcorr colour f hcolour hsep hclasses Q m ε hcapacity hd hmult hmargin hdef
  have hPB' : packs PB F := fun e => (hPB e).trans (hbank e)
  have hres := assemble hq A X F Y hAX hAF hXF hY h PC PA PB hv hcover hmark habs hPB'
  refine ⟨Q ∪ PB, hres.1, ?_, hres.2⟩
  intro t
  simpa only [union_comm Q PB] using hhist t

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.corrected_completion
