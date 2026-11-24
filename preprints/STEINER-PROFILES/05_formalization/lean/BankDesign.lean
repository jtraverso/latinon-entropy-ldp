module
public import BankSwitch
public import BankDefect

@[expose] public section
noncomputable section
namespace KqR75.PhysicalBank

open Finset ColouredCliques SlotProfiles CompleteJohnson SparseGram

variable {C K : Type*} [Fintype C] [DecidableEq C]
  [Field K] [Fintype K] [DecidableEq K]

/-- Edge multiplicity in a family of physical cliques. -/
def edgeMultiplicity {n q : ℕ} (P : Finset (Clique n q)) (e : Edge n) : ℕ :=
  (P.filter (fun b => e ∈ resources n q b)).card

private theorem multiplicity_union {n q : ℕ} {P Q : Finset (Clique n q)}
    (hd : Disjoint P Q) (e : Edge n) :
    edgeMultiplicity (P ∪ Q) e = edgeMultiplicity P e + edgeMultiplicity Q e := by
  rw [edgeMultiplicity, filter_union,
    card_union_of_disjoint (hd.mono (filter_subset _ _) (filter_subset _ _))]
  rfl

private theorem histogram_union {n q : ℕ} (colour : Fin n → C)
    {P Q : Finset (Clique n q)} (hd : Disjoint P Q) (t : TypeProfile C q) :
    BankCapacity.integerHistogram colour (P ∪ Q) t =
      BankCapacity.integerHistogram colour P t + BankCapacity.integerHistogram colour Q t := by
  rw [BankCapacity.integerHistogram, filter_union,
    card_union_of_disjoint (hd.mono (filter_subset _ _) (filter_subset _ _)), Nat.cast_add]
  rfl

/-- If two families have total edge multiplicity at most one everywhere,
they share no q-block. -/
private theorem disjoint_of_multiplicities {n q : ℕ} (hq : 2 ≤ q)
    {P Q : Finset (Clique n q)} (h : ∀ e, edgeMultiplicity P e + edgeMultiplicity Q e = 1) :
    Disjoint P Q := by
  apply disjoint_left.mpr
  intro b hbP hbQ
  have hpos : 0 < (resources n q b).card := by rw [resources_card]; exact Nat.choose_pos hq
  obtain ⟨e, he⟩ := card_pos.mp hpos
  have hp : 0 < edgeMultiplicity P e := card_pos.mpr ⟨b, mem_filter.mpr ⟨hbP, he⟩⟩
  have hq' : 0 < edgeMultiplicity Q e := card_pos.mpr ⟨b, mem_filter.mpr ⟨hbQ, he⟩⟩
  have he' := h e
  omega

/-- A fixed family of affine cells corrects every compatible, sufficiently
small integer defect. All the cliques outside the bank are retained. -/
theorem correct_design_with_bank {q : ℕ} (hq : 2 ≤ q)
    (s : Fin q → K) (hs : Function.Injective s) (ref : C) :
    ∃ (tag : High C q ref → Fin q → C) (r : High C q ref → Fin q) (B : ℤ),
      (∀ j, slotType (tag j) = j.val) ∧ 0 ≤ B ∧
      ∀ {n M : ℕ} (colour : Fin n → C)
        (f : Copy q ref M → (Fin q × K) ↪ Fin n)
        (hcolour : ∀ j i x, colour (f j (i, x)) = if x = 0 then tag j.1 i else ref)
        (hsep : ∀ i j, i ≠ j → ((univ.map (f i)) ∩ (univ.map (f j))).card ≤ 1)
        (hclasses : ∀ i, 2 ≤ profile colour univ i)
        (Q : Finset (Clique n q)) (m : TypeProfile C q → ℤ) (ε : ℤ),
        B * ε ≤ M → Disjoint (basalBlocks hq r s hs f) Q →
        (∀ e : Edge n, edgeMultiplicity (basalBlocks hq r s hs f ∪ Q) e = 1) →
        (∀ e : Edge n, pairMargin colour (fun t => (m t : ℝ)) e =
          ∑ g : Edge n,
            if profile colour (g : Finset (Fin n)) = profile colour (e : Finset (Fin n)) then 1 else 0) →
        (∀ t, |m t - BankCapacity.integerHistogram colour (basalBlocks hq r s hs f ∪ Q) t| ≤ ε) →
        ∃ P : Finset (Clique n q), Disjoint P Q ∧
          (∀ e : Edge n, edgeMultiplicity P e = edgeMultiplicity (basalBlocks hq r s hs f) e) ∧
          (∀ e : Edge n, edgeMultiplicity (P ∪ Q) e = 1) ∧
          ∀ t, BankCapacity.integerHistogram colour (P ∪ Q) t = m t := by
  classical
  obtain ⟨tag, r, B, htag, hB, hsolve⟩ := BankCapacity.bounded_integer_correction hq s hs ref
  refine ⟨tag, r, B, htag, hB, ?_⟩
  intro n M colour f hcolour hsep hclasses Q m ε hcap hd hdecomp hm hdef
  let base := basalBlocks hq r s hs f
  let w := fun t => m t - BankCapacity.integerHistogram colour (base ∪ Q) t
  have hker := BankCapacity.defect_in_kernel colour hclasses (base ∪ Q) m hdecomp hm
  obtain ⟨a, ha, hw⟩ := hsolve w ε (fun j => hdef j.val) hker
  obtain ⟨P, hload, hhist⟩ := switch_whole_bank hq ref tag r s hs colour f hcolour hsep w a
    (fun j => (ha j).trans hcap) hw
  have htotal (e : Edge n) : edgeMultiplicity P e + edgeMultiplicity Q e = 1 := by
    have hh := hload e
    change edgeMultiplicity P e = edgeMultiplicity base e at hh
    rw [hh, ← multiplicity_union hd]
    exact hdecomp e
  have hPQ := disjoint_of_multiplicities hq htotal
  refine ⟨P, hPQ, hload, fun e => (multiplicity_union hPQ e).trans (htotal e), ?_⟩
  intro t
  have h := hhist t
  change BankCapacity.integerHistogram colour P t - BankCapacity.integerHistogram colour base t = w t at h
  change BankCapacity.integerHistogram colour P t - BankCapacity.integerHistogram colour base t =
    m t - BankCapacity.integerHistogram colour (base ∪ Q) t at h
  have hd' : Disjoint base Q := hd
  rw [histogram_union colour hd'] at h
  rw [histogram_union colour hPQ]
  omega

end KqR75.PhysicalBank

#print axioms KqR75.PhysicalBank.correct_design_with_bank
