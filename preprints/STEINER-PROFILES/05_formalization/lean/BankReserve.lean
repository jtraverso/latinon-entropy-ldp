module
public import CompletionBudget

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Finset CliqueGram ColouredCliques CompleteJohnson SparseGram SlotProfiles
open PhysicalBank (Copy basalBlocks edgeMultiplicity)
open ReserveCuts ReserveRandom
open Filter

variable {C K : Type*} [Fintype C] [DecidableEq C]
  [Field K] [Fintype K] [DecidableEq K]

/-- Place all basal cells outside a given reserve, carrying forward the
packing and degree certificates in the physical edge type. -/
theorem eventually_basal_outside_reserve (q : ℕ) (hq : 2 ≤ q) (ref : C)
    (s : Fin q → K) (hs : Function.Injective s)
    {ρ z B D : ℝ} (hρ : 0 < ρ) (hz : 0 < z) (hz₁ : z ≤ 1) (hB : 0 ≤ B) :
    ∃ G : ℝ, 0 < G ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (M degree : ℕ), (M : ℝ) ≤ B * (n : ℝ) ^ (2 - z) →
        (degree : ℝ) ≤ D * (n : ℝ) ^ (1 - z) →
        ∀ (tag : High C q ref → Fin q → C) (r : High C q ref → Fin q)
          (colour : Fin n → C) (ω : Sym2 (Fin n) → Bool),
          (∀ c, ρ * (n : ℝ) ≤ (profile colour univ c : ℝ)) →
          (∀ v, (common (adj ω) univ {v}).card ≤ degree) →
          ∃ (f : Copy q ref M → (Fin q × K) ↪ Fin n) (F : Finset (Edge n)),
            (∀ j i x, colour (f j (i, x)) = if x = 0 then tag j.1 i else ref) ∧
            (∀ i j, i ≠ j → ((univ.map (f i)) ∩ (univ.map (f j))).card ≤ 1) ∧
            packs (basalBlocks hq r s hs f) F ∧ Disjoint (PhysicalReserve.edges ω) F ∧
            ∀ v : Fin n, ∑ e : F, incidence 2 e v ≤ G * (n : ℝ) ^ (1 - z) := by
  classical
  obtain ⟨G, hG, hev⟩ := BankScales.eventually_place_copies (K := K) q ref
    (D := D) hρ hz hz₁ hB
  refine ⟨G, hG, ?_⟩
  filter_upwards [hev] with n he
  intro M degree hM hdegree tag r colour ω hclasses hreserve
  let forbidden (v : Fin n) := common (adj ω) univ {v}
  have hfmem (a b : Fin n) : a ∈ forbidden b ↔ adj ω b a := by simp [forbidden, common]
  have hsym (a b : Fin n) : a ∈ forbidden b ↔ b ∈ forbidden a := by
    rw [hfmem, hfmem]
    exact ⟨Std.Symm.symm _ _, Std.Symm.symm _ _⟩
  obtain ⟨f, hcolour, havoid, hsep, hdegreeF⟩ :=
    he M degree hM hdegree tag colour forbidden hclasses hreserve hsym
  let P := basalBlocks hq r s hs f
  let F := (univ : Finset (Edge n)).filter fun e => ∃ b ∈ P, e ∈ resources n q b
  let σ (j : Copy q ref M) (i : Fin q) :=
    if ¬j.2.1 ∧ i = r j.1 then Equiv.swap (0 : K) 1 else Equiv.refl K
  have hb := BasalBank.packing_and_degree univ hq f s hs σ
    (fun i _ j _ hij => hsep i j hij)
  change (∀ e : Edge n, (edgeMultiplicity P e : ℝ) = if e ∈ Fᶜ then 0 else 1) ∧
    (∀ v : Fin n, ∑ e : ((Fᶜ)ᶜ : Finset (Edge n)), incidence 2 e v ≤ _) at hb
  refine ⟨f, F, hcolour, hsep, ?_, ?_, ?_⟩
  · intro e
    have he := hb.1 e
    by_cases hF : e ∈ F
    · simp [mem_compl, hF] at he ⊢
      exact_mod_cast he
    · simp [mem_compl, hF] at he ⊢
      exact_mod_cast he
  · apply disjoint_left.mpr
    intro e heX heF
    obtain ⟨b, hbP, hbe⟩ := (mem_filter.mp heF).2
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp hbP
    obtain ⟨t, _, rfl⟩ := mem_map.mp hj
    obtain ⟨a, b, hab, habE⟩ := card_eq_two.mp (mem_powersetCard.mp e.property).2
    have hsub : (e.val : Finset (Fin n)) ⊆ univ.map (f j) :=
      (mem_filter.mp hbe).2.trans (PhysicalAffineCell.block_subset_cell (f j) s (σ j) t)
    have ha : a ∈ univ.map (f j) := hsub (by simp [habE])
    have hb : b ∈ univ.map (f j) := hsub (by simp [habE])
    obtain ⟨u, _, rfl⟩ := mem_map.mp ha
    obtain ⟨v, _, rfl⟩ := mem_map.mp hb
    have huv : u ≠ v := fun he => hab (congrArg (f j) he)
    have hpair : e = PhysicalReserve.pairEdge _ _ hab := Subtype.ext habE
    have hadj := (PhysicalReserve.pairEdge_mem ω hab).mp (hpair ▸ heX)
    exact havoid j v u huv.symm ((hfmem _ _).mpr hadj)
  · intro v
    have hd := hb.2 v
    rw [compl_compl] at hd
    exact hd.trans (hdegreeF v)

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.eventually_basal_outside_reserve
