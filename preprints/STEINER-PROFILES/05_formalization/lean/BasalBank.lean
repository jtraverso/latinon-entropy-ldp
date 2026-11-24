module
public import PhysicalBank
public import ResidualSeed

@[expose] public section
noncomputable section
namespace KqR75.BasalBank

open Finset ColouredCliques CompleteJohnson CliqueGram SparseGram

variable {K : Type*} [Field K] [Fintype K]

/-- The union of the chosen cell decompositions is an edge-disjoint
packing. Its deleted degree is bounded by the number of vertices in
cells meeting the given vertex. These are the two inputs used by
the residual seed correction. -/
theorem packing_and_degree {I : Type*} (cells : Finset I) {n q : ℕ} (hq : 2 ≤ q)
    (f : I → (Fin q × K) ↪ Fin n) (s : Fin q → K) (hs : Function.Injective s)
    (σ : I → Fin q → Equiv.Perm K)
    (hsep : ∀ i ∈ cells, ∀ j ∈ cells, i ≠ j →
      ((univ.map (f i)) ∩ (univ.map (f j))).card ≤ 1) :
    let P := cells.biUnion fun j => PhysicalAffineCell.blocks hq (f j) s hs (σ j)
    let F := (univ : Finset (Edge n)).filter fun e => ∃ b ∈ P, e ∈ resources n q b
    let J := Fᶜ
    (∀ e : Edge n, ((P.filter fun b => e ∈ resources n q b).card : ℝ) =
      if e ∈ J then 0 else 1) ∧
    ∀ v : Fin n, ∑ e : (Jᶜ : Finset (Edge n)), incidence 2 e v ≤
      (↑((cells.biUnion fun j => if v ∈ univ.map (f j) then univ.map (f j) else ∅).card) : ℝ) := by
  classical
  let P := cells.biUnion fun j => PhysicalAffineCell.blocks hq (f j) s hs (σ j)
  let F := (univ : Finset (Edge n)).filter fun e => ∃ b ∈ P, e ∈ resources n q b
  let J := Fᶜ
  have hcontained {i : I} {b : Clique n q} (hb : b ∈ PhysicalAffineCell.blocks hq (f i) s hs (σ i)) :
      (b : Finset (Fin n)) ⊆ univ.map (f i) := by
    obtain ⟨p, _, rfl⟩ := mem_map.mp hb
    exact PhysicalAffineCell.block_subset_cell (f i) s (σ i) p
  have hF (e : Edge n) : e ∈ F ↔ ∃ b ∈ P, e ∈ resources n q b := by simp [F]
  have hcard (e : Edge n) : (P.filter fun b => e ∈ resources n q b).card ≤ 1 := by
    apply card_le_one.mpr
    intro b hb c hc
    obtain ⟨hbP, hbe⟩ := mem_filter.mp hb
    obtain ⟨hcP, hce⟩ := mem_filter.mp hc
    obtain ⟨i, hi, hbi⟩ := mem_biUnion.mp hbP
    obtain ⟨j, hj, hcj⟩ := mem_biUnion.mp hcP
    by_cases hij : i = j
    · subst j
      have h := PhysicalAffineCell.blocks_cover_count hq (f i) s hs (σ i) e
      have hle : ((PhysicalAffineCell.blocks hq (f i) s hs (σ i)).filter
          (fun b => e ∈ resources n q b)).card ≤ 1 := by rw [h]; split_ifs <;> omega
      exact card_le_one_iff.mp hle (mem_filter.mpr ⟨hbi, hbe⟩) (mem_filter.mpr ⟨hcj, hce⟩)
    · have he : (e : Finset (Fin n)) ⊆ univ.map (f i) ∩ univ.map (f j) :=
        subset_inter ((mem_filter.mp hbe).2.trans (hcontained hbi))
          ((mem_filter.mp hce).2.trans (hcontained hcj))
      have h := (card_le_card he).trans (hsep i hi j hj hij)
      rw [(mem_powersetCard.mp e.property).2] at h
      omega
  constructor
  · intro e
    change (↑((P.filter fun b => e ∈ resources n q b).card) : ℝ) = if e ∈ J then 0 else 1
    by_cases he : e ∈ F
    · have hne : (P.filter fun b => e ∈ resources n q b).Nonempty := by
        obtain ⟨b, hb, he'⟩ := (hF e).mp he
        exact ⟨b, mem_filter.mpr ⟨hb, he'⟩⟩
      have h1 : (P.filter fun b => e ∈ resources n q b).card = 1 :=
        le_antisymm (hcard e) (card_pos.mpr hne)
      simp [J, he, h1]
    · have hz : (P.filter fun b => e ∈ resources n q b) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro b hb
        exact he ((hF e).mpr ⟨b, (mem_filter.mp hb).1, (mem_filter.mp hb).2⟩)
      simp [J, he, hz]
  · intro v
    let N := cells.biUnion fun j => if v ∈ univ.map (f j) then univ.map (f j) else ∅
    let E := F.filter fun e : Edge n => v ∈ (e : Finset (Fin n))
    have hE : E.card ≤ N.card := by
      have hb : E.card ≤ (N.powersetCard 1).card := by
        apply card_le_card_of_injOn (fun e : Edge n => (e : Finset (Fin n)).erase v)
        · intro e he
          obtain ⟨heF, hv⟩ := mem_filter.mp he
          obtain ⟨b, hb, hbe⟩ := (hF e).mp heF
          obtain ⟨j, hj, hbj⟩ := mem_biUnion.mp hb
          have hsub : (e : Finset (Fin n)) ⊆ univ.map (f j) :=
            (mem_filter.mp hbe).2.trans (hcontained hbj)
          refine mem_powersetCard.mpr ⟨?_, ?_⟩
          · intro x hx
            exact mem_biUnion.mpr ⟨j, hj, by
              simpa only [ite_eq_left (hsub hv)] using hsub (mem_of_mem_erase hx)⟩
          · rw [card_erase_of_mem hv, (mem_powersetCard.mp e.property).2]
        · intro e he e' he' h
          apply Subtype.ext
          have hv := (mem_filter.mp he).2
          have hv' := (mem_filter.mp he').2
          calc
            _ = insert v ((e : Finset (Fin n)).erase v) := (insert_erase hv).symm
            _ = insert v ((e' : Finset (Fin n)).erase v) := congrArg (insert v) h
            _ = _ := insert_erase hv'
      simpa only [card_powersetCard, Nat.choose_one_right] using hb
    change (∑ e : (Jᶜ : Finset (Edge n)), incidence 2 e v) ≤ (N.card : ℝ)
    have hJF : (Jᶜ : Finset (Edge n)) = F := compl_compl F
    rw [hJF]
    change (∑ e : F, if v ∈ ((e : Edge n) : Finset (Fin n)) then (1 : ℝ) else 0) ≤ (N.card : ℝ)
    rw [sum_coe_sort F (fun e : Edge n => if v ∈ (e : Finset (Fin n)) then (1 : ℝ) else 0), sum_boole]
    exact_mod_cast hE

end KqR75.BasalBank

#print axioms KqR75.BasalBank.packing_and_degree
