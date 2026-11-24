module
public import CoverAssembly
public import PhysicalReserve
public import ColouredCliques

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Finset CompleteJohnson ColouredCliques

/-- View typed k-sets as vertex sets. -/
def vertexSets {n k : ℕ} (P : Finset ↥((univ : Finset (Fin n)).powersetCard k)) :
    Finset (Finset (Fin n)) := P.map ⟨Subtype.val, Subtype.val_injective⟩

theorem vertexSets_mem {n k : ℕ} (P : Finset ↥((univ : Finset (Fin n)).powersetCard k))
    (e : ↥((univ : Finset (Fin n)).powersetCard k)) :
    e.val ∈ vertexSets P ↔ e ∈ P := by
  exact mem_map' ⟨Subtype.val, Subtype.val_injective⟩ (a := e) (s := P)

theorem vertexSets_card {n k : ℕ} {P : Finset ↥((univ : Finset (Fin n)).powersetCard k)}
    {e : Finset (Fin n)} (he : e ∈ vertexSets P) : e.card = k := by
  obtain ⟨f, _, rfl⟩ := mem_map.mp he
  exact (mem_powersetCard.mp f.property).2

theorem vertexSets_size {n k : ℕ} (P : Finset ↥((univ : Finset (Fin n)).powersetCard k)) :
    (vertexSets P).card = P.card := card_map _

/-- Take the k-element sets of an untyped family in the physical universe. -/
def physicalSets {n : ℕ} (k : ℕ) (E : Finset (Finset (Fin n))) :
    Finset ↥((univ : Finset (Fin n)).powersetCard k) :=
  univ.filter (fun e => e.val ∈ E)

theorem physicalSets_mem {n k : ℕ} (P : Finset (Finset (Fin n)))
    (e : ↥((univ : Finset (Fin n)).powersetCard k)) :
    e ∈ physicalSets k P ↔ e.val ∈ P := by simp [physicalSets]

theorem vertexSets_physicalSets {n k : ℕ} {P : Finset (Finset (Fin n))}
    (hP : ∀ C ∈ P, C.card = k) : vertexSets (physicalSets k P) = P := by
  ext e
  constructor
  · intro he
    obtain ⟨b, hb, rfl⟩ := mem_map.mp he
    exact (physicalSets_mem P b).mp hb
  · intro he
    let b : ↥((univ : Finset (Fin n)).powersetCard k) :=
      ⟨e, mem_powersetCard.mpr ⟨subset_univ _, hP e he⟩⟩
    exact (vertexSets_mem _ b).mpr ((physicalSets_mem _ b).mpr he)

/-- The two forms of the reserve graph coincide. -/
theorem reserve_vertexSets {n : ℕ} (ω : Sym2 (Fin n) → Bool) :
    vertexSets (PhysicalReserve.edges ω) = reserveEdges (ReserveRandom.adj ω) univ := by
  ext e
  constructor
  · intro he
    obtain ⟨b, hb, rfl⟩ := mem_map.mp he
    exact mem_filter.mpr ⟨b.property, (mem_filter.mp hb).2⟩
  · intro he
    obtain ⟨heCard, heR⟩ := mem_filter.mp he
    let b : Edge n := ⟨e, heCard⟩
    exact (vertexSets_mem _ b).mpr (mem_filter.mpr ⟨mem_univ _, heR⟩)

/-- Transfer a completed cover-down back to the physical incidence
family. The reserve witness also certifies that each new block can be
distinguished from the greedy prefix. -/
theorem physical_completion {n q : ℕ} {L X : Finset (Edge n)} {P Y : Finset (Finset (Fin n))}
    (h : Cover q (vertexSets L) (vertexSets X) P ∅ Y) :
    let out := physicalSets q P
    let Y' := physicalSets 2 Y
    Y' ⊆ X ∧ Y'.card = Y.card ∧
      (∀ e : Edge n, (out.filter (fun C => e ∈ SparseGram.resources n q C)).card =
        if e ∈ L ∪ Y' then 1 else 0) ∧
      (∀ C ∈ out, ((SparseGram.resources n q C) ∩ X).Nonempty) := by
  classical
  let out := physicalSets q P
  let Y' := physicalSets 2 Y
  have hY : ∀ e ∈ Y, e.card = 2 := fun _ he => vertexSets_card (h.used_sub he)
  have hY' : vertexSets Y' = Y := vertexSets_physicalSets hY
  have hcov : P.biUnion (fun C => C.powersetCard 2) = vertexSets L ∪ vertexSets Y' := by
    rw [h.covered, sdiff_empty, hY']
  refine ⟨fun e he => (vertexSets_mem X e).mp (h.used_sub ((physicalSets_mem Y e).mp he)),
    (vertexSets_size Y').symm.trans (congrArg Finset.card hY'), ?_, ?_⟩
  · intro e
    let F := out.filter (fun C => e ∈ SparseGram.resources n q C)
    have hf : ∀ C : Clique n q, C ∈ F ↔ C.val ∈ P ∧ e.val ∈ C.val.powersetCard 2 := by
      intro C
      change C ∈ out.filter _ ↔ _
      rw [mem_filter, physicalSets_mem]
      simp only [SparseGram.resources, mem_filter, mem_univ, true_and, mem_powersetCard,
        (mem_powersetCard.mp e.property).2, and_true]
    have hu : F.card ≤ 1 := by
      apply card_le_one.mpr
      intro C hC D hD
      by_contra hne
      have hne' : C.val ≠ D.val := fun he => hne (Subtype.ext he)
      obtain ⟨hc, heC⟩ := (hf C).mp hC
      obtain ⟨hd, heD⟩ := (hf D).mp hD
      exact disjoint_left.mp (h.edge_disjoint hc hd hne') heC heD
    have hex : F.Nonempty ↔ e ∈ L ∪ Y' := by
      constructor
      · rintro ⟨C, hC⟩
        obtain ⟨hc, heC⟩ := (hf C).mp hC
        have hmem : e.val ∈ P.biUnion (fun C => C.powersetCard 2) := mem_biUnion.mpr ⟨C.val, hc, heC⟩
        rw [hcov, mem_union, vertexSets_mem, vertexSets_mem] at hmem
        exact mem_union.mpr hmem
      · intro he
        have hmem : e.val ∈ P.biUnion (fun C => C.powersetCard 2) := by
          rw [hcov, mem_union, vertexSets_mem, vertexSets_mem]
          exact mem_union.mp he
        obtain ⟨A, hA, heA⟩ := mem_biUnion.mp hmem
        let C : Clique n q := ⟨A, mem_powersetCard.mpr ⟨subset_univ _, h.block_size A hA⟩⟩
        exact ⟨C, (hf C).mpr ⟨hA, heA⟩⟩
    change F.card = _
    by_cases he : e ∈ L ∪ Y'
    · rw [ite_eq_left he]
      exact le_antisymm hu (Nat.succ_le_of_lt (card_pos.mpr (hex.mpr he)))
    · rw [ite_eq_right he, not_nonempty_iff_eq_empty.mp (fun hf' => he (hex.mp hf')) , card_empty]
  · intro C hC
    obtain ⟨f, hf⟩ := h.block_uses_reserve C.val ((physicalSets_mem P C).mp hC)
    obtain ⟨hfC, hfX⟩ := mem_inter.mp hf
    let e : Edge n := ⟨f, mem_powersetCard.mpr ⟨subset_univ _, (mem_powersetCard.mp hfC).2⟩⟩
    refine ⟨e, mem_inter.mpr ⟨?_, (vertexSets_mem X e).mp hfX⟩⟩
    exact mem_filter.mpr ⟨mem_univ _, (mem_powersetCard.mp hfC).1⟩

end KqR75.CoverDown

#print axioms KqR75.CoverDown.reserve_vertexSets
#print axioms KqR75.CoverDown.physical_completion
