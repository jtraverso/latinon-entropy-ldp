module
public import CoverDown

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Finset
variable {V : Type*} [DecidableEq V]

/-- The edge accounting for a partial cover-down, including the
condition needed to recover the original greedy prefix. -/
structure Cover (q : ℕ) (L X P L' Y : Finset (Finset V)) : Prop where
  leave_sub : L' ⊆ L
  used_sub : Y ⊆ X
  edge_disjoint : (P : Set (Finset V)).PairwiseDisjoint (fun C => C.powersetCard 2)
  covered : P.biUnion (fun C => C.powersetCard 2) = (L \ L') ∪ Y
  block_size : ∀ C ∈ P, C.card = q
  block_uses_reserve : ∀ C ∈ P, ((C.powersetCard 2) ∩ X).Nonempty

theorem cover_empty (q : ℕ) (L X : Finset (Finset V)) : Cover q L X ∅ L ∅ where
  leave_sub := Subset.rfl
  used_sub := empty_subset _
  edge_disjoint := by simp
  covered := by simp
  block_size := by simp
  block_uses_reserve := by simp

/-- Adding a fresh clique preserves the edge partition and the reserve
certificate for every block. -/
theorem cover_insert {q : ℕ} {L X P L' Y : Finset (Finset V)}
    (h : Cover q L X P L' Y) (hd : Disjoint L X) (C : Finset V)
    (hC : C.card = q) (hnew : C.powersetCard 2 ⊆ L' ∪ (X \ Y))
    (hX : (C.powersetCard 2 ∩ X).Nonempty) :
    let out := take L' Y (C.powersetCard 2)
    Cover q L X (insert C P) out.1 out.2 := by
  let B := C.powersetCard 2
  let E := P.biUnion (fun D => D.powersetCard 2)
  have hBL (e : Finset V) (he : e ∈ B) :
      e ∉ L' → e ∈ X \ Y := fun hn => (mem_union.mp (hnew he)).resolve_left hn
  have hfresh : Disjoint B E := by
    apply disjoint_left.mpr
    intro e he hE
    change e ∈ P.biUnion (fun D => D.powersetCard 2) at hE
    rw [h.covered] at hE
    rcases mem_union.mp (hnew he) with hL | hX'
    · rcases mem_union.mp hE with hl | hy
      · exact (mem_sdiff.mp hl).2 hL
      · exact disjoint_left.mp hd (h.leave_sub hL) (h.used_sub hy)
    · rcases mem_union.mp hE with hl | hy
      · exact disjoint_left.mp hd (mem_sdiff.mp hl).1 (mem_sdiff.mp hX').1
      · exact (mem_sdiff.mp hX').2 hy
  refine ⟨sdiff_subset.trans h.leave_sub, ?_, ?_, ?_, ?_, ?_⟩
  · exact union_subset h.used_sub (fun e he => (mem_sdiff.mp (hBL e (mem_sdiff.mp he).1
      (mem_sdiff.mp he).2)).1)
  · intro U hU W hW hne
    have hdisj {D : Finset V} (hD : D ∈ P) : Disjoint B (D.powersetCard 2) :=
      hfresh.mono_right (fun e he => mem_biUnion.mpr ⟨D, hD, he⟩)
    rcases mem_insert.mp hU with rfl | hUP
    · exact hdisj ((mem_insert.mp hW).resolve_left hne.symm)
    · rcases mem_insert.mp hW with rfl | hWP
      · exact (hdisj hUP).symm
      · exact h.edge_disjoint hUP hWP hne
  · change (insert C P).biUnion (fun D => D.powersetCard 2) =
      (L \ (L' \ B)) ∪ (Y ∪ (B \ L'))
    rw [biUnion_insert, h.covered]
    ext e
    simp only [mem_union, mem_sdiff]
    have hs : e ∈ L' → e ∈ L := fun he => h.leave_sub he
    tauto
  · intro D hD
    rcases mem_insert.mp hD with rfl | hD
    · exact hC
    · exact h.block_size D hD
  · intro D hD
    rcases mem_insert.mp hD with rfl | hD
    · exact hX
    · exact h.block_uses_reserve D hD

end KqR75.CoverDown

#print axioms KqR75.CoverDown.cover_insert
