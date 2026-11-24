module
public import CoverChoices

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Finset ReserveCuts

variable {V : Type*} [DecidableEq V]

/-- The graph selected by a reserve adjacency relation on S. -/
def reserveEdges (R : V → V → Prop) [DecidableRel R] (S : Finset V) :
    Finset (Finset V) :=
  (S.powersetCard 2).filter (fun e => (e : Set V).Pairwise R)

private theorem pair_mem_reserve (R : V → V → Prop) [DecidableRel R] [Std.Symm R]
    (S : Finset V) {u v : V} (hu : u ∈ S) (hv : v ∈ S) (hn : u ≠ v) (hadj : R u v) :
    ({u, v} : Finset V) ∈ reserveEdges R S := by
  apply mem_filter.mpr
  refine ⟨mem_powersetCard.mpr ⟨by simp [insert_subset_iff, hu, hv], card_eq_two.mpr ⟨u, v, hn, rfl⟩⟩,
    ?_⟩
  intro x hx y hy hxy
  have hx' : x = u ∨ x = v := by simpa using hx
  have hy' : y = u ∨ y = v := by simpa using hy
  rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
  · exact (hxy rfl).elim
  · exact hadj
  · exact Std.Symm.symm _ _ hadj
  · exact (hxy rfl).elim

private theorem clique_edges_subset (R : V → V → Prop) [DecidableRel R]
    (S C : Finset V) (hs : C ⊆ S) (hc : (C : Set V).Pairwise R) :
    C.powersetCard 2 ⊆ reserveEdges R S := by
  intro e he
  obtain ⟨hC, hcard⟩ := mem_powersetCard.mp he
  exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hC.trans hs, hcard⟩, hc.mono hC⟩

/-- An auxiliary clique for a high-degree vertex supplies a star step
using its internal pairs from the unused reserve. -/
theorem star_extension (R : V → V → Prop) [DecidableRel R]
    (S C : Finset V) (u : V) (L Y : Finset (Finset V))
    (hS : C ⊆ S) (hClique : (C : Set V).Pairwise R)
    (hu : u ∉ C) (hsize : 2 ≤ C.card)
    (hstar : ∀ w ∈ C, ({u, w} : Finset V) ∈ L)
    (hclean : Disjoint (C.powersetCard 2) Y) :
    let B := (insert u C).powersetCard 2
    B ⊆ L ∪ (reserveEdges R S \ Y) ∧
      (B ∩ reserveEdges R S).Nonempty ∧ (L ∩ B).Nonempty := by
  have haux := clique_edges_subset R S C hS hClique
  have hl : star u C ⊆ L := fun e he => by
    obtain ⟨w, hw, rfl⟩ := mem_image.mp he
    exact hstar w hw
  let B := (insert u C).powersetCard 2
  have hsplit : B = C.powersetCard 2 ∪ star u C := star_clique_split u C hu
  change B ⊆ L ∪ (reserveEdges R S \ Y) ∧ (B ∩ reserveEdges R S).Nonempty ∧ (L ∩ B).Nonempty
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    rw [hsplit] at he
    rcases mem_union.mp he with hC | hL
    · exact mem_union_right _ (mem_sdiff.mpr ⟨haux hC, fun hy => disjoint_left.mp hclean hC hy⟩)
    · exact mem_union_left _ (hl hL)
  · obtain ⟨e, he⟩ := powersetCard_nonempty_of_le hsize
    exact ⟨e, mem_inter.mpr ⟨by rw [hsplit]; exact mem_union_left _ he, haux he⟩⟩
  · obtain ⟨w, hw⟩ := card_pos.mp (by omega : 0 < C.card)
    have hs : ({u, w} : Finset V) ∈ star u C := mem_image.mpr ⟨w, hw, rfl⟩
    exact ⟨{u, w}, mem_inter.mpr ⟨hl hs, by rw [hsplit]; exact mem_union_right _ hs⟩⟩

/-- A rooted auxiliary clique with fresh links to both roots supplies a
pair step while the auxiliary edges come from the unused reserve. -/
theorem pair_extension (R : V → V → Prop) [DecidableRel R] [Std.Symm R]
    (S C : Finset V) (u v : V) (Y : Finset (Finset V))
    (hS : C ⊆ S) (hClique : (C : Set V).Pairwise R)
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v)
    (huC : u ∉ C) (hvC : v ∉ C) (hsize : 0 < C.card)
    (hlinks : ∀ w ∈ C, R u w ∧ R v w)
    (hclean : Disjoint (C.powersetCard 2) Y)
    (hlinksClean : ∀ w ∈ C, ({u, w} : Finset V) ∉ Y ∧ ({v, w} : Finset V) ∉ Y) :
    let B := (insert u (insert v C)).powersetCard 2
    ({u, v} : Finset V) ∈ B ∧
      B.erase {u, v} ⊆ (reserveEdges R S \ Y) ∧
      (B ∩ reserveEdges R S).Nonempty := by
  let B := (insert u (insert v C)).powersetCard 2
  have hstar (a : V) (ha : a ∈ S) (haC : a ∉ C)
      (hl : ∀ w ∈ C, R a w) (hy : ∀ w ∈ C, ({a, w} : Finset V) ∉ Y) :
      star a C ⊆ reserveEdges R S \ Y := by
    intro e he'
    obtain ⟨w, hw, rfl⟩ := mem_image.mp he'
    have hn : a ≠ w := fun hh => haC (hh.symm ▸ hw)
    exact mem_sdiff.mpr ⟨pair_mem_reserve R S ha (hS hw) hn (hl w hw), hy w hw⟩
  have hsU := hstar u hu huC (fun w hw => (hlinks w hw).1) (fun w hw => (hlinksClean w hw).1)
  have hsV := hstar v hv hvC (fun w hw => (hlinks w hw).2) (fun w hw => (hlinksClean w hw).2)
  have hn : u ∉ insert v C := fun h => (mem_insert.mp h).elim huv huC
  have hsplit : B = (C.powersetCard 2 ∪ star v C) ∪ insert {u, v} (star u C) := by
    rw [show B = _ from star_clique_split u (insert v C) hn, star_clique_split v C hvC]
    simp [star]
  change ({u, v} : Finset V) ∈ B ∧ B.erase {u, v} ⊆ reserveEdges R S \ Y ∧
    (B ∩ reserveEdges R S).Nonempty
  refine ⟨by rw [hsplit]; exact mem_union_right _ (mem_insert_self _ _), ?_, ?_⟩
  · intro f hf
    obtain ⟨hne, hB⟩ := mem_erase.mp hf
    rw [hsplit] at hB
    rcases mem_union.mp hB with hL | hR
    · rcases mem_union.mp hL with hC | hV
      · exact mem_sdiff.mpr ⟨clique_edges_subset R S C hS hClique hC,
          fun hy => disjoint_left.mp hclean hC hy⟩
      · exact hsV hV
    · exact hsU ((mem_insert.mp hR).resolve_left hne)
  · obtain ⟨w, hw⟩ := card_pos.mp hsize
    have hm : ({u, w} : Finset V) ∈ star u C := mem_image.mpr ⟨w, hw, rfl⟩
    refine ⟨{u, w}, mem_inter.mpr ⟨?_, (mem_sdiff.mp (hsU hm)).1⟩⟩
    rw [hsplit]
    exact mem_union_right _ (mem_insert_of_mem hm)

end KqR75.CoverDown

#print axioms KqR75.CoverDown.star_extension
#print axioms KqR75.CoverDown.pair_extension
