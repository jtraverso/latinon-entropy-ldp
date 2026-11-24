module
public import SlotPairMargins

@[expose] public section
noncomputable section
namespace KqR75.PhysicalAffineCell

open Finset ColouredCliques Transversal SlotProfiles CompleteJohnson SparseGram

variable {K C : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Fintype C] [DecidableEq C] {n q : ℕ}

def slotEmbedding (s : Fin q → K) (σ : Fin q → Equiv.Perm K) (p : K × K) :
    Fin q ↪ (Fin q × K) :=
  ⟨fun i => (i, σ i (point (s i) p)), fun _ _ h => congrArg Prod.fst h⟩

/-- The physical clique obtained by carrying one transversal through the
embedding of the cell's vertices into the host. -/
def block (f : (Fin q × K) ↪ Fin n) (s : Fin q → K)
    (σ : Fin q → Equiv.Perm K) (p : K × K) : Clique n q :=
  ⟨univ.map ((slotEmbedding s σ p).trans f), mem_powersetCard.mpr ⟨subset_univ _, by simp⟩⟩

omit [Fintype K] [DecidableEq K] in
theorem mem_block (f : (Fin q × K) ↪ Fin n) (s : Fin q → K)
    (σ : Fin q → Equiv.Perm K) (p : K × K) (a : Fin q × K) :
    f a ∈ (block f s σ p : Finset (Fin n)) ↔ σ a.1 (point (s a.1) p) = a.2 := by
  change f a ∈ univ.map ((slotEmbedding s σ p).trans f) ↔ _
  constructor
  · intro h
    obtain ⟨i, _, hi⟩ := mem_map.mp h
    have hpair : (i, σ i (point (s i) p)) = a := f.injective hi
    have hidx : i = a.1 := congrArg Prod.fst hpair
    subst i
    exact congrArg Prod.snd hpair
  · intro h
    exact mem_map.mpr ⟨a.1, mem_univ _, by
      change f (a.1, σ a.1 (point (s a.1) p)) = f a
      rw [h]⟩

omit [Fintype K] [DecidableEq K] in
/-- Each cross-group pair is covered exactly once by every permuted
transversal decomposition of the physical cell. -/
theorem pair_covered_once (f : (Fin q × K) ↪ Fin n) (s : Fin q → K)
    (hs : Function.Injective s) (σ : Fin q → Equiv.Perm K)
    (a b : Fin q × K) (hab : a.1 ≠ b.1) :
    ∃! p : K × K, f a ∈ (block f s σ p : Finset (Fin n)) ∧
      f b ∈ (block f s σ p : Finset (Fin n)) := by
  have hbij := pair_bijective (s a.1) (s b.1) (fun h => hab (hs h))
  obtain ⟨p, hp⟩ := hbij.2 ((σ a.1).symm a.2, (σ b.1).symm b.2)
  have hpair (p' : K × K) :
      (f a ∈ (block f s σ p' : Finset (Fin n)) ∧
        f b ∈ (block f s σ p' : Finset (Fin n))) ↔
      (point (s a.1) p', point (s b.1) p') = ((σ a.1).symm a.2, (σ b.1).symm b.2) := by
    rw [mem_block, mem_block, Prod.mk.injEq]
    exact and_congr (σ a.1).eq_symm_apply.symm (σ b.1).eq_symm_apply.symm
  exact ⟨p, (hpair p).mpr hp, fun p' hp' => hbij.1 (((hpair p').mp hp').trans hp.symm)⟩

omit [Fintype K] [DecidableEq K] in
theorem cross_pair_of_resource (f : (Fin q × K) ↪ Fin n) (s : Fin q → K)
    (σ : Fin q → Equiv.Perm K) (p : K × K) (e : Edge n)
    (hp : e ∈ resources n q (block f s σ p)) :
    ∃ a b : Fin q × K, a.1 ≠ b.1 ∧ (e : Finset (Fin n)) = {f a, f b} := by
  obtain ⟨x, y, hxy, he⟩ := card_eq_two.mp (mem_powersetCard.mp e.property).2
  have he' := (mem_filter.mp hp).2
  rw [he] at he'
  have hx : x ∈ (block f s σ p : Finset (Fin n)) := he' (by simp)
  have hy : y ∈ (block f s σ p : Finset (Fin n)) := he' (by simp)
  obtain ⟨i, _, rfl⟩ := mem_map.mp hx
  obtain ⟨j, _, rfl⟩ := mem_map.mp hy
  refine ⟨slotEmbedding s σ p i, slotEmbedding s σ p j, ?_, he⟩
  exact fun h => hxy (congrArg ((slotEmbedding s σ p).trans f) h)

omit [Fintype K] [DecidableEq K] in
/-- The edge coverage equation of a physical cell holds for each
permutation of its groups, with the same set of cross-group edges. -/
theorem resources_iff_cross_pair (f : (Fin q × K) ↪ Fin n) (s : Fin q → K)
    (hs : Function.Injective s) (σ : Fin q → Equiv.Perm K) (e : Edge n) :
    (∃! p : K × K, e ∈ resources n q (block f s σ p)) ↔
      ∃ a b : Fin q × K, a.1 ≠ b.1 ∧ (e : Finset (Fin n)) = {f a, f b} := by
  constructor
  · rintro ⟨p, hp, _⟩
    exact cross_pair_of_resource f s σ p e hp
  · rintro ⟨a, b, hab, he⟩
    have hm (p : K × K) : e ∈ resources n q (block f s σ p) ↔
        f a ∈ (block f s σ p : Finset (Fin n)) ∧
        f b ∈ (block f s σ p : Finset (Fin n)) := by
      simp only [resources, mem_filter, mem_univ, true_and, he, insert_subset_iff, singleton_subset_iff]
    simpa only [hm] using pair_covered_once f s hs σ a b hab

omit [Fintype K] [DecidableEq K] in
theorem block_injective (hq : 2 ≤ q) (f : (Fin q × K) ↪ Fin n)
    (s : Fin q → K) (hs : Function.Injective s) (σ : Fin q → Equiv.Perm K) :
    Function.Injective (block f s σ) := by
  intro p p' he
  let i : Fin q := ⟨0, by omega⟩
  let j : Fin q := ⟨1, by omega⟩
  let a := slotEmbedding s σ p i
  let b := slotEmbedding s σ p j
  have hab : a.1 ≠ b.1 := by
    intro h
    have hij : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  obtain ⟨w, _, hw⟩ := pair_covered_once f s hs σ a b hab
  have hp : f a ∈ (block f s σ p : Finset (Fin n)) ∧
      f b ∈ (block f s σ p : Finset (Fin n)) :=
    ⟨mem_map.mpr ⟨i, mem_univ _, rfl⟩, mem_map.mpr ⟨j, mem_univ _, rfl⟩⟩
  have hp' := hp
  rw [he] at hp'
  exact (hw p hp).trans (hw p' hp').symm

omit [Fintype K] in
/-- The embedding preserves the type of each transversal, hence the
abstract histogram computations apply to the physical cliques. -/
theorem block_type (f : (Fin q × K) ↪ Fin n) (s : Fin q → K)
    (σ : Fin q → Equiv.Perm K) (tag : Fin q → C) (ref : C)
    (colour : Fin n → C) (hcolour : ∀ i x, colour (f (i, x)) = if x = 0 then tag i else ref)
    (p : K × K) :
    cliqueType colour (block f s σ p) = slotType (AffineCellCounts.lineColours s σ tag ref p) := by
  apply (cliqueType_eq _ _ _).mpr
  funext c
  change ((univ.map ((slotEmbedding s σ p).trans f)).filter (fun v => colour v = c)).card =
    (univ.filter (fun i => AffineCellCounts.lineColours s σ tag ref p i = c)).card
  rw [filter_map, card_map]
  congr 1
  apply filter_congr
  intro i _
  change (colour (f (i, σ i (point (s i) p))) = c) ↔ _
  rw [hcolour]
  rfl

def blocks (hq : 2 ≤ q) (f : (Fin q × K) ↪ Fin n) (s : Fin q → K)
    (hs : Function.Injective s) (σ : Fin q → Equiv.Perm K) : Finset (Clique n q) :=
  univ.map ⟨block f s σ, block_injective hq f s hs σ⟩

omit [DecidableEq K] in
theorem blocks_cover_count (hq : 2 ≤ q) (f : (Fin q × K) ↪ Fin n) (s : Fin q → K)
    (hs : Function.Injective s) (σ : Fin q → Equiv.Perm K) (e : Edge n) :
    ((blocks hq f s hs σ).filter (fun b => e ∈ resources n q b)).card =
      if ∃ a b : Fin q × K, a.1 ≠ b.1 ∧ (e : Finset (Fin n)) = {f a, f b} then 1 else 0 := by
  classical
  rw [blocks, filter_map, card_map]
  change ((univ : Finset (K × K)).filter (fun p => e ∈ resources n q (block f s σ p))).card = _
  split_ifs with he
  · obtain ⟨p, hp, hu⟩ := (resources_iff_cross_pair f s hs σ e).mpr he
    have heq : (univ : Finset (K × K)).filter (fun p => e ∈ resources n q (block f s σ p)) = {p} := by
      ext p'
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨hu p', fun h => h.symm ▸ hp⟩
    rw [heq, card_singleton]
  · have heq : (univ : Finset (K × K)).filter (fun p => e ∈ resources n q (block f s σ p)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact he (cross_pair_of_resource f s σ p e (mem_filter.mp hp).2)
    rw [heq, card_empty]

theorem blocks_histogram (hq : 2 ≤ q) (f : (Fin q × K) ↪ Fin n) (s : Fin q → K)
    (hs : Function.Injective s) (σ : Fin q → Equiv.Perm K) (tag : Fin q → C) (ref : C)
    (colour : Fin n → C) (hcolour : ∀ i x, colour (f (i, x)) = if x = 0 then tag i else ref)
    (t : TypeProfile C q) :
    (((blocks hq f s hs σ).filter (fun b => cliqueType colour b = t)).card : ℤ) =
      AffineCellCounts.histogram slotType s σ tag ref t := by
  rw [blocks, filter_map, card_map]
  change (((univ : Finset (K × K)).filter (fun p => cliqueType colour (block f s σ p) = t)).card : ℤ) = _
  calc
    _ = ∑ p ∈ univ.filter (fun p => cliqueType colour (block f s σ p) = t), (1 : ℤ) := by simp
    _ = _ := by simp only [sum_filter, block_type f s σ tag ref colour hcolour, AffineCellCounts.histogram]

/-- Switching the two decompositions preserves the multiplicity of every
physical edge and changes the type histogram by the prescribed column. -/
theorem switch_cell (hq : 2 ≤ q) (f : (Fin q × K) ↪ Fin n) (s : Fin q → K)
    (hs : Function.Injective s) (r : Fin q) (tag : Fin q → C) (ref : C)
    (colour : Fin n → C) (hcolour : ∀ i x, colour (f (i, x)) = if x = 0 then tag i else ref) :
    let plus := blocks hq f s hs (fun _ => Equiv.refl K)
    let minus := blocks hq f s hs (fun i => if i = r then Equiv.swap 0 1 else Equiv.refl K)
    (∀ e : Edge n, (plus.filter fun b => e ∈ resources n q b).card =
      (minus.filter fun b => e ∈ resources n q b).card) ∧
    ∀ t, ((plus.filter (fun b => cliqueType colour b = t)).card : ℤ) -
      ((minus.filter (fun b => cliqueType colour b = t)).card : ℤ) =
      SlotPairMargins.cellDifference s ref tag r t := by
  dsimp only
  constructor
  · intro e
    rw [blocks_cover_count, blocks_cover_count]
  · intro t
    rw [blocks_histogram hq f s hs _ tag ref colour hcolour t,
      blocks_histogram hq f s hs _ tag ref colour hcolour t]
    rfl

omit [DecidableEq K] in
theorem block_subset_cell (f : (Fin q × K) ↪ Fin n) (s : Fin q → K)
    (σ : Fin q → Equiv.Perm K) (p : K × K) :
    (block f s σ p : Finset (Fin n)) ⊆ univ.map f := by
  intro x hx
  obtain ⟨i, _, hi⟩ := mem_map.mp hx
  exact mem_map.mpr ⟨slotEmbedding s σ p i, mem_univ _, hi⟩

omit [DecidableEq K] in
theorem disjoint_blocks {I : Type*} (cells : Finset I) (hq : 2 ≤ q)
    (f : I → (Fin q × K) ↪ Fin n) (s : Fin q → K) (hs : Function.Injective s)
    (σ : I → Fin q → Equiv.Perm K)
    (hsep : ∀ i ∈ cells, ∀ j ∈ cells, i ≠ j →
      ((univ.map (f i)) ∩ (univ.map (f j))).card ≤ 1) :
    Set.PairwiseDisjoint (↑cells : Set I) (fun i => blocks hq (f i) s hs (σ i)) := by
  intro i hi j hj hij
  apply disjoint_left.mpr
  intro b hb hc
  obtain ⟨p, _, hp⟩ := mem_map.mp hb
  obtain ⟨p', _, hp'⟩ := mem_map.mp hc
  have hsub : (b : Finset (Fin n)) ⊆ (univ.map (f i)) ∩ (univ.map (f j)) := by
    apply subset_inter
    · rw [← hp]
      exact block_subset_cell (f i) s (σ i) p
    · rw [← hp']
      exact block_subset_cell (f j) s (σ j) p'
  have hh := (card_le_card hsub).trans (hsep i hi j hj hij)
  rw [(mem_powersetCard.mp b.property).2] at hh
  omega

/-- Switching a finite family with disjoint pairs preserves the edge
loads of the union and adds its signed histogram columns. A flipped cell
starts in the opposite decomposition and contributes the negative column. -/
theorem switch_disjoint_cells {I : Type*} (cells : Finset I) (hq : 2 ≤ q)
    (f : I → (Fin q × K) ↪ Fin n) (s : Fin q → K) (hs : Function.Injective s)
    (r : I → Fin q) (tag : I → Fin q → C) (flip : I → Bool) (ref : C) (colour : Fin n → C)
    (hcolour : ∀ j ∈ cells, ∀ i x, colour (f j (i, x)) = if x = 0 then tag j i else ref)
    (hsep : ∀ i ∈ cells, ∀ j ∈ cells, i ≠ j →
      ((univ.map (f i)) ∩ (univ.map (f j))).card ≤ 1) :
    let after := fun j => blocks hq (f j) s hs
      (fun i => if flip j ∧ i = r j then Equiv.swap 0 1 else Equiv.refl K)
    let before := fun j => blocks hq (f j) s hs
      (fun i => if ¬flip j ∧ i = r j then Equiv.swap 0 1 else Equiv.refl K)
    (∀ e : Edge n, ((cells.biUnion after).filter fun b => e ∈ resources n q b).card =
      ((cells.biUnion before).filter fun b => e ∈ resources n q b).card) ∧
    ∀ t, (((cells.biUnion after).filter (fun b => cliqueType colour b = t)).card : ℤ) -
      (((cells.biUnion before).filter (fun b => cliqueType colour b = t)).card : ℤ) =
      ∑ j ∈ cells, (if flip j then -1 else 1) * SlotPairMargins.cellDifference s ref (tag j) (r j) t := by
  classical
  let after := fun j => blocks hq (f j) s hs
    (fun i => if flip j ∧ i = r j then Equiv.swap 0 1 else Equiv.refl K)
  let before := fun j => blocks hq (f j) s hs
    (fun i => if ¬flip j ∧ i = r j then Equiv.swap 0 1 else Equiv.refl K)
  have hp : Set.PairwiseDisjoint (↑cells : Set I) after :=
    disjoint_blocks cells hq f s hs _ hsep
  have hm : Set.PairwiseDisjoint (↑cells : Set I) before :=
    disjoint_blocks cells hq f s hs _ hsep
  have hcount (P : Clique n q → Prop) [DecidablePred P] :
      ((cells.biUnion after).filter P).card = ∑ j ∈ cells, ((after j).filter P).card ∧
      ((cells.biUnion before).filter P).card = ∑ j ∈ cells, ((before j).filter P).card := by
    simp only [filter_biUnion]
    exact ⟨card_biUnion (pairwiseDisjoint_filter hp P), card_biUnion (pairwiseDisjoint_filter hm P)⟩
  have hcell (j : I) (hj : j ∈ cells) := switch_cell hq (f j) s hs (r j) (tag j) ref colour (hcolour j hj)
  constructor
  · intro e
    obtain ⟨he₁, he₂⟩ := hcount (fun b => e ∈ resources n q b)
    change ((cells.biUnion after).filter _).card = ((cells.biUnion before).filter _).card
    rw [he₁, he₂]
    apply sum_congr rfl
    intro j hj
    by_cases h : flip j
    · simpa [after, before, h] using ((hcell j hj).1 e).symm
    · simpa [after, before, h] using (hcell j hj).1 e
  · intro t
    obtain ⟨ht₁, ht₂⟩ := hcount (fun b => cliqueType colour b = t)
    change (((cells.biUnion after).filter _).card : ℤ) -
      (((cells.biUnion before).filter _).card : ℤ) = _
    rw [ht₁, ht₂, Nat.cast_sum, Nat.cast_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    by_cases h : flip j
    · simpa [after, before, h, neg_sub] using congrArg Neg.neg ((hcell j hj).2 t)
    · simpa [after, before, h] using (hcell j hj).2 t

end KqR75.PhysicalAffineCell

#print axioms KqR75.PhysicalAffineCell.pair_covered_once
#print axioms KqR75.PhysicalAffineCell.resources_iff_cross_pair
#print axioms KqR75.PhysicalAffineCell.block_injective
#print axioms KqR75.PhysicalAffineCell.block_type
#print axioms KqR75.PhysicalAffineCell.blocks_histogram
#print axioms KqR75.PhysicalAffineCell.blocks_cover_count
#print axioms KqR75.PhysicalAffineCell.switch_cell
#print axioms KqR75.PhysicalAffineCell.switch_disjoint_cells
