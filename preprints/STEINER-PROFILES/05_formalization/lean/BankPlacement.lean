module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.Forall2

@[expose] public section
namespace KqR75.BankPlacement

open Finset

variable {C V : Type*}

/-- The total used degree bounds the number of vertices with too little
room left for the next cell. -/
theorem saturated_card_mul_le (vertices : Finset V) (degree : V → ℕ) (limit : ℕ) :
    (vertices.filter fun v => limit ≤ degree v).card * limit ≤ ∑ v ∈ vertices, degree v := by
  classical
  let saturated := vertices.filter fun v => limit ≤ degree v
  change saturated.card * limit ≤ _
  calc
    _ = ∑ _v ∈ saturated, limit := (sum_const_nat fun _ _ => rfl).symm
    _ ≤ ∑ v ∈ saturated, degree v := sum_le_sum (fun v hv => (mem_filter.mp hv).2)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)

/-- A cell can be placed inside prescribed colour classes while avoiding
all used or forbidden pairs. Avoiding those pairs even within a group
costs at most one forbidden neighborhood per chosen vertex. -/
theorem choose_vertices [DecidableEq V] (classes : C → Finset V) (blocked : Finset V)
    (neighbors : V → Finset V) (degree : ℕ) (hneighbors : ∀ v, (neighbors v).card ≤ degree)
    (colours : List C)
    (hspace : ∀ c ∈ colours, blocked.card + colours.length * (degree + 1) < (classes c).card) :
    ∃ picks : List V,
      List.Forall₂ (fun c v => v ∈ classes c ∧ v ∉ blocked) colours picks ∧
      picks.Nodup ∧ picks.Pairwise (fun a b => a ∉ neighbors b) := by
  induction colours with
  | nil => exact ⟨[], .nil, List.nodup_nil, .nil⟩
  | cons c tail ih =>
      have hlength : blocked.card + tail.length * (degree + 1) ≤
          blocked.card + (c :: tail).length * (degree + 1) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ (by simp)) _
      have htail (c' : C) (hc' : c' ∈ tail) :
          blocked.card + tail.length * (degree + 1) < (classes c').card := by
        have h := hspace c' (List.mem_cons_of_mem _ hc')
        exact hlength.trans_lt h
      obtain ⟨picks, hcolors, hnodup, hpairs⟩ := ih htail
      let used := picks.toFinset
      let excluded := (blocked ∪ used) ∪ used.biUnion neighbors
      have hused : used.card ≤ tail.length := by
        exact (List.toFinset_card_le picks).trans_eq hcolors.length_eq.symm
      have hsize : excluded.card ≤ blocked.card + tail.length * (degree + 1) := by
        have hN := card_biUnion_le_card_mul used neighbors degree (fun v _ => hneighbors v)
        calc
          _ ≤ (blocked ∪ used).card + (used.biUnion neighbors).card := card_union_le _ _
          _ ≤ blocked.card + used.card + used.card * degree :=
            Nat.add_le_add (card_union_le _ _) hN
          _ = blocked.card + used.card * (degree + 1) := by
            simp only [Nat.mul_add, Nat.mul_one]
            omega
          _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ hused) _
      obtain ⟨v, hv, hvnot⟩ := exists_mem_notMem_of_card_lt_card
        ((hsize.trans hlength).trans_lt (hspace c List.mem_cons_self))
      have hblock : v ∉ blocked := fun hb => hvnot (mem_union_left _ (mem_union_left _ hb))
      have hfresh : v ∉ picks := fun hv' =>
        hvnot (mem_union_left _ (mem_union_right _ (List.mem_toFinset.mpr hv')))
      have havoid (b : V) (hb : b ∈ picks) : v ∉ neighbors b := fun h =>
        hvnot (mem_union_right _ (mem_biUnion.mpr ⟨b, List.mem_toFinset.mpr hb, h⟩))
      exact ⟨v :: picks, .cons ⟨hv, hblock⟩ hcolors,
        List.nodup_cons.mpr ⟨hfresh, hnodup⟩, List.pairwise_cons.mpr ⟨havoid, hpairs⟩⟩

/-- The selected vertices indexed by their slots, for a symmetric forbidden
relation. This is the input needed to carry a cell to the physical host. -/
theorem choose_embedding [DecidableEq V] {m : ℕ} (colour : Fin m → C)
    (classes : C → Finset V) (blocked : Finset V) (neighbors : V → Finset V) (degree : ℕ)
    (hneighbors : ∀ v, (neighbors v).card ≤ degree)
    (hsym : ∀ a b, a ∈ neighbors b ↔ b ∈ neighbors a)
    (hspace : ∀ i, blocked.card + m * (degree + 1) < (classes (colour i)).card) :
    ∃ f : Fin m ↪ V,
      (∀ i, f i ∈ classes (colour i) ∧ f i ∉ blocked) ∧
      ∀ i j, i ≠ j → f i ∉ neighbors (f j) := by
  have hspace' (c : C) (hc : c ∈ List.ofFn colour) :
      blocked.card + (List.ofFn colour).length * (degree + 1) < (classes c).card := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hc
    simpa only [List.length_ofFn] using hspace i
  obtain ⟨picks, hcolors, hnodup, hpairs⟩ :=
    choose_vertices classes blocked neighbors degree hneighbors (List.ofFn colour) hspace'
  have hlen : picks.length = m := hcolors.length_eq.symm.trans List.length_ofFn
  have hi (i : Fin m) : i.val < picks.length := hlen.symm ▸ i.isLt
  let f (i : Fin m) : V := picks[i.val]'(hi i)
  have hf : Function.Injective f := fun i j hij => Fin.ext (hnodup.getElem_inj.mp hij)
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro i
    have hi' : i.val < (List.ofFn colour).length := by simpa only [List.length_ofFn] using i.isLt
    have hm := hcolors.get hi' (hi i)
    simpa [f, List.getElem_ofFn] using hm
  · intro i j hij
    change f i ∉ neighbors (f j)
    rcases lt_or_gt_of_ne hij with h | h
    · exact hpairs.rel_getElem_of_lt (hi i) (hi j) h
    · exact fun hm => hpairs.rel_getElem_of_lt (hi j) (hi i) h ((hsym _ _).mp hm)

/-- An arbitrary finite set of cell slots can be embedded without
identifying any vertices or using any forbidden pair. -/
theorem place_cell [DecidableEq V] {S : Type*} [Fintype S] (colour : S → C)
    (classes : C → Finset V) (blocked : Finset V) (neighbors : V → Finset V) (degree : ℕ)
    (hneighbors : ∀ v, (neighbors v).card ≤ degree)
    (hsym : ∀ a b, a ∈ neighbors b ↔ b ∈ neighbors a)
    (hspace : ∀ i, blocked.card + Fintype.card S * (degree + 1) < (classes (colour i)).card) :
    ∃ f : S ↪ V,
      (∀ i, f i ∈ classes (colour i) ∧ f i ∉ blocked) ∧
      ∀ i j, i ≠ j → f i ∉ neighbors (f j) := by
  classical
  let e := Fintype.equivFin S
  obtain ⟨f, hclasses, havoid⟩ := choose_embedding (colour ∘ e.symm)
    classes blocked neighbors degree hneighbors hsym (fun i => hspace (e.symm i))
  refine ⟨e.toEmbedding.trans f, ?_, ?_⟩
  · intro i
    simpa using hclasses (e i)
  · exact fun i j hij => havoid (e i) (e j) (fun h => hij (e.injective h))

section MultipleCells

variable [DecidableEq V] {m : ℕ}

def cellVertices (f : Fin m ↪ V) : Finset V := univ.map f

def useCount (cells : List (Fin m ↪ V)) (v : V) : ℕ :=
  (cells.filter fun f => v ∈ cellVertices f).length

def usedNeighbors : List (Fin m ↪ V) → V → Finset V
  | [], _ => ∅
  | f :: cells, v =>
    (if v ∈ cellVertices f then cellVertices f else ∅) ∪ usedNeighbors cells v

private theorem usedNeighbors_symm (cells : List (Fin m ↪ V)) (a b : V) :
    a ∈ usedNeighbors cells b ↔ b ∈ usedNeighbors cells a := by
  induction cells with
  | nil => simp [usedNeighbors]
  | cons f cells ih =>
    by_cases ha : a ∈ cellVertices f <;> by_cases hb : b ∈ cellVertices f <;>
      simp [usedNeighbors, ha, hb, ih]

private theorem mem_usedNeighbors {cells : List (Fin m ↪ V)} {f : Fin m ↪ V} (hf : f ∈ cells)
    {a b : V} (ha : a ∈ cellVertices f) (hb : b ∈ cellVertices f) :
    a ∈ usedNeighbors cells b := by
  induction cells with
  | nil => simp at hf
  | cons g cells ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · exact mem_union_left _ (by simpa [hb] using ha)
    · exact mem_union_right _ (ih hf)

private theorem usedNeighbors_card (cells : List (Fin m ↪ V)) (v : V) :
    (usedNeighbors cells v).card ≤ m * useCount cells v := by
  induction cells with
  | nil => simp [usedNeighbors, useCount]
  | cons f cells ih =>
    by_cases h : v ∈ cellVertices f
    · simp only [usedNeighbors, useCount, List.filter_cons, h, decide_true,
        ite_true, List.length_cons]
      calc
        _ ≤ (cellVertices f).card + (usedNeighbors cells v).card := card_union_le _ _
        _ ≤ m + m * useCount cells v := by
          simpa [cellVertices] using Nat.add_le_add_left ih m
        _ = _ := by rw [Nat.mul_succ, Nat.add_comm]; rfl
    · simpa [usedNeighbors, useCount, h] using ih

private theorem total_useCount [Fintype V] (cells : List (Fin m ↪ V)) :
    (∑ v : V, useCount cells v) = cells.length * m := by
  induction cells with
  | nil => simp [useCount]
  | cons f cells ih =>
    have hcount (v : V) :
        useCount (f :: cells) v = useCount cells v + if v ∈ cellVertices f then 1 else 0 := by
      by_cases h : v ∈ cellVertices f <;> simp [useCount, h]
    simp_rw [hcount, sum_add_distrib, ih]
    rw [← sum_filter, filter_mem_eq_of_subset (subset_univ (cellVertices f))]
    simp [cellVertices, Nat.succ_mul]

/-- Place a list of equally sized cells. The budget bounds the number of
vertices excluded by saturation. Reserving every pair within each cell
allows different cells to share a vertex but never a pair. -/
theorem place_bank [Fintype V] (requests : List (Fin m → C))
    (classes : C → Finset V) (forbidden : V → Finset V)
    (degree cap budget : ℕ) (hcap : 0 < cap)
    (hforbid : ∀ v, (forbidden v).card ≤ degree)
    (hsym : ∀ a b, a ∈ forbidden b ↔ b ∈ forbidden a)
    (htotal : requests.length * m ≤ budget * cap)
    (hspace : ∀ c, budget + m * (degree + m * cap + 1) < (classes c).card) :
    ∃ cells : List (Fin m ↪ V),
      List.Forall₂
        (fun colour f => (∀ i, f i ∈ classes (colour i)) ∧
          ∀ i j, i ≠ j → f i ∉ forbidden (f j)) requests cells ∧
      cells.Pairwise (fun f g => (cellVertices f ∩ cellVertices g).card ≤ 1) ∧
      (∀ v, useCount cells v ≤ cap) ∧
      ∀ v, (usedNeighbors cells v).card ≤ m * cap := by
  classical
  induction requests with
  | nil => exact ⟨[], .nil, .nil, fun _ => by simp [useCount], fun _ => by simp [usedNeighbors]⟩
  | cons colour tail ih =>
    have htail : tail.length * m ≤ budget * cap :=
      (Nat.mul_le_mul_right _ (Nat.le_succ _)).trans htotal
    obtain ⟨cells, hlabels, hdisjoint, hload, hdegree⟩ := ih htail
    let blocked := (univ : Finset V).filter fun v => cap ≤ useCount cells v
    have hb : blocked.card ≤ budget := by
      have hh : blocked.card * cap ≤ ∑ v : V, useCount cells v :=
        saturated_card_mul_le univ (useCount cells) cap
      rw [total_useCount, ← hlabels.length_eq] at hh
      exact Nat.le_of_mul_le_mul_right (hh.trans htail) hcap
    let allNeighbors (v : V) := forbidden v ∪ usedNeighbors cells v
    have hN (v : V) : (allNeighbors v).card ≤ degree + m * cap :=
      (card_union_le _ _).trans (Nat.add_le_add (hforbid v) (hdegree v))
    have hsym' (a b : V) : a ∈ allNeighbors b ↔ b ∈ allNeighbors a := by
      simp only [allNeighbors, mem_union]
      exact or_congr (hsym a b) (usedNeighbors_symm cells a b)
    obtain ⟨f, hf, havoid⟩ := choose_embedding colour classes blocked allNeighbors
      (degree + m * cap) hN hsym'
      (fun i => (Nat.add_le_add_right hb _).trans_lt (hspace (colour i)))
    have hforbid' (i j : Fin m) (hne : i ≠ j) : f i ∉ forbidden (f j) :=
      fun h => havoid i j hne (mem_union_left _ h)
    have hpairs (g : Fin m ↪ V) (hg : g ∈ cells) :
        (cellVertices f ∩ cellVertices g).card ≤ 1 := by
      by_contra! h
      obtain ⟨a, ha, b, hb', hab⟩ := one_lt_card.mp h
      obtain ⟨i, _, rfl⟩ := mem_map.mp (mem_inter.mp ha).1
      obtain ⟨j, _, rfl⟩ := mem_map.mp (mem_inter.mp hb').1
      exact havoid i j (fun h => hab (congrArg f h)) (mem_union_right _
        (mem_usedNeighbors hg (mem_inter.mp ha).2 (mem_inter.mp hb').2))
    have hload' (v : V) : useCount (f :: cells) v ≤ cap := by
      by_cases hv : v ∈ cellVertices f
      · obtain ⟨i, _, rfl⟩ := mem_map.mp hv
        have hn : ¬cap ≤ useCount cells (f i) := fun h =>
          (hf i).2 (mem_filter.mpr ⟨mem_univ _, h⟩)
        have hh : useCount cells (f i) + 1 ≤ cap := by omega
        simpa [useCount, hv] using hh
      · simpa [useCount, hv] using hload v
    exact ⟨f :: cells, .cons ⟨fun i => (hf i).1, hforbid'⟩ hlabels,
      List.pairwise_cons.mpr ⟨hpairs, hdisjoint⟩, hload',
      fun v => (usedNeighbors_card (f :: cells) v).trans (Nat.mul_le_mul_left _ (hload' v))⟩

end MultipleCells

/-- Place the cells of an indexed bank and retain the index of each copy.
This allows the index to record its histogram generator, orientation and
copy number. -/
theorem place_indexed_bank [DecidableEq V] [Fintype V]
    {I S : Type*} [Fintype I] [Fintype S] (colour : I → S → C)
    (classes : C → Finset V) (forbidden : V → Finset V)
    (degree cap budget : ℕ) (hcap : 0 < cap)
    (hforbid : ∀ v, (forbidden v).card ≤ degree)
    (hsym : ∀ a b, a ∈ forbidden b ↔ b ∈ forbidden a)
    (htotal : Fintype.card I * Fintype.card S ≤ budget * cap)
    (hspace : ∀ c, budget + Fintype.card S * (degree + Fintype.card S * cap + 1) <
      (classes c).card) :
    ∃ f : I → S ↪ V,
      (∀ i x, f i x ∈ classes (colour i x)) ∧
      (∀ i x y, x ≠ y → f i x ∉ forbidden (f i y)) ∧
      (∀ i j, i ≠ j → ((univ.map (f i)) ∩ (univ.map (f j))).card ≤ 1) ∧
      ∀ v, ((univ : Finset I).biUnion fun i =>
        if v ∈ univ.map (f i) then univ.map (f i) else ∅).card ≤ Fintype.card S * cap := by
  classical
  let eI := Fintype.equivFin I
  let eS := Fintype.equivFin S
  let labels (i : Fin (Fintype.card I)) (x : Fin (Fintype.card S)) :=
    colour (eI.symm i) (eS.symm x)
  let requests := List.ofFn labels
  have hlen : requests.length = Fintype.card I := List.length_ofFn
  obtain ⟨cells, hlabels, hsep, _, hdegree⟩ := place_bank requests
    classes forbidden degree cap budget hcap hforbid hsym (by rwa [hlen]) hspace
  have hlen' : cells.length = Fintype.card I := hlabels.length_eq.symm.trans hlen
  have hi (i : I) : (eI i).val < cells.length := hlen'.symm ▸ (eI i).isLt
  let atIndex (i : I) : Fin (Fintype.card S) ↪ V := cells[(eI i).val]'(hi i)
  let f (i : I) : S ↪ V := eS.toEmbedding.trans (atIndex i)
  have hcell (i : I) : (∀ x, atIndex i x ∈ classes (colour i (eS.symm x))) ∧
      ∀ x y, x ≠ y → atIndex i x ∉ forbidden (atIndex i y) := by
    have hreq : (eI i).val < requests.length := hlen.symm ▸ (eI i).isLt
    have hc := hlabels.get hreq (hi i)
    simpa [requests, List.getElem_ofFn, labels, atIndex] using hc
  have himage (i : I) : univ.map (f i) = cellVertices (atIndex i) := by
    ext v
    simp only [f, cellVertices, mem_map, mem_univ, true_and, Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply]
    exact ⟨fun ⟨x, h⟩ => ⟨eS x, h⟩, fun ⟨x, h⟩ => ⟨eS.symm x, by simpa using h⟩⟩
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro i x
    simpa [f] using (hcell i).1 (eS x)
  · exact fun i x y hxy => (hcell i).2 (eS x) (eS y) (fun h => hxy (eS.injective h))
  · intro i j hij
    rw [himage, himage]
    rcases lt_or_gt_of_ne (fun h => hij (eI.injective h)) with h | h
    · exact hsep.rel_getElem_of_lt (hi i) (hi j) h
    · rw [inter_comm]
      exact hsep.rel_getElem_of_lt (hi j) (hi i) h
  · intro v
    refine (card_le_card ?_).trans (hdegree v)
    intro a ha
    obtain ⟨i, _, hai⟩ := mem_biUnion.mp ha
    by_cases hv : v ∈ univ.map (f i)
    · have hmem : atIndex i ∈ cells := List.getElem_mem (hi i)
      rw [ite_eq_left hv, himage] at hai
      rw [himage] at hv
      exact mem_usedNeighbors hmem hai hv
    · simp [hv] at hai

end KqR75.BankPlacement

#print axioms KqR75.BankPlacement.choose_vertices
#print axioms KqR75.BankPlacement.saturated_card_mul_le
#print axioms KqR75.BankPlacement.choose_embedding
#print axioms KqR75.BankPlacement.place_cell
#print axioms KqR75.BankPlacement.place_bank
#print axioms KqR75.BankPlacement.place_indexed_bank
