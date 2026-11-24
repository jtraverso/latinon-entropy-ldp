module
public import PackingJoin

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Finset ColouredCliques CompleteJohnson SparseGram CoverDown

/-- Cardinality and vertex-degree divisibility for K_q-decomposition. -/
def Divisible {n : ℕ} (q : ℕ) (A : Finset (Edge n)) : Prop :=
  q.choose 2 ∣ A.card ∧ ∀ v : Fin n, q - 1 ∣ degree (vertexSets A) v

private theorem clique_pairs {n q : ℕ} (b : Clique n q) :
    vertexSets (resources n q b) = b.val.powersetCard 2 := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := mem_map.mp he
    exact mem_powersetCard.mpr ⟨(mem_filter.mp hf).2, (mem_powersetCard.mp f.property).2⟩
  · intro he
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp he
    let f : Edge n := ⟨e, mem_powersetCard.mpr ⟨subset_univ _, hcard⟩⟩
    exact (vertexSets_mem _ f).mpr (mem_filter.mpr ⟨mem_univ _, hsub⟩)

/-- The union of the resource families of a packing is its edge set. -/
private theorem cover_edges {n q : ℕ} {P : Finset (Clique n q)} {A : Finset (Edge n)}
    (hP : packs P A) : P.biUnion (resources n q) = A := by
  ext e
  constructor
  · intro he
    obtain ⟨b, hb, he'⟩ := mem_biUnion.mp he
    exact edge_of_packs hP hb he'
  · intro he
    have hh := hP e
    rw [ite_eq_left he] at hh
    have hf : 0 < (P.filter fun b => e ∈ resources n q b).card := by
      change 0 < PhysicalBank.edgeMultiplicity P e
      omega
    obtain ⟨b, hb⟩ := card_pos.mp hf
    exact mem_biUnion.mpr ⟨b, (mem_filter.mp hb).1, (mem_filter.mp hb).2⟩

private theorem resource_disjoint {n q : ℕ} {P : Finset (Clique n q)} {A : Finset (Edge n)}
    (hP : packs P A) :
    Set.PairwiseDisjoint (P : Set (Clique n q)) (resources n q) := by
  intro b hb c hc hne
  apply disjoint_left.mpr
  intro e he he'
  have h : (P.filter (fun d => e ∈ resources n q d)).card ≤ 1 := by
    change PhysicalBank.edgeMultiplicity P e ≤ 1
    rw [hP e]
    split_ifs <;> omega
  exact hne (card_le_one.mp h b (mem_filter.mpr ⟨hb, he⟩) c (mem_filter.mpr ⟨hc, he'⟩))

/-- Physical packings imply the two divisibility conditions. -/
theorem divisible_of_packs {n q : ℕ} {P : Finset (Clique n q)} {A : Finset (Edge n)}
    (hP : packs P A) : Divisible q A := by
  classical
  have hc := cover_edges hP
  have hd := resource_disjoint hP
  refine ⟨⟨P.card, ?_⟩, ?_⟩
  · rw [← hc, card_biUnion hd]
    simp [resources_card, Nat.mul_comm]
  · intro v
    let F := fun b : Clique n q => (vertexSets (resources n q b)).filter (fun e => v ∈ e)
    have hF : Set.PairwiseDisjoint (P : Set (Clique n q)) F := by
      intro b hb c hc hne
      apply disjoint_left.mpr
      intro e he he'
      obtain ⟨f, hf, rfl⟩ := mem_map.mp (mem_filter.mp he).1
      exact disjoint_left.mp (hd hb hc hne) hf
        ((vertexSets_mem _ f).mp (mem_filter.mp he').1)
    have he : (vertexSets A).filter (fun e => v ∈ e) = P.biUnion F := by
      rw [← hc]
      ext e
      constructor
      · intro h
        obtain ⟨h, hv⟩ := mem_filter.mp h
        obtain ⟨f, hf, rfl⟩ := mem_map.mp h
        obtain ⟨b, hb, hb'⟩ := mem_biUnion.mp hf
        exact mem_biUnion.mpr ⟨b, hb, mem_filter.mpr ⟨(vertexSets_mem _ f).mpr hb', hv⟩⟩
      · intro he
        obtain ⟨b, hb, hb'⟩ := mem_biUnion.mp he
        obtain ⟨hf, hv⟩ := mem_filter.mp hb'
        obtain ⟨f, hf, rfl⟩ := mem_map.mp hf
        exact mem_filter.mpr ⟨(vertexSets_mem _ f).mpr (mem_biUnion.mpr ⟨b, hb, (vertexSets_mem _ f).mp hf⟩), hv⟩
    rw [degree, he, card_biUnion hF]
    apply dvd_sum
    intro b _
    change q - 1 ∣ degree (vertexSets (resources n q b)) v
    rw [clique_pairs, clique_degree, (mem_powersetCard.mp b.property).2]
    split_ifs <;> simp

/-- Divisibility is additive on disjoint edge sets. -/
theorem divisible_union {n q : ℕ} {A B : Finset (Edge n)}
    (hd : Disjoint A B) (hA : Divisible q A) (hB : Divisible q B) : Divisible q (A ∪ B) := by
  have hv : Disjoint (vertexSets A) (vertexSets B) := by
    apply disjoint_left.mpr
    intro e he he'
    obtain ⟨f, hf, rfl⟩ := mem_map.mp he
    exact disjoint_left.mp hd hf ((vertexSets_mem B f).mp he')
  refine ⟨by rw [card_union_of_disjoint hd]; exact dvd_add hA.1 hB.1, ?_⟩
  intro v
  have he : vertexSets (A ∪ B) = vertexSets A ∪ vertexSets B := map_union _ _
  rw [he, degree_union hv]
  exact dvd_add (hA.2 v) (hB.2 v)

/-- Removing a divisible piece from a divisible graph preserves divisibility. -/
theorem divisible_sdiff {n q : ℕ} {A B : Finset (Edge n)}
    (hBA : B ⊆ A) (hA : Divisible q A) (hB : Divisible q B) : Divisible q (A \ B) := by
  refine ⟨by rw [card_sdiff_of_subset hBA]; exact Nat.dvd_sub hA.1 hB.1, ?_⟩
  intro v
  have he : vertexSets (A \ B) = vertexSets A \ vertexSets B := by
    ext e
    constructor
    · intro h
      obtain ⟨f, hf, rfl⟩ := mem_map.mp h
      obtain ⟨hfA, hfB⟩ := mem_sdiff.mp hf
      exact mem_sdiff.mpr ⟨(vertexSets_mem A f).mpr hfA, fun hf => hfB ((vertexSets_mem B f).mp hf)⟩
    · intro h
      obtain ⟨hA, hB⟩ := mem_sdiff.mp h
      obtain ⟨f, hf, rfl⟩ := mem_map.mp hA
      exact (vertexSets_mem _ f).mpr (mem_sdiff.mpr ⟨hf, fun h => hB ((vertexSets_mem B f).mpr h)⟩)
  have hsub : vertexSets B ⊆ vertexSets A := map_subset_map.mpr hBA
  have hd := degree_sdiff_add hsub v
  have hdegree_eq : degree (vertexSets A \ vertexSets B) v =
      degree (vertexSets A) v - degree (vertexSets B) v := by omega
  rw [he, hdegree_eq]
  exact Nat.dvd_sub (hA.2 v) (hB.2 v)

/-- Ordinary divisibility of the complete graph in the physical edge universe. -/
theorem divisible_complete {n q : ℕ} (hcard : q.choose 2 ∣ n.choose 2)
    (hdegree : q - 1 ∣ n - 1) : Divisible q (univ : Finset (Edge n)) := by
  have hE : vertexSets (univ : Finset (Edge n)) =
      (univ : Finset (Fin n)).powersetCard 2 := by
    ext e
    constructor
    · intro he
      exact mem_powersetCard.mpr ⟨subset_univ _, vertexSets_card he⟩
    · intro he
      let f : Edge n := ⟨e, he⟩
      exact (vertexSets_mem _ f).mpr (mem_univ f)
  refine ⟨?_, fun v => ?_⟩
  · rw [← vertexSets_size, hE, card_powersetCard]
    simpa using hcard
  · rw [hE, clique_degree]
    simpa using hdegree

/-- After cover-down, the unused reserve is divisible. The removed parts
are the packed greedy host and used reserve, the bank, and the absorber's
decomposition with empty input. -/
theorem divisible_after_cover {n q : ℕ} (hq : 2 ≤ q)
    (A X F Y : Finset (Edge n)) (hAX : Disjoint A X) (hAF : Disjoint A F)
    (hXF : Disjoint X F) (hY : Y ⊆ X)
    (h : List (Option (Clique n q))) (PA PF PC : Finset (Clique n q))
    (hv : WeightedGreedy.valid (resources n q) (A ∪ X ∪ F)ᶜ h)
    (hA : packs PA A) (hF : packs PF F)
    (hcover : packs PC (WeightedGreedy.remaining (resources n q) (A ∪ X ∪ F)ᶜ h ∪ Y))
    (hK : Divisible q (univ : Finset (Edge n))) : Divisible q (X \ Y) := by
  let J := (A ∪ X ∪ F)ᶜ
  have hJ : Disjoint J (A ∪ X ∪ F) := disjoint_compl_left
  have hJX : Disjoint J X := hJ.mono_right
    ((subset_union_right : X ⊆ A ∪ X).trans subset_union_left)
  have hJA : Disjoint J A := hJ.mono_right
    ((subset_union_left : A ⊆ A ∪ X).trans subset_union_left)
  have hJF : Disjoint J F := hJ.mono_right subset_union_right
  have hP := prefix_cover_packs hq J Y h PC hv hcover (hJX.mono_right hY)
  have hJA' : Disjoint (J ∪ Y) A := disjoint_union_left.mpr
    ⟨hJA, hAX.symm.mono_left hY⟩
  have hJF' : Disjoint (J ∪ Y ∪ A) F := disjoint_union_left.mpr
    ⟨disjoint_union_left.mpr ⟨hJF, hXF.mono_left hY⟩, hAF⟩
  have hdiv := divisible_union hJF'
    (divisible_union hJA' (divisible_of_packs hP) (divisible_of_packs hA))
    (divisible_of_packs hF)
  have he : (univ : Finset (Edge n)) \ (J ∪ Y ∪ A ∪ F) = X \ Y := by
    ext e
    simp only [J, mem_sdiff, mem_univ, true_and, mem_union, mem_compl]
    have ha (hx : e ∈ X) : e ∉ A := fun ea => disjoint_left.mp hAX ea hx
    have hf (hx : e ∈ X) : e ∉ F := fun ef => disjoint_left.mp hXF hx ef
    tauto
  rw [← he]
  exact divisible_sdiff (subset_univ _) hK hdiv

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.divisible_of_packs
#print axioms KqR75.PhysicalCompletion.divisible_sdiff
#print axioms KqR75.PhysicalCompletion.divisible_after_cover
