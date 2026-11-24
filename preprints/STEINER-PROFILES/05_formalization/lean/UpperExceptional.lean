module
public import CompletionBudget

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset ColouredCliques CompleteJohnson SparseGram CliqueGram PhysicalCompletion

/-- Candidates through the test edge which meet a true block in at
least three vertices. -/
def overlapCandidates {n q : ℕ} (e : Edge n) (b : Clique n q) : Finset (Clique n q) :=
  univ.filter fun c => e ∈ resources n q c ∧ 3 ≤ (b.val ∩ c.val).card

def exceptional {n q : ℕ} (P : Finset (Clique n q)) (e : Edge n) : Finset (Clique n q) :=
  P.biUnion (overlapCandidates e)

private def through {n q : ℕ} (S : Finset (Fin n)) : Finset (Clique n q) :=
  univ.filter fun c => S ⊆ c.val

private theorem through_card {n q : ℕ} (S : Finset (Fin n)) (h : S.card ≤ q) :
    (through (q := q) S).card = (n - S.card).choose (q - S.card) := by
  have he : (through (q := q) S).card =
      (((univ : Finset (Fin n)).powersetCard q).filter (S ⊆ ·)).card := by
    apply card_bij (fun c _ => c.val)
    · intro c hc
      exact mem_filter.mpr ⟨c.property, (mem_filter.mp hc).2⟩
    · intro c _ d _ he
      exact Subtype.ext he
    · intro c hc
      exact ⟨⟨c, (mem_filter.mp hc).1⟩,
        mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hc).2⟩, rfl⟩
  rw [he, card_filter_powersetCard_subset _ _ _ (subset_univ _) h, card_univ, Fintype.card_fin]

private theorem through_card_le {n q : ℕ} (S : Finset (Fin n)) (k : ℕ)
    (hS : k ≤ S.card) (hn : 0 < n) :
    (through (q := q) S).card ≤ if k ≤ q then n ^ (q - k) else 0 := by
  by_cases h : S.card ≤ q
  · rw [ite_eq_left (hS.trans h), through_card S h]
    calc
      _ ≤ (n - S.card) ^ (q - S.card) := Nat.choose_le_pow _ _
      _ ≤ n ^ (q - S.card) := Nat.pow_le_pow_left (Nat.sub_le _ _) _
      _ ≤ _ := Nat.pow_le_pow_right hn (Nat.sub_le_sub_left hS _)
  · have he : through (q := q) S = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro c hc
      exact h ((card_le_card (mem_filter.mp hc).2).trans_eq (mem_powersetCard.mp c.property).2)
    simp [he]

/-- A test edge and a triple in a true block force at least five minus
the number of test endpoints in that block. -/
theorem overlapCandidates_card_le {n q : ℕ} (e : Edge n) (b : Clique n q) (j : ℕ)
    (hj : (e.val ∩ b.val).card ≤ j) :
    (overlapCandidates e b).card ≤ (q.choose 3) *
      (if 5 - j ≤ q then n ^ (q - (5 - j)) else 0) := by
  let T := b.val.powersetCard 3
  have hsub : overlapCandidates e b ⊆ T.biUnion (fun S => through (q := q) (e.val ∪ S)) := by
    intro c hc
    obtain ⟨he, hbc⟩ := (mem_filter.mp hc).2
    obtain ⟨S, hS, hScard⟩ := exists_subset_card_eq hbc
    have hb : S ⊆ b.val := hS.trans inter_subset_left
    have hc' : S ⊆ c.val := hS.trans inter_subset_right
    exact mem_biUnion.mpr ⟨S, mem_powersetCard.mpr ⟨hb, hScard⟩,
      mem_filter.mpr ⟨mem_univ _, union_subset (mem_filter.mp he).2 hc'⟩⟩
  have hcard (S : Finset (Fin n)) (hS : S ∈ T) :
      (through (q := q) (e.val ∪ S)).card ≤
        (if 5 - j ≤ q then n ^ (q - (5 - j)) else 0) := by
    obtain ⟨hSb, hScard⟩ := mem_powersetCard.mp hS
    have hinter : (e.val ∩ S).card ≤ j := (card_le_card (inter_subset_inter_left hSb)).trans hj
    have he := (mem_powersetCard.mp e.property).2
    have h := card_union_add_card_inter e.val S
    refine through_card_le _ _ (by omega) ?_
    have hc : e.val.card ≤ n := by simpa using card_le_univ e.val
    omega
  calc
    _ ≤ (T.biUnion (fun S => through (q := q) (e.val ∪ S))).card := card_le_card hsub
    _ ≤ ∑ S ∈ T, (through (q := q) (e.val ∪ S)).card := card_biUnion_le
    _ ≤ ∑ _S ∈ T, (if 5 - j ≤ q then n ^ (q - (5 - j)) else 0) := sum_le_sum hcard
    _ = _ := by simp [T, card_powersetCard, (mem_powersetCard.mp b.property).2]

private theorem pack_limit {n q : ℕ} {P : Finset (Clique n q)} (hP : packs P univ)
    (e : Edge n) : (P.filter fun b => e ∈ resources n q b).card ≤ 1 := by
  change PhysicalBank.edgeMultiplicity P e ≤ 1
  rw [hP e]
  simp

private theorem incident_blocks_le {n q : ℕ} (hq : 2 ≤ q) {P : Finset (Clique n q)}
    (hP : packs P univ) (v : Fin n) :
    (P.filter fun b => v ∈ b.val).card ≤ n := by
  let star : Finset (Edge n) := univ.filter fun e => v ∈ e.val
  have hstar := incidence_column_sum v
  change (∑ e : Edge n, if v ∈ e.val then (1 : ℝ) else 0) =
    ((Fintype.card (Fin n) - 1 : ℕ) : ℝ) at hstar
  rw [sum_boole] at hstar
  simp only [Fintype.card_fin] at hstar
  have hcard : star.card = n - 1 := by exact_mod_cast hstar
  refine le_trans ?_ (hcard.le.trans (Nat.sub_le _ _))
  apply BankCapacity.block_card_of_marking
  · intro e
    refine (card_le_card ?_).trans (pack_limit hP e)
    exact fun b hb => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hb).1).1, (mem_filter.mp hb).2⟩
  · intro b hb
    have hv := (mem_filter.mp hb).2
    have hc := (mem_powersetCard.mp b.property).2
    have hne : (b.val.erase v).Nonempty := by
      apply card_pos.mp
      rw [card_erase_of_mem hv, hc]
      omega
    obtain ⟨u, hu⟩ := hne
    have huv := (mem_erase.mp hu).1
    let e := PhysicalReserve.pairEdge u v huv
    refine ⟨e, mem_inter.mpr ⟨?_, ?_⟩⟩
    · apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      change ({u, v} : Finset (Fin n)) ⊆ b.val
      exact insert_subset (mem_of_mem_erase hu) (singleton_subset_iff.mpr hv)
    · change e ∈ univ.filter (fun a : Edge n => v ∈ a.val)
      exact mem_filter.mpr ⟨mem_univ _, by simp [e, PhysicalReserve.pairEdge]⟩

theorem blocks_le_square {n q : ℕ} (hq : 2 ≤ q) {P : Finset (Clique n q)}
    (hP : packs P univ) : P.card ≤ n ^ 2 := by
  have h := BankCapacity.block_card_of_marking P univ (pack_limit hP) (fun b _ => by
    rw [inter_univ]
    apply card_pos.mp
    rw [resources_card]
    exact Nat.choose_pos hq)
  have hcard : Fintype.card (Edge n) = n.choose 2 := by
    rw [Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]
  simpa only [card_univ, hcard] using h.trans (by simpa only [card_univ, hcard] using Nat.choose_le_pow n 2)

/-- At most four times the number of triples of one block, times
n^(q-3), candidates through an edge share three vertices with a true
block. The estimates also apply when q is three or four. -/
theorem exceptional_card_le {n q : ℕ} (hq : 3 ≤ q) (P : Finset (Clique n q))
    (hP : packs P univ) (e : Edge n) :
    (exceptional P e).card ≤ 4 * (q.choose 3) * n ^ (q - 3) := by
  let N (j : ℕ) := P.filter fun b => (e.val ∩ b.val).card = j
  let f := overlapCandidates (q := q) e
  have he := (mem_powersetCard.mp e.property).2
  have hP₂ : (N 2).card ≤ 1 := by
    refine (card_le_card ?_).trans (pack_limit hP e)
    intro b hb
    obtain ⟨hbP, h₂⟩ := mem_filter.mp hb
    have hEq : e.val ∩ b.val = e.val :=
      eq_of_subset_of_card_le inter_subset_left (by omega)
    exact mem_filter.mpr ⟨hbP, mem_filter.mpr
      ⟨mem_univ _, fun v hv => (mem_inter.mp (hEq.symm ▸ hv)).2⟩⟩
  have hP₁ : (N 1).card ≤ 2 * n := by
    let family (v : Fin n) := P.filter fun b => v ∈ b.val
    have hsub : N 1 ⊆ e.val.biUnion family := by
      intro b hb
      obtain ⟨hbP, h₁⟩ := mem_filter.mp hb
      obtain ⟨v, hv⟩ := card_pos.mp (by omega : 0 < (e.val ∩ b.val).card)
      exact mem_biUnion.mpr ⟨v, (mem_inter.mp hv).1, mem_filter.mpr ⟨hbP, (mem_inter.mp hv).2⟩⟩
    exact (card_le_card hsub).trans (by
      simpa only [he] using card_biUnion_le_card_mul e.val family n
        (fun v _ => incident_blocks_le (by omega) hP v))
  have hP₀ : (N 0).card ≤ n ^ 2 := (card_filter_le _ _).trans (blocks_le_square (by omega) hP)
  let U := q.choose 3 * n ^ (q - 3)
  have hcount (j c k : ℕ) (hk : k = 5 - j) (hk₀ : 3 ≤ k)
      (hN : (N j).card ≤ c * n ^ (k - 3)) :
      ((N j).biUnion f).card ≤ c * U := by
    have hh := card_biUnion_le_card_mul (N j) f
      (q.choose 3 * (if k ≤ q then n ^ (q - k) else 0))
      (fun b hb => by
        have h := (mem_filter.mp hb).2
        simpa only [hk] using overlapCandidates_card_le e b j h.le)
    by_cases hfit : k ≤ q
    · have hpow : n ^ (k - 3) * n ^ (q - k) = n ^ (q - 3) := by
        rw [← pow_add, show k - 3 + (q - k) = q - 3 by omega]
      refine hh.trans ?_
      rw [ite_eq_left hfit]
      calc
        _ ≤ (c * n ^ (k - 3)) * (q.choose 3 * n ^ (q - k)) :=
          Nat.mul_le_mul_right _ hN
        _ = (c * q.choose 3) * (n ^ (k - 3) * n ^ (q - k)) := by ac_rfl
        _ = _ := by rw [hpow]; simp [U, Nat.mul_assoc]
    · simpa [hfit] using hh.trans (by simp [hfit] : _ ≤ c * U)
  have h₂ := hcount 2 1 3 (by decide) (by decide) (by simpa using hP₂)
  have h₁ := hcount 1 2 4 (by decide) (by decide) (by simpa using hP₁)
  have h₀ := hcount 0 1 5 (by decide) (by decide) (by simpa using hP₀)
  have hsub : exceptional P e ⊆ (N 2).biUnion f ∪ (N 1).biUnion f ∪ (N 0).biUnion f := by
    intro b hb
    obtain ⟨c, hc, hb'⟩ := mem_biUnion.mp hb
    have hle := card_le_card (inter_subset_left : e.val ∩ c.val ⊆ e.val)
    rw [he] at hle
    rcases (show (e.val ∩ c.val).card = 0 ∨ (e.val ∩ c.val).card = 1 ∨
      (e.val ∩ c.val).card = 2 by omega) with hj | hj | hj
    · exact mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨c, mem_filter.mpr ⟨hc, hj⟩, hb'⟩))
    · exact mem_union.mpr (Or.inl (mem_union.mpr
        (Or.inr (mem_biUnion.mpr ⟨c, mem_filter.mpr ⟨hc, hj⟩, hb'⟩))))
    · exact mem_union.mpr (Or.inl (mem_union.mpr
        (Or.inl (mem_biUnion.mpr ⟨c, mem_filter.mpr ⟨hc, hj⟩, hb'⟩))))
  have hcard := (card_le_card hsub).trans (card_union_le _ _)
  have hcard' := card_union_le ((N 2).biUnion f) ((N 1).biUnion f)
  rw [Nat.mul_assoc]
  change (exceptional P e).card ≤ 4 * U
  omega

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.overlapCandidates_card_le
#print axioms KqR75.UpperCounting.exceptional_card_le
