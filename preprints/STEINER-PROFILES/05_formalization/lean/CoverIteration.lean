module
public import CoverPacking

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Finset
variable {V : Type*} [DecidableEq V]

/-- Iterating one phase preserves a physical packing and charges at most
one clique's worth of reserve edges per removed leave edge. -/
theorem run_phase {q : ℕ} {L X P R Y : Finset (Finset V)}
    (hd : Disjoint L X) (done : Finset (Finset V) → Prop)
    (guard : Finset (Finset V) → Finset (Finset V) → Prop)
    (hP : Cover q L X P R Y) (hg : guard R Y)
    (hY : Y.card ≤ q.choose 2 * (L.card - R.card))
    (select : ∀ R' Y' : Finset (Finset V),
      R' ⊆ L → Y' ⊆ X → guard R' Y' →
      Y'.card ≤ q.choose 2 * (L.card - R'.card) → ¬ done R' →
      ∃ C : Finset V, C.card = q ∧ C.powersetCard 2 ⊆ R' ∪ (X \ Y') ∧
        (C.powersetCard 2 ∩ X).Nonempty ∧ (R' ∩ C.powersetCard 2).Nonempty ∧
        let out := take R' Y' (C.powersetCard 2)
        guard out.1 out.2) :
    ∃ P' R' Y', P ⊆ P' ∧ Cover q L X P' R' Y' ∧ done R' ∧ guard R' Y' ∧
      Y'.card ≤ q.choose 2 * (L.card - R'.card) := by
  classical
  generalize hm : R.card = m
  induction m using Nat.strong_induction_on generalizing P R Y with
  | h m ih =>
    by_cases hdone : done R
    · exact ⟨P, R, Y, Subset.rfl, hP, hdone, hg, hY⟩
    · obtain ⟨C, hq, hnew, huses, hrem, hguard⟩ :=
        select R Y hP.leave_sub hP.used_sub hg hY hdone
      let B := C.powersetCard 2
      let out := take R Y B
      have hnext : Cover q L X (insert C P) out.1 out.2 :=
        cover_insert hP hd C hq hnew huses
      obtain ⟨e, he⟩ := hrem
      obtain ⟨heR, heB⟩ := mem_inter.mp he
      have hlt : out.1.card < R.card := by
        apply card_lt_card
        exact (ssubset_iff_of_subset sdiff_subset).mpr
          ⟨e, heR, fun he => (mem_sdiff.mp he).2 heB⟩
      have hB : B.card = q.choose 2 := by rw [card_powersetCard, hq]
      have hy : out.2.card ≤ Y.card + q.choose 2 := by
        change (Y ∪ (B \ R)).card ≤ _
        rw [← hB]
        exact (card_union_le _ _).trans (Nat.add_le_add_left (card_le_card sdiff_subset) _)
      have hstep : (L.card - R.card) + 1 ≤ L.card - out.1.card := by
        have hR := card_le_card hP.leave_sub
        omega
      have hbudget : out.2.card ≤ q.choose 2 * (L.card - out.1.card) := by
        calc
          _ ≤ _ := hy
          _ ≤ q.choose 2 * (L.card - R.card) + q.choose 2 := Nat.add_le_add_right hY _
          _ = q.choose 2 * ((L.card - R.card) + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ _ := Nat.mul_le_mul_left _ hstep
      obtain ⟨P', R', Y', hsub, hfinal, hdone', hg', hb'⟩ :=
        ih out.1.card (hlt.trans_le (le_of_eq hm)) hnext hguard hbudget rfl
      exact ⟨P', R', Y', (subset_insert C P).trans hsub, hfinal, hdone', hg', hb'⟩

end KqR75.CoverDown

#print axioms KqR75.CoverDown.run_phase
