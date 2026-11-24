module
public import CoverGuards
public import CoverIteration
public import CoverSteps

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Finset
variable {V : Type*} [DecidableEq V]

/-- Assemble the two phases from a star selector and a rooted-pair selector.
The output covers the whole leave, uses at most one clique's worth of
reserve edges per leave edge, and records a reserve edge in each block. -/
theorem cover_two_phases (R : V → V → Prop) [DecidableRel R] [Std.Symm R]
    (S : Finset V) (L : Finset (Finset V)) (q dL dY dP : ℕ) (hq : 3 ≤ q)
    (hd : Disjoint L (reserveEdges R S)) (hcap : dY + (q - 2) * dL ≤ dP)
    (chooseStar : ∀ J Y : Finset (Finset V),
      J ⊆ L → Y ⊆ reserveEdges R S → Y.card ≤ q.choose 2 * (L.card - J.card) →
      (∀ v, degree Y v ≤ dY) → ∀ u, dL < degree J u →
      ∃ C : Finset V, C ⊆ S ∧ (C : Set V).Pairwise R ∧ u ∉ C ∧ C.card = q - 1 ∧
        (∀ w ∈ C, ({u, w} : Finset V) ∈ J ∧ degree Y w + (q - 2) ≤ dY) ∧
        Disjoint (C.powersetCard 2) Y)
    (choosePair : ∀ J Y : Finset (Finset V),
      J ⊆ L → Y ⊆ reserveEdges R S → Y.card ≤ q.choose 2 * (L.card - J.card) →
      (∀ v, potential q J Y v ≤ dP) → ∀ e ∈ J,
      ∃ C : Finset V, C.card = q ∧ e ∈ C.powersetCard 2 ∧
        (C.powersetCard 2).erase e ⊆ reserveEdges R S \ Y ∧
        (C.powersetCard 2 ∩ reserveEdges R S).Nonempty ∧
        ∀ w ∈ C, w ∉ e → potential q J Y w + (q - 1) ≤ dP) :
    ∃ P Y : Finset (Finset V), Cover q L (reserveEdges R S) P ∅ Y ∧
      Y.card ≤ q.choose 2 * L.card := by
  classical
  let X := reserveEdges R S
  let done₁ := fun J : Finset (Finset V) => ∀ v, degree J v ≤ dL
  let guard₁ := fun (_ : Finset (Finset V)) (Y : Finset (Finset V)) => ∀ v, degree Y v ≤ dY
  have starStep (J Y : Finset (Finset V)) (hJ : J ⊆ L) (hY : Y ⊆ X)
      (hg : guard₁ J Y)
      (hb : Y.card ≤ q.choose 2 * (L.card - J.card)) (hn : ¬ done₁ J) :
      ∃ C : Finset V, C.card = q ∧ C.powersetCard 2 ⊆ J ∪ (X \ Y) ∧
        (C.powersetCard 2 ∩ X).Nonempty ∧ (J ∩ C.powersetCard 2).Nonempty ∧
        let out := take J Y (C.powersetCard 2)
        guard₁ out.1 out.2 := by
    obtain ⟨u, hu⟩ := not_forall.mp hn
    obtain ⟨C, hs, hc, hout, hcard, hlinks, hclean⟩ :=
      chooseStar J Y hJ hY hb hg u (lt_of_not_ge hu)
    have hc₂ : 2 ≤ C.card := by omega
    have hstar : star u C ⊆ J := by
      intro e he
      obtain ⟨w, hw, rfl⟩ := mem_image.mp he
      exact (hlinks w hw).1
    have hinsideX : C.powersetCard 2 ⊆ X := by
      intro e he
      obtain ⟨hsub, hec⟩ := mem_powersetCard.mp he
      exact mem_filter.mpr
        ⟨mem_powersetCard.mpr ⟨hsub.trans hs, hec⟩, hc.mono hsub⟩
    have hinside : Disjoint (C.powersetCard 2) J := hd.symm.mono hinsideX hJ
    obtain ⟨hnew, hX, hrem⟩ :=
      star_extension R S C u J Y hs hc hout hc₂ (fun w hw => (hlinks w hw).1) hclean
    refine ⟨insert u C, by rw [card_insert_of_notMem hout, hcard]; omega, hnew, hX, hrem, ?_⟩
    change ∀ w : V, degree (take J Y ((insert u C).powersetCard 2)).2 w ≤ dY
    intro w
    rw [(star_step u C hout hstar hinside hclean.symm).2.2 w]
    by_cases hw : w ∈ C
    · rw [ite_eq_left hw, hcard, show q - 1 - 1 = q - 2 by omega]
      exact (hlinks w hw).2
    · simpa only [ite_eq_right hw, Nat.add_zero] using hg w
  have h0 : guard₁ L ∅ := by simp [guard₁, degree]
  obtain ⟨P, J, Y, _, hcover, hdone, hdeg, hy⟩ :=
    run_phase hd done₁ guard₁ (cover_empty q L X) h0 (by simp) starStep

  let done₂ := fun J : Finset (Finset V) => J = ∅
  let guard₂ := fun (J Y : Finset (Finset V)) => ∀ v, potential q J Y v ≤ dP
  have hguard₂ : guard₂ J Y := by
    intro v
    exact (Nat.add_le_add (hdeg v) (Nat.mul_le_mul_left _ (hdone v))).trans hcap
  have pairStep (J' Y' : Finset (Finset V)) (hJ : J' ⊆ L) (hY : Y' ⊆ X)
      (hg : guard₂ J' Y')
      (hb : Y'.card ≤ q.choose 2 * (L.card - J'.card)) (hn : ¬ done₂ J') :
      ∃ C : Finset V, C.card = q ∧ C.powersetCard 2 ⊆ J' ∪ (X \ Y') ∧
        (C.powersetCard 2 ∩ X).Nonempty ∧ (J' ∩ C.powersetCard 2).Nonempty ∧
        let out := take J' Y' (C.powersetCard 2)
        guard₂ out.1 out.2 := by
    obtain ⟨e, he⟩ := nonempty_iff_ne_empty.mpr hn
    obtain ⟨C, hqC, heC, hfresh, hX, haux⟩ := choosePair J' Y' hJ hY hb hg e he
    have hfX : (C.powersetCard 2).erase e ⊆ X := hfresh.trans sdiff_subset
    have hother : Disjoint ((C.powersetCard 2).erase e) J' := hd.symm.mono hfX hJ
    have hYother : Disjoint Y' ((C.powersetCard 2).erase e) :=
      disjoint_left.mpr (fun f hfy hf => (mem_sdiff.mp (hfresh hf)).2 hfy)
    have hsub : C.powersetCard 2 ⊆ J' ∪ (X \ Y') := by
      intro f hf
      by_cases hfe : f = e
      · exact mem_union_left _ (hfe.symm ▸ he)
      · exact mem_union_right _ (hfresh (mem_erase.mpr ⟨hfe, hf⟩))
    refine ⟨C, hqC, hsub, hX, ⟨e, mem_inter.mpr ⟨he, heC⟩⟩, ?_⟩
    change ∀ w : V, potential q (take J' Y' (C.powersetCard 2)).1
      (take J' Y' (C.powersetCard 2)).2 w ≤ dP
    intro w
    have hpot := pair_step_potential C e heC he hother hYother w
    simp only [hqC] at hpot
    unfold potential
    rw [hpot]
    by_cases hw : w ∈ C ∧ w ∉ e
    · rw [ite_eq_left hw]
      exact haux w hw.1 hw.2
    · simpa only [ite_eq_right hw, Nat.add_zero, potential] using hg w
  obtain ⟨P', J', Y', _, hcover', he, _, hy'⟩ :=
    run_phase hd done₂ guard₂ hcover hguard₂ hy pairStep
  change J' = ∅ at he
  subst J'
  exact ⟨P', Y', hcover', by simpa using hy'⟩

end KqR75.CoverDown

#print axioms KqR75.CoverDown.cover_two_phases
