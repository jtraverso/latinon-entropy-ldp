module
public import CoverAssembly

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Finset ReserveCuts

variable {V : Type*} [DecidableEq V]

private theorem extension_spec (R : V → V → Prop) [DecidableRel R]
    (S H : Finset V) (k : ℕ) (C : Finset V) :
    C ∈ extensions R S H k ↔
      C ⊆ common R S H ∧ C.card = k ∧ (C : Set V).Pairwise R := by
  rw [extensions, cliquesIn, mem_filter, mem_powersetCard, and_assoc]

private theorem restrict_extensions (R : V → V → Prop) [DecidableRel R]
    {S T : Finset V} (h : S ⊆ T) (H : Finset V) (k : ℕ) :
    extensions R S H k ⊆ extensions R T H k := by
  intro C hC
  obtain ⟨hsub, hcard, hclique⟩ := (extension_spec R S H k C).mp hC
  refine (extension_spec R T H k C).mpr ⟨fun w hw => ?_, hcard, hclique⟩
  obtain ⟨hs, hR⟩ := mem_filter.mp (hsub hw)
  exact mem_filter.mpr ⟨h hs, hR⟩

variable [Fintype V]

/-- A phase-one selector derived from the finite clique lower bound and the
common-neighbour upper bound. The numerical hypotheses bound excluded vertices
and the total incidence of used edges with candidate cliques. -/
theorem select_star (R : V → V → Prop) [DecidableRel R] (hirr : ∀ v, ¬ R v v)
    (p : ℝ) (hp : 0 ≤ p) (q dL dY m zmax B : ℕ) (hq : 3 ≤ q) (hcap : q - 2 ≤ dY)
    (hcommon : ∀ H : Finset V, H.card < q →
      ((common R univ H).card : ℝ) ≤ 2 * (Fintype.card V : ℝ) * p ^ H.card)
    (hZ : 2 * B ≤ zmax * (dY - (q - 2) + 1))
    (hm : m + zmax ≤ dL + 1)
    (hcount : ∀ S : Finset V, m ≤ S.card →
      (B : ℝ) * ((2 * (Fintype.card V : ℝ)) ^ (q - 3) *
        p ^ (2 * (q - 3) + (q - 3).choose 2)) < (cliquesIn R S (q - 1)).card)
    (J Y : Finset (Finset V)) (hJ : ∀ e ∈ J, e.card = 2) (hY : ∀ e ∈ Y, e.card = 2)
    (hYcard : Y.card ≤ B) (u : V) (hu : dL < degree J u) :
    ∃ C : Finset V, (C : Set V).Pairwise R ∧ u ∉ C ∧ C.card = q - 1 ∧
      (∀ w ∈ C, ({u, w} : Finset V) ∈ J ∧ degree Y w + (q - 2) ≤ dY) ∧
      Disjoint (C.powersetCard 2) Y := by
  classical
  let Z := saturated (degree Y) dY (q - 2)
  let S := adjacentVertices J u \ Z
  let eBound := (2 * (Fintype.card V : ℝ)) ^ (q - 3) * p ^ (2 * (q - 3) + (q - 3).choose 2)
  have heBound : 0 ≤ eBound := by dsimp [eBound]; positivity
  have hZcard : Z.card ≤ zmax := by
    have h := saturated_card (degree Y) dY (q - 2) hcap
    rw [sum_degrees Y hY] at h
    exact Nat.le_of_mul_le_mul_right
      (h.trans ((Nat.mul_le_mul_left 2 hYcard).trans hZ)) (by omega)
  have hS : m ≤ S.card := by
    have h := star_candidates_card J Y u dY (q - 2) hJ
    change degree J u ≤ S.card + Z.card at h
    omega
  have hroots : common R S ∅ = S := by
    ext v
    simp [common]
  have hE : extensions R S ∅ (q - 1) = cliquesIn R S (q - 1) := by
    rw [extensions, hroots]
  have hfib (e : Finset V) (he : e ∈ Y) :
      (((extensions R S ∅ (q - 1)).filter (e ⊆ ·)).card : ℝ) ≤ eBound := by
    have hf : (extensions R S ∅ (q - 1)).filter (e ⊆ ·) ⊆
        (extensions R univ ∅ (q - 1)).filter (e ⊆ ·) := by
      intro C hC
      obtain ⟨hc, hec⟩ := mem_filter.mp hC
      exact mem_filter.mpr ⟨restrict_extensions R (subset_univ _) ∅ _ hc, hec⟩
    have hc : (((extensions R S ∅ (q - 1)).filter (e ⊆ ·)).card : ℝ) ≤
        (((extensions R univ ∅ (q - 1)).filter (e ⊆ ·)).card : ℝ) := by
      exact_mod_cast card_le_card hf
    refine hc.trans ?_
    have h := extension_fibre_density R hirr univ p hp q (fun H _ hh => by
      simpa only [card_univ] using hcommon H hh) ∅ e (q - 1) (empty_subset _) (by simp)
    rw [hY e he, card_empty, card_univ, zero_add, show q - 1 - 2 = q - 3 by omega] at h
    exact h
  have hroom : ((∅ : Finset V).card : ℝ) * 0 + (Y.card : ℝ) * eBound <
      (extensions R S ∅ (q - 1)).card := by
    rw [hE]
    simp only [card_empty, Nat.cast_zero, zero_mul, zero_add]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hYcard) heBound).trans_lt (hcount S hS)
  obtain ⟨C, hC, _, hclean⟩ :=
    exists_clean_extension_of_bounds R S ∅ ∅ Y (q - 1) 0 eBound (by norm_num) heBound
      (by simp) hfib hroom
  obtain ⟨hsub, hcard, hpw⟩ := (extension_spec R S ∅ (q - 1) C).mp hC
  rw [hroots] at hsub
  refine ⟨C, hpw, fun huC => ?_, hcard, ?_, hclean⟩
  · have h := (mem_sdiff.mp (hsub huC)).1
    exact (mem_erase.mp (mem_filter.mp h).1).1 rfl
  · intro w hw
    obtain ⟨hN, hsat⟩ := mem_sdiff.mp (hsub hw)
    refine ⟨(mem_filter.mp hN).2, le_of_not_gt ?_⟩
    intro h
    exact hsat (mem_filter.mpr ⟨mem_univ _, h⟩)

end KqR75.CoverDown

#print axioms KqR75.CoverDown.select_star
