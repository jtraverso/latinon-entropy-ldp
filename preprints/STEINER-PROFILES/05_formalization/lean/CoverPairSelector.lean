module
public import CoverAssembly

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Finset ReserveCuts

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A phase-two selector with separate budgets for forbidden auxiliary
vertices and for used internal edges. At q = 3 no internal pair can occur. -/
theorem select_pair (R : V → V → Prop) [DecidableRel R] [Std.Symm R]
    (hirr : ∀ v, ¬ R v v) (p : ℝ) (hp : 0 ≤ p)
    (q cap zmax B M : ℕ) (hq : 3 ≤ q) (hcap : q - 1 ≤ cap)
    (hcommon : ∀ H : Finset V, H.card < q →
      ((common R univ H).card : ℝ) ≤ 2 * (Fintype.card V : ℝ) * p ^ H.card)
    (hZ : 2 * (B + (q - 2) * M) ≤ zmax * (cap - (q - 1) + 1))
    (hcount : ∀ u v : V, u ≠ v →
      ((zmax + 2 * cap : ℕ) : ℝ) *
          ((2 * (Fintype.card V : ℝ)) ^ (q - 3) * p ^ (3 * (q - 3) + (q - 3).choose 2)) +
        (B : ℝ) * (if 4 ≤ q then
          (2 * (Fintype.card V : ℝ)) ^ (q - 4) * p ^ (4 * (q - 4) + (q - 4).choose 2)
          else 0) <
        (rootedExtensions R univ u v (q - 2)).card)
    (J Y : Finset (Finset V)) (hY : ∀ e ∈ Y, e.card = 2)
    (hJ : ∀ e ∈ J, e.card = 2) (hJcard : J.card ≤ M) (hYcard : Y.card ≤ B)
    (hP : ∀ w, potential q J Y w ≤ cap) (e : Finset V) (he : e ∈ J) :
    ∃ D : Finset V, D.card = q ∧ e ∈ D.powersetCard 2 ∧
      (D.powersetCard 2).erase e ⊆ reserveEdges R univ \ Y ∧
      (D.powersetCard 2 ∩ reserveEdges R univ).Nonempty ∧
      ∀ w ∈ D, w ∉ e → potential q J Y w + (q - 1) ≤ cap := by
  classical
  obtain ⟨u, v, huv, rfl⟩ := card_eq_two.mp (hJ e he)
  let H : Finset V := {u, v}
  let k := q - 2
  let Z₀ := saturated (potential q J Y) cap (q - 1)
  let Z := (Z₀ ∪ adjacentVertices Y u) ∪ adjacentVertices Y v
  let bv : ℝ := (2 * (Fintype.card V : ℝ)) ^ (q - 3) * p ^ (3 * (q - 3) + (q - 3).choose 2)
  let be : ℝ := if 4 ≤ q then
    (2 * (Fintype.card V : ℝ)) ^ (q - 4) * p ^ (4 * (q - 4) + (q - 4).choose 2) else 0
  have hh : H.card = 2 := card_eq_two.mpr ⟨u, v, huv, rfl⟩
  have hk : H.card + k ≤ q := by dsimp [k]; omega
  have hbv : 0 ≤ bv := by dsimp [bv]; positivity
  have hbe : 0 ≤ be := by dsimp [be]; split <;> positivity
  have hZ₀ : Z₀.card ≤ zmax := by
    have h := saturated_card (potential q J Y) cap (q - 1) hcap
    rw [sum_potential q J Y hJ hY] at h
    have hsum : Y.card + (q - 2) * J.card ≤ B + (q - 2) * M :=
      Nat.add_le_add hYcard (Nat.mul_le_mul_left _ hJcard)
    exact Nat.le_of_mul_le_mul_right
      (h.trans ((Nat.mul_le_mul_left 2 hsum).trans hZ)) (by omega)
  have hZcard : Z.card ≤ zmax + 2 * cap :=
    (pair_forbidden_card q J Y cap (q - 1) u v hY hP).trans (Nat.add_le_add_right hZ₀ _)
  have hfib (A : Finset V) :
      (((extensions R univ H k).filter (A ⊆ ·)).card : ℝ) ≤
        (2 * (Fintype.card V : ℝ)) ^ (k - A.card) *
          p ^ ((H.card + A.card) * (k - A.card) + (k - A.card).choose 2) := by
    simpa only [card_univ] using extension_fibre_density R hirr univ p hp q
      (fun H _ h => by simpa only [card_univ] using hcommon H h)
      H A k (subset_univ _) hk
  have hvb (w : V) (_ : w ∈ Z) :
      (((extensions R univ H k).filter (fun C => w ∈ C)).card : ℝ) ≤ bv := by
    have hs := hfib {w}
    have hF : (extensions R univ H k).filter (fun C => w ∈ C) =
        (extensions R univ H k).filter ({w} ⊆ ·) := by
      exact filter_congr (fun _ _ => singleton_subset_iff.symm)
    rw [hF]
    rw [hh, card_singleton, show 2 + 1 = 3 by decide, show k - 1 = q - 3 by dsimp [k]; omega] at hs
    exact hs
  have heb (f : Finset V) (hf : f ∈ Y) :
      (((extensions R univ H k).filter (f ⊆ ·)).card : ℝ) ≤ be := by
    have hf₂ := hY f hf
    by_cases hq4 : 4 ≤ q
    · dsimp [be]
      rw [ite_eq_left hq4]
      have h := hfib f
      rw [hf₂, hh, show 2 + 2 = 4 by decide, show k - 2 = q - 4 by dsimp [k]; omega] at h
      exact h
    · have hF : (extensions R univ H k).filter (f ⊆ ·) = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro A hA hfa
        have hc : A.card = k := by
          rw [extensions, cliquesIn, mem_filter, mem_powersetCard] at hA
          exact hA.1.2
        have hs := card_le_card hfa
        dsimp [k] at hc
        omega
      rw [hF, card_empty, Nat.cast_zero]
      exact hbe
  have hext : extensions R univ H k = rootedExtensions R univ u v (q - 2) := by
    rw [extensions, rootedExtensions, show common R univ H = commonPair R univ u v
      from common_pair_eq R univ u v]
  have hroom : (Z.card : ℝ) * bv + (Y.card : ℝ) * be < (extensions R univ H k).card := by
    rw [hext]
    exact (add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast hZcard) hbv)
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hYcard) hbe)).trans_lt (hcount u v huv)
  obtain ⟨C, hC, hcleanZ, hcleanY⟩ :=
    exists_clean_extension_of_bounds R univ H Z Y k bv be hbv hbe hvb heb hroom
  rw [hext] at hC
  obtain ⟨hcard, hpw, hlinks⟩ := (mem_rootedExtensions R univ u v (q - 2) C).mp hC
  have huC : u ∉ C := fun hu' => hirr u (hlinks u hu').2.1
  have hvC : v ∉ C := fun hv' => hirr v (hlinks v hv').2.2
  have hlinksClean (w : V) (hw : w ∈ C) :
      ({u, w} : Finset V) ∉ Y ∧ ({v, w} : Finset V) ∉ Y := by
    have hz : w ∉ Z := fun hz => disjoint_left.mp hcleanZ hw hz
    constructor
    · intro h
      have hwN : w ∈ adjacentVertices Y u :=
        mem_filter.mpr ⟨mem_erase.mpr ⟨fun hwu => huC (hwu ▸ hw), mem_univ _⟩, h⟩
      exact hz (mem_union_left _ (mem_union_right _ hwN))
    · intro h
      have hwN : w ∈ adjacentVertices Y v :=
        mem_filter.mpr ⟨mem_erase.mpr ⟨fun hwv => hvC (hwv ▸ hw), mem_univ _⟩, h⟩
      exact hz (mem_union_right _ hwN)
  have hpos : 0 < C.card := by omega
  obtain ⟨hem, hnew, hres⟩ := pair_extension R univ C u v Y (subset_univ _) hpw
    (mem_univ _) (mem_univ _) huv huC hvC hpos (fun w hw => (hlinks w hw).2) hcleanY hlinksClean
  refine ⟨insert u (insert v C), ?_, hem, hnew, hres, ?_⟩
  · rw [card_insert_of_notMem (show u ∉ insert v C from fun h => (mem_insert.mp h).elim huv huC),
      card_insert_of_notMem hvC, hcard]
    omega
  · intro w hw hwe
    have hwC : w ∈ C := by
      have hwv := (mem_insert.mp hw).resolve_left (fun hh => hwe (by simp [hh]))
      exact (mem_insert.mp hwv).resolve_left (fun hh => hwe (by simp [hh]))
    apply le_of_not_gt
    intro h
    have hwZ : w ∈ Z₀ := mem_filter.mpr ⟨mem_univ _, h⟩
    exact disjoint_left.mp hcleanZ hwC (mem_union_left _ (mem_union_left _ hwZ))

end KqR75.CoverDown

#print axioms KqR75.CoverDown.select_pair
