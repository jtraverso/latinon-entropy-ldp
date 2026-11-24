module
public import LowerGeometry
public import RefinedAbsorption.Original2024.Host
public import SparseGram

@[expose] public section
noncomputable section
namespace KqR75.OmniBridge

open Finset CliqueGram CompleteJohnson ColouredCliques CoverDown
open scoped Topology
open RefinedAbsorption RefinedAbsorption.Original2024

theorem vertexSets_isRGraph {n k : ℕ} (E : Finset ↥((univ : Finset (Fin n)).powersetCard k)) :
    IsRGraph k (vertexSets E) :=
  fun _ he => vertexSets_card he

theorem divisible_vertexSets {n q : ℕ} {E : Finset (Edge n)}
    (h : PhysicalCompletion.Divisible q E) : IsDivisible q 2 (vertexSets E) := by
  classical
  intro S hS
  by_cases hzero : S.card = 0
  · have hS₀ := card_eq_zero.mp hzero
    subst S
    simpa [RefinedAbsorption.deg, vertexSets_size] using h.1
  · obtain ⟨v, rfl⟩ := card_eq_one.mp (by omega : S.card = 1)
    simpa [RefinedAbsorption.deg, CoverDown.degree, singleton_subset_iff] using h.2 v

theorem singleton_degree {n : ℕ} (E : Finset (Edge n)) (v : Fin n) :
    (RefinedAbsorption.deg (vertexSets E) {v} : ℝ) = ∑ e : E, incidence 2 e v := by
  classical
  rw [RefinedAbsorption.deg, vertexSets, filter_map, card_map,
    sum_coe_sort E (fun e : Edge n => incidence 2 e v)]
  change ((E.filter (fun e => {v} ⊆ e.val)).card : ℝ) = ∑ e ∈ E, if v ∈ e.val then 1 else 0
  rw [sum_boole]
  simp [singleton_subset_iff]

/-- A physical degree bound supplies the singleton degree hypothesis of
the omni-absorber theorem. -/
theorem max_degree {n : ℕ} (E : Finset (Edge n)) (D : ℝ)
    (h : ∀ v : Fin n, ∑ e : E, incidence 2 e v ≤ D) : MaxDegLE 2 (vertexSets E) D := by
  intro S hS
  obtain ⟨v, rfl⟩ := card_eq_one.mp (by omega : S.card = 1)
  rw [singleton_degree]
  exact h v

theorem min_degree_compl {n : ℕ} (F : Finset (Edge n)) (ε t : ℝ) (hn : 1 ≤ n)
    (ht : 1 + t ≤ ε * n) (h : ∀ v : Fin n, ∑ e : F, incidence 2 e v ≤ t) :
    MinDegGE 2 (vertexSets Fᶜ) ((1 - ε) * n) := by
  intro S hS
  obtain ⟨v, rfl⟩ := card_eq_one.mp (by omega : S.card = 1)
  rw [singleton_degree]
  have hv := h v
  have hsplit := sum_add_sum_compl F (fun e : Edge n => incidence 2 e v)
  rw [← sum_coe_sort F, ← sum_coe_sort Fᶜ] at hsplit
  have htotal : (∑ e : Edge n, incidence 2 e v) = (n : ℝ) - 1 := by
    simpa only [Fintype.card_fin, Nat.cast_sub hn, Nat.cast_one] using incidence_column_sum v
  rw [htotal] at hsplit
  linarith only [hv, hsplit, ht]

/-- The omni-absorber can be chosen in the complement of the bank, and
its disjointness and degree statements are in the physical edge universe. -/
theorem exists_omni (q : ℕ) (hq : 3 ≤ q) :
    ∃ C : ℕ, 1 ≤ C ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ)
      (F X : Finset (Edge n)) (D t : ℝ), 1 ≤ n →
      1 + t ≤ ε * n → X ⊆ Fᶜ → D ≤ n / (C : ℝ) →
      (∀ v : Fin n, ∑ e : F, incidence 2 e v ≤ t) →
      (∀ v : Fin n, ∑ e : X, incidence 2 e v ≤ D) →
      ∃ (A : Finset (Edge n)) (W : Finset (Finset (Fin n)))
        (finish : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
        A ⊆ Fᶜ ∧ Disjoint X A ∧
        (∀ v : Fin n, ∑ e : A, incidence 2 e v ≤ C * max D (budget n 2)) ∧
        IsOmniAbsorberOn q 2 univ (vertexSets X) (vertexSets A) W finish := by
  obtain ⟨C, hC, ε, hε, h⟩ := theorem_1_7_two_le (q := q) (r := 2) (by decide) (by omega)
  refine ⟨C, hC, ε, hε, ?_⟩
  intro n F X D t hn ht hX hD hF hd
  have hsub : vertexSets X ⊆ vertexSets Fᶜ := map_subset_map.mpr hX
  obtain ⟨A, W, finish, hOmni, hA, _, hdeg⟩ :=
    h n (vertexSets Fᶜ) (vertexSets X) D (vertexSets_isRGraph Fᶜ)
      (min_degree_compl F ε t hn ht hF) hsub (max_degree X D hd) hD
  let A' : Finset (Edge n) := physicalSets 2 A
  have he : vertexSets A' = A := vertexSets_physicalSets (fun e he => (hOmni.graphA e he).1)
  rw [← he] at hA hOmni hdeg
  refine ⟨A', W, finish, map_subset_map.mp hA, disjoint_left.mpr ?_, ?_, hOmni⟩
  · intro e hx ha
    exact disjoint_left.mp hOmni.disjoint ((vertexSets_mem X e).mpr hx) ((vertexSets_mem A' e).mpr ha)
  · intro v
    rw [← singleton_degree]
    exact hdeg {v} (by simp)

/-- The absorber's clique decomposition has the physical edge multiplicities
consumed by the bank and the final counting argument. -/
theorem physical_completion {n q : ℕ} {X A : Finset (Edge n)}
    {W : Finset (Finset (Fin n))}
    {finish : Finset (Finset (Fin n)) → Finset (Finset (Fin n))}
    (hO : IsOmniAbsorberOn q 2 univ (vertexSets X) (vertexSets A) W finish)
    {L : Finset (Edge n)} (hL : L ⊆ X) (hdiv : IsDivisible q 2 (vertexSets L)) :
    ∃ P : Finset (Clique n q), ∀ e : Edge n,
      (P.filter (fun b => e ∈ SparseGram.resources n q b)).card =
        if e ∈ A ∪ L then 1 else 0 := by
  classical
  have hdec := hO.decomp (vertexSets L) (map_subset_map.mpr hL) hdiv
  let P : Finset (Clique n q) := physicalSets q (finish (vertexSets L))
  have hp : vertexSets P = finish (vertexSets L) := vertexSets_physicalSets hdec.card_eq
  refine ⟨P, fun e => ?_⟩
  have hm := hdec.mult_eq e.val (mem_powersetCard.mp e.property).2
  rw [← hp] at hm
  have hmult : cliqueMult (vertexSets P) e.val =
      (P.filter (fun b => e ∈ SparseGram.resources n q b)).card := by
    rw [cliqueMult, vertexSets, filter_map, card_map]
    simp [SparseGram.resources]
  rw [hmult] at hm
  rw [← show vertexSets (A ∪ L) = vertexSets A ∪ vertexSets L from map_union _ _] at hm
  simpa only [vertexSets_mem] using hm

open Filter

/-- In the range used by R75 the ambient budget sqrt(n) log n is at most
n^(1−z) for all sufficiently large n. -/
theorem eventually_absorption_budget (z : ℝ) (hz : z < 1 / 2) :
    ∀ᶠ n : ℕ in atTop, budget n 2 ≤ (n : ℝ) ^ (1 - z) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := hnat.eventually ((isLittleO_log_rpow_atTop (show 0 < 1 / 2 - z by linarith)).eventuallyLE)
  filter_upwards [hlog, eventually_ge_atTop (1 : ℕ)] with n hh hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hr : 0 ≤ (n : ℝ) ^ (1 / 2 - z) := Real.rpow_nonneg hn₀.le _
  have hlog' : Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 2 - z) := by
    change ‖Real.log (n : ℝ)‖ ≤ ‖(n : ℝ) ^ (1 / 2 - z)‖ at hh
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hn₁),
      abs_of_nonneg hr] at hh
  calc
    budget n 2 = (n : ℝ) ^ (1 / 2 : ℝ) * Real.log (n : ℝ) := by norm_num [budget]
    _ ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 - z) :=
      mul_le_mul_of_nonneg_left hlog' (Real.rpow_nonneg hn₀.le _)
    _ = _ := by rw [← Real.rpow_add hn₀]; congr 1; ring

/-- The omni-absorber for a reserve of degree O(n^(1−z)) can be placed
outside any bank with the same degree scale. -/
theorem eventually_omni (q : ℕ) (hq : 3 ≤ q) (z U : ℝ) (hz : 0 < z) (hz₂ : z < 1 / 2)
    (_hU : 0 ≤ U) :
    ∃ G : ℝ, 0 < G ∧ ∀ T : ℝ, 0 ≤ T → ∀ᶠ n : ℕ in atTop, ∀ (F X : Finset (Edge n)),
      X ⊆ Fᶜ →
      (∀ v : Fin n, ∑ e : F, incidence 2 e v ≤ T * (n : ℝ) ^ (1 - z)) →
      (∀ v : Fin n, ∑ e : X, incidence 2 e v ≤ U * (n : ℝ) ^ (1 - z)) →
      ∃ (A : Finset (Edge n)) (W : Finset (Finset (Fin n)))
        (finish : Finset (Finset (Fin n)) → Finset (Finset (Fin n))),
        A ⊆ Fᶜ ∧ Disjoint X A ∧
        (∀ v : Fin n, ∑ e : A, incidence 2 e v ≤ G * (n : ℝ) ^ (1 - z)) ∧
        IsOmniAbsorberOn q 2 univ (vertexSets X) (vertexSets A) W finish := by
  obtain ⟨C, hC, ε, hε, h⟩ := exists_omni q hq
  have hC₀ : (0 : ℝ) < C := by exact_mod_cast (by omega : 0 < C)
  let G : ℝ := (C : ℝ) * max U 1
  have hG : 0 < G := mul_pos hC₀ (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  refine ⟨G, hG, ?_⟩
  intro T hT
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdec : Tendsto (fun n : ℕ => (n : ℝ) ^ (-z)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hz).comp hnat
  have hsmall : Tendsto (fun n : ℕ => max (T + 1) (U * C) * (n : ℝ) ^ (-z)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdec
  have hε₀ : 0 < min ε 1 := lt_min hε zero_lt_one
  filter_upwards [hsmall.eventually_lt_const hε₀, eventually_absorption_budget z hz₂,
    eventually_ge_atTop (1 : ℕ)] with n hsmall hbudget hn
  intro F X hXF hF hX
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  let s := (n : ℝ) ^ (1 - z)
  have hs : 1 ≤ s := Real.one_le_rpow hn₁ (by linarith)
  have hsn : (n : ℝ) * (n : ℝ) ^ (-z) = s := by
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-z) := by rw [Real.rpow_one]
      _ = s := by rw [← Real.rpow_add hn₀]; rfl
  have hh : max (T + 1) (U * C) * s ≤ min ε 1 * n := by
    have h' := mul_le_mul_of_nonneg_right hsmall.le hn₀.le
    rw [mul_assoc, mul_comm ((n : ℝ) ^ (-z)), hsn] at h'
    exact h'
  have hhF := (mul_le_mul_of_nonneg_right (le_max_left (T + 1) (U * C)) (by linarith : 0 ≤ s)).trans
    (hh.trans (mul_le_mul_of_nonneg_right (min_le_left ε 1) hn₀.le))
  have hhX := (mul_le_mul_of_nonneg_right (le_max_right (T + 1) (U * C)) (by linarith : 0 ≤ s)).trans
    (hh.trans (mul_le_mul_of_nonneg_right (min_le_right ε 1) hn₀.le))
  have hfitF : 1 + T * s ≤ ε * n := by nlinarith only [hs, hhF]
  have hfitX : U * s ≤ (n : ℝ) / C := (le_div_iff₀ hC₀).mpr (by nlinarith only [hhX])
  obtain ⟨A, W, finish, hAF, hAX, hdeg, hO⟩ := h n F X (U * s) (T * s) hn hfitF hXF hfitX hF hX
  refine ⟨A, W, finish, hAF, hAX, fun v => (hdeg v).trans ?_, hO⟩
  change (C : ℝ) * max (U * s) (budget n 2) ≤ ((C : ℝ) * max U 1) * s
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC₀.le
  apply max_le
  · exact mul_le_mul_of_nonneg_right (le_max_left U 1) (by linarith)
  · exact hbudget.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (le_max_right U 1) (by linarith : 0 ≤ s))

/-- Instantiate the physical placement interface with the Palomar theorem. -/
theorem physicalOmniPlacement_of_omni (q : ℕ) (hq : 3 ≤ q) (z : ℝ)
    (hz : 0 < z) (hz₂ : z < 1 / 2) : PhysicalCompletion.PhysicalOmniPlacement q z := by
  intro U hU
  obtain ⟨G, hG, hplace⟩ := eventually_omni q hq z U hz hz₂ hU
  refine ⟨G, hG, fun T hT => ?_⟩
  filter_upwards [hplace T hT] with n hn
  intro F X hXF hF hX
  have hXc : X ⊆ Fᶜ := by
    intro e he
    exact mem_compl.mpr (fun hf => disjoint_left.mp hXF he hf)
  obtain ⟨A, W, finish, hAF, hXA, hdeg, hO⟩ := hn F X hXc hF hX
  have hAF' : Disjoint A F := disjoint_left.mpr fun e he hf => mem_compl.mp (hAF he) hf
  exact ⟨A, hXA.symm, hAF', hdeg,
    fun S hS hdiv => physical_completion hO hS (divisible_vertexSets hdiv)⟩

end KqR75.OmniBridge

#print axioms KqR75.OmniBridge.exists_omni
#print axioms KqR75.OmniBridge.physical_completion
#print axioms KqR75.OmniBridge.eventually_omni

#print axioms KqR75.OmniBridge.physicalOmniPlacement_of_omni
