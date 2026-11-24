module
public import SlotPairMargins
public import HostCorrection
public import JointCorrection

@[expose] public section
noncomputable section
namespace KqR75.ProfileBalance

open Finset ColouredCliques SlotPairMargins SlotProfiles CompleteJohnson SparseGram
open scoped Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

def histogram {n q : ℕ} (colour : Fin n → C) (w : Clique n q → ℝ) (t : TypeProfile C q) : ℝ :=
  ∑ b ∈ ProfileWeights.fibre (cliqueType colour) t, w b

theorem card_block_pairs {n q : ℕ} (colour : Fin n → C) (b : Clique n q) (e : Edge n) :
    ((resources n q b).filter
      (fun f : Edge n => profile colour (f : Finset (Fin n)) = profile colour (e : Finset (Fin n)))).card =
      cliques colour b (profile colour (e : Finset (Fin n))) := by
  classical
  rw [← card_extensions_empty]
  apply card_bij (fun (f : Edge n) _ => (f : Finset (Fin n)))
  · intro f hf
    obtain ⟨hf, h⟩ := mem_filter.mp hf
    exact mem_filter.mpr ⟨mem_powerset.mpr (mem_filter.mp hf).2, empty_subset _, h⟩
  · intro f _ g _ h
    exact Subtype.ext h
  · intro f hf
    obtain ⟨hf, _, hp⟩ := mem_filter.mp hf
    have hcard : f.card = 2 := by
      rw [← sum_profile colour f, hp, sum_profile]
      exact (mem_powersetCard.mp e.property).2
    let g : Edge n := ⟨f, mem_powersetCard.mpr ⟨subset_univ _, hcard⟩⟩
    exact ⟨g, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, mem_powerset.mp hf⟩, hp⟩, rfl⟩

/-- The histogram's pair margin is the sum of loads over edges of that
colour profile. This is a weighted incidence identity for signed weights. -/
theorem margin_histogram {n q : ℕ} (colour : Fin n → C) (w : Clique n q → ℝ) (e : Edge n) :
    pairMargin colour (histogram colour w) e =
      ∑ f : Edge n, WeightedEnergy.load (resources n q) w f *
        (if profile colour (f : Finset (Fin n)) = profile colour (e : Finset (Fin n)) then 1 else 0) := by
  classical
  let a (t : TypeProfile C q) : ℝ :=
    ((∏ i, (t.val i : ℕ).choose (profile colour (e : Finset (Fin n)) i) : ℕ) : ℝ)
  let g (f : Edge n) : ℝ :=
    if profile colour (f : Finset (Fin n)) = profile colour (e : Finset (Fin n)) then 1 else 0
  have hg (b : Clique n q) : (∑ f ∈ resources n q b, g f) = a (cliqueType colour b) := by
    dsimp only [g, a]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast card_block_pairs colour b e
  rw [← WeightedEnergy.incidence_sum (resources n q) w g]
  change (∑ t, a t * ∑ b ∈ ProfileWeights.fibre (cliqueType colour) t, w b) =
    ∑ b, w b * ∑ f ∈ resources n q b, g f
  simp_rw [hg, Finset.mul_sum, mul_comm (a _) (w _)]
  rw [← Finset.sum_fiberwise univ (cliqueType colour) (fun b => w b * a (cliqueType colour b))]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro b hb
  rw [(mem_filter.mp hb).2]

theorem profiles_eq_of_margins {n q : ℕ} (hq : 2 ≤ q) (colour : Fin n → C)
    (hclasses : ∀ i, 2 ≤ profile colour univ i) (ref : C)
    (m₁ m₂ : TypeProfile C q → ℝ)
    (hmargin : ∀ e : Edge n, pairMargin colour m₁ e = pairMargin colour m₂ e)
    (hhigh : ∀ t : High C q ref, m₁ t.val = m₂ t.val) : m₁ = m₂ := by
  let d := fun t => m₁ t - m₂ t
  have hd (e : Edge n) : pairMargin colour d e = 0 := by
    simp only [pairMargin, d, mul_sub, Finset.sum_sub_distrib] at hmargin ⊢
    rw [hmargin e, sub_self]
  have hz := SlotPairMargins.low_eq_zero hq ref d
    (fun t ht => sub_eq_zero.mpr (hhigh ⟨t, ht⟩))
    ((ordered_margins_zero_iff colour hclasses d).mpr hd)
  funext t
  exact sub_eq_zero.mp (congrFun hz t)

/-- On actual cliques, matching edge loads and high types is sufficient
to match any prescribed histogram with compatible pair margins. -/
theorem histogram_eq_of_loads {n q : ℕ} (hq : 2 ≤ q) (colour : Fin n → C)
    (hclasses : ∀ i, 2 ≤ profile colour univ i) (ref : C)
    (w : Clique n q → ℝ) (m : TypeProfile C q → ℝ) (v : Edge n → ℝ)
    (hload : ∀ e, WeightedEnergy.load (resources n q) w e = v e)
    (hmargin : ∀ e : Edge n, pairMargin colour m e =
      ∑ f : Edge n, v f *
        (if profile colour (f : Finset (Fin n)) = profile colour (e : Finset (Fin n)) then 1 else 0))
    (hhigh : ∀ t : High C q ref, histogram colour w t.val = m t.val) :
    histogram colour w = m := by
  apply profiles_eq_of_margins hq colour hclasses ref _ _ _ hhigh
  intro e
  rw [margin_histogram, hmargin]
  simp_rw [hload]

def extend {n q : ℕ} (J : Finset (Edge n))
    (w : HostCorrection.availableBlocks n q J → ℝ) (b : Clique n q) : ℝ :=
  if h : resources n q b ⊆ J then
    w ⟨b, mem_filter.mpr ⟨mem_univ _, h⟩⟩ else 0

def hostHistogram {n q : ℕ} (colour : Fin n → C) (J : Finset (Edge n))
    (w : HostCorrection.availableBlocks n q J → ℝ) : TypeProfile C q → ℝ :=
  histogram colour (extend J w)

theorem extend_coe {n q : ℕ} (J : Finset (Edge n))
    (w : HostCorrection.availableBlocks n q J → ℝ)
    (b : HostCorrection.availableBlocks n q J) : extend J w b = w b := by
  unfold extend
  rw [dif_pos (mem_filter.mp b.property).2]

theorem load_extend {n q : ℕ} (J : Finset (Edge n))
    (w : HostCorrection.availableBlocks n q J → ℝ) (e : Edge n) :
    WeightedEnergy.load (resources n q) (extend J w) e =
      if h : e ∈ J then (HostCorrection.hostIncidence n q J *ᵥ w) ⟨e, h⟩ else 0 := by
  classical
  by_cases he : e ∈ J
  · rw [dif_pos he]
    simp only [Matrix.mulVec, dotProduct, HostCorrection.hostIncidence, ite_mul, one_mul, zero_mul]
    let F := HostCorrection.availableBlocks n q J
    let g (b : Clique n q) := if e ∈ resources n q b then extend J w b else 0
    have hS : (∑ b : F, if e ∈ resources n q b then w b else 0) = ∑ b ∈ F, g b := by
      rw [← Finset.sum_coe_sort F g]
      apply Finset.sum_congr rfl
      intro b _
      dsimp only [g]
      rw [extend_coe J w b]
    rw [hS]
    change (∑ b, g b) = ∑ b ∈ F, g b
    change (∑ b, g b) = ∑ b ∈ univ.filter (fun b => resources n q b ⊆ J), g b
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : resources n q b ⊆ J <;> simp [g, extend, hb]
  · rw [dif_neg he]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : e ∈ resources n q b
    · have hsub : ¬ resources n q b ⊆ J := fun h => he (h hb)
      simp [hb, extend, hsub]
    · simp [hb]

theorem histogram_extend {n q : ℕ} (colour : Fin n → C) (J : Finset (Edge n))
    (w : HostCorrection.availableBlocks n q J → ℝ) (v : TypeProfile C q) :
    hostHistogram colour J w v =
      ∑ b : HostCorrection.availableBlocks n q J,
        if cliqueType colour (b : Clique n q) = v then w b else 0 := by
  classical
  let g (b : Clique n q) := if cliqueType colour b = v then extend J w b else 0
  have hg : (∑ b : HostCorrection.availableBlocks n q J,
      if cliqueType colour (b : Clique n q) = v then w b else 0) =
      ∑ b ∈ HostCorrection.availableBlocks n q J, g b := by
    rw [← Finset.sum_coe_sort _ g]
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [g]
    rw [extend_coe J w b]
  rw [hg]
  simp only [hostHistogram, histogram, ProfileWeights.fibre, HostCorrection.availableBlocks,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : resources n q b ⊆ J
  · simp [hb, g]
  · simp [hb, extend, g]

def highIncidence {n q : ℕ} (colour : Fin n → C) (ref : C) (J : Finset (Edge n)) :
    Matrix (High C q ref) (HostCorrection.availableBlocks n q J) ℝ :=
  fun i b => if cliqueType colour (b : Clique n q) = i.val then 1 else 0

theorem highIncidence_apply {n q : ℕ} (colour : Fin n → C) (ref : C) (J : Finset (Edge n))
    (w : HostCorrection.availableBlocks n q J → ℝ) (i : High C q ref) :
    (highIncidence colour ref J *ᵥ w) i = hostHistogram colour J w i.val := by
  rw [histogram_extend]
  simp only [Matrix.mulVec, dotProduct, highIncidence, ite_mul, one_mul, zero_mul]

def compatible {n q : ℕ} (colour : Fin n → C) (J : Finset (Edge n))
    (m : TypeProfile C q → ℝ) (ν : J → ℝ) : Prop :=
  ∀ e : Edge n, pairMargin colour m e =
    ∑ f : J, ν f *
      (if profile colour (f : Finset (Fin n)) = profile colour (e : Finset (Fin n)) then 1 else 0)

theorem hostHistogram_eq {n q : ℕ} (hq : 2 ≤ q) (colour : Fin n → C)
    (hclasses : ∀ i, 2 ≤ profile colour univ i)
    (ref : C) (J : Finset (Edge n)) (w : HostCorrection.availableBlocks n q J → ℝ)
    (m : TypeProfile C q → ℝ) (ν : J → ℝ)
    (hcompat : compatible colour J m ν)
    (hload : HostCorrection.hostIncidence n q J *ᵥ w = ν)
    (hhigh : highIncidence colour ref J *ᵥ w = fun t => m t.val) :
    hostHistogram colour J w = m := by
  apply profiles_eq_of_margins hq colour hclasses ref _ _
  · intro e
    rw [hostHistogram, margin_histogram, hcompat]
    simp_rw [load_extend, hload]
    let g (f : Edge n) := if profile colour (f : Finset (Fin n)) =
      profile colour (e : Finset (Fin n)) then (1 : ℝ) else 0
    let G (f : Edge n) := (if h : f ∈ J then ν ⟨f, h⟩ else 0) * g f
    have hS : (∑ f : J, ν f * g f) = ∑ f ∈ J, G f := by
      rw [← Finset.sum_coe_sort J G]
      apply Finset.sum_congr rfl
      intro f _
      dsimp only [G]
      rw [dif_pos f.property]
    change (∑ f, G f) = ∑ f : J, ν f * g f
    rw [hS]
    calc
      _ = ∑ f ∈ univ.filter (fun f => f ∈ J), G f := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro f _
        by_cases hf : f ∈ J <;> simp [hf, G]
      _ = _ := by rw [filter_mem_eq_of_subset (subset_univ J)]
  · intro t
    rw [← highIncidence_apply colour ref J w t, hhigh]

/-- Finite simultaneous correction on the physical host, with the full
histogram as its conclusion. The matrices R and L are the load repair and
the repaired coordinate directions. -/
theorem repair_full_histogram {n q : ℕ} (hq : 2 ≤ q)
    (colour : Fin n → C) (hclasses : ∀ i, 2 ≤ profile colour univ i)
    (ref : C) (J : Finset (Edge n))
    (R : Matrix (HostCorrection.availableBlocks n q J) J ℝ)
    (L : Matrix (HostCorrection.availableBlocks n q J) (High C q ref) ℝ)
    (hR : HostCorrection.hostIncidence n q J * R = 1)
    (hL : HostCorrection.hostIncidence n q J * L = 0)
    (hnear : ∀ i : High C q ref, (∑ j : High C q ref,
      |(1 : Matrix (High C q ref) (High C q ref) ℝ) i j -
        ((highIncidence colour ref J * L : Matrix (High C q ref) (High C q ref) ℝ) i j)|) ≤ (1 / 2 : ℝ))
    (CR CL u t ε : ℝ) (hu : 0 ≤ u) (ht : 0 ≤ t) (hε : 0 < ε)
    (hrowsR : ∀ b, ∑ e, |R b e| ≤ CR) (hrowsL : ∀ b, ∑ i, |L b i| ≤ CL)
    (μ : HostCorrection.availableBlocks n q J → ℝ) (ν : J → ℝ) (m : TypeProfile C q → ℝ)
    (hcompat : compatible colour J m ν)
    (hμ : ∀ b, ε ≤ μ b)
    (hdef : ∀ e, |(ν - HostCorrection.hostIncidence n q J *ᵥ μ) e| ≤ u)
    (htype : ∀ i : High C q ref,
      |m i.val - (highIncidence colour ref J *ᵥ μ) i -
        (highIncidence colour ref J *ᵥ (R *ᵥ (ν - HostCorrection.hostIncidence n q J *ᵥ μ))) i| ≤ t)
    (hsmall : CR * u + CL * (8 * t) ≤ ε / 2) :
    ∃ μ' : HostCorrection.availableBlocks n q J → ℝ,
      HostCorrection.hostIncidence n q J *ᵥ μ' = ν ∧ hostHistogram colour J μ' = m ∧
      (∀ b, 0 < μ' b) ∧ (∀ b, |μ' b - μ b| ≤ CR * u + CL * (8 * t)) := by
  obtain ⟨μ', hload, hhigh, hpos, hbound⟩ := JointCorrection.repair_positive
    (HostCorrection.hostIncidence n q J) R (highIncidence colour ref J) L
    hR hL hnear CR CL u t ε hu ht hε hrowsR hrowsL μ ν (fun i => m i.val) hμ hdef htype hsmall
  exact ⟨μ', hload, hostHistogram_eq hq colour hclasses ref J μ' m ν hcompat hload hhigh, hpos, hbound⟩

end KqR75.ProfileBalance

#print axioms KqR75.ProfileBalance.margin_histogram
#print axioms KqR75.ProfileBalance.histogram_eq_of_loads
#print axioms KqR75.ProfileBalance.repair_full_histogram
