module
public import HorizonCountTheorem
public import ProfileBalance
public import CliqueCodegrees
public import SeedScales

@[expose] public section
noncomputable section
namespace KqR75.PhysicalHorizonCounts

open Finset Filter ColouredCliques CompleteJohnson SparseGram CliqueGram
open scoped Topology Matrix

def fibre {C : Type*} [Fintype C] [DecidableEq C] {n q : ℕ}
    (colour : Fin n → C) (d : TypeProfile C q) : Finset (Clique n q) :=
  univ.filter (fun b => cliqueType colour b = d)

theorem extend_nonneg {n q : ℕ} (J : Finset (Edge n))
    (w : HostCorrection.availableBlocks n q J → ℝ) (hw : ∀ b, 0 ≤ w b) :
    ∀ b, 0 ≤ ProfileBalance.extend J w b := by
  intro b
  unfold ProfileBalance.extend
  split
  · exact hw _
  · exact le_rfl

private theorem initial_available {n q : ℕ} (J : Finset (Edge n))
    (w : HostCorrection.availableBlocks n q J → ℝ) :
    WeightedGreedy.availableWeight (resources n q) (ProfileBalance.extend J w) J [] =
      ProfileBalance.extend J w := by
  funext b
  by_cases h : resources n q b ⊆ J <;>
    simp [WeightedGreedy.availableWeight, WeightedGreedy.remaining, ProfileBalance.extend, h]

theorem initial_proportion {C : Type*} [Fintype C] [DecidableEq C] {n q : ℕ} (hq : 2 ≤ q)
    (J : Finset (Edge n)) (colour : Fin n → C) (w : HostCorrection.availableBlocks n q J → ℝ)
    (hw : HostCorrection.hostIncidence n q J *ᵥ w = (fun _ => 1)) (d : TypeProfile C q) :
    TypeWeights.proportion (resources n q) (ProfileBalance.extend J w) J (fibre colour d) [] =
      ProfileBalance.hostHistogram colour J w d / ((J.card : ℝ) / (q.choose 2 : ℝ)) := by
  classical
  let μ := ProfileBalance.extend J w
  let I := resources n q
  have ht := WeightedGreedy.sum_load I μ J (q.choose 2) (resources_card n q) []
  have hl (e : Edge n) : WeightedGreedy.load I μ J [] e = if e ∈ J then 1 else 0 := by
    rw [WeightedGreedy.load, initial_available, ProfileBalance.load_extend, hw]
    split_ifs <;> rfl
  simp_rw [hl] at ht
  rw [← sum_filter] at ht
  simp only [filter_mem_eq_of_subset (subset_univ J), sum_const, nsmul_eq_mul, mul_one] at ht
  have hq₀ : (0 : ℝ) < q.choose 2 := by exact_mod_cast Nat.choose_pos hq
  have hm : WeightedGreedy.totalWeight I μ J [] = (J.card : ℝ) / (q.choose 2 : ℝ) := by
    apply (eq_div_iff hq₀.ne').2
    rw [mul_comm]
    exact ht.symm
  rw [TypeWeights.proportion, TypeWeights.total_marked, initial_available, hm]
  congr 1
  simp only [TypeWeights.marked, ProfileBalance.hostHistogram, ProfileBalance.histogram,
    ProfileWeights.fibre, fibre, sum_filter, mem_filter, mem_univ, true_and]

/-- The physical leave after all steps contains at most the mass left
at the horizon, including the floor error. -/
theorem leave_bound {n q : ℕ} (hn : 1 ≤ n) (a : ℝ) (ha : 0 ≤ a)
    (J : Finset (Edge n)) (M : ℝ) (hM : 0 < M)
    (hcard : (J.card : ℝ) = (q.choose 2 : ℝ) * M)
    (h : List (Option (Clique n q))) (hh : h.length = GreedyScales.horizon M n a)
    (hvalid : WeightedGreedy.valid (resources n q) J h) (hstop : none ∉ h) :
    ((WeightedGreedy.remaining (resources n q) J h).card : ℝ) ≤
      (q.choose 2 : ℝ) * (M * (n : ℝ) ^ (-a) + 1) := by
  have he := WeightedGreedy.resource_count (resources n q) J (q.choose 2) (resources_card n q) h hvalid
  rw [TypeDriftEnvelope.count_eq_length h hstop, hh] at he
  have he' : ((WeightedGreedy.remaining (resources n q) J h).card : ℝ) +
      (q.choose 2 : ℝ) * (GreedyScales.horizon M n a : ℝ) = J.card := by exact_mod_cast he
  rw [hcard] at he'
  calc
    _ = (q.choose 2 : ℝ) * (M - (GreedyScales.horizon M n a : ℝ)) := by linarith only [he']
    _ ≤ _ := mul_le_mul_of_nonneg_left (GreedyScales.horizon_bounds M n a hM hn ha).2.1 (by positivity)

/-- A sublinear bound on the removed degree supplies the host
density used by the physical counting theorem. -/
theorem eventually_dense (D z : ℝ) (hz : 0 < z) :
    ∀ᶠ n : ℕ in atTop, ∀ (J : Finset (Edge n)) (t : ℝ),
      t ≤ D * (n : ℝ) ^ (1 - z) →
      (∀ v : Fin n, (∑ e : (Jᶜ : Finset (Edge n)), incidence 2 e v) ≤ t) →
      (n : ℝ) ^ 2 / 4 ≤ (J.card : ℝ) := by
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-z)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hz).comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => D * (n : ℝ) ^ (-z)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul D
  have hsmall := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  filter_upwards [eventually_ge_atTop (4 : ℕ), hsmall] with n hn hs
  intro J t ht hdeg
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hrel := SeedScales.relative_degree_bound (show 0 < n by omega) ht
  have ht' : t ≤ (n : ℝ) / 4 := by
    have hh := (div_le_iff₀ hn₀).mp (hrel.trans hs.le)
    linarith only [hh]
  have hcard := sparse_card_bound (incidence (V := Fin n) 2) (Jᶜ : Finset (Edge n))
    t (incidence_row_sum 2) hdeg
  simp only [Fintype.card_fin] at hcard
  have hsum : (J.card : ℝ) + ((Jᶜ : Finset (Edge n)).card : ℝ) = Fintype.card (Edge n) := by
    exact_mod_cast Finset.card_add_card_compl J
  rw [edge_card n (by omega)] at hsum
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith only [hsum, hcard, mul_le_mul_of_nonneg_left ht' hn₀.le,
    mul_nonneg (sub_nonneg.mpr hn') hn₀.le]

/-- L15g for the actual edge–clique incidence. The diffusion envelope
and the density of the surviving host are the only size hypotheses
on the input to the stopped process. -/
theorem eventually_count {C : Type*} [Fintype C] [DecidableEq C] (q : ℕ) (hq : 3 ≤ q)
    (W : ℝ) (hW : 0 ≤ W) :
    ∃ D : ℝ, ∀ᶠ n : ℕ in Filter.atTop,
      ∀ (J : Finset (Edge n)) (colour : Fin n → C)
        (w : HostCorrection.availableBlocks n q J → ℝ) (hμ : ∀ b, 0 ≤ w b),
      (n : ℝ) ^ 2 / 4 ≤ (J.card : ℝ) →
      (∀ b, w b ≤ W * HostCorrection.scale n q) →
      HostCorrection.hostIncidence n q J *ᵥ w = (fun _ => 1) →
      let r := q.choose 2
      let M := (J.card : ℝ) / (r : ℝ)
      let z := GreedyScales.criticalExponent q
      let a := (2 * (q : ℝ) - 1) * z
      let T := GreedyScales.horizon M n a
      let μ := ProfileBalance.extend J w
      let I := resources n q
      let b := 2 * W * (q : ℝ)
      let A := 1 + 4 * PhysicalDrift.noiseConstant r b
      let K := WeightedGreedy.kernel I μ (extend_nonneg J w hμ) J
        (HorizonCountTheorem.guard I μ J r T M n (b / n) (A * n))
      1 / 2 ≤ FiniteProcess.eventMass K T (fun h =>
        none ∉ h ∧ WeightedGreedy.valid I J h ∧
          ¬EnergyExit.crossed (HorizonCountTheorem.energy I μ J r M) (A * n) h ∧
        ∀ d : TypeProfile C q, |(TypeCounts.count (fibre colour d) h : ℝ) -
          (T : ℝ) * TypeWeights.proportion I μ J (fibre colour d) []| ≤ D * (n : ℝ) ^ (2 - z)) := by
  classical
  -- The density margin leaves room for the floor in the horizon.
  let r := q.choose 2
  have hr : 2 ≤ r := by
    have h := Nat.choose_le_choose 2 hq
    exact (show 2 ≤ Nat.choose 3 2 by decide).trans h
  have hr₀ : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  let c := 1 / (4 * (r : ℝ))
  let z := GreedyScales.criticalExponent q
  let a := (2 * (q : ℝ) - 1) * z
  obtain ⟨hz, _, ha, hs⟩ := GreedyScales.criticalExponent_bounds q hq
  have hz' : z ≤ 1/2 := by
    have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
    have hh : 0 ≤ a * (4 * (r : ℝ) - 1) := mul_nonneg ha.le (by linarith)
    linarith only [hs, hh]
  let b := 2 * W * (q : ℝ)
  let A := 1 + 4 * PhysicalDrift.noiseConstant r b
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hnoise : 0 ≤ PhysicalDrift.noiseConstant r b := by
    unfold PhysicalDrift.noiseConstant
    positivity
  have hA : 0 < A := by dsimp [A]; positivity
  let k := Fintype.card (TypeProfile C q)
  let e := Fintype.equivFin (TypeProfile C q)
  let D := 1 + 1 * (1 + CumulativeTypeDrift.driftConstant r c 1 A b)
  have hw := HorizonCountTheorem.eventually_count r hr k c 1 A b a z
    (by dsimp [c]; positivity) (by norm_num) hA hb ha hz hz' hs (by dsimp [A]; linarith)
  refine ⟨D, ?_⟩
  filter_upwards [hw, eventually_ge_atTop (q + 2)] with n hn hlarge
  intro J colour w hμ hdense hweight hloads
  dsimp only
  let I := resources n q
  let M := (J.card : ℝ) / (r : ℝ)
  let β := b / (n : ℝ)
  let μ := ProfileBalance.extend J w
  have hμ' := extend_nonneg J w hμ
  have hMₗ : c * (n : ℝ) ^ 2 ≤ M := by
    apply (le_div_iff₀ hr₀).2
    dsimp [c]
    calc
      _ = (n : ℝ) ^ 2 / 4 := by field_simp
      _ ≤ _ := hdense
  have hMᵤ : M ≤ 1 * (n : ℝ) ^ 2 := by
    have hcard : (J.card : ℝ) ≤ Fintype.card (Edge n) := by exact_mod_cast card_le_univ J
    rw [edge_card n (by omega)] at hcard
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    apply (div_le_iff₀ hr₀).2
    exact (show (J.card : ℝ) ≤ (n : ℝ)^2 by nlinarith only [hcard, (show (0 : ℝ) ≤ n by positivity)]).trans
      (by nlinarith only [mul_le_mul_of_nonneg_left hr1 (sq_nonneg (n : ℝ))])
  have hsupport (v : Clique n q) (hv : ¬I v ⊆ J) : μ v = 0 := by
    simp [μ, ProfileBalance.extend, I, hv]
  have hunit (v : Edge n) : WeightedEnergy.load I μ v = if v ∈ J then 1 else 0 := by
    change WeightedEnergy.load (resources n q) (ProfileBalance.extend J w) v = _
    rw [ProfileBalance.load_extend, hloads]
    split_ifs <;> rfl
  have hμbound (v : Clique n q) : μ v ≤ W * HostCorrection.scale n q := by
    dsimp [μ, ProfileBalance.extend]
    split
    · exact hweight _
    · unfold HostCorrection.scale
      positivity
  have hcodeg (v f : Edge n) (hne : v ≠ f) :
      CodegreeLoss.codegree I μ v f ≤ β := by
    have heq : WeightedGreedy.availableWeight I μ J [] = μ := by
      funext w
      by_cases h : I w ⊆ J <;> simp [WeightedGreedy.availableWeight, WeightedGreedy.remaining, h, hsupport]
    have h := CliqueCodegrees.history_codegree_rate n q hq hlarge W hW μ hμbound J [] v f hne
    change CodegreeLoss.codegree I (WeightedGreedy.availableWeight I μ J []) v f ≤ β at h
    rwa [heq] at h
  have hgood := hn (Edge n) (Clique n q) M β I μ hμ' J (fun i => fibre colour (e.symm i))
    hMₗ hMᵤ (by dsimp [β]; positivity) le_rfl (resources_card n q)
    (by dsimp [M]; field_simp) hsupport hunit hcodeg
  refine hgood.trans (PrefixTypeTests.mono_support _ _ _ _ ?_)
  intro h _ _ ⟨hnone, hv, hx, hh⟩
  refine ⟨hnone, hv, hx, fun d => ?_⟩
  simpa only [Equiv.symm_apply_apply] using hh (e d)

end KqR75.PhysicalHorizonCounts

#print axioms KqR75.PhysicalHorizonCounts.eventually_count
