module
public import LowerHostScales

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Filter Finset LatinonEntropy ColouredCliques CompleteJohnson SparseGram WeightedGreedy
open ProfileBalance
open scoped Matrix Topology

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The stopping and type deviation constant is selected before the
completion parameters. A dense repaired host with completing histories
then gives the uniform lower count at the critical exponent. -/
theorem eventually_lower_with_recovering_host (q : ℕ) (hq : 3 ≤ q)
    (ℓ W : ℝ) (hℓ : 0 < ℓ) (hW : 0 < W) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ E R U : ℝ, 0 ≤ E → 0 ≤ R → 0 ≤ U →
    ∃ err : ℝ, 0 ≤ err ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (colour : Fin n → C) (m : TypeProfile C q → ℤ)
        (P₀ : Finset (Clique n q)) (J : Finset (Edge n))
        (w : HostCorrection.availableBlocks n q J → ℝ),
      (∀ i, q ≤ profile colour univ i) →
      (n : ℝ) ^ 2 / 4 ≤ (J.card : ℝ) →
      (∀ b, 0 ≤ w b ∧ w b ≤ W * HostCorrection.scale n q) →
      HostCorrection.hostIncidence n q J *ᵥ w = (fun _ => 1) →
      (∀ b : Clique n q, ℓ * HostCorrection.scale n q ≤
        ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ)) b ∧
        ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ)) b ≤
          W * HostCorrection.scale n q) →
      let r := q.choose 2
      let M := (J.card : ℝ) / (r : ℝ)
      let B := (Fintype.card (Edge n) : ℝ) / (r : ℝ)
      let z := GreedyScales.criticalExponent q
      let a := (2 * (q : ℝ) - 1) * z
      let T := GreedyScales.horizon M n a
      let μ := extend J w
      (∀ b, |w b - ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ)) b| ≤
        HostCorrection.scale n q * (E * (n : ℝ) ^ (-z))) →
      (∀ t, |(m t : ℝ) - (BankCapacity.integerHistogram colour P₀ t : ℝ) -
        hostHistogram colour J w t| ≤ R * (n : ℝ) ^ (2 - z)) →
      (P₀.card : ℝ) ≤ U * (n : ℝ) ^ (2 - z) →
      (∀ h : List (Option (Clique n q)), h.length = T → none ∉ h → valid (resources n q) J h →
        (∀ t, |(TypeCounts.count (PhysicalHorizonCounts.fibre colour t) h : ℝ) -
          (T : ℝ) * TypeWeights.proportion (resources n q) μ J
            (PhysicalHorizonCounts.fibre colour t) []| ≤ D * (n : ℝ) ^ (2 - z)) →
        ∃ P : Finset (Clique n q), packs P univ ∧
          (∀ t, BankCapacity.integerHistogram colour P t = m t) ∧
          P.filter (fun b => resources n q b ⊆ J) = picked h) →
      0 < (designFibre colour m).card ∧
        -(∑ t, (m t : ℝ) * Real.log ((m t : ℝ) /
          ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ))) -
        ((r : ℝ) - 1) * B - err * ((n : ℝ) ^ (2 - z) * Real.log n) ≤
          Real.log ((designFibre colour m).card : ℝ) := by
  let r := q.choose 2
  let z := GreedyScales.criticalExponent q
  let a := (2 * (q : ℝ) - 1) * z
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.choose_pos (show 2 ≤ q by omega)
  obtain ⟨hz, hz', hza, _, hscale, _⟩ := critical_completion_scales q hq
  have ha : 0 < a := hz.trans_le hza
  let b := 2 * W * (q : ℝ)
  let A := 1 + 4 * PhysicalDrift.noiseConstant r b
  have hA : 0 ≤ A := by dsimp [A, b, PhysicalDrift.noiseConstant]; positivity
  let c : ℝ := 1 / (4 * (r : ℝ))
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨D', hprob⟩ := PhysicalHorizonCounts.eventually_count (C := C) q hq W hW.le
  let D := max 0 D'
  have hD : 0 ≤ D := le_max_left _ _
  refine ⟨D, hD, ?_⟩
  intro E R U hE hR hU
  let d := D + 2 + R + U
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let V := 2 * (E / ℓ) + 2 * Real.sqrt (A / ((r : ℝ) * c))
  let L₀ := |Real.log ℓ| + |Real.log W|
  let err := (3 + V) / Real.log 2 + 3 +
    (Fintype.card (TypeProfile C q) : ℝ) * d * (L₀ / Real.log 2 + (q - 2 : ℕ))
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hL₀ : 0 ≤ L₀ := by dsimp [L₀]; positivity
  refine ⟨err, by dsimp only [err]; positivity, ?_⟩
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdec : Tendsto (fun n : ℕ => (n : ℝ) ^ (-z)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hz).comp hnat
  have hpertSmall : Tendsto (fun n : ℕ => E * (n : ℝ) ^ (-z) / ℓ) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (E / ℓ) * (n : ℝ) ^ (-z)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hdec.const_mul (E / ℓ)
    convert hh using 1
    ext n
    ring
  have hnormSmall : Tendsto (fun n : ℕ => Real.sqrt (A / ((r : ℝ) * c)) * (n : ℝ) ^ (-z))
      atTop (𝓝 0) := by simpa only [mul_zero] using hdec.const_mul (Real.sqrt (A / ((r : ℝ) * c)))
  filter_upwards [hprob, eventually_ge_atTop q, eventually_horizon_positive c a hc ha,
    hpertSmall.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num),
    hnormSmall.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num)] with n hp hn hT hsmall hnorm
  intro colour m P₀ J w hcol hdense hw hload hs
  dsimp only
  intro hpert hrepair hP₀ hcomp
  let M := (J.card : ℝ) / (r : ℝ)
  let T := GreedyScales.horizon M n a
  let μ := extend J w
  let guard := HorizonCountTheorem.guard (resources n q) μ J r T M n (b / n) (A * n)
  let K := kernel (resources n q) μ
    (PhysicalHorizonCounts.extend_nonneg J w (fun b => (hw b).1)) J guard
  let good := fun h : List (Option (Clique n q)) =>
    none ∉ h ∧ valid (resources n q) J h ∧
      ¬ EnergyExit.crossed (HorizonCountTheorem.energy (resources n q) μ J r M) (A * n) h ∧
      ∀ t : TypeProfile C q, |(TypeCounts.count (PhysicalHorizonCounts.fibre colour t) h : ℝ) -
        (T : ℝ) * TypeWeights.proportion (resources n q) μ J
          (PhysicalHorizonCounts.fibre colour t) []| ≤ D * (n : ℝ) ^ (2 - z)
  have hM : c * (n : ℝ) ^ 2 ≤ M := by
    apply (le_div_iff₀ hr).mpr
    dsimp only [c]
    convert hdense using 1
    field_simp
  have hJ : 0 < J.card := by
    have h : (0 : ℝ) < J.card :=
      (div_pos (sq_pos_of_pos (by exact_mod_cast (by omega : 0 < n))) (by norm_num)).trans_le hdense
    exact_mod_cast h
  have hmass : (1 : ℝ) / 2 ≤ FiniteProcess.eventMass K T good := by
    refine (hp J colour w (fun b => (hw b).1) hdense (fun b => (hw b).2) hload).trans ?_
    refine PrefixTypeTests.mono_support K T _ good ?_
    intro h _ _ hh
    refine ⟨hh.1, hh.2.1, hh.2.2.1, fun t => (hh.2.2.2 t).trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine lower_from_host hq hn colour hcol J w (fun b => (hw b).1) guard m ℓ W E hℓ hW hE
    (fun b => (hs b).1) (fun b => (hs b).2) c A a z d hc hA hpert ha.le (by linarith)
    hza hd hscale good hM (hT M hM) hsmall.le hnorm.le hmass ?_
  intro h hh hg hpos
  have hlen : h.length = T := histories_length hh
  obtain ⟨hstop, hvalid, hcross, hcounts⟩ := hg
  refine ⟨hvalid, hstop, hcross, ?_, hcomp h hlen hstop hvalid hcounts⟩
  exact prefix_counts_close_to_target hq (by omega) colour J hJ P₀ (fun t => (m t : ℝ))
    w (fun b => (hw b).1) hload a z D R U ha.le (by linarith) hza h hvalid hlen
    (by simpa only [hlen] using hcounts) hrepair hP₀

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.eventually_lower_with_recovering_host
