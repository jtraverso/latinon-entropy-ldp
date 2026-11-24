module
public import GoodPrefixProbability
public import SeedLog
public import PhysicalHorizonCounts

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Finset LatinonEntropy ColouredCliques CompleteJohnson SparseGram WeightedGreedy
open ProfileBalance

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Bound the probability of a physical good history using the original
profile weights, even though the process uses the repaired seed. -/
theorem physical_prefix_score {n q : ℕ} (hq : 3 ≤ q) (hnq : q ≤ n)
    (colour : Fin n → C) (hclasses : ∀ i, q ≤ profile colour univ i)
    (J : Finset (Edge n)) (w' : HostCorrection.availableBlocks n q J → ℝ)
    (hw' : ∀ b, 0 ≤ w' b)
    (m : TypeProfile C q → ℝ) (ℓ W E : ℝ) (hℓ : 0 < ℓ) (hW : 0 < W) (hE : 0 ≤ E)
    (hwlo : ∀ b : Clique n q, ℓ * HostCorrection.scale n q ≤
      ProfileWeights.weight (cliqueType colour) m b)
    (hwhi : ∀ b : Clique n q, ProfileWeights.weight (cliqueType colour) m b ≤
      W * HostCorrection.scale n q)
    (hpert : ∀ b, |w' b - ProfileWeights.weight (cliqueType colour) m b| ≤
      HostCorrection.scale n q * E)
    (hsmall : E / ℓ ≤ 1 / 2)
    (guard : List (Option (Clique n q)) → Prop)
    (c A a z D : ℝ) (hc : 0 < c) (hA : 0 ≤ A) (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hscale : a * (4 * (q.choose 2 : ℝ) - 1) = 1 - 2 * z)
    (h : List (Option (Clique n q))) :
    let M := (J.card : ℝ) / (q.choose 2 : ℝ)
    let μ := extend J w'
    let K := kernel (resources n q) μ (PhysicalHorizonCounts.extend_nonneg J w' hw') J guard
    let ε := Real.sqrt (A / ((q.choose 2 : ℝ) * c)) * (n : ℝ) ^ (-z)
    c * (n : ℝ) ^ 2 ≤ M →
    1 ≤ h.length → h.length ≤ GreedyScales.horizon M n a →
    none ∉ h → 0 < historyWeight K h →
    ¬ EnergyExit.crossed (HorizonCountTheorem.energy (resources n q) μ J (q.choose 2) M)
      (A * n) h →
    (∀ t, |(TypeCounts.count (PhysicalHorizonCounts.fibre colour t) h : ℝ) - m t| ≤ D) →
    ε ≤ 1 / 2 →
    Real.log (historyWeight K h) + Real.log (h.length.factorial : ℝ) ≤
      (∑ t, m t * Real.log (m t / ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ))) +
        ((q.choose 2 : ℝ) - 1) * M + (M - h.length) + 1 + Real.log h.length +
        (h.length : ℝ) * (2 * (E / ℓ) + 2 * ε) +
        (Fintype.card (TypeProfile C q) : ℝ) *
          (D * (|Real.log ℓ| + |Real.log W| + (q - 2 : ℕ) * Real.log n)) := by
  intro M μ K ε hM hT₁ hT hnone hp hcross hcount hε
  have hr : 1 ≤ q.choose 2 := Nat.choose_pos (by omega)
  have hr' : (0 : ℝ) < q.choose 2 := by exact_mod_cast (by omega : 0 < q.choose 2)
  have hJ : (J.card : ℝ) = (q.choose 2 : ℝ) * M := by
    dsimp [M]
    rw [mul_comm, div_mul_cancel₀ _ hr'.ne']
  have hα : 0 < HostCorrection.scale n q := by
    unfold HostCorrection.scale
    exact inv_pos.mpr (by exact_mod_cast Nat.choose_pos (by omega : q - 2 ≤ n - 2))
  let score := fun t : TypeProfile C q =>
    Real.log (m t / ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ))
  have hs (b : Clique n q) (hb : 0 < μ b) : Real.log (μ b) ≤ score (cliqueType colour b) + 2 * (E / ℓ) := by
    have hfit : resources n q b ⊆ J := by
      by_contra! hfit
      simp [μ, extend, hfit] at hb
    let b' : HostCorrection.availableBlocks n q J := ⟨b, mem_filter.mpr ⟨mem_univ _, hfit⟩⟩
    have hb' : μ b = w' b' := extend_coe J w' b'
    have hbound := log_repaired_weight hα hℓ hE (hwlo b)
      (by simpa only [mul_comm E] using hpert b') hsmall
    rw [hb']
    exact sub_le_iff_le_add.mp ((abs_le.mp hbound).2) |>.trans_eq (add_comm _ _)
  exact log_probability_on_good_history (resources n q) μ
    (PhysicalHorizonCounts.extend_nonneg J w' hw') J guard (cliqueType colour) score m
    (q.choose 2) n hr (by omega) (resources_card n q) M c A a z D
    (|Real.log ℓ| + |Real.log W| + (q - 2 : ℕ) * Real.log n) (2 * (E / ℓ))
    hc hA ha hD hscale hM hJ h hT₁ hT hnone hp hcross hs hcount
    (seed_log_abs_le colour (by omega) hnq hclasses m ℓ W hℓ hW hwlo hwhi) hε

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.physical_prefix_score
