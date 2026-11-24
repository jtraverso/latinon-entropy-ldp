module
public import PrefixScoreBudget
public import DesignFibreMass

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Finset LatinonEntropy ColouredCliques CompleteJohnson SparseGram WeightedGreedy
open ProfileBalance

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The quantitative lower bound once a dense host supplies a good
event and recovering completions. The error constant is explicit in
the uniform seed and profile bounds supplied by the construction. -/
theorem lower_from_host {n q : ℕ} (hq : 3 ≤ q) (hnq : q ≤ n)
    (colour : Fin n → C) (hclasses : ∀ i, q ≤ profile colour univ i)
    (J : Finset (Edge n)) (w : HostCorrection.availableBlocks n q J → ℝ)
    (hw : ∀ b, 0 ≤ w b) (guard : List (Option (Clique n q)) → Prop)
    (m : TypeProfile C q → ℤ) (ℓ W E : ℝ) (hℓ : 0 < ℓ) (hW : 0 < W) (hE : 0 ≤ E)
    (hseedlo : ∀ b : Clique n q, ℓ * HostCorrection.scale n q ≤
      ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ)) b)
    (hseedhi : ∀ b : Clique n q, ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ)) b ≤
      W * HostCorrection.scale n q)
    (c A a z D : ℝ) (hc : 0 < c) (hA : 0 ≤ A)
    (hpert : ∀ b, |w b - ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ)) b| ≤
      HostCorrection.scale n q * (E * (n : ℝ) ^ (-z)))
    (ha : 0 ≤ a) (hz : z ≤ 2) (haz : z ≤ a) (hD : 0 ≤ D)
    (hscale : a * (4 * (q.choose 2 : ℝ) - 1) = 1 - 2 * z)
    (good : List (Option (Clique n q)) → Prop) :
    let r := q.choose 2
    let M := (J.card : ℝ) / (r : ℝ)
    let B := (Fintype.card (Edge n) : ℝ) / (r : ℝ)
    let T := GreedyScales.horizon M n a
    let μ := extend J w
    let K := kernel (resources n q) μ (PhysicalHorizonCounts.extend_nonneg J w hw) J guard
    let V := 2 * (E / ℓ) + 2 * Real.sqrt (A / ((r : ℝ) * c))
    let L₀ := |Real.log ℓ| + |Real.log W|
    let err := (3 + V) / Real.log 2 + 3 +
      (Fintype.card (TypeProfile C q) : ℝ) * D * (L₀ / Real.log 2 + (q - 2 : ℕ))
    c * (n : ℝ) ^ 2 ≤ M →
    1 ≤ T →
    E * (n : ℝ) ^ (-z) / ℓ ≤ 1 / 2 →
    Real.sqrt (A / ((r : ℝ) * c)) * (n : ℝ) ^ (-z) ≤ 1 / 2 →
    (1 : ℝ) / 2 ≤ FiniteProcess.eventMass K T good →
    (∀ h ∈ histories (Option (Clique n q)) T, good h → 0 < historyWeight K h →
      valid (resources n q) J h ∧ none ∉ h ∧
        ¬ EnergyExit.crossed (HorizonCountTheorem.energy (resources n q) μ J r M) (A * n) h ∧
        (∀ t, |(TypeCounts.count (PhysicalHorizonCounts.fibre colour t) h : ℝ) - (m t : ℝ)| ≤
          D * (n : ℝ) ^ (2 - z)) ∧
        ∃ P : Finset (Clique n q), packs P univ ∧
          (∀ t, BankCapacity.integerHistogram colour P t = m t) ∧
          P.filter (fun b => resources n q b ⊆ J) = picked h) →
    0 < (designFibre colour m).card ∧
      -(∑ t, (m t : ℝ) * Real.log ((m t : ℝ) /
        ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ))) -
      ((r : ℝ) - 1) * B - err * ((n : ℝ) ^ (2 - z) * Real.log n) ≤
        Real.log ((designFibre colour m).card : ℝ) := by
  intro r M B T μ K V L₀ err hM hT hsmall hε hmass hgood
  have hn : 2 ≤ n := by omega
  have hr : 1 ≤ r := Nat.choose_pos (by omega)
  have hr₀ : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hnz : 0 ≤ (n : ℝ) ^ (-z) := Real.rpow_nonneg hn₀.le _
  have hM₀ : 0 < M := (mul_pos hc (sq_pos_of_pos hn₀)).trans_le hM
  have hMB : M ≤ B := div_le_div_of_nonneg_right (by exact_mod_cast card_le_univ J) hr₀.le
  have hB : B ≤ (n : ℝ) ^ 2 := by
    have hcard : Fintype.card (Edge n) = n.choose 2 := by
      rw [Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]
    have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast hr
    dsimp [B]
    rw [hcard]
    exact (div_le_self (Nat.cast_nonneg _) hr₁).trans (by exact_mod_cast Nat.choose_le_pow n 2)
  have hMup := hMB.trans hB
  have hTup : (T : ℝ) ≤ (n : ℝ) ^ 2 :=
    (GreedyScales.horizon_bounds M n a hM₀ (by omega) ha).1.le.trans hMup
  have hrem := BankCapacity.horizon_loss_bound (by omega : 1 ≤ n) hM₀ hMup ha hz haz
  let S := ∑ t, (m t : ℝ) * Real.log ((m t : ℝ) /
    ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ))
  let Q := S + ((r : ℝ) - 1) * B + err * ((n : ℝ) ^ (2 - z) * Real.log n) - Real.log 2
  have hresult := log_designFibre_of_good_histories (by omega : 2 ≤ q)
    colour m J K T good Q hmass (fun h hh hg hp => by
      obtain ⟨hv, hnone, hcross, hcount, hcomp⟩ := hgood h hh hg hp
      have hlen := histories_length hh
      refine ⟨hv, hnone, hcomp, ?_⟩
      have hscore := physical_prefix_score hq hnq colour hclasses J w hw
        (fun t => (m t : ℝ)) ℓ W (E * (n : ℝ) ^ (-z)) hℓ hW (mul_nonneg hE hnz)
        hseedlo hseedhi hpert hsmall guard c A a z (D * (n : ℝ) ^ (2 - z)) hc hA ha
        (mul_nonneg hD (Real.rpow_nonneg hn₀.le _)) hscale h hM (by rwa [hlen])
        hlen.le hnone hp hcross hcount hε
      have hV : 0 ≤ V := by dsimp [V]; positivity
      have hL₀ : 0 ≤ L₀ := by dsimp [L₀]; positivity
      have herr := prefix_score_error_budget hn hT M z D V L₀ (q - 2 : ℕ)
        (Fintype.card (TypeProfile C q) : ℝ) hz hD hV hL₀ (Nat.cast_nonneg _) hTup hrem
      have hlead := mul_le_mul_of_nonneg_left hMB
        (sub_nonneg.mpr (show (1 : ℝ) ≤ r by exact_mod_cast hr))
      rw [hlen] at hscore
      change Real.log (historyWeight K h) + Real.log (T.factorial : ℝ) ≤
        S + ((r : ℝ) - 1) * M + (M - T) + 1 + Real.log T +
          (T : ℝ) * (2 * (E * (n : ℝ) ^ (-z) / ℓ) +
            2 * (Real.sqrt (A / ((r : ℝ) * c)) * (n : ℝ) ^ (-z))) +
          (Fintype.card (TypeProfile C q) : ℝ) *
            ((D * (n : ℝ) ^ (2 - z)) * (L₀ + (q - 2 : ℕ) * Real.log n)) at hscore
      have hEeq : 2 * (E * (n : ℝ) ^ (-z) / ℓ) +
          2 * (Real.sqrt (A / ((r : ℝ) * c)) * (n : ℝ) ^ (-z)) =
          V * (n : ℝ) ^ (-z) := by dsimp [V]; ring
      rw [hEeq] at hscore
      change M - (T : ℝ) + 1 + Real.log T + (T : ℝ) * (V * (n : ℝ) ^ (-z)) +
        (Fintype.card (TypeProfile C q) : ℝ) *
          ((D * (n : ℝ) ^ (2 - z)) * (L₀ + (q - 2 : ℕ) * Real.log n)) + Real.log 2 ≤
        err * ((n : ℝ) ^ (2 - z) * Real.log n) at herr
      dsimp only [Q]
      linarith only [hscore, herr, hlead])
  exact ⟨hresult.1, by dsimp only [Q, S] at hresult; linarith only [hresult.2]⟩

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.lower_from_host
