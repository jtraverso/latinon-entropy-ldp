module
public import PrefixMassScales
public import ColouredCliques
public import HostCorrection

@[expose] public section
noncomputable section
namespace KqR75.ColouredCliques

open Finset

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- A weight perturbation measured in diffuse units is a relative
perturbation for every positive reference weight in the interior. -/
theorem log_repaired_weight {α ℓ d base μ : ℝ}
    (hα : 0 < α) (hℓ : 0 < ℓ) (hd : 0 ≤ d) (hbase : ℓ * α ≤ base)
    (hμ : |μ - base| ≤ d * α) (hsmall : d / ℓ ≤ 1 / 2) :
    |Real.log μ - Real.log base| ≤ 2 * (d / ℓ) := by
  have hbaseε : 0 < base := (mul_pos hℓ hα).trans_le hbase
  have hrel : |μ - base| ≤ (d / ℓ) * base := by
    calc
      _ ≤ d * α := hμ
      _ = (d / ℓ) * (ℓ * α) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hbase (div_nonneg hd hℓ.le)
  exact GreedySchedule.log_difference_of_relative_error hbaseε (div_nonneg hd hℓ.le) hsmall hrel

/-- The seed score of every type has logarithmic size, uniformly over
the profiles with the same diffuse lower and upper coefficients. -/
theorem seed_log_abs_le {n q : ℕ} (colour : Fin n → C) (hq : 2 ≤ q) (hn : q ≤ n)
    (hclasses : ∀ i, q ≤ profile colour univ i)
    (m : TypeProfile C q → ℝ) (ℓ U : ℝ) (hℓ : 0 < ℓ) (hU : 0 < U)
    (hwlo : ∀ b : Clique n q,
      ℓ * HostCorrection.scale n q ≤ ProfileWeights.weight (cliqueType colour) m b)
    (hwhi : ∀ b : Clique n q,
      ProfileWeights.weight (cliqueType colour) m b ≤ U * HostCorrection.scale n q)
    (t : TypeProfile C q) :
    |Real.log (m t / ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ))| ≤
      |Real.log ℓ| + |Real.log U| + (q - 2 : ℕ) * Real.log n := by
  let C₀ : ℝ := (n - 2).choose (q - 2)
  have hC : 1 ≤ C₀ := by
    dsimp [C₀]
    have hc := Nat.choose_pos (by omega : q - 2 ≤ n - 2)
    exact_mod_cast (show 1 ≤ (n - 2).choose (q - 2) from hc)
  have hC₀ : 0 < C₀ := by linarith
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hCN : C₀ ≤ (n : ℝ) ^ (q - 2) := by
    have hle := (Nat.choose_le_pow (n - 2) (q - 2)).trans
      (Nat.pow_le_pow_left (by omega : n - 2 ≤ n) (q - 2))
    dsimp [C₀]
    exact_mod_cast hle
  have hlogC := Real.log_le_log hC₀ hCN
  rw [Real.log_pow] at hlogC
  obtain ⟨b, hb⟩ := card_pos.mp (fibre_pos colour hclasses t)
  have hbt : cliqueType colour b = t := (mem_filter.mp hb).2
  have hlo := hwlo b
  have hhi := hwhi b
  let base := m t / ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ)
  change ℓ * C₀⁻¹ ≤ ProfileWeights.weight (cliqueType colour) m b at hlo
  change ProfileWeights.weight (cliqueType colour) m b ≤ U * C₀⁻¹ at hhi
  simp only [ProfileWeights.weight, hbt] at hlo hhi
  change ℓ * C₀⁻¹ ≤ base at hlo
  change base ≤ U * C₀⁻¹ at hhi
  have hbase := (mul_pos hℓ (inv_pos.mpr hC₀)).trans_le hlo
  have hL := Real.log_le_log (mul_pos hℓ (inv_pos.mpr hC₀)) hlo
  have hH := Real.log_le_log hbase hhi
  rw [Real.log_mul hℓ.ne' (inv_ne_zero hC₀.ne'), Real.log_inv] at hL
  rw [Real.log_mul hU.ne' (inv_ne_zero hC₀.ne'), Real.log_inv] at hH
  have hcLog := Real.log_nonneg hC
  have hnLog := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n) : (1 : ℝ) ≤ n)
  exact abs_le.mpr ⟨by linarith only [hL, hlogC, neg_le_abs (Real.log ℓ), abs_nonneg (Real.log U)],
    by linarith only [hH, hcLog, le_abs_self (Real.log U), abs_nonneg (Real.log ℓ),
      mul_nonneg (Nat.cast_nonneg (α := ℝ) (q - 2)) hnLog]⟩

end KqR75.ColouredCliques

#print axioms KqR75.ColouredCliques.log_repaired_weight
#print axioms KqR75.ColouredCliques.seed_log_abs_le
