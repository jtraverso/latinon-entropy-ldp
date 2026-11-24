module
public import UpperExceptional

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset ColouredCliques CompleteJohnson SparseGram PhysicalCompletion

/-- A uniform diffuse envelope gives an O(1/n) bound on the total
reference mass of the exceptional candidates through one edge. -/
theorem exceptional_weight_le {n q : ℕ} (hq : 3 ≤ q) (hn : 1 ≤ n)
    (P : Finset (Clique n q)) (hP : packs P univ) (e : Edge n)
    (w : Clique n q → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hw : ∀ b, w b ≤ W / (n : ℝ) ^ (q - 2)) :
    (∑ b ∈ exceptional P e, w b) ≤ (4 * (q.choose 3 : ℝ) * W) / n := by
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hcard : ((exceptional P e).card : ℝ) ≤ 4 * (q.choose 3 : ℝ) * (n : ℝ) ^ (q - 3) := by
    exact_mod_cast exceptional_card_le hq P hP e
  have he : q - 2 = q - 3 + 1 := by omega
  calc
    _ ≤ ∑ _b ∈ exceptional P e, W / (n : ℝ) ^ (q - 2) := sum_le_sum (fun b _ => hw b)
    _ = ((exceptional P e).card : ℝ) * (W / (n : ℝ) ^ (q - 2)) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (4 * (q.choose 3 : ℝ) * (n : ℝ) ^ (q - 3)) * (W / (n : ℝ) ^ (q - 2)) :=
      mul_le_mul_of_nonneg_right hcard (div_nonneg hW (by positivity))
    _ = _ := by
      rw [he, pow_succ]
      field_simp

/-- Convert from the Gram normalization to the elementary power
envelope used to count exceptional cliques. -/
theorem scale_le_power {n q : ℕ} (hq : 2 ≤ q) (hn : 2 * q ≤ n) :
    HostCorrection.scale n q ≤ ((2 : ℝ) ^ (q - 2) * ((q - 2).factorial : ℝ)) /
      (n : ℝ) ^ (q - 2) := by
  let D : ℝ := (n - 2).choose (q - 2)
  let F : ℝ := 2 ^ (q - 2) * ((q - 2).factorial : ℝ)
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast Nat.choose_pos (by omega : q - 2 ≤ n - 2)
  have hF : 0 < F := by dsimp [F]; positivity
  have hb : (n : ℝ) / 2 ≤ (((n - 2 + 1 - (q - 2) : ℕ)) : ℝ) := by
    have h : (n : ℝ) ≤ 2 * (((n - 2 + 1 - (q - 2) : ℕ)) : ℝ) := by
      exact_mod_cast (by omega : n ≤ 2 * (n - 2 + 1 - (q - 2)))
    linarith
  have hc : (n : ℝ) ^ (q - 2) / F ≤ D := by
    calc
      _ = ((n : ℝ) / 2) ^ (q - 2) / ((q - 2).factorial : ℝ) := by
        dsimp only [F]
        rw [div_pow, div_div]
      _ ≤ (((n - 2 + 1 - (q - 2) : ℕ)) : ℝ) ^ (q - 2) / ((q - 2).factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hb _) (by positivity)
      _ ≤ D := by
        simpa only [D, Nat.cast_pow] using (Nat.pow_le_choose (α := ℝ) (q - 2) (n - 2))
  change D⁻¹ ≤ F / (n : ℝ) ^ (q - 2)
  rw [← one_div]
  apply (div_le_div_iff₀ hD (pow_pos hn₀ _)).mpr
  simpa [mul_comm] using (div_le_iff₀ hF).mp hc

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.exceptional_weight_le
#print axioms KqR75.UpperCounting.scale_le_power
