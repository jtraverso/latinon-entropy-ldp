module
public import PhysicalPrefixTargets

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

/-- Sum the scalar errors in the physical history score and the mass
one-half deduction. The expression allows all weight and type constants
to depend on the already chosen completion parameters. -/
theorem prefix_score_error_budget {n T : ℕ} (hn : 2 ≤ n) (hT : 1 ≤ T)
    (M z B V L k j : ℝ) (hz : z ≤ 2)
    (hB : 0 ≤ B) (hV : 0 ≤ V) (hL : 0 ≤ L) (hj : 0 ≤ j)
    (hTup : (T : ℝ) ≤ (n : ℝ) ^ 2)
    (hrem : M - (T : ℝ) ≤ 2 * (n : ℝ) ^ (2 - z)) :
    let X := (n : ℝ) ^ (2 - z)
    M - (T : ℝ) + 1 + Real.log T + (T : ℝ) * (V * (n : ℝ) ^ (-z)) +
      j * (B * X * (L + k * Real.log n)) + Real.log 2 ≤
        ((3 + V) / Real.log 2 + 3 + j * B * (L / Real.log 2 + k)) * (X * Real.log n) := by
  let X := (n : ℝ) ^ (2 - z)
  dsimp only
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hn₂
  have hlog₀ := hlog₂.trans_le hlog
  have hX : 1 ≤ X := Real.one_le_rpow (by linarith) (by linarith)
  have hT₀ : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hTlog := Real.log_le_log hT₀ hTup
  rw [Real.log_pow] at hTlog
  norm_num only [Nat.cast_ofNat] at hTlog
  have hpow : (n : ℝ) ^ 2 * (n : ℝ) ^ (-z) = X := by
    rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hn₀, Nat.cast_ofNat]
    rfl
  have hweights : (T : ℝ) * (V * (n : ℝ) ^ (-z)) ≤ V * X := by
    calc
      _ ≤ (n : ℝ) ^ 2 * (V * (n : ℝ) ^ (-z)) :=
        mul_le_mul_of_nonneg_right hTup (by positivity)
      _ = V * ((n : ℝ) ^ 2 * (n : ℝ) ^ (-z)) := by ring
      _ = _ := by rw [hpow]
  have hfactor : 1 ≤ Real.log n / Real.log 2 :=
    (one_le_div hlog₂).mpr hlog
  have hscale₁ : (3 + V) * X ≤ ((3 + V) / Real.log 2) * (X * Real.log n) := by
    calc
      _ ≤ ((3 + V) * X) * (Real.log n / Real.log 2) :=
        le_mul_of_one_le_right (by positivity) hfactor
      _ = _ := by ring
  have hscale₂ : L + k * Real.log n ≤ (L / Real.log 2 + k) * Real.log n := by
    calc
      _ ≤ L * (Real.log n / Real.log 2) + k * Real.log n :=
        add_le_add (le_mul_of_one_le_right hL hfactor) le_rfl
      _ = _ := by ring
  have hscore : j * (B * X * (L + k * Real.log n)) ≤
      (j * B * (L / Real.log 2 + k)) * (X * Real.log n) := by
    calc
      _ = (j * B * X) * (L + k * Real.log n) := by ring
      _ ≤ (j * B * X) * ((L / Real.log 2 + k) * Real.log n) :=
        mul_le_mul_of_nonneg_left hscale₂ (by positivity)
      _ = _ := by ring
  have hlogs : Real.log T + Real.log 2 ≤ 3 * (X * Real.log n) := by
    nlinarith only [hlog, hTlog, mul_le_mul_of_nonneg_right hX hlog₀.le]
  change M - (T : ℝ) + 1 + Real.log T + (T : ℝ) * (V * (n : ℝ) ^ (-z)) +
      j * (B * X * (L + k * Real.log n)) + Real.log 2 ≤ _
  nlinarith only [hrem, hX, hweights, hscale₁, hscore, hlogs]

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.prefix_score_error_budget
