module
public import CoverScales

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Filter

/-- The four obstruction terms in the two cover-down phases fit
arbitrarily small fractions of the candidate scales. The same fixed K
controls the two terms with zero residual exponent. -/
theorem eventually_cover_ratios (q : ℕ) (hq : 3 ≤ q) (z : ℝ) (hz : 0 < z)
    (Mstar Mlink Msat Mused cstar cpair : ℝ) (hcstar : 0 < cstar) (hcpair : 0 < cpair) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K : ℝ, K₀ ≤ K → ∀ᶠ n : ℕ in atTop,
      let x : ℝ := n
      let p := K * x ^ (-z)
      let a := (2 * (q : ℝ) - 1) * z
      let s := ((q - 1 : ℕ) : ℝ) * (1 - 2 * z)
      let l := ((q - 2 : ℕ) : ℝ)
      let b := (q - 1).choose 2
      let r := q.choose 2 - 1
      (Mstar * x ^ (((q - 3 : ℕ) : ℝ) + 2 - a) * p ^ (b - 1) <
        cstar * x ^ s * p ^ b) ∧
      (Mlink * x ^ (((q - 3 : ℕ) : ℝ) + 1 - 2 * z) * p ^ (r - 2) <
        cpair * x ^ l * p ^ r) ∧
      (Msat * x ^ (((q - 3 : ℕ) : ℝ) + 1 - a + 2 * z) * p ^ (r - 2) <
        cpair * x ^ l * p ^ r) ∧
      (4 ≤ q → Mused * x ^ (((q - 4 : ℕ) : ℝ) + 2 - a) * p ^ (r - 5) <
        cpair * x ^ l * p ^ r) := by
  let a := (2 * (q : ℝ) - 1) * z
  let s := ((q - 1 : ℕ) : ℝ) * (1 - 2 * z)
  let l := ((q - 2 : ℕ) : ℝ)
  let b := (q - 1).choose 2
  let r := q.choose 2 - 1
  let K₀ := 2 + max 0 (Mstar / cstar) + max 0 (Mlink / cpair)
  have hK₀ : 1 ≤ K₀ := by dsimp [K₀]; linarith [le_max_left 0 (Mstar / cstar), le_max_left 0 (Mlink / cpair)]
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have castSub (j : ℕ) (hj : j ≤ q) : ((q - j : ℕ) : ℝ) = (q : ℝ) - j := Nat.cast_sub hj
  have hs : (((q - 3 : ℕ) : ℝ) + 2 - a) - s + z * ((1 : ℕ) : ℝ) = 0 := by
    dsimp [a, s]
    rw [castSub 3 hq, castSub 1 (by omega)]
    push_cast
    ring
  have hl : (((q - 3 : ℕ) : ℝ) + 1 - 2 * z) - l + z * ((2 : ℕ) : ℝ) = 0 := by
    dsimp [l]
    rw [castSub 3 hq, castSub 2 (by omega)]
    push_cast
    ring
  have hsat : (((q - 3 : ℕ) : ℝ) + 1 - a + 2 * z) - l + z * ((2 : ℕ) : ℝ) < 0 := by
    have hmul := mul_le_mul_of_nonneg_right hqR hz.le
    dsimp [a, l]
    rw [castSub 3 hq, castSub 2 (by omega)]
    push_cast
    nlinarith only [hmul, hz]
  have hused (h4 : 4 ≤ q) : (((q - 4 : ℕ) : ℝ) + 2 - a) - l + z * ((5 : ℕ) : ℝ) < 0 := by
    have hq4 : (4 : ℝ) ≤ q := by exact_mod_cast h4
    have hmul := mul_le_mul_of_nonneg_right hq4 hz.le
    dsimp [a, l]
    rw [castSub 4 h4, castSub 2 (by omega)]
    push_cast
    nlinarith only [hmul, hz]
  have hb : 1 ≤ b := Nat.choose_pos (by omega)
  have hr : 2 ≤ r := by
    have h := Nat.choose_le_choose 2 hq
    norm_num at h
    dsimp [r]
    omega
  have hr' (h4 : 4 ≤ q) : 5 ≤ r := by
    have h : 6 ≤ q.choose 2 :=
      (by decide : 6 ≤ (4 : ℕ).choose 2).trans (Nat.choose_le_choose 2 h4)
    dsimp [r]
    omega
  refine ⟨K₀, hK₀, fun K hK => ?_⟩
  have hK₁ : 1 ≤ K := hK₀.trans hK
  have hKp : 0 < K := by linarith
  have hcs : Mstar / K < cstar := by
    apply (div_lt_iff₀ hKp).mpr
    have h : Mstar / cstar < K := by
      dsimp [K₀] at hK
      linarith [le_max_right 0 (Mstar / cstar), le_max_left 0 (Mlink / cpair)]
    rw [div_lt_iff₀ hcstar] at h
    rwa [mul_comm]
  have hcl : Mlink / K ^ 2 < cpair := by
    apply (div_lt_iff₀ (pow_pos hKp _)).mpr
    have h : Mlink / cpair < K := by
      dsimp [K₀] at hK
      linarith [le_max_left 0 (Mstar / cstar), le_max_right 0 (Mlink / cpair)]
    have hpow : K ≤ K ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hK₁ hKp.le]
    have hh := (div_lt_iff₀ hcpair).mp (h.trans_le hpow)
    rwa [mul_comm]
  have hU : ∀ᶠ n : ℕ in atTop, 4 ≤ q → Mused * (n : ℝ) ^ (((q - 4 : ℕ) : ℝ) + 2 - a) *
      (K * (n : ℝ) ^ (-z)) ^ (r - 5) < cpair * (n : ℝ) ^ l * (K * (n : ℝ) ^ (-z)) ^ r := by
    by_cases h4 : 4 ≤ q
    · filter_upwards [eventually_small_obstruction hKp hcpair (hr' h4) (hused h4)] with n hn
      exact fun _ => hn
    · exact Eventually.of_forall fun _ hh => (h4 hh).elim
  filter_upwards [eventually_small_obstruction hKp hcpair hr hsat,
    hU, eventually_ge_atTop (1 : ℕ)] with n hS hU' hn
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let p := K * (n : ℝ) ^ (-z)
  have hp : 0 < p := mul_pos hKp (Real.rpow_pos_of_pos hn₀ _)
  refine ⟨?_, ?_, hS, hU'⟩
  · have he := obstruction_ratio (z := z) hn₀ hKp
      (((q - 3 : ℕ) : ℝ) + 2 - a) s hb
    dsimp only at he
    rw [hs, Real.rpow_zero, pow_one] at he
    change Mstar * (n : ℝ) ^ (((q - 3 : ℕ) : ℝ) + 2 - a) * p ^ (b - 1) <
      cstar * (n : ℝ) ^ s * p ^ b
    calc
      _ = (Mstar / K) * ((n : ℝ) ^ s * p ^ b) := by
        rw [mul_assoc, he]
        ring
      _ < _ := by
        simpa only [mul_assoc] using mul_lt_mul_of_pos_right hcs
          (mul_pos (Real.rpow_pos_of_pos hn₀ s) (pow_pos hp b))
  · have he := obstruction_ratio (z := z) hn₀ hKp
      (((q - 3 : ℕ) : ℝ) + 1 - 2 * z) l hr
    dsimp only at he
    rw [hl, Real.rpow_zero] at he
    change Mlink * (n : ℝ) ^ (((q - 3 : ℕ) : ℝ) + 1 - 2 * z) * p ^ (r - 2) <
      cpair * (n : ℝ) ^ l * p ^ r
    calc
      _ = (Mlink / K ^ 2) * ((n : ℝ) ^ l * p ^ r) := by
        rw [mul_assoc, he]
        ring
      _ < _ := by
        simpa only [mul_assoc] using mul_lt_mul_of_pos_right hcl
          (mul_pos (Real.rpow_pos_of_pos hn₀ l) (pow_pos hp r))

end KqR75.CoverDown

#print axioms KqR75.CoverDown.eventually_cover_ratios
