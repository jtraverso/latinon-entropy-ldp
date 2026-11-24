module
public import ReserveScales

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Filter
open scoped Topology

/-- Normalize a forbidden-family estimate by the scale of the candidate family.
The loss of j powers of reserve density contributes n^(z*j)/K^j. -/
theorem obstruction_ratio {x K z : ℝ} (hx : 0 < x) (hK : 0 < K)
    (s u : ℝ) {b j : ℕ} (hj : j ≤ b) :
    let p := K * x ^ (-z)
    x ^ s * p ^ (b - j) =
      (x ^ u * p ^ b) * (x ^ (s - u + z * (j : ℝ)) / K ^ j) := by
  let p := K * x ^ (-z)
  have hp : 0 < p := mul_pos hK (Real.rpow_pos_of_pos hx _)
  have hd : p ^ (b - j) = p ^ b / p ^ j := by
    apply (eq_div_iff (pow_ne_zero _ hp.ne')).mpr
    rw [← pow_add, Nat.sub_add_cancel hj]
  have hpj : p ^ j = K ^ j * (x ^ (z * (j : ℝ)))⁻¹ := by
    dsimp [p]
    rw [mul_pow, ← Real.rpow_natCast (x ^ (-z)) j, ← Real.rpow_mul hx.le, neg_mul, Real.rpow_neg hx.le]
  have hexp : x ^ s * x ^ (z * (j : ℝ)) = x ^ u * x ^ (s - u + z * (j : ℝ)) := by
    rw [← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    ring
  calc
    _ = (x ^ s * x ^ (z * (j : ℝ))) * p ^ b / K ^ j := by
      change x ^ s * p ^ (b - j) = _
      rw [hd, hpj]
      field_simp [hK.ne', (Real.rpow_pos_of_pos hx _).ne']
    _ = _ := by rw [hexp]; ring

/-- Strictly negative residual exponents make the corresponding
obstruction families negligible after reserving any fixed fraction
of the candidate count. -/
theorem eventually_small_obstruction {s u z K M c : ℝ} {b j : ℕ}
    (hK : 0 < K) (hc : 0 < c) (hj : j ≤ b)
    (hgap : s - u + z * (j : ℝ) < 0) :
    ∀ᶠ n : ℕ in atTop,
      let p := K * (n : ℝ) ^ (-z)
      M * (n : ℝ) ^ s * p ^ (b - j) < c * (n : ℝ) ^ u * p ^ b := by
  let A : ℝ := M / K ^ j
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hdec : Tendsto (fun n : ℕ => (n : ℝ) ^ (s - u + z * (j : ℝ))) atTop (𝓝 0) := by
    have hpow := tendsto_rpow_neg_atTop (neg_pos.mpr hgap)
    simp only [neg_neg] at hpow
    exact hpow.comp hnat
  have ht : Tendsto (fun n : ℕ => A * (n : ℝ) ^ (s - u + z * (j : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hdec
  filter_upwards [ht.eventually_lt_const hc, eventually_ge_atTop (1 : ℕ)] with n hsmall hn
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  let p := K * (n : ℝ) ^ (-z)
  have hp : 0 < p := mul_pos hK (Real.rpow_pos_of_pos hn₀ _)
  change M * (n : ℝ) ^ s * p ^ (b - j) < c * (n : ℝ) ^ u * p ^ b
  rw [mul_assoc, show (n : ℝ) ^ s * p ^ (b - j) = _ from obstruction_ratio (z := z) hn₀ hK s u hj]
  calc
    _ = (A * (n : ℝ) ^ (s - u + z * (j : ℝ))) * ((n : ℝ) ^ u * p ^ b) := by
      dsimp [A]
      ring
    _ < _ := by
      simpa only [mul_assoc] using mul_lt_mul_of_pos_right hsmall
        (mul_pos (Real.rpow_pos_of_pos hn₀ u) (pow_pos hp _))

end KqR75.CoverDown

#print axioms KqR75.CoverDown.obstruction_ratio
#print axioms KqR75.CoverDown.eventually_small_obstruction
