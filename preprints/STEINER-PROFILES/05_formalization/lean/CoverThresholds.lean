module
public import CoverRatios

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Filter
open scoped Topology

/-- Integer thresholds for both phases. The same bound on the number
of saturated vertices works for the reserve degree and for the potential. -/
theorem eventually_cover_thresholds (q : ℕ) (hq : 3 ≤ q) (z c M : ℝ)
    (hz : 0 < z) (hc : 0 < c) (hM : 0 ≤ M) (hgap : (2 * (q : ℝ) + 1) * z < 1) :
    let a := (2 * (q : ℝ) - 1) * z
    let β := 1 - 2 * z
    let γ := 1 - a + 2 * z
    let D := 1 + 4 * ((q.choose 2 : ℝ) + (q - 2 : ℕ)) * M
    let P := 2 + ((q - 2 : ℕ) : ℝ) * (2 * c + 1)
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, (N : ℝ) ≤ M * (n : ℝ) ^ (2 - a) →
      let x : ℝ := n
      let B := q.choose 2 * N
      let dL := ⌈2 * c * x ^ β⌉₊
      let dY := ⌈x ^ β⌉₊
      let cap := dY + (q - 2) * dL
      let m := ⌈c * x ^ β⌉₊
      let zmax := ⌈D * x ^ γ⌉₊
      q - 2 ≤ dY ∧ q - 1 ≤ cap ∧ m + zmax ≤ dL + 1 ∧
      2 * B ≤ zmax * (dY - (q - 2) + 1) ∧
      2 * (B + (q - 2) * N) ≤ zmax * (cap - (q - 1) + 1) ∧
      (zmax : ℝ) ≤ (D + 1) * x ^ γ ∧ (cap : ℝ) ≤ P * x ^ β := by
  let a := (2 * (q : ℝ) - 1) * z
  let β := 1 - 2 * z
  let γ := 1 - a + 2 * z
  let D := 1 + 4 * ((q.choose 2 : ℝ) + (q - 2 : ℕ)) * M
  let P := 2 + ((q - 2 : ℕ) : ℝ) * (2 * c + 1)
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hmul := mul_le_mul_of_nonneg_right hqR hz.le
  have hβ : 0 < β := by dsimp [β]; nlinarith only [hgap, hmul, hz]
  have hγ : 0 < γ := by dsimp [γ, a]; nlinarith only [hgap, hz]
  have hγβ : γ - β < 0 := by dsimp [γ, β, a]; nlinarith only [hmul, hz]
  have hD : 0 < D := by dsimp [D]; positivity
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hbig : Tendsto (fun n : ℕ => (n : ℝ) ^ β) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp hnat
  have hpow := tendsto_rpow_neg_atTop (neg_pos.mpr hγβ)
  simp only [neg_neg] at hpow
  have hsmall₀ : Tendsto (fun n : ℕ => (n : ℝ) ^ (γ - β)) atTop (𝓝 0) := hpow.comp hnat
  have hsmall : Tendsto (fun n : ℕ => (D + 1) * (n : ℝ) ^ (γ - β)) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hsmall₀
  filter_upwards [hbig.eventually_ge_atTop (2 * ((q - 1 : ℕ) : ℝ)),
    hsmall.eventually_lt_const hc, eventually_ge_atTop (1 : ℕ)] with n hlarge hsmall' hn
  intro N hN
  let x : ℝ := n
  let B := q.choose 2 * N
  let dL := ⌈2 * c * x ^ β⌉₊
  let dY := ⌈x ^ β⌉₊
  let cap := dY + (q - 2) * dL
  let m := ⌈c * x ^ β⌉₊
  let zmax := ⌈D * x ^ γ⌉₊
  have hx₁ : 1 ≤ x := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hx : 0 < x := by linarith
  have hxβ : 1 ≤ x ^ β := Real.one_le_rpow hx₁ hβ.le
  have hxγ : 1 ≤ x ^ γ := Real.one_le_rpow hx₁ hγ.le
  have hdy : x ^ β ≤ (dY : ℝ) := Nat.le_ceil _
  have hstep : q - 1 ≤ dY := by
    have hl : (2 : ℝ) * ((q - 1 : ℕ) : ℝ) ≤ (dY : ℝ) := (show _ ≤ x ^ β from hlarge).trans hdy
    exact_mod_cast (show ((q - 1 : ℕ) : ℝ) ≤ (dY : ℝ) by linarith)
  have hdcap : q - 1 ≤ cap := hstep.trans (Nat.le_add_right _ _)
  have hD1 : x ^ β / 2 ≤ ((dY - (q - 2) + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]
    have hcast : (((q - 2 : ℕ) : ℝ)) ≤ ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (show q - 2 ≤ q - 1 by omega)
    linarith only [hcast, hdy, hlarge]
  have hD2 : x ^ β / 2 ≤ ((cap - (q - 1) + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub hdcap, Nat.cast_one]
    have hdycap : (dY : ℝ) ≤ cap := by exact_mod_cast (Nat.le_add_right dY ((q - 2) * dL))
    linarith only [hdycap, hdy, hlarge]
  have hzlo : D * x ^ γ ≤ (zmax : ℝ) := Nat.le_ceil _
  have hzup : (zmax : ℝ) ≤ (D + 1) * x ^ γ := by
    have ht := Nat.ceil_lt_add_one (show 0 ≤ D * x ^ γ by positivity)
    linarith only [ht, hxγ]
  have hZsmall : (zmax : ℝ) ≤ c * x ^ β := by
    have hh := mul_le_mul_of_nonneg_right hsmall'.le (Real.rpow_nonneg hx.le β)
    change (D + 1) * x ^ (γ - β) * x ^ β ≤ c * x ^ β at hh
    rw [mul_assoc, ← Real.rpow_add hx, show γ - β + β = γ by ring] at hh
    exact hzup.trans hh
  have hm : (m : ℝ) ≤ c * x ^ β + 1 := (Nat.ceil_lt_add_one (show 0 ≤ c * x ^ β by positivity)).le
  have hdL : 2 * c * x ^ β ≤ (dL : ℝ) := Nat.le_ceil _
  have hmdL : m + zmax ≤ dL + 1 := by
    exact_mod_cast (show (m : ℝ) + zmax ≤ (dL : ℝ) + 1 by linarith only [hm, hZsmall, hdL])
  have hscale : x ^ γ * x ^ β = x ^ (2 - a) := by
    rw [← Real.rpow_add hx, show γ + β = 2 - a by dsimp [γ, β]; ring]
  have hbudget : 2 * ((B : ℝ) + ((q - 2 : ℕ) : ℝ) * N) ≤ (D / 2) * x ^ (2 - a) := by
    have hcoef : 2 * ((q.choose 2 : ℝ) + (q - 2 : ℕ)) * M ≤ D / 2 := by dsimp [D]; linarith
    dsimp [B]
    push_cast
    calc
      _ = (2 * ((q.choose 2 : ℝ) + (q - 2 : ℕ))) * (N : ℝ) := by ring
      _ ≤ (2 * ((q.choose 2 : ℝ) + (q - 2 : ℕ))) * (M * x ^ (2 - a)) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
      _ = (2 * ((q.choose 2 : ℝ) + (q - 2 : ℕ)) * M) * x ^ (2 - a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (by positivity)
  have hproduct (d : ℕ) (hd : x ^ β / 2 ≤ (d : ℝ)) :
      2 * (B + (q - 2) * N) ≤ zmax * d := by
    have h := mul_le_mul hzlo hd (show 0 ≤ x ^ β / 2 by positivity) (Nat.cast_nonneg _)
    have hh : D * x ^ γ * (x ^ β / 2) = (D / 2) * x ^ (2 - a) := by rw [← hscale]; ring
    rw [hh] at h
    exact_mod_cast hbudget.trans h
  have hUpY : (dY : ℝ) ≤ 2 * x ^ β := by
    have ht := Nat.ceil_lt_add_one (Real.rpow_nonneg hx.le β)
    linarith only [ht, hxβ]
  have hUpL : (dL : ℝ) ≤ (2 * c + 1) * x ^ β := by
    have ht := Nat.ceil_lt_add_one (show 0 ≤ 2 * c * x ^ β by positivity)
    nlinarith only [ht, hxβ]
  have hUpP : (cap : ℝ) ≤ P * x ^ β := by
    dsimp [cap, P]
    push_cast
    have hh := mul_le_mul_of_nonneg_left hUpL (Nat.cast_nonneg (q - 2))
    nlinarith only [hUpY, hh]
  change q - 2 ≤ dY ∧ q - 1 ≤ cap ∧ m + zmax ≤ dL + 1 ∧
    2 * B ≤ zmax * (dY - (q - 2) + 1) ∧
    2 * (B + (q - 2) * N) ≤ zmax * (cap - (q - 1) + 1) ∧
    (zmax : ℝ) ≤ (D + 1) * x ^ γ ∧ (cap : ℝ) ≤ P * x ^ β
  refine ⟨by omega, hdcap, hmdL, ?_, hproduct _ hD2, hzup, hUpP⟩
  exact (Nat.mul_le_mul_left 2 (Nat.le_add_right _ _)).trans (hproduct _ hD1)

end KqR75.CoverDown

#print axioms KqR75.CoverDown.eventually_cover_thresholds
