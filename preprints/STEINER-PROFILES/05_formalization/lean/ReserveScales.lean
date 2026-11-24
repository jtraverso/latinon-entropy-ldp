module
public import ReserveExistence
public import GreedyScales
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
noncomputable section
namespace KqR75.ReserveRandom

open Filter Finset
open scoped Topology

private theorem nat_mul_rpow (x : ℝ) (hx : 0 < x) (s : ℝ) :
    x * x ^ s = x ^ (1 + s) := by
  rw [Real.rpow_add hx, Real.rpow_one]

private theorem rpow_nat_pow (x : ℝ) (hx : 0 ≤ x) (s : ℝ) (k : ℕ) :
    (x ^ s) ^ k = x ^ (s * k) := by
  rw [Real.rpow_mul hx, Real.rpow_natCast]

/-- An exponential number of cuts is absorbed by a superlinear exponent. -/
private theorem eventually_cut_budget {A a : ℝ} (hA : 0 < A) (ha : 1 < a) :
    ∀ᶠ n : ℕ in atTop,
      (4 : ℝ) ^ n * Real.exp (-(A * (n : ℝ) ^ a)) < 1 / 2 := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - 1)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp hnat
  have hdec := Real.tendsto_exp_neg_atTop_nhds_zero.comp hnat
  filter_upwards [hpow.eventually_ge_atTop ((Real.log 4 + 1) / A),
    hdec.eventually_lt_const (show (0 : ℝ) < 1 / 2 by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hn hsmall hpos
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast hpos
  have hh := mul_le_mul_of_nonneg_left ((div_le_iff₀ hA).mp hn) hn₀.le
  have hprod : (n : ℝ) * (n : ℝ) ^ (a - 1) = (n : ℝ) ^ a := by
    rw [nat_mul_rpow _ hn₀, show 1 + (a - 1) = a by ring]
  have hb : (n : ℝ) * (Real.log 4 + 1) ≤ A * (n : ℝ) ^ a := by
    calc
      _ ≤ (n : ℝ) * ((n : ℝ) ^ (a - 1) * A) := hh
      _ = _ := by rw [← mul_assoc, hprod, mul_comm]
  calc
    _ = Real.exp ((n : ℝ) * Real.log 4 - A * (n : ℝ) ^ a) := by
      rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 4),
        div_eq_mul_inv, Real.exp_neg]
    _ ≤ Real.exp (-(n : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    _ < _ := hsmall

/-- A polynomial number of root tests is absorbed by any positive power
in the exponential tail. -/
private theorem eventually_root_budget (d : ℕ) {B b : ℝ} (hB : 0 < B) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop,
      ((d + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ d *
        (2 * Real.exp (-(B * (n : ℝ) ^ b))) < 1 / 2 := by
  let C : ℝ := ((d + 1 : ℕ) : ℝ) * 2 ^ d * 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ b) atTop atTop :=
    (tendsto_rpow_atTop hb).comp hnat
  have hdec := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((d : ℝ) / b) B hB).comp hpow
  filter_upwards [hdec.eventually_lt_const (show (0 : ℝ) < (1 / 2) / C by positivity),
    eventually_ge_atTop (1 : ℕ)] with n hsmall hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) ≤ n := by linarith
  have hsmall' := (lt_div_iff₀ hC).mp hsmall
  simp only [Function.comp_apply, neg_mul] at hsmall'
  rw [← Real.rpow_mul hn₀, show b * ((d : ℝ) / b) = d by field_simp, Real.rpow_natCast] at hsmall'
  have hmul : ((n : ℝ) + 1) ^ d ≤ (2 * (n : ℝ)) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  calc
    _ ≤ ((d + 1 : ℕ) : ℝ) * (2 * (n : ℝ)) ^ d *
        (2 * Real.exp (-(B * (n : ℝ) ^ b))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmul (by positivity)) (by positivity)
    _ = (n : ℝ) ^ d * Real.exp (-(B * (n : ℝ) ^ b)) * C := by
      rw [mul_pow]
      dsimp [C]
      ring
    _ < _ := hsmall'

/-- At density K n⁻ᶻ, the reserve works simultaneously for all cuts of
size at least ceil(c n^(1−qz)) and all root sets of size at most q−1. -/
theorem eventually_reserve (q : ℕ) (hq : 3 ≤ q) {K c z : ℝ}
    (hK : 0 < K) (hc : 0 < c) (hz : 0 < z) (hgap : (2 * (q : ℝ) + 1) * z < 1) :
    ∀ᶠ n : ℕ in atTop, ∃ (p : unitInterval) (ω : Sym2 (Fin n) → Bool),
      (p : ℝ) = K * (n : ℝ) ^ (-z) ∧
      ReserveCuts.cutLower (adj ω) (p : ℝ) ⌈c * (n : ℝ) ^ (1 - (q : ℝ) * z)⌉₊ ∧
      RootGood p ω (q - 1) := by
  let a : ℝ := 2 - (2 * (q : ℝ) + 1) * z
  let b : ℝ := 1 - z * ((q - 1 : ℕ) : ℝ)
  let A : ℝ := K * c ^ 2 / 36
  let B : ℝ := K ^ (q - 1) / 72
  have ha : 1 < a := by dsimp [a]; linarith
  have hb : 0 < b := by
    have ht : (((q - 1 : ℕ) : ℝ)) ≤ q := by exact_mod_cast Nat.sub_le q 1
    have hqz : 0 ≤ (q : ℝ) * z := by positivity
    have hh := mul_le_mul_of_nonneg_right ht hz.le
    dsimp [b]
    nlinarith only [hgap, hqz, hh, hz]
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hp0 : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-z)) atTop (𝓝 0) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    simpa only [mul_zero, Function.comp_apply] using (tendsto_const_nhds (x := K)).mul
      ((tendsto_rpow_neg_atTop hz).comp hnat)
  filter_upwards [eventually_cut_budget hA ha, eventually_root_budget (q - 1) hB hb,
    hp0.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
    eventually_ge_atTop (max 1 (4 * (q - 1)))] with n hlo hup hpn hn
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one ((le_max_left _ _).trans hn)
  let p : unitInterval := ⟨K * (n : ℝ) ^ (-z), mul_nonneg hK.le (Real.rpow_nonneg hn₀.le _), hpn.le⟩
  let t := ⌈c * (n : ℝ) ^ (1 - (q : ℝ) * z)⌉₊
  have ht : c * (n : ℝ) ^ (1 - (q : ℝ) * z) ≤ (t : ℝ) := Nat.le_ceil _
  have htc : A * (n : ℝ) ^ a ≤ (p : ℝ) * (t : ℝ) ^ 2 / 36 := by
    have hsq := pow_le_pow_left₀ (show 0 ≤ c * (n : ℝ) ^ (1 - (q : ℝ) * z) by positivity) ht 2
    refine le_trans ?_ (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq p.2.1) (by norm_num))
    apply le_of_eq
    change _ = K * (n : ℝ) ^ (-z) * (c * (n : ℝ) ^ (1 - (q : ℝ) * z)) ^ 2 / 36
    rw [mul_pow, rpow_nat_pow _ hn₀.le]
    dsimp [A, a]
    have he : (n : ℝ) ^ (-z) * (n : ℝ) ^ ((1 - (q : ℝ) * z) * (2 : ℕ)) =
        (n : ℝ) ^ (2 - (2 * (q : ℝ) + 1) * z) := by
      rw [← Real.rpow_add hn₀]
      congr 1
      push_cast
      ring
    rw [← he]
    ring
  have htr : (n : ℝ) * (p : ℝ) ^ (q - 1) / 72 = B * (n : ℝ) ^ b := by
    change (n : ℝ) * (K * (n : ℝ) ^ (-z)) ^ (q - 1) / 72 = _
    rw [mul_pow, rpow_nat_pow _ hn₀.le]
    have he : (n : ℝ) * (n : ℝ) ^ ((-z) * ((q - 1 : ℕ) : ℝ)) = (n : ℝ) ^ b := by
      rw [nat_mul_rpow _ hn₀]
      dsimp [b]
      congr 1
      ring
    rw [← he]
    dsimp [B]
    ring
  have hcut : (4 : ℝ) ^ n * Real.exp (-((p : ℝ) * t ^ 2) / 36) < 1 / 2 := by
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)) hlo
    linarith only [htc]
  have hroot : (((q - 1) + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (q - 1) *
      (2 * Real.exp (-((n : ℝ) * (p : ℝ) ^ (q - 1)) / 72)) < 1 / 2 := by
    rw [neg_div, htr]
    exact hup
  have hbudget : (4 : ℝ) ^ n * Real.exp (-((p : ℝ) * t ^ 2) / 36) +
      (((q - 1) + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ (q - 1) *
        (2 * Real.exp (-((n : ℝ) * (p : ℝ) ^ (q - 1)) / 72)) < 1 := by linarith
  obtain ⟨ω, hcut', hroot'⟩ := exists_reserve (V := Fin n) p t (q - 1)
    (by simpa using (le_max_right _ _).trans hn) (by simpa using hbudget)
  exact ⟨p, ω, rfl, hcut', hroot'⟩

/-- Rounding the cut threshold preserves the clique budget for every
admissible clique size and candidate set. -/
private theorem eventually_clique_budget (q : ℕ) (hq : 3 ≤ q) {K D z : ℝ}
    (hK : 0 < K) (hD : 0 < D) (hz : 0 < z) (hgap : (2 * (q : ℝ) + 1) * z < 1) :
    let c := D * (K / 2) ^ (q - 2) / (8 * (q : ℝ) ^ 2)
    ∀ᶠ n : ℕ in atTop,
      let p := K * (n : ℝ) ^ (-z)
      let t := ⌈c * (n : ℝ) ^ (1 - (q : ℝ) * z)⌉₊
      0 < t ∧ ∀ (l : ℕ), 0 < l → l ≤ q - 1 → ∀ m : ℝ,
        D * (n : ℝ) ^ (1 - 2 * z) ≤ m → 2 * (l : ℝ) ≤ m ∧
        (l : ℝ) * t ≤ (m / (4 * (l : ℝ))) * (p / 2) ^ (l - 1) := by
  let c := D * (K / 2) ^ (q - 2) / (8 * (q : ℝ) ^ 2)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hc : 0 < c := by dsimp [c]; positivity
  have hqz : 0 ≤ (q : ℝ) * z := by positivity
  have hqR1 : (1 : ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hqz1 := mul_le_mul_of_nonneg_right hqR1 hz.le
  have hα : 0 < 1 - (q : ℝ) * z := by nlinarith only [hgap, hqz, hz]
  have hβ : 0 < 1 - 2 * z := by nlinarith only [hgap, hqz, hqz1, hz]
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpowα : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - (q : ℝ) * z)) atTop atTop :=
    (tendsto_rpow_atTop hα).comp hnat
  have hpowβ : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - 2 * z)) atTop atTop :=
    (tendsto_rpow_atTop hβ).comp hnat
  have hp0 : Tendsto (fun n : ℕ => K * (n : ℝ) ^ (-z)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (tendsto_const_nhds (x := K)).mul
      ((tendsto_rpow_neg_atTop hz).comp hnat)
  filter_upwards [hpowα.eventually_ge_atTop (1 / c), hpowβ.eventually_ge_atTop (2 * (q : ℝ) / D),
    hp0.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
    eventually_ge_atTop (1 : ℕ)] with n hnα hnβ hp hn
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  let x := c * (n : ℝ) ^ (1 - (q : ℝ) * z)
  let p := K * (n : ℝ) ^ (-z)
  have hx : 1 ≤ x := by
    have h := (div_le_iff₀ hc).mp hnα
    simpa only [x, mul_comm c] using h
  have hlarge : 2 * (q : ℝ) ≤ D * (n : ℝ) ^ (1 - 2 * z) := by
    have h := (div_le_iff₀ hD).mp hnβ
    simpa only [mul_comm D] using h
  have hp₀ : 0 ≤ p / 2 := by dsimp [p]; positivity
  have hp₁ : p / 2 ≤ 1 := by change p < 1 at hp; linarith
  have hpower : (D * (n : ℝ) ^ (1 - 2 * z)) * (p / 2) ^ (q - 2) =
      D * (K / 2) ^ (q - 2) * (n : ℝ) ^ (1 - (q : ℝ) * z) := by
    have hcast : (((q - 2 : ℕ) : ℝ)) = (q : ℝ) - 2 := by
      exact Nat.cast_sub (by omega)
    rw [show p / 2 = (K / 2) * (n : ℝ) ^ (-z) by dsimp [p]; ring, mul_pow,
      rpow_nat_pow _ hn₀.le, hcast]
    have he : (n : ℝ) ^ (1 - 2 * z) * (n : ℝ) ^ (-z * ((q : ℝ) - 2)) =
        (n : ℝ) ^ (1 - (q : ℝ) * z) := by
      rw [← Real.rpow_add hn₀]
      congr 1
      ring
    rw [← he]
    ring
  have hceil : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
    linarith
  have htpos : 0 < ⌈x⌉₊ := by
    have h : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil _
    exact_mod_cast (show (0 : ℝ) < (⌈x⌉₊ : ℝ) by linarith)
  refine ⟨htpos, ?_⟩
  intro l hl hlq m hm
  have hqdom : (l : ℝ) ≤ q := by exact_mod_cast hlq.trans (Nat.sub_le _ _)
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hm0 : 0 ≤ m := (by positivity : 0 ≤ D * (n : ℝ) ^ (1 - 2 * z)).trans hm
  have hm4 : D * (n : ℝ) ^ (1 - 2 * z) / (4 * (q : ℝ)) ≤ m / (4 * (l : ℝ)) :=
    (div_le_div_of_nonneg_right hm (by positivity)).trans
      (div_le_div_of_nonneg_left hm0 (by positivity) (by linarith))
  have hpow : (p / 2) ^ (q - 2) ≤ (p / 2) ^ (l - 1) := by
    have hle : l - 1 ≤ q - 2 := by omega
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
    rw [hj, pow_add]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ hp₀ hp₁)
  refine ⟨by linarith only [hqdom, hlarge, hm], ?_⟩
  change (l : ℝ) * (⌈x⌉₊ : ℝ) ≤ m / (4 * (l : ℝ)) * (p / 2) ^ (l - 1)
  calc
    _ ≤ (q : ℝ) * (2 * x) := mul_le_mul hqdom hceil (by positivity) hqR.le
    _ = (D * (n : ℝ) ^ (1 - 2 * z) / (4 * (q : ℝ))) * (p / 2) ^ (q - 2) := by
      rw [div_mul_eq_mul_div, hpower]
      dsimp [x, c]
      field_simp; ring
    _ ≤ _ := mul_le_mul hm4 hpow (by positivity) (by positivity)

/-- An asymptotic reserve with the lower and upper clique counts used by
cover-down. Root pairs need not themselves be edges of the reserve. -/
theorem eventually_reserve_counts (q : ℕ) (hq : 3 ≤ q) {K c z : ℝ}
    (hK : 0 < K) (hc : 0 < c) (hz : 0 < z) (hgap : (2 * (q : ℝ) + 1) * z < 1) :
    ∀ᶠ n : ℕ in atTop, ∃ (p : unitInterval) (ω : Sym2 (Fin n) → Bool),
      (p : ℝ) = K * (n : ℝ) ^ (-z) ∧ RootGood p ω (q - 1) ∧
      (∀ (S : Finset (Fin n)) (l : ℕ), 0 < l → l ≤ q - 1 →
        c * (n : ℝ) ^ (1 - 2 * z) ≤ S.card →
        ((S.card : ℝ) / (4 * l)) ^ l * ((p : ℝ) / 2) ^ l.choose 2 ≤
          ((ReserveCuts.cliquesIn (adj ω) S l).card : ℝ)) ∧
      (∀ u v : Fin n, u ≠ v →
        let l := q - 2
        ((n : ℝ) * (p : ℝ) ^ 2 / (8 * l)) ^ l * ((p : ℝ) / 2) ^ l.choose 2 ≤
          ((ReserveCuts.rootedExtensions (adj ω) univ u v l).card : ℝ)) ∧
      (∀ (H : Finset (Fin n)) (k : ℕ), H.card + k ≤ q →
        ((ReserveCuts.extensions (adj ω) univ H k).card : ℝ) ≤
          (2 * (n : ℝ)) ^ k * (p : ℝ) ^ (H.card * k + k.choose 2)) := by
  let D := min c (K ^ 2 / 2)
  let c' := D * (K / 2) ^ (q - 2) / (8 * (q : ℝ) ^ 2)
  have hD : 0 < D := lt_min hc (by positivity)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hc' : 0 < c' := by dsimp [c']; positivity
  filter_upwards [eventually_reserve q hq hK hc' hz hgap,
    eventually_clique_budget q hq hK hD hz hgap, eventually_ge_atTop (1 : ℕ)] with n hn hbud hpos
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨p, ω, hp, hcut, hroot⟩ := hn
  obtain ⟨ht, hbud'⟩ := hbud
  have hp₂ : (p : ℝ) ≤ 2 := p.2.2.trans (by norm_num)
  refine ⟨p, ω, hp, hroot, ?_, ?_, ?_⟩
  · intro S l hl hlq hS
    have hDS := (mul_le_mul_of_nonneg_right (min_le_left c (K ^ 2 / 2))
      (Real.rpow_nonneg hn₀.le _)).trans hS
    obtain ⟨hsmall, hcl⟩ := hbud' l hl hlq (S.card : ℝ) hDS
    rw [← hp] at hcl
    exact ReserveCuts.count_cliques_large (adj ω) (p : ℝ) p.2.1 hp₂ ht hcut
      S l hl (by exact_mod_cast hsmall) hcl
  · intro u v huv
    let l := q - 2
    have hl : 0 < l := by dsimp [l]; omega
    have hlq : l ≤ q - 1 := by dsimp [l]; omega
    have hpair : ({u, v} : Finset (Fin n)).card = 2 := by
      simp [card_insert_of_notMem, huv]
    have hlow := (hroot {u, v} (by rw [hpair]; omega)).2 (by rw [hpair])
    rw [ReserveCuts.common_pair_eq, hpair, Fintype.card_fin] at hlow
    have hmass : (n : ℝ) * (p : ℝ) ^ 2 / 2 = K ^ 2 / 2 * (n : ℝ) ^ (1 - 2 * z) := by
      rw [hp, mul_pow, rpow_nat_pow _ hn₀.le]
      have he : (n : ℝ) * (n : ℝ) ^ ((-z) * (2 : ℕ)) = (n : ℝ) ^ (1 - 2 * z) := by
        rw [nat_mul_rpow _ hn₀]
        norm_num
        congr 1
        ring
      rw [← he]
      ring
    have hDm : D * (n : ℝ) ^ (1 - 2 * z) ≤ (n : ℝ) * (p : ℝ) ^ 2 / 2 := by
      rw [hmass]
      exact mul_le_mul_of_nonneg_right (min_le_right c (K ^ 2 / 2)) (Real.rpow_nonneg hn₀.le _)
    obtain ⟨hsmall, hcl⟩ := hbud' l hl hlq _ hDm
    rw [← hp] at hcl
    have hS : 2 * l ≤ (ReserveCuts.commonPair (adj ω) univ u v).card := by
      exact_mod_cast hsmall.trans hlow
    have hb : (l : ℝ) * (⌈c' * (n : ℝ) ^ (1 - (q : ℝ) * z)⌉₊ : ℕ) ≤
        ((n : ℝ) * (p : ℝ) ^ 2 / (8 * l)) * ((p : ℝ) / 2) ^ (l - 1) := by
      convert hcl using 1
      ring
    simpa only [card_univ, Fintype.card_fin] using
      ReserveCuts.count_rooted_extensions (adj ω) (p : ℝ) p.2.1 hp₂ ht hcut
        univ u v l hl hS (by simpa only [card_univ, Fintype.card_fin] using hlow)
        (by simpa only [card_univ, Fintype.card_fin] using hb)
  · intro H k hlim
    have hu (H' : Finset (Fin n)) (_ : H' ⊆ univ) (hk : H'.card < q) :
        ((ReserveCuts.common (adj ω) univ H').card : ℝ) ≤
          2 * ((univ : Finset (Fin n)).card : ℝ) * (p : ℝ) ^ H'.card := by
      simpa only [card_univ] using (hroot H' (by omega)).1
    simpa only [card_univ, Fintype.card_fin] using
      ReserveCuts.extensions_card_le_density (adj ω) (fun v h => h.1 rfl)
        univ (p : ℝ) p.2.1 q hu H (subset_univ _) k hlim

/-- The R75 exponent is in the strict cut-concentration range. -/
theorem critical_cut_gap (q : ℕ) (hq : 3 ≤ q) :
    (2 * (q : ℝ) + 1) * GreedyScales.criticalExponent q < 1 := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hr : (1 : ℝ) ≤ q.choose 2 := by
    exact_mod_cast Nat.choose_pos (show 2 ≤ q by omega)
  let M := (4 * (q.choose 2 : ℝ) - 1) * (2 * (q : ℝ) - 1) + 2
  have hmul := mul_le_mul_of_nonneg_right
    (show (3 : ℝ) ≤ 4 * (q.choose 2 : ℝ) - 1 by linarith) (show 0 ≤ 2 * (q : ℝ) - 1 by linarith)
  have hM : 2 * (q : ℝ) + 1 < M := by dsimp [M]; linarith
  change (2 * (q : ℝ) + 1) * (1 / M) < 1
  rw [mul_one_div]
  exact (div_lt_iff₀ (by linarith : 0 < M)).mpr (by simpa using hM)

end KqR75.ReserveRandom

#print axioms KqR75.ReserveRandom.eventually_reserve
#print axioms KqR75.ReserveRandom.eventually_reserve_counts
#print axioms KqR75.ReserveRandom.critical_cut_gap
