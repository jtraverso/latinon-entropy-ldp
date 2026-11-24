module
public import DesignProfileCounts
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
noncomputable section
namespace KqR75.ProfileLDP

open Finset Filter Topology ColouredCliques CompleteJohnson PhysicalCompletion

variable {C : Type*} [Fintype C] [DecidableEq C]

abbrev admissibleOrders (q : ℕ) : Filter ℕ := atTop ⊓ 𝓟 {n | admissible q n}

theorem admissibleOrders_neBot (q : ℕ) (hq : 2 ≤ q) : (admissibleOrders q).NeBot := by
  rw [admissibleOrders, ← frequently_mem_iff_neBot, frequently_atTop]
  intro N
  let k := q.choose 2 * (q - 1) * N
  have hk : N ≤ k := by
    have h₁ : 1 ≤ q.choose 2 := Nat.choose_pos hq
    have h₂ : 1 ≤ q - 1 := by omega
    simpa [k] using Nat.mul_le_mul_right N (Nat.mul_pos h₁ h₂)
  refine ⟨2 * k + 1, by omega, ?_⟩
  change admissible q (2 * k + 1)
  have hsub : 2 * k + 1 - 1 = 2 * k := by omega
  have hchoose : (2 * k + 1).choose 2 = (2 * k + 1) * k := by
    rw [Nat.choose_two_right, hsub, show (2 * k + 1) * (2 * k) = ((2 * k + 1) * k) * 2 by ring]
    exact Nat.mul_div_cancel _ (by decide)
  unfold admissible
  rw [hchoose, hsub]
  constructor
  · have hk' : q.choose 2 ∣ k := by
      exact ⟨(q - 1) * N, by simp [k, Nat.mul_assoc]⟩
    exact dvd_mul_of_dvd_right hk' _
  · have hk' : q - 1 ∣ k := by
      exact ⟨q.choose 2 * N, by simp [k, Nat.mul_left_comm, Nat.mul_comm]⟩
    exact dvd_mul_of_dvd_right hk' _

theorem blockMass_square_le {n q : ℕ} (hn : 2 ≤ n) (hq : 2 ≤ q) :
    (n : ℝ) ^ 2 ≤ (4 * (q.choose 2 : ℝ)) * blockMass n q := by
  rw [blockMass, edge_card]
  have hr : (q.choose 2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hq).ne'
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  calc
    (n : ℝ) ^ 2 ≤ 4 * (n.choose 2 : ℝ) := by
      rw [Nat.cast_choose_two ℝ n]
      nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) by positivity) (sub_nonneg.mpr hn')]
    _ = _ := by
      rw [mul_assoc, mul_div_cancel₀ _ hr]

theorem tendsto_blockMass {q : ℕ} (hq : 2 ≤ q) :
    Tendsto (fun n => blockMass n q) atTop atTop := by
  have hr : (0 : ℝ) < 4 * (q.choose 2 : ℝ) := by
    have h : (0 : ℝ) < q.choose 2 := by exact_mod_cast Nat.choose_pos hq
    positivity
  have h := Tendsto.atTop_div_const hr ((tendsto_pow_atTop (n := 2) (by decide)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ)))
  refine tendsto_atTop_mono' _ ?_ h
  filter_upwards [eventually_ge_atTop 2] with n hn
  change (n : ℝ) ^ 2 / (4 * (q.choose 2 : ℝ)) ≤ blockMass n q
  exact (div_le_iff₀ hr).mpr (by rw [mul_comm]; exact blockMass_square_le hn hq)

private theorem eventually_power_budget {q : ℕ} (hq : 2 ≤ q) {f : ℝ → ℝ} {z : ℝ}
    (h : Tendsto (fun x => x ^ (-z) * f x) atTop (𝓝 0))
    (L : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, L * ((n : ℝ) ^ (2 - z) * f n) ≤ blockMass n q * ε := by
  have hr : (0 : ℝ) < 4 * (q.choose 2 : ℝ) := by
    have h : (0 : ℝ) < q.choose 2 := by exact_mod_cast Nat.choose_pos hq
    positivity
  have ht := ((h.const_mul L).comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  simp only [mul_zero] at ht
  filter_upwards [eventually_ge_atTop 2, ht.eventually (ge_mem_nhds (div_pos hε hr))]
    with n hn he
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  change L * ((n : ℝ) ^ (-z) * f n) ≤ ε / (4 * (q.choose 2 : ℝ)) at he
  calc
    _ = (n : ℝ) ^ 2 * (L * ((n : ℝ) ^ (-z) * f n)) := by
      rw [sub_eq_add_neg, Real.rpow_add hn0 (2 : ℝ), Real.rpow_two]
      ring
    _ ≤ (n : ℝ) ^ 2 * (ε / (4 * (q.choose 2 : ℝ))) := by gcongr
    _ ≤ (4 * (q.choose 2 : ℝ) * blockMass n q) * (ε / (4 * (q.choose 2 : ℝ))) :=
      mul_le_mul_of_nonneg_right (blockMass_square_le hn hq) (div_nonneg hε.le hr.le)
    _ = blockMass n q * ε := by
      rw [← mul_div_assoc, mul_assoc, mul_div_cancel_left₀ _ hr.ne']

theorem eventually_upper_budget {q : ℕ} (hq : 3 ≤ q) (L : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, L * (n : ℝ) ^ (2 - 1 / ((q.choose 2 - 1 : ℕ) : ℝ)) ≤
      blockMass n q * ε := by
  have hr : 1 < q.choose 2 :=
    (show 1 < (3 : ℕ).choose 2 by decide).trans_le (Nat.choose_le_choose 2 hq)
  have hz : (0 : ℝ) < 1 / ((q.choose 2 - 1 : ℕ) : ℝ) :=
    one_div_pos.mpr (by exact_mod_cast (Nat.sub_pos_of_lt hr))
  simpa only [mul_one] using eventually_power_budget (by omega : 2 ≤ q)
    (f := fun _ => 1) (by simpa only [mul_one] using tendsto_rpow_neg_atTop hz) L hε

theorem eventually_lower_budget {q : ℕ} (hq : 3 ≤ q) (L : ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, L * ((n : ℝ) ^ (2 - GreedyScales.criticalExponent q) * Real.log n) ≤
      blockMass n q * ε := by
  have hz := (critical_completion_scales q hq).1
  refine eventually_power_budget (by omega : 2 ≤ q) (f := Real.log) ?_ L hε
  have hn : ∀ᶠ x : ℝ in atTop, x ^ GreedyScales.criticalExponent q = 0 → Real.log x = 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact fun he => ((Real.rpow_pos_of_pos hx _).ne' he).elim
  have ht := (Asymptotics.isLittleO_iff_tendsto' hn).mp (isLittleO_log_rpow_atTop hz)
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [div_eq_mul_inv, Real.rpow_neg hx, mul_comm]

theorem eventually_profiles_subexponential (q : ℕ) (hq : 2 ≤ q)
    (colour : (n : ℕ) → Fin n → C) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ((profiles (q := q) (colour n)).card : ℝ) ≤ Real.exp (blockMass n q * ε) := by
  let d : ℝ := Fintype.card (TypeProfile C q)
  let r : ℝ := q.choose 2
  have hr : 0 < r := by dsimp [r]; exact_mod_cast Nat.choose_pos hq
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2, (tendsto_atTop.mp hnat) (8 * r * d / ε)]
    with n hn hs
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log ((n.choose 2 : ℝ) + 1) ≤ 2 * n := by
    have hbase : (n.choose 2 : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by
      rw [Nat.cast_choose_two]
      nlinarith
    calc
      _ ≤ Real.log (((n : ℝ) + 1) ^ 2) := Real.log_le_log (by positivity) hbase
      _ ≤ _ := by
        rw [Real.log_pow]
        norm_num only [Nat.cast_ofNat]
        linarith [Real.log_le_sub_one_of_pos (by positivity : 0 < (n : ℝ) + 1)]
  have hbudget : 2 * n * d ≤ blockMass n q * ε := by
    have h := (div_le_iff₀ hε).mp hs
    have hb := blockMass_square_le hn hq
    change (n : ℝ) ^ 2 ≤ (4 * r) * blockMass n q at hb
    have h₁ := mul_le_mul_of_nonneg_right h (show 0 ≤ (n : ℝ) by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hb hε.le
    have hh : (4 * r) * (2 * n * d) ≤ (4 * r) * (blockMass n q * ε) := by
      linarith only [h₁, h₂]
    exact le_of_mul_le_mul_left hh (by positivity)
  calc
    _ ≤ ((n.choose 2 : ℝ) + 1) ^ Fintype.card (TypeProfile C q) := by
      exact_mod_cast profiles_card_le hq (colour n)
    _ = Real.exp (Real.log ((n.choose 2 : ℝ) + 1) * d) := by
      rw [Real.exp_mul, Real.exp_log (by positivity)]
      exact (Real.rpow_natCast _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right hlog (by positivity)).trans hbudget)

theorem eventually_total_designs {q : ℕ} (hq : 3 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in admissibleOrders q, 0 < (designs q n).card ∧
      Real.exp (blockMass n q * (baseline q n - ε)) ≤ ((designs q n).card : ℝ) ∧
      ((designs q n).card : ℝ) ≤ Real.exp (blockMass n q * (baseline q n + ε)) := by
  obtain ⟨L, _, hCount⟩ :=
    eventually_designFibre_bilateral (C := Unit) q hq 1 1 one_pos one_pos
  apply eventually_inf_principal.mpr
  filter_upwards [eventually_ge_atTop q, hCount,
    eventually_lower_budget hq L hε, eventually_upper_budget hq L hε]
    with n hn hCnt hLo hUp
  intro had
  change admissible q n at had
  obtain ⟨hD, hm, hK⟩ := total_eq_unit_fibre hn (by omega : 2 ≤ q) had
  let m : TypeProfile Unit q → ℤ := fun _ => (n.choose 2 / q.choose 2 : ℕ)
  have hB : 0 < blockMass n q := blockMass_pos (by omega) (by omega)
  have hN (t : TypeProfile Unit q) : normalizedQuota n m t = 1 := (hK t).1
  have hP (t : TypeProfile Unit q) : finiteTypeLaw (fun _ : Fin n => ()) t = 1 := (hK t).2
  have hm' (t : TypeProfile Unit q) : blockMass n q ≤ (m t : ℝ) := by
    have ht : (m t : ℝ) / blockMass n q = 1 := hN t
    exact le_of_eq (by simpa only [one_mul] using ((div_eq_iff hB.ne').mp ht).symm)
  obtain ⟨hp, hl, hu⟩ := hCnt (fun _ => ()) m
    (fun c => by cases c; simp [profile, part]) hm
    (by simpa only [one_mul, blockMass] using hm') had.1 had.2
  have hk₀ : KL (normalizedQuota n m) (finiteTypeLaw (fun _ : Fin n => ())) = 0 := by
    unfold KL
    simp only [hN, hP, div_one, Real.log_one, mul_zero, sum_const_zero]
  change blockMass n q * (baseline q n - KL (normalizedQuota n m)
    (finiteTypeLaw (fun _ : Fin n => ()))) - _ ≤ _ at hl
  change _ ≤ blockMass n q * (baseline q n - KL (normalizedQuota n m)
    (finiteTypeLaw (fun _ : Fin n => ()))) + _ at hu
  rw [hk₀, sub_zero] at hl hu
  have hl' : blockMass n q * baseline q n - L * ((n : ℝ) ^
      (2 - GreedyScales.criticalExponent q) * Real.log n) ≤
      Real.log ((designs q n).card : ℝ) := by
    rw [hD]
    exact hl
  have hu' : Real.log ((designs q n).card : ℝ) ≤ blockMass n q * baseline q n +
      L * (n : ℝ) ^ (2 - 1 / ((q.choose 2 - 1 : ℕ) : ℝ)) := by
    rw [hD]
    exact hu
  have hp' : 0 < (designs q n).card := by rwa [hD]
  have hpR : 0 < ((designs q n).card : ℝ) := by exact_mod_cast hp'
  exact ⟨hp', (Real.le_log_iff_exp_le hpR).mp (by linarith only [hl', hLo]),
    (Real.log_le_iff_le_exp hpR).mp (by linarith only [hu', hUp])⟩

end KqR75.ProfileLDP
