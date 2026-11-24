module
public import StoppingGuard
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
noncomputable section
namespace KqR75.GreedyScales

open Filter Finset MeasureTheory
open scoped Interval Topology

/-- The power-sum bound for the normalized remaining mass. The
initial mass is real, so the estimate also applies to fractional mass. -/
theorem sum_inverse_remaining_power (M s : ℝ) (T : ℕ)
    (hM : 0 < M) (hT : (T : ℝ) < M) (hs : 1 < s) :
    let p := fun i : ℕ => (M - (i : ℝ)) / M
    (∑ i ∈ range T, p i ^ (-s)) ≤ M * p T ^ (1 - s) / (s - 1) := by
  let p (i : ℕ) := (M - (i : ℝ)) / M
  let F (i : ℕ) := p i ^ (1 - s) / (s - 1)
  have hstep (i : ℕ) : p i - p (i + 1) = 1 / M := by
    simp only [p, Nat.cast_add, Nat.cast_one]
    ring
  have hm : 0 < s - 1 := by linarith
  have hterm (i : ℕ) (hi : i ∈ range T) : p i ^ (-s) / M ≤ F (i + 1) - F i := by
    have hiT : ((i + 1 : ℕ) : ℝ) ≤ T := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hi)
    have hp : 0 < p (i + 1) := div_pos (sub_pos.mpr (hiT.trans_lt hT)) hM
    have hle : p (i + 1) ≤ p i := by linarith [hstep i, one_div_pos.mpr hM]
    have hzero : (0 : ℝ) ∉ [[p (i + 1), p i]] := by
      rw [Set.uIcc_of_le hle]
      exact fun h => hp.not_ge h.1
    calc
      _ = ∫ _x in p (i + 1)..p i, p i ^ (-s) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, hstep]
        ring
      _ ≤ ∫ x in p (i + 1)..p i, x ^ (-s) :=
        intervalIntegral.integral_mono_on hle intervalIntegrable_const
          (intervalIntegral.intervalIntegrable_rpow (Or.inr hzero))
          (fun x hx => Real.rpow_le_rpow_of_nonpos (hp.trans_le hx.1) hx.2 (by linarith))
      _ = _ := by
        rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩), show -s + 1 = 1 - s by ring]
        dsimp [F]
        rw [← sub_div]
        exact (div_eq_div_iff (by linarith : 1 - s ≠ 0) hm.ne').mpr (by ring)
  have hsum := sum_le_sum hterm
  rw [← sum_div, sum_range_sub] at hsum
  have hf₀ : 0 ≤ F 0 := by simp [F, p, hM.ne', hm.le]
  change (∑ i ∈ range T, p i ^ (-s)) ≤ _
  calc
    _ ≤ F T * M := (div_le_iff₀ hM).mp (hsum.trans (sub_le_self _ hf₀))
    _ = _ := by dsimp [F, p]; ring

def horizon (M : ℝ) (n : ℕ) (a : ℝ) : ℕ := ⌊M * (1 - (n : ℝ) ^ (-a))⌋₊

/-- The integer horizon preserves the mass lower bound and loses less
than one further block of mass to rounding. -/
theorem horizon_bounds (M : ℝ) (n : ℕ) (a : ℝ) (hM : 0 < M)
    (hn : 1 ≤ n) (ha : 0 ≤ a) :
    let T := horizon M n a
    (T : ℝ) < M ∧ (M - (T : ℝ)) ≤ M * (n : ℝ) ^ (-a) + 1 ∧
    ∀ i : ℕ, i ≤ T → (n : ℝ) ^ (-a) ≤ (M - (i : ℝ)) / M := by
  let p := (n : ℝ) ^ (-a)
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < p := by dsimp [p]; exact Real.rpow_pos_of_pos (by linarith) _
  have hp₁ : p ≤ 1 := by
    dsimp [p]
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < 1 by norm_num) hn₁ (neg_nonpos.mpr ha)
  have harg : 0 ≤ M * (1 - p) := mul_nonneg hM.le (sub_nonneg.mpr hp₁)
  have hfloor : (horizon M n a : ℝ) ≤ M * (1 - p) := Nat.floor_le harg
  have hlo : M * (1 - p) < (horizon M n a : ℝ) + 1 := Nat.lt_floor_add_one _
  have hMp : 0 < M * p := mul_pos hM hp
  refine ⟨?_, ?_, ?_⟩
  · linarith only [hfloor, hMp]
  · linarith only [hlo]
  · intro i hi
    have hic : (i : ℝ) ≤ horizon M n a := by exact_mod_cast hi
    change p ≤ (M - (i : ℝ)) / M
    apply (le_div_iff₀ hM).2
    linarith only [hic, hfloor, mul_comm M p]

/-- The three numerical guards for the stopped physical process follow
uniformly below the horizon from the R75 exponent identity. -/
theorem eventually_guard_scales (r : ℕ) (hr : 1 ≤ r) {a z c b A : ℝ}
    (ha : 0 < a) (hz : 0 < z) (hscale : a * (4 * (r : ℝ) - 1) = 1 - 2 * z)
    (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧
      ∀ (M β : ℝ), c * (n : ℝ) ^ 2 ≤ M → β ≤ b / (n : ℝ) →
      ∀ i ≤ horizon M n a,
        (n : ℝ) ≤ M - (i : ℝ) ∧
        64 * (r : ℝ) ^ 2 * β ≤ ((M - (i : ℝ)) / M) ^ (r - 1) ∧
        16 * (r : ℝ) * (A * (n : ℝ)) ≤
          M * ((M - (i : ℝ)) / M) ^ (4 * r - 1) := by
  have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have ha₁ : 0 < 1 - a := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hr₁)]
  have he : 0 < 1 - a * (r - 1 : ℕ) := by
    rw [Nat.cast_sub hr, Nat.cast_one]
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hr₁)]
  have hmass := ((tendsto_rpow_atTop ha₁).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hcodeg := ((tendsto_rpow_atTop he).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have henergy := ((tendsto_rpow_atTop (show 0 < 2 * z by positivity)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  filter_upwards [eventually_ge_atTop (1 : ℕ), (tendsto_atTop.1 hmass) (1 / c),
    (tendsto_atTop.1 hcodeg) (64 * (r : ℝ) ^ 2 * b),
    (tendsto_atTop.1 henergy) (16 * (r : ℝ) * A / c)] with n hn hnMass hnCodeg hnEnergy
  refine ⟨hn, ?_⟩
  intro M β hM hβ i hi
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hM₀ : 0 < M := (mul_pos hc (by positivity)).trans_le hM
  let p := (M - (i : ℝ)) / M
  have hp := (horizon_bounds M n a hM₀ hn ha.le).2.2 i hi
  have hp₀ : 0 ≤ p := (Real.rpow_nonneg hn₀.le _).trans hp
  have hpPow (j : ℕ) : (n : ℝ) ^ (-a * j) ≤ p ^ j := by
    rw [Real.rpow_mul hn₀.le, Real.rpow_natCast]
    exact pow_le_pow_left₀ (by positivity) hp j
  have hmass_scale : 1 ≤ c * (n : ℝ) ^ (1 - a) := by
    simpa only [Function.comp_apply, mul_comm c] using (div_le_iff₀ hc).mp hnMass
  have heng_scale : 16 * (r : ℝ) * A ≤ c * (n : ℝ) ^ (2 * z) := by
    simpa only [Function.comp_apply, mul_comm c] using (div_le_iff₀ hc).mp hnEnergy
  have henergy_eq : -(a * (4 * r - 1 : ℕ)) + 2 = 1 + 2 * z := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_one]
    norm_num
    linarith only [hscale]
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = (n : ℝ) * 1 := by ring
      _ ≤ (n : ℝ) * (c * (n : ℝ) ^ (1 - a)) :=
        mul_le_mul_of_nonneg_left hmass_scale hn₀.le
      _ = (c * (n : ℝ) ^ 2) * (n : ℝ) ^ (-a) := by
        rw [show 1 - a = 1 + (-a) by ring, Real.rpow_add hn₀, Real.rpow_one]
        ring
      _ ≤ M * p := mul_le_mul hM hp (by positivity) hM₀.le
      _ = _ := by
        rw [mul_comm M p]
        exact div_mul_cancel₀ _ hM₀.ne'
  · calc
      _ ≤ 64 * (r : ℝ) ^ 2 * (b / (n : ℝ)) := mul_le_mul_of_nonneg_left hβ (by positivity)
      _ = (64 * (r : ℝ) ^ 2 * b) / (n : ℝ) := by ring
      _ ≤ (n : ℝ) ^ (1 - a * (r - 1 : ℕ)) / (n : ℝ) :=
        div_le_div_of_nonneg_right hnCodeg hn₀.le
      _ = (n : ℝ) ^ (-a * (r - 1 : ℕ)) := by
        rw [show 1 - a * (r - 1 : ℕ) = 1 + (-a * (r - 1 : ℕ)) by ring,
          Real.rpow_add hn₀, Real.rpow_one]
        exact (div_eq_iff hn₀.ne').mpr (mul_comm _ _)
      _ ≤ _ := hpPow _
  · calc
      _ = (16 * (r : ℝ) * A) * (n : ℝ) := by ring
      _ ≤ (c * (n : ℝ) ^ (2 * z)) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right heng_scale hn₀.le
      _ = (c * (n : ℝ) ^ 2) * (n : ℝ) ^ (-a * (4 * r - 1 : ℕ)) := by
        have hEq : (n : ℝ) ^ (-a * (4 * r - 1 : ℕ)) * (n : ℝ) ^ (2 : ℝ) =
            (n : ℝ) * (n : ℝ) ^ (2 * z) := by
          rw [← Real.rpow_add hn₀, neg_mul, henergy_eq, Real.rpow_add hn₀, Real.rpow_one]
        rw [← Real.rpow_natCast (n : ℝ) 2]
        calc
          _ = c * ((n : ℝ) * (n : ℝ) ^ (2 * z)) := by ring
          _ = _ := by rw [← hEq]; ring
      _ ≤ _ := mul_le_mul hM (hpPow _) (by positivity) hM₀.le

def criticalExponent (q : ℕ) : ℝ := 1 / ((4 * (q.choose 2 : ℝ) - 1) * (2 * (q : ℝ) - 1) + 2)

theorem criticalExponent_bounds (q : ℕ) (hq : 3 ≤ q) :
    let z := criticalExponent q
    let a := (2 * (q : ℝ) - 1) * z
    0 < z ∧ z ≤ 1 ∧ 0 < a ∧ a * (4 * (q.choose 2 : ℝ) - 1) = 1 - 2 * z := by
  let L := (4 * (q.choose 2 : ℝ) - 1) * (2 * (q : ℝ) - 1) + 2
  have hr : (1 : ℝ) ≤ q.choose 2 := by exact_mod_cast Nat.choose_pos (show 2 ≤ q by omega)
  have hq' : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hfactor : 0 ≤ (4 * (q.choose 2 : ℝ) - 1) * (2 * (q : ℝ) - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hL : 0 < L := by dsimp [L]; linarith
  have hL₁ : 1 ≤ L := by dsimp [L]; linarith
  change 0 < 1 / L ∧ 1 / L ≤ 1 ∧ 0 < (2 * (q : ℝ) - 1) * (1 / L) ∧
    ((2 * (q : ℝ) - 1) * (1 / L)) * (4 * (q.choose 2 : ℝ) - 1) = 1 - 2 * (1 / L)
  refine ⟨one_div_pos.mpr hL, (div_le_iff₀ hL).2 (by simpa only [one_mul] using hL₁),
    mul_pos (by linarith) (one_div_pos.mpr hL), ?_⟩
  field_simp [hL.ne']
  dsimp [L]
  ring

/-- Summing a power envelope up to any prefix of the horizon gives the
precise exponent used in the drift and quadratic-variation estimates. -/
theorem scaled_sum_at_prefix (n T : ℕ) (M C a s b : ℝ)
    (hn : 1 ≤ n) (hM : 0 < M) (hbound : M ≤ C * (n : ℝ) ^ 2)
    (ha : 0 ≤ a) (hs : 1 < s) (hT : T ≤ horizon M n a) :
    (n : ℝ) ^ b * (∑ i ∈ range T, ((M - (i : ℝ)) / M) ^ (-s)) ≤
      C / (s - 1) * (n : ℝ) ^ (2 + b + a * (s - 1)) := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  obtain ⟨hT₀, _, hT₁⟩ := horizon_bounds M n a hM hn ha
  have hT' : (T : ℝ) < M := (Nat.cast_le.mpr hT).trans_lt hT₀
  have hp : (n : ℝ) ^ (-a) ≤ (M - (T : ℝ)) / M := hT₁ T hT
  have hpow : (((M - (T : ℝ)) / M) ^ (1 - s)) ≤ (n : ℝ) ^ (a * (s - 1)) := by
    calc
      _ ≤ ((n : ℝ) ^ (-a)) ^ (1 - s) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hn₀ _) hp (by linarith)
      _ = _ := by rw [← Real.rpow_mul hn₀.le]; congr 1; ring
  have hsum := sum_inverse_remaining_power M s T hM hT' hs
  calc
    _ ≤ (n : ℝ) ^ b * (M * (((M - (T : ℝ)) / M) ^ (1 - s)) / (s - 1)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (n : ℝ) ^ b * ((C * (n : ℝ) ^ 2) * (n : ℝ) ^ (a * (s - 1)) / (s - 1)) := by
      gcongr
      exact hM.le.trans hbound
    _ = _ := by
      rw [Real.rpow_add hn₀, Real.rpow_add hn₀, Real.rpow_two]
      ring

/-- The four envelopes summed in the type drift. The last exponent
is kept exact because the same sum controls quadratic variation. -/
theorem type_drift_sums (n T r : ℕ) (M C a z : ℝ) (hn : 1 ≤ n) (hr : 2 ≤ r)
    (hM : 0 < M) (hC : 0 ≤ C) (hbound : M ≤ C * (n : ℝ) ^ 2)
    (ha : 0 ≤ a) (_hz : 0 ≤ z) (hscale : a * (4 * (r : ℝ) - 1) = 1 - 2 * z)
    (hT : T ≤ horizon M n a) :
    let S := fun s : ℝ => ∑ i ∈ range T, ((M - (i : ℝ)) / M) ^ (-s)
    (n : ℝ) ^ (-3 : ℝ) * S (4 * r) ≤ C / (4 * (r : ℝ) - 1) * (n : ℝ) ^ (-2 * z) ∧
    (n : ℝ) ^ (-5 / 2 : ℝ) * S (2 * r + 1 / 2) ≤
      C / (2 * (r : ℝ) - 1 / 2) * (n : ℝ) ^ (-z) ∧
    (n : ℝ) ^ (-3 : ℝ) * S r ≤ C / ((r : ℝ) - 1) * (n : ℝ) ^ (-z) ∧
    ((n : ℝ) ^ (-4 : ℝ) * S (2 * r) ≤
      C / (2 * (r : ℝ) - 1) * (n : ℝ) ^ (-2 + a * (2 * (r : ℝ) - 1))) ∧
    -2 + a * (2 * (r : ℝ) - 1) ≤ -z := by
  let S (s : ℝ) := ∑ i ∈ range T, ((M - (i : ℝ)) / M) ^ (-s)
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsum (s b : ℝ) (hs : 1 < s) :
      (n : ℝ) ^ b * S s ≤ C / (s - 1) * (n : ℝ) ^ (2 + b + a * (s - 1)) :=
    scaled_sum_at_prefix n T M C a s b hn hM hbound ha hs hT
  have hexp (s b e : ℝ) (hs : 1 < s) (he : 2 + b + a * (s - 1) ≤ e) :
      (n : ℝ) ^ b * S s ≤ C / (s - 1) * (n : ℝ) ^ e :=
    (hsum s b hs).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn' he)
      (div_nonneg hC (by linarith)))
  have hlast : -2 + a * (2 * (r : ℝ) - 1) ≤ -z := by
    nlinarith [mul_nonneg ha (show 0 ≤ (r : ℝ) by linarith)]
  refine ⟨?_, ?_, ?_, ?_, hlast⟩
  · exact hexp (4 * r) (-3) (-2 * z) (by linarith) (by linarith only [hscale])
  · have hd : 2 * (r : ℝ) + 1 / 2 - 1 = 2 * (r : ℝ) - 1 / 2 := by ring
    simpa only [hd] using hexp (2 * r + 1 / 2) (-5 / 2) (-z) (by linarith)
      (by rw [hd]; linarith only [hscale])
  · exact hexp r (-3) (-z) (by linarith)
      (by nlinarith [mul_nonneg ha (show 0 ≤ (r : ℝ) by linarith)])
  · exact hexp (2 * r) (-4) (-2 + a * (2 * r - 1)) (by linarith) (by linarith)

end KqR75.GreedyScales

#print axioms KqR75.GreedyScales.sum_inverse_remaining_power
#print axioms KqR75.GreedyScales.horizon_bounds
#print axioms KqR75.GreedyScales.eventually_guard_scales
#print axioms KqR75.GreedyScales.criticalExponent_bounds
#print axioms KqR75.GreedyScales.scaled_sum_at_prefix
#print axioms KqR75.GreedyScales.type_drift_sums
