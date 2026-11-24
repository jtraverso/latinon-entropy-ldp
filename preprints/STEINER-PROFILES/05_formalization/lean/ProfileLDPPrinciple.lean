/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-!
# A finite-profile large-deviation principle
The abstract counting argument and relative-entropy estimates are adapted
from Paper II, ColourStatsLower/ExtAsmLDP.lean and ColourStats/Statements.lean,
source revision 8f004aa5b6bb9bb6cb76bd1cb266968942fd50d2.
-/

@[expose] public section

noncomputable section
namespace KqR75.ProfileLDP

open Finset Filter Topology

/-- Large deviations in counting form. `count n A` counts the objects of size `n` whose
normalised statistic lies in `A`, out of `total n`; the speed is `speed n`, the feasible set
`Feas` and the rate `I` on it (the rate is `+∞` off `Feas`). -/
def CountLDP {ι : Type*} [Fintype ι] (adm : ℕ → Prop) (total : ℕ → ℝ)
    (count : ℕ → Set (ι → ℝ) → ℝ) (speed : ℕ → ℝ) (Feas : Set (ι → ℝ))
    (I : (ι → ℝ) → ℝ) : Prop :=
  (∀ F : Set (ι → ℝ), IsClosed F → ∀ r : ℝ, (∀ Q ∈ F, Q ∈ Feas → r < I Q) →
      ∀ᶠ n in atTop, adm n → count n F ≤ total n * Real.exp (-(speed n * r))) ∧
    ∀ U : Set (ι → ℝ), IsOpen U → ∀ Q ∈ U, Q ∈ Feas → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, adm n → total n * Real.exp (-(speed n * (I Q + ε))) ≤ count n U

/-- Relative entropy `D(Q‖P) = Σ Q log(Q/P)`, with `0 log(0/P) = 0`. -/
noncomputable def KL {ι : Type*} [Fintype ι] (Q P : ι → ℝ) : ℝ :=
  ∑ i, Q i * Real.log (Q i / P i)

variable {ι : Type*} [Fintype ι]

/-! ### Relative entropy -/

/-- `Σ_i (Q_i log Q_i − Q_i log P_i)`: the relative entropy when `P` has no zero entry. -/
noncomputable def KLf (Q P : ι → ℝ) : ℝ := ∑ i, (Q i * Real.log (Q i) - Q i * Real.log (P i))

theorem KL_eq_KLf {Q P : ι → ℝ} (hP : ∀ i, P i ≠ 0) : KL Q P = KLf Q P := by
  unfold KL KLf
  refine sum_congr rfl fun i _ => ?_
  by_cases hQ : Q i = 0
  · simp [hQ]
  · rw [Real.log_div hQ (hP i)]; ring

theorem continuous_KLf_left (P : ι → ℝ) : Continuous fun Q => KLf Q P := by
  unfold KLf
  refine continuous_finsetSum _ fun i _ => ?_
  exact (Real.continuous_mul_log.comp (continuous_apply i)).sub
    ((continuous_apply i).mul continuous_const)

theorem continuous_KL_left {P : ι → ℝ} (hP : ∀ i, P i ≠ 0) : Continuous fun Q => KL Q P := by
  have : (fun Q => KL Q P) = fun Q => KLf Q P := funext fun Q => KL_eq_KLf hP
  rw [this]; exact continuous_KLf_left P

theorem tendsto_KLf {l : Filter ℕ} {Qs Ps : ℕ → ι → ℝ} {Q P : ι → ℝ} (hQ : Tendsto Qs l (𝓝 Q))
    (hPs : Tendsto Ps l (𝓝 P)) (hP : ∀ i, P i ≠ 0) :
    Tendsto (fun n => KLf (Qs n) (Ps n)) l (𝓝 (KLf Q P)) := by
  unfold KLf
  refine tendsto_finsetSum _ fun i _ => ?_
  have hQi : Tendsto (fun n => Qs n i) l (𝓝 (Q i)) := tendsto_pi_nhds.mp hQ i
  have hPi : Tendsto (fun n => Ps n i) l (𝓝 (P i)) := tendsto_pi_nhds.mp hPs i
  have h1 : Tendsto (fun n => Qs n i * Real.log (Qs n i)) l (𝓝 (Q i * Real.log (Q i))) :=
    (Real.continuous_mul_log.tendsto (Q i)).comp hQi
  have h2 : Tendsto (fun n => Real.log (Ps n i)) l (𝓝 (Real.log (P i))) :=
    ((Real.continuousAt_log (hP i)).tendsto).comp hPi
  exact h1.sub (hQi.mul h2)

/-- On the box, changing `P` changes the relative entropy by at most `Σ |log P' − log P|`. -/
theorem abs_KLf_sub_le {Q : ι → ℝ} (hQ : Q ∈ Set.Icc (0 : ι → ℝ) 1) (P P' : ι → ℝ) :
    |KLf Q P' - KLf Q P| ≤ ∑ i, |Real.log (P' i) - Real.log (P i)| := by
  unfold KLf
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  have h0 : 0 ≤ Q i := hQ.1 i
  have h1 : Q i ≤ 1 := hQ.2 i
  have e : Q i * Real.log (Q i) - Q i * Real.log (P' i) - (Q i * Real.log (Q i) - Q i * Real.log (P i))
      = -(Q i * (Real.log (P' i) - Real.log (P i))) := by ring
  rw [e, abs_neg, abs_mul, abs_of_nonneg h0]
  calc Q i * |Real.log (P' i) - Real.log (P i)| ≤ 1 * |Real.log (P' i) - Real.log (P i)| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = _ := one_mul _

/-- If `P_n → P` with `P` without zero entries, then eventually `Σ |log P_n − log P| ≤ ε`. -/
theorem eventually_sum_log_le {l : Filter ℕ} {Ps : ℕ → ι → ℝ} {P : ι → ℝ} (hPs : Tendsto Ps l (𝓝 P))
    (hP : ∀ i, P i ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in l, ∑ i, |Real.log (Ps n i) - Real.log (P i)| ≤ ε := by
  have h : Tendsto (fun n => ∑ i, |Real.log (Ps n i) - Real.log (P i)|) l
      (𝓝 (∑ i : ι, |Real.log (P i) - Real.log (P i)|)) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    have hPi : Tendsto (fun n => Ps n i) l (𝓝 (P i)) := tendsto_pi_nhds.mp hPs i
    exact (((Real.continuousAt_log (hP i)).tendsto.comp hPi).sub tendsto_const_nhds).abs
  simp only [sub_self, abs_zero, sum_const_zero] at h
  exact (h.eventually (ge_mem_nhds hε))

/-! ### The gap on closed sets -/

omit [Fintype ι] in
/-- **The rate gap.** Let `F` be closed, `I` and `d ≥ 0` continuous, and suppose that every
point of `F` in the box `[0, 1]^ι` with `d = 0` has `I > r`. Then for some `c > 0`, every point
of `F` in the box with `d ≤ c` has `I ≥ r + 2c`. -/
theorem closed_gap {F : Set (ι → ℝ)} (hF : IsClosed F) {I d : (ι → ℝ) → ℝ}
    (hI : Continuous I) (hd : Continuous d) (hd0 : ∀ Q, 0 ≤ d Q) {r : ℝ}
    (hr : ∀ Q ∈ F, Q ∈ Set.Icc (0 : ι → ℝ) 1 → d Q = 0 → r < I Q) :
    ∃ c : ℝ, 0 < c ∧ ∀ Q ∈ F, Q ∈ Set.Icc (0 : ι → ℝ) 1 → d Q ≤ c → r + 2 * c ≤ I Q := by
  set K := F ∩ Set.Icc (0 : ι → ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_Icc.inter_left hF
  rcases K.eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun Q hQ hb _ => ?_⟩
    have : Q ∈ K := ⟨hQ, hb⟩
    rw [he] at this; exact absurd this (Set.notMem_empty Q)
  set ψ : (ι → ℝ) → ℝ := fun Q => max (d Q) (I Q - r) with hψ
  have hψc : Continuous ψ := hd.max (hI.sub continuous_const)
  obtain ⟨Q₀, hQ₀, hmin⟩ := hKc.exists_isMinOn hne hψc.continuousOn
  have hm : 0 < ψ Q₀ := by
    rcases (hd0 Q₀).eq_or_lt with h0 | h0
    · have := hr Q₀ hQ₀.1 hQ₀.2 h0.symm
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · exact lt_of_lt_of_le h0 (le_max_left _ _)
  refine ⟨ψ Q₀ / 2, by positivity, fun Q hQ hb hdQ => ?_⟩
  have hge : ψ Q₀ ≤ ψ Q := hmin ⟨hQ, hb⟩
  have hlt : d Q < ψ Q₀ := by linarith
  have : ψ Q₀ ≤ I Q - r := by
    rcases le_max_iff.mp hge with h | h
    · exact absurd h (not_le.mpr hlt)
    · exact h
  linarith

/-! ### The abstract large-deviation principle -/

open Classical in
/-- **Large deviations from counting bounds.** -/
theorem countLDP_of_bounds {adm : ℕ → Prop} {total : ℕ → ℝ}
    {count : ℕ → Set (ι → ℝ) → ℝ} {speed : ℕ → ℝ} {Feas : Set (ι → ℝ)} {I : (ι → ℝ) → ℝ}
    (R : ℕ → Finset (ι → ℝ)) (w : ℕ → (ι → ℝ) → ℝ) (d : (ι → ℝ) → ℝ)
    (hI : Continuous I) (hd : Continuous d) (hd0 : ∀ Q, 0 ≤ d Q)
    (hfeas : ∀ Q, Q ∈ Set.Icc (0 : ι → ℝ) 1 → d Q = 0 → Q ∈ Feas)
    (hsp : ∀ n, 0 ≤ speed n) (htot : ∀ n, 0 ≤ total n)
    (hcount_up : ∀ n A, count n A ≤ ∑ Q ∈ (R n).filter (· ∈ A), w n Q)
    (hcount_low : ∀ n A Q, Q ∈ R n → Q ∈ A → w n Q ≤ count n A)
    (hR : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, adm n → ((R n).card : ℝ) ≤ Real.exp (speed n * ε))
    (hbox : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, adm n →
      ∀ Q ∈ R n, Q ∈ Set.Icc (0 : ι → ℝ) 1 ∧ d Q ≤ ε)
    (hw : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, adm n →
      ∀ Q ∈ R n, w n Q ≤ total n * Real.exp (-(speed n * (I Q - ε))))
    (hlow : ∀ Q ∈ Feas, (∀ i, 0 < Q i) → ∀ ε : ℝ, 0 < ε → ∀ V ∈ 𝓝 Q,
      ∀ᶠ n in atTop, adm n →
        ∃ Q' ∈ R n, Q' ∈ V ∧ total n * Real.exp (-(speed n * (I Q + ε))) ≤ w n Q')
    (P : ι → ℝ) (hPpos : ∀ i, 0 < P i)
    (hconv : ∀ Q ∈ Feas, ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (fun i => (1 - s) * Q i + s * P i) ∈ Feas)
    (hFeas0 : ∀ Q ∈ Feas, ∀ i, 0 ≤ Q i) :
    CountLDP adm total count speed Feas I := by
  constructor
  · -- upper bound on closed sets
    intro F hF r hr
    obtain ⟨c, hc, hgap⟩ := closed_gap hF hI hd hd0 (r := r)
      (fun Q hQ hb hd0' => hr Q hQ (hfeas Q hb hd0'))
    filter_upwards [hR (c / 2) (by positivity), hbox c hc, hw (c / 2) (by positivity)]
      with n hRn hbn hwn
    intro hadm
    have hRn := hRn hadm
    have hbn := hbn hadm
    have hwn := hwn hadm
    have hterm : ∀ Q ∈ (R n).filter (· ∈ F),
        w n Q ≤ total n * Real.exp (-(speed n * (r + 3 * c / 2))) := by
      intro Q hQ
      obtain ⟨hQR, hQF⟩ := mem_filter.mp hQ
      obtain ⟨hb, hdQ⟩ := hbn Q hQR
      have hI' := hgap Q hQF hb hdQ
      refine (hwn Q hQR).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (htot n))
      have : r + 3 * c / 2 ≤ I Q - c / 2 := by linarith
      nlinarith [hsp n]
    calc count n F ≤ ∑ Q ∈ (R n).filter (· ∈ F), w n Q := hcount_up n F
      _ ≤ ∑ _Q ∈ (R n).filter (· ∈ F), total n * Real.exp (-(speed n * (r + 3 * c / 2))) :=
          sum_le_sum hterm
      _ = ((R n).filter (· ∈ F)).card * (total n * Real.exp (-(speed n * (r + 3 * c / 2)))) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ (R n).card * (total n * Real.exp (-(speed n * (r + 3 * c / 2)))) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_le _ _) (mul_nonneg (htot n) (Real.exp_pos _).le)
      _ ≤ Real.exp (speed n * (c / 2)) * (total n * Real.exp (-(speed n * (r + 3 * c / 2)))) :=
          mul_le_mul_of_nonneg_right hRn (mul_nonneg (htot n) (Real.exp_pos _).le)
      _ = total n * Real.exp (-(speed n * (r + c))) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
      _ ≤ total n * Real.exp (-(speed n * r)) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (htot n)
          nlinarith [hsp n]
  · -- lower bound on open sets
    intro U hU Q hQU hQ ε hε
    -- move `Q` towards `P`
    set Qs : ℝ → ι → ℝ := fun s i => (1 - s) * Q i + s * P i with hQs
    have hQs_cont : Continuous Qs := by
      refine continuous_pi fun i => ?_
      exact ((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)
    have hQs0 : Qs 0 = Q := by funext i; simp [hQs]
    have hT : Tendsto Qs (𝓝[>] 0) (𝓝 Q) := by
      rw [← hQs0]; exact hQs_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hIT : Tendsto (fun s => I (Qs s)) (𝓝[>] 0) (𝓝 (I Q)) := (hI.tendsto Q).comp hT
    have hev1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), Qs s ∈ U := hT (hU.mem_nhds hQU)
    have hev2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), I (Qs s) < I Q + ε / 2 :=
      hIT (Iio_mem_nhds (by linarith))
    have hev3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num))
    have hev4 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ := (hev1.and (hev2.and (hev3.and hev4))).exists
    have hQsF : Qs s ∈ Feas := hconv Q hQ s hs4.le hs3.le
    have hQspos : ∀ i, 0 < Qs s i := by
      intro i
      have h1 : 0 ≤ (1 - s) * Q i := mul_nonneg (by linarith) (hFeas0 Q hQ i)
      have h2 : 0 < s * P i := mul_pos hs4 (hPpos i)
      simp only [hQs]; linarith
    filter_upwards [hlow (Qs s) hQsF hQspos (ε / 2) (by positivity) U (hU.mem_nhds hs1)]
      with n hn
    intro hadm
    obtain ⟨Q', hQ'R, hQ'U, hQ'w⟩ := hn hadm
    refine le_trans ?_ (hQ'w.trans (hcount_low n U Q' hQ'R hQ'U))
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (htot n)
    nlinarith [hsp n]

omit [Fintype ι] in
/-- A continuous rate on a closed subset of the profile box has compact sublevels. -/
theorem isCompact_rate_sublevel {Feas : Set (ι → ℝ)} (hFeas : IsClosed Feas)
    (hbox : Feas ⊆ Set.Icc (0 : ι → ℝ) 1) {I : (ι → ℝ) → ℝ}
    (hI : Continuous I) (a : ℝ) :
    IsCompact {Q | Q ∈ Feas ∧ I Q ≤ a} := by
  have hcompact : IsCompact Feas := isCompact_Icc.of_isClosed_subset hFeas hbox
  exact hcompact.inter_right (isClosed_Iic.preimage hI)

end KqR75.ProfileLDP

#print axioms KqR75.ProfileLDP.countLDP_of_bounds
#print axioms KqR75.ProfileLDP.isCompact_rate_sublevel
