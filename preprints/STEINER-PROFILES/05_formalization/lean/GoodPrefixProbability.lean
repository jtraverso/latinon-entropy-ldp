module
public import PrefixProbability
public import HorizonCountTheorem

@[expose] public section
noncomputable section
namespace KqR75.WeightedGreedy

open Finset LatinonEntropy

variable {E B τ : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]
  [Fintype τ] [DecidableEq τ]

omit [Fintype B] [DecidableEq B] in
private theorem selectedCount_eq_length_of_no_stop (h : List (Option B)) (hn : none ∉ h) :
    selectedCount h = h.length := by
  induction h with
  | nil => rfl
  | cons b h ih =>
    cases b with
    | none => exact (hn (by simp)).elim
    | some b => simp [selectedCount, ih (fun hm => hn (by simp [hm]))]

/-- The actual good-history test supplies the normalizer estimates at
every visited prefix, so the probability estimate requires no additional
assumption on transition denominators. -/
theorem log_probability_on_good_history (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop)
    (type : B → τ) (w target : τ → ℝ) (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n)
    (hsize : ∀ b, (I b).card = r) (M c A a z D L εw : ℝ)
    (hc : 0 < c) (hA : 0 ≤ A) (ha : 0 ≤ a) (hD : 0 ≤ D)
    (hscale : a * (4 * (r : ℝ) - 1) = 1 - 2 * z)
    (hM : c * (n : ℝ) ^ 2 ≤ M) (hJ : (J.card : ℝ) = (r : ℝ) * M)
    (h : List (Option B)) (hT₁ : 1 ≤ h.length) (hT : h.length ≤ GreedyScales.horizon M n a)
    (hnone : none ∉ h) (hp : 0 < historyWeight (kernel I μ hμ J guard) h)
    (hcross : ¬ EnergyExit.crossed (HorizonCountTheorem.energy I μ J r M) (A * n) h)
    (hw : ∀ b : B, 0 < μ b → Real.log (μ b) ≤ w (type b) + εw)
    (hcount : ∀ t, |(TypeCounts.count (univ.filter (fun c => type c = t)) h : ℝ) -
      target t| ≤ D) (hlog : ∀ t, |w t| ≤ L) :
    let ε := Real.sqrt (A / ((r : ℝ) * c)) * (n : ℝ) ^ (-z)
    ε ≤ 1 / 2 →
    Real.log (historyWeight (kernel I μ hμ J guard) h) + Real.log (h.length.factorial : ℝ) ≤
      (∑ t, target t * w t) + ((r : ℝ) - 1) * M +
        (M - h.length) + 1 + Real.log h.length +
        (h.length : ℝ) * (εw + 2 * ε) + (Fintype.card τ : ℝ) * (D * L) := by
  dsimp only
  intro hε
  let ε := Real.sqrt (A / ((r : ℝ) * c)) * (n : ℝ) ^ (-z)
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hM₀ : 0 < M := (mul_pos hc (by positivity)).trans_le hM
  have hTM : (h.length : ℝ) < M := (Nat.cast_le.mpr hT).trans_lt
    (GreedyScales.horizon_bounds M n a hM₀ hn ha).1
  apply log_probability_with_ordering I μ hμ J guard type w target r M D L εw (2 * ε)
    hD h hT₁ hTM hnone hp hw hcount hlog
  intro j hj
  let g := h.drop (h.length - j)
  have hlen : g.length = j := by dsimp [g]; rw [List.length_drop]; omega
  have hgn : none ∉ g := fun hm => hnone (List.mem_of_mem_drop hm)
  have hsel : selectedCount g = j := (selectedCount_eq_length_of_no_stop g hgn).trans hlen
  have hg := TypeCountHorizon.drop_support (kernel I μ hμ J guard) h (h.length - j) hp
  have hvalid := positive_history_valid I μ hμ J guard g hg
  have hgc := TypeCountHorizon.drop_no_cross (HorizonCountTheorem.energy I μ J r M)
    (A * n) h (h.length - j) hcross
  have hY := TypeCountHorizon.below_of_not_crossed (HorizonCountTheorem.energy I μ J r M)
    (A * n) g hgc
  have hgj : selectedCount g ≤ GreedyScales.horizon M n a := by
    rw [hsel]; exact hj.le.trans hT
  have hrel := GreedySchedule.relative_mass_at_horizon I μ J r n hr hn hsize M c A a z hc hA
    ha hscale hM hJ g hvalid hgj hY.le
  rw [hsel] at hrel
  let p := (M - (j : ℝ)) / M
  have hjM : (j : ℝ) < M := (Nat.cast_le.mpr hj.le).trans_lt hTM
  have hp₀ : 0 < p := div_pos (sub_pos.mpr hjM) hM₀
  have hε₀ : 0 ≤ ε := by dsimp [ε]; positivity
  have hlogZ := GreedySchedule.log_difference_of_relative_error (ε := ε)
    (mul_pos hM₀ (pow_pos hp₀ r)) hε₀ hε hrel
  rw [Real.log_mul hM₀.ne' (pow_pos hp₀ r).ne', Real.log_pow] at hlogZ
  have hl := (abs_le.mp hlogZ).1
  linarith only [hl]

end KqR75.WeightedGreedy

#print axioms KqR75.WeightedGreedy.log_probability_on_good_history
