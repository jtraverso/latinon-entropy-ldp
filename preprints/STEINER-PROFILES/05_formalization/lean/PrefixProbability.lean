module
public import PrefixCount
public import PrefixLogSum

@[expose] public section
noncomputable section
namespace KqR75.WeightedGreedy

open Finset LatinonEntropy

variable {E B τ : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]
  [Fintype τ] [DecidableEq τ]

private theorem type_sum_cons (type : B → τ) (w : τ → ℝ) (b : B) (g : List (Option B)) :
    ∑ t, (TypeCounts.count (univ.filter (fun c => type c = t)) (some b :: g) : ℝ) * w t =
      (∑ t, (TypeCounts.count (univ.filter (fun c => type c = t)) g : ℝ) * w t) +
        w (type b) := by
  simp only [TypeCounts.count, mem_filter, mem_univ, true_and, Nat.cast_add, add_mul,
    sum_add_distrib]
  congr 1
  simp_rw [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul]
  simp [eq_comm]

/-- Accumulate the logarithmic probability along a positive, unstopped
prefix, grouping the numerator by block type. The lower bounds on the
normalizers are required at the actual visited prefixes. -/
theorem log_history_upper_of_bounds (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop)
    (type : B → τ) (w : τ → ℝ) (d : ℕ → ℝ) (ε : ℝ)
    (hw : ∀ b : B, 0 < μ b → Real.log (μ b) ≤ w (type b) + ε)
    (h : List (Option B)) (hn : none ∉ h)
    (hp : 0 < historyWeight (kernel I μ hμ J guard) h)
    (hd : ∀ j < h.length,
      d j ≤ Real.log (totalWeight I μ J (h.drop (h.length - j)))) :
    Real.log (historyWeight (kernel I μ hμ J guard) h) ≤
      (∑ t, (TypeCounts.count (univ.filter (fun c => type c = t)) h : ℝ) * w t) -
        (∑ j ∈ range h.length, d j) + (h.length : ℝ) * ε := by
  let K := kernel I μ hμ J guard
  induction h with
  | nil => simp [historyWeight, TypeCounts.count]
  | cons a g ih =>
    cases a with
    | none => exact (hn (by simp)).elim
    | some b =>
      have hn' : none ∉ g := fun h => hn (by simp [h])
      change 0 < historyWeight K g * K.transition g (some b) at hp
      have hpg : 0 < historyWeight K g := by
        by_contra! h
        exact not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg h (K.nonneg _ _)) hp
      have htrans : 0 < K.transition g (some b) := by
        by_contra! h
        exact not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hpg.le h) hp
      have hfit := positive_some_available I μ hμ J guard g b htrans
      have hlive : live I μ J guard g := by
        by_contra hn
        simp [K, kernel, hn] at htrans
      have he : K.transition g (some b) = μ b / totalWeight I μ J g := by
        simp [K, kernel, hlive, availableWeight, hfit]
      have hμb : 0 < μ b := (div_pos_iff_of_pos_right hlive.2.2).mp (he ▸ htrans)
      have hdg (j : ℕ) (hj : j < g.length) :
          d j ≤ Real.log (totalWeight I μ J (g.drop (g.length - j))) := by
        have hstep : (some b :: g).length - j = (g.length - j) + 1 := by
          simp only [List.length_cons]; omega
        simpa only [hstep, List.drop_succ_cons] using hd j (by simp only [List.length_cons]; omega)
      have htime : d g.length ≤ Real.log (totalWeight I μ J g) := by
        simpa using hd g.length (by simp)
      have htt := ih hn' hpg hdg
      change Real.log (historyWeight K g * K.transition g (some b)) ≤ _
      rw [Real.log_mul hpg.ne' htrans.ne', he, Real.log_div hμb.ne' hlive.2.2.ne',
        type_sum_cons, List.length_cons, sum_range_succ, Nat.cast_add, Nat.cast_one]
      linarith only [htt, hw b hμb, htime]

private theorem type_score_upper (type : B → τ) (w target : τ → ℝ)
    (h : List (Option B)) (D L : ℝ) (hD : 0 ≤ D)
    (hc : ∀ t, |(TypeCounts.count (univ.filter (fun c => type c = t)) h : ℝ) -
      target t| ≤ D) (hw : ∀ t, |w t| ≤ L) :
    (∑ t, (TypeCounts.count (univ.filter (fun c => type c = t)) h : ℝ) * w t) ≤
      (∑ t, target t * w t) + (Fintype.card τ : ℝ) * (D * L) := by
  have hb (t : τ) :
      (TypeCounts.count (univ.filter (fun c => type c = t)) h : ℝ) * w t ≤
        target t * w t + D * L := by
    have ht := mul_le_mul (hc t) (hw t) (abs_nonneg _) hD
    rw [← abs_mul] at ht
    have hu := (le_abs_self _).trans ht
    linarith only [hu]
  calc
    _ ≤ ∑ t, (target t * w t + D * L) := sum_le_sum (fun t _ => hb t)
    _ = _ := by rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]

/-- The logarithm of the history probability, including the cost of
forgetting the order, in terms of the prescribed type score and the
uniform errors supplied by the stopped process. -/
theorem log_probability_with_ordering (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop)
    (type : B → τ) (w target : τ → ℝ) (r : ℕ) (M D L εw εZ : ℝ) (hD : 0 ≤ D)
    (h : List (Option B)) (hT₁ : 1 ≤ h.length) (hT : (h.length : ℝ) < M)
    (hn : none ∉ h) (hp : 0 < historyWeight (kernel I μ hμ J guard) h)
    (hw : ∀ b : B, 0 < μ b → Real.log (μ b) ≤ w (type b) + εw)
    (hc : ∀ t, |(TypeCounts.count (univ.filter (fun c => type c = t)) h : ℝ) -
      target t| ≤ D) (hlog : ∀ t, |w t| ≤ L)
    (hd : ∀ j < h.length, Real.log M + (r : ℝ) * Real.log ((M - (j : ℝ)) / M) - εZ ≤
      Real.log (totalWeight I μ J (h.drop (h.length - j)))) :
    Real.log (historyWeight (kernel I μ hμ J guard) h) + Real.log (h.length.factorial : ℝ) ≤
      (∑ t, target t * w t) + ((r : ℝ) - 1) * M +
        (M - h.length) + 1 + Real.log h.length +
        (h.length : ℝ) * (εw + εZ) + (Fintype.card τ : ℝ) * (D * L) := by
  let d := fun j : ℕ => Real.log M + (r : ℝ) * Real.log ((M - (j : ℝ)) / M) - εZ
  have hp' := log_history_upper_of_bounds I μ hμ J guard type w d εw hw h hn hp hd
  have hsum : ∑ j ∈ range h.length, d j =
      (h.length : ℝ) * Real.log M +
        (r : ℝ) * (∑ i ∈ range h.length, Real.log ((M - (i : ℝ)) / M)) -
        (h.length : ℝ) * εZ := by
    simp only [d, sum_sub_distrib, sum_add_distrib, sum_const, card_range, nsmul_eq_mul, mul_sum]
  rw [hsum] at hp'
  have ht := type_score_upper type w target h D L hD hc hlog
  have hn := GreedySchedule.normalizer_minus_factorial_lower M r h.length hT₁ hT
  linarith only [hp', ht, hn]

end KqR75.WeightedGreedy

#print axioms KqR75.WeightedGreedy.log_history_upper_of_bounds
#print axioms KqR75.WeightedGreedy.log_probability_with_ordering
