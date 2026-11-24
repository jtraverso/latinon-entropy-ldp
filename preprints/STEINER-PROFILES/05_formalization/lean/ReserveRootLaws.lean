module
public import ReserveRandom
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section
noncomputable section
namespace KqR75.ReserveRandom

open Finset MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped Sym2 ENNReal

variable {V : Type*} [Fintype V]

/-- Disjoint groups of edge coordinates have a product law on their rows. -/
theorem grouped_coins {I J : Type*} [Fintype I] [Fintype J]
    (p : unitInterval) (f : (Σ _ : I, J) ↪ Sym2 V) :
    HasLaw (fun (ω : Sym2 V → Bool) (i : I) (j : J) => ω (f ⟨i, j⟩))
      (Measure.pi (fun _ : I => Measure.pi (fun _ : J => bernoulliMeasure true false p)))
      (law V p) := by
  classical
  let μ := bernoulliMeasure true false p
  let flat := fun (ω : Sym2 V → Bool) (a : Σ _ : I, J) => ω (f a)
  have he (e : Sym2 V) : (law V p).map (fun ω => ω e) = μ :=
    (measurePreserving_eval (fun _ : Sym2 V => μ) e).map_eq
  have hflat : Measurable flat := measurable_pi_iff.mpr (fun a => measurable_pi_apply (f a))
  have hi : iIndepFun (fun (a : Σ _ : I, J) (ω : Sym2 V → Bool) => flat ω a) (law V p) := by
    have h : iIndepFun (fun (e : Sym2 V) (ω : Sym2 V → Bool) => ω e) (law V p) :=
      iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
    exact h.precomp f.injective
  have hm := (iIndepFun_iff_map_fun_eq_pi_map
    (fun a : Σ _ : I, J => (measurable_pi_apply (f a)).aemeasurable)).mp hi
  simp_rw [he] at hm
  let e := MeasurableEquiv.piCurry (fun (_ : I) (_ : J) => Bool)
  change (law V p).map flat = Measure.pi (fun _ : Σ _ : I, J => μ) at hm
  have hg : Measurable (e ∘ flat) := e.measurable.comp hflat
  refine ⟨hg.aemeasurable, ?_⟩
  change (law V p).map (e ∘ flat) = _
  rw [← Measure.map_map e.measurable hflat, hm]
  have h := infinitePi_map_piCurry (fun (_ : I) (_ : J) => μ)
  simpa only [infinitePi_eq_pi, e] using h

/-- The probability that one row of independent coins is entirely true. -/
theorem all_true_probability {J : Type*} [Fintype J] (p : unitInterval) :
    (Measure.pi (fun _ : J => bernoulliMeasure true false p)).real
      {row | ∀ j : J, row j = true} = (p : ℝ) ^ Fintype.card J := by
  classical
  have he : {row : J → Bool | ∀ j : J, row j = true} =
      Set.univ.pi (fun _ => ({true} : Set Bool)) := by
    ext row
    simp
  rw [he, measureReal_def, pi_pi]
  have ht : bernoulliMeasure true false p ({true} : Set Bool) =
      (unitInterval.toNNReal p : ℝ≥0∞) :=
    bernoulliMeasure_apply_of_mem_of_notMem p (measurableSet_singleton true) (by simp) (by simp)
  simp [ht]

/-- Indicators that all edges in each disjoint row are present are independent
Bernoulli variables with parameter p to the number of columns. -/
theorem grouped_indicators {I J : Type*} [Fintype I] [Fintype J]
    (p : unitInterval) (f : (Σ _ : I, J) ↪ Sym2 V) :
    let a : unitInterval := ⟨(p : ℝ) ^ Fintype.card J,
      pow_nonneg p.2.1 _, pow_le_one₀ p.2.1 p.2.2⟩
    let Y := fun (i : I) (ω : Sym2 V → Bool) => if ∀ j : J, ω (f ⟨i, j⟩) = true then (1 : ℝ) else 0
    iIndepFun Y (law V p) ∧ (∀ i, Measurable (Y i)) ∧
      ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 a) (law V p) := by
  classical
  let a : unitInterval := ⟨(p : ℝ) ^ Fintype.card J,
    pow_nonneg p.2.1 _, pow_le_one₀ p.2.1 p.2.2⟩
  let U := Measure.pi (fun _ : J => bernoulliMeasure true false p)
  let T := bernoulliMeasure (1 : ℝ) 0 a
  let success : Set (J → Bool) := {row | ∀ j : J, row j = true}
  let mark := fun row : J → Bool => if row ∈ success then (1 : ℝ) else 0
  let rows := fun (ω : Sym2 V → Bool) (i : I) (j : J) => ω (f ⟨i, j⟩)
  let Y := fun (i : I) ω => mark (rows ω i)
  change iIndepFun Y (law V p) ∧ (∀ i, Measurable (Y i)) ∧
    ∀ i, HasLaw (Y i) T (law V p)
  have hsuccess : MeasurableSet success := success.to_countable.measurableSet
  have hmark : Measurable mark := measurable_of_countable _
  have hmarkLaw : HasLaw mark T U := by
    have h := hasLaw_indicator_bernoulliMeasure (P := U) (1 : ℝ) hsuccess.nullMeasurableSet
    have hparam : (⟨U.real success, by simp⟩ : unitInterval) = a :=
      Subtype.ext (all_true_probability p)
    rw [hparam] at h
    have he : mark = success.indicator (fun _ => (1 : ℝ)) := by
      funext row
      by_cases hr : row ∈ success <;> simp [mark, hr]
    rw [he]
    exact h
  have hrows : HasLaw rows (Measure.pi (fun _ : I => U)) (law V p) := grouped_coins p f
  have hmap := measurePreserving_pi (fun _ : I => U) (fun _ : I => T)
    (fun _ => ⟨hmark, hmarkLaw.map_eq⟩ : ∀ _ : I, MeasurePreserving mark U T)
  have hall : HasLaw (fun ω i => Y i ω) (Measure.pi (fun _ : I => T)) (law V p) :=
    hmap.hasLaw.fun_comp hrows
  have hm (i : I) : Measurable (Y i) := hmark.comp <|
    measurable_pi_iff.mpr (fun j => measurable_pi_apply (f ⟨i, j⟩))
  have hY (i : I) : HasLaw (Y i) T (law V p) :=
    (measurePreserving_eval (fun _ : I => T) i).hasLaw.fun_comp hall
  refine ⟨(iIndepFun_iff_map_fun_eq_pi_map (fun i => (hm i).aemeasurable)).mpr ?_, hm, hY⟩
  simp_rw [hall.map_eq, (hY _).map_eq]

section RootCounts

variable [DecidableEq V]

private def rootEdges (S H : Finset V) :
    (Σ _ : ↥(S \ H), ↥H) ↪ Sym2 V where
  toFun a := s(a.2.val, a.1.val)
  inj' := by
    rintro ⟨w, u⟩ ⟨w', u'⟩ he
    rcases Sym2.eq_iff.mp he with ⟨hu, hw⟩ | ⟨hu, _⟩
    · cases Subtype.ext hw
      cases Subtype.ext hu
      rfl
    · exact ((mem_sdiff.mp w'.property).2 (hu ▸ u.property)).elim

private theorem card_common_eq_sum (ω : Sym2 V → Bool) (S H : Finset V) :
    ((ReserveCuts.common (adj ω) S H).card : ℝ) =
      ∑ w : ↥(S \ H), if ∀ u : ↥H, ω (rootEdges S H ⟨w, u⟩) = true then 1 else 0 := by
  classical
  have he : ReserveCuts.common (adj ω) S H =
      (S \ H).filter (fun w => ∀ u ∈ H, ω s(u, w) = true) := by
    ext w
    simp only [ReserveCuts.common, mem_filter, mem_sdiff]
    constructor
    · rintro ⟨hw, hn⟩
      exact ⟨⟨hw, fun hwH => (hn w hwH).1 rfl⟩, fun u hu => (hn u hu).2⟩
    · rintro ⟨⟨hw, hwH⟩, hn⟩
      exact ⟨hw, fun u hu => ⟨fun he => hwH (he ▸ hu), hn u hu⟩⟩
  rw [he, ← sum_boole, ← Finset.sum_coe_sort]
  apply sum_congr rfl
  intro w _
  apply if_congr _ rfl rfl
  change (∀ u ∈ H, ω s(u, w.val) = true) ↔ ∀ u : ↥H, ω s(u.val, w.val) = true
  exact ⟨fun h u => h u.val u.property, fun h u hu => h ⟨u, hu⟩⟩

/-- Both tails at a fixed root set. The mean counts only vertices outside
the roots. -/
theorem common_tails (p : unitInterval) (S H : Finset V) (hH : H ⊆ S) :
    let m : ℝ := ((S.card : ℝ) - H.card) * (p : ℝ) ^ H.card
    (law V p).real {ω | ((ReserveCuts.common (adj ω) S H).card : ℝ) ≤ (2 / 3) * m} ≤
        Real.exp (-m / 36) ∧
      (law V p).real {ω | 2 * m ≤ ((ReserveCuts.common (adj ω) S H).card : ℝ)} ≤
        Real.exp (-m / 6) := by
  classical
  let a : unitInterval := ⟨(p : ℝ) ^ H.card, pow_nonneg p.2.1 _, pow_le_one₀ p.2.1 p.2.2⟩
  let Y := fun (w : ↥(S \ H)) (ω : Sym2 V → Bool) =>
    if ∀ u : ↥H, ω (rootEdges S H ⟨w, u⟩) = true then (1 : ℝ) else 0
  let m : ℝ := ((S.card : ℝ) - H.card) * (p : ℝ) ^ H.card
  have ha : (Fintype.card ↥(S \ H) : ℝ) * a = m := by
    have h := card_sdiff_add_card_eq_card hH
    have hR : ((S \ H).card : ℝ) + H.card = S.card := by exact_mod_cast h
    rw [Fintype.card_coe]
    change ((S \ H).card : ℝ) * (p : ℝ) ^ H.card = m
    rw [show ((S \ H).card : ℝ) = S.card - H.card by linarith]
  have h0 : 0 ≤ m := ha ▸ mul_nonneg (Nat.cast_nonneg _) a.2.1
  have ⟨hI, hM, hY⟩ : iIndepFun Y (law V p) ∧ (∀ w, Measurable (Y w)) ∧
      ∀ w, HasLaw (Y w) (bernoulliMeasure (1 : ℝ) 0 a) (law V p) := by
    simpa only [Fintype.card_coe, Y, a] using grouped_indicators p (rootEdges S H)
  have hsum (ω : Sym2 V → Bool) :
      ((ReserveCuts.common (adj ω) S H).card : ℝ) = (∑ w, Y w) ω := by
    rw [Finset.sum_apply]
    exact card_common_eq_sum ω S H
  have hmgf (t : ℝ) := ReserveTails.independent_bernoulli_sum a univ hI hM hY t
  change (law V p).real {ω | ((ReserveCuts.common (adj ω) S H).card : ℝ) ≤ (2 / 3) * m} ≤
      Real.exp (-m / 36) ∧
    (law V p).real {ω | 2 * m ≤ ((ReserveCuts.common (adj ω) S H).card : ℝ)} ≤
      Real.exp (-m / 6)
  simp_rw [hsum]
  have hlo := hmgf (-1 / 3)
  have hup := hmgf (1 / 3)
  rw [card_univ, ha] at hlo hup
  exact ⟨ReserveTails.lower h0 hlo.1 hlo.2, ReserveTails.upper h0 hup.1 hup.2⟩

end RootCounts

end KqR75.ReserveRandom

#print axioms KqR75.ReserveRandom.grouped_coins
#print axioms KqR75.ReserveRandom.all_true_probability
#print axioms KqR75.ReserveRandom.grouped_indicators
#print axioms KqR75.ReserveRandom.common_tails
