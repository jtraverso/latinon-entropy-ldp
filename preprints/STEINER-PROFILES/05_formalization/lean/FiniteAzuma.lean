module
public import FiniteProcess
public import HistoryMartingale
public import FiniteHoeffding
public import FiniteChernoff

@[expose] public section
noncomputable section
namespace KqR75.FiniteAzuma

open Finset LatinonEntropy

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- Centering uses the actual one-step law, including the stopped history. -/
def centered (K : FiniteKernel Ω) (F : List Ω → Ω → ℝ) (h : List Ω) (a : Ω) : ℝ :=
  F h a - ∑ c, K.transition h c * F h c

theorem centered_zero (K : FiniteKernel Ω) (F : List Ω → Ω → ℝ) (h : List Ω) :
    (∑ a, K.transition h a * centered K F h a) = 0 := by
  simp only [centered, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    K.total, one_mul, sub_self]

theorem centered_abs_le (K : FiniteKernel Ω) (F : List Ω → Ω → ℝ) (b : ℕ → ℝ)
    (hbound : ∀ h a, |F h a| ≤ b h.length) (h : List Ω) (a : Ω) :
    |centered K F h a| ≤ 2 * b h.length := by
  have hm : |∑ c, K.transition h c * F h c| ≤ b h.length := by
    calc
      _ ≤ ∑ c, |K.transition h c * F h c| := abs_sum_le_sum_abs _ _
      _ = ∑ c, K.transition h c * |F h c| := by
        simp only [abs_mul, abs_of_nonneg (K.nonneg h _)]
      _ ≤ ∑ c, K.transition h c * b h.length := Finset.sum_le_sum
        (fun c _ => mul_le_mul_of_nonneg_left (hbound h c) (K.nonneg h c))
      _ = _ := by rw [← Finset.sum_mul, K.total, one_mul]
  dsimp only [centered]
  rw [sub_eq_add_neg]
  exact (abs_add_le _ _).trans (by rw [abs_neg]; linarith only [hbound h a, hm])

theorem increment_mgf (K : FiniteKernel Ω) (Z : List Ω → Ω → ℝ) (b : ℕ → ℝ)
    (hb : ∀ s, 0 < b s) (hzero : ∀ h, ∑ a, K.transition h a * Z h a = 0)
    (hbound : ∀ h a, |Z h a| ≤ b h.length) (lam : ℝ) (h : List Ω) :
    (∑ a, K.transition h a * Real.exp (lam * Z h a)) ≤
      Real.exp (lam ^ 2 * (b h.length) ^ 2 / 2) := by
  have hg (a : Ω) : |Z h a / b h.length| ≤ 1 := by
    rw [abs_div, abs_of_pos (hb _)]
    exact (div_le_one (hb _)).mpr (hbound h a)
  have hm : (∑ a, K.transition h a * (Z h a / b h.length)) = 0 := by
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, hzero h, zero_div]
  have ht := finite_centered_hoeffding (K.transition h) (fun a => Z h a / b h.length)
    (K.nonneg h) (K.total h) hg (lam * b h.length)
  simp only [hm, sub_zero] at ht
  have he (a : Ω) : lam * b h.length * (Z h a / b h.length) = lam * Z h a := by
    field_simp [(hb h.length).ne']
    <;> ring
  simp_rw [he] at ht
  have hp : (lam * b h.length) ^ 2 / 2 = lam ^ 2 * (b h.length) ^ 2 / 2 := by ring
  simpa only [hp] using ht

theorem history_mgf (K : FiniteKernel Ω) (Z : List Ω → Ω → ℝ) (b : ℕ → ℝ)
    (hb : ∀ s, 0 < b s) (hzero : ∀ h, ∑ a, K.transition h a * Z h a = 0)
    (hbound : ∀ h a, |Z h a| ≤ b h.length) (lam : ℝ) (T : ℕ) :
    historyExpectation K T (fun h => Real.exp (lam * pathSum Z h)) ≤
      Real.exp (lam ^ 2 * (∑ s ∈ range T, (b s) ^ 2) / 2) := by
  have hm := history_mgf_le K Z (fun s => lam ^ 2 * (b s) ^ 2 / 2) lam
    (increment_mgf K Z b hb hzero hbound lam) T
  have hs : (∑ s ∈ range T, lam ^ 2 * (b s) ^ 2 / 2) =
      lam ^ 2 * (∑ s ∈ range T, (b s) ^ 2) / 2 := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
  simpa only [hs] using hm

/-- Finite-history Azuma with a time-varying variance proxy. The tail has
no artificial restriction u≤V or |lam|≤1; the optimizing lam may grow with n. -/
theorem tail (K : FiniteKernel Ω) (Z : List Ω → Ω → ℝ) (b : ℕ → ℝ)
    (hb : ∀ s, 0 < b s) (hzero : ∀ h, ∑ a, K.transition h a * Z h a = 0)
    (hbound : ∀ h a, |Z h a| ≤ b h.length) (T : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hV : 0 < ∑ s ∈ range T, (b s) ^ 2) :
    FiniteProcess.eventMass K T (fun h => u ≤ |pathSum Z h|) ≤
      2 * Real.exp (-(u ^ 2 / (2 * ∑ s ∈ range T, (b s) ^ 2))) := by
  classical
  let H := histories Ω T
  let p : H → ℝ := fun h => historyWeight K h
  let X : H → ℝ := fun h => pathSum Z h
  let V := ∑ s ∈ range T, (b s) ^ 2
  have hp (h : H) : 0 ≤ p h := historyWeight_nonneg K h
  have hmass : ∑ h : H, p h = 1 := by
    change (∑ h : H, historyWeight K h) = 1
    rw [Finset.sum_coe_sort H (historyWeight K)]
    exact historyWeight_total K T
  have hlog (lam : ℝ) : Real.log (∑ h : H, p h * Real.exp (lam * X h)) ≤ lam ^ 2 * V / 2 := by
    have hm := history_mgf K Z b hb hzero hbound lam T
    have he : (∑ h : H, p h * Real.exp (lam * X h)) =
        historyExpectation K T (fun h => Real.exp (lam * pathSum Z h)) :=
      Finset.sum_coe_sort H (fun h => historyWeight K h * Real.exp (lam * pathSum Z h))
    rw [← he] at hm
    have hpos := finite_exponential_sum_pos p (fun h => lam * X h) hp hmass
    have hl := Real.log_le_log hpos hm
    simpa only [Real.log_exp] using hl
  let t := u / V
  have ht : 0 ≤ t := div_nonneg hu hV.le
  have hplus := finite_chernoff_one_side p X hp hmass t u (t ^ 2 * V / 2) ht (hlog t)
  have hneg : Real.log (∑ h : H, p h * Real.exp (t * (-X h))) ≤ t ^ 2 * V / 2 := by
    simpa only [neg_mul, mul_neg, neg_sq] using hlog (-t)
  have hminus := finite_chernoff_one_side p (fun h => -X h) hp hmass t u
    (t ^ 2 * V / 2) ht hneg
  have he : t ^ 2 * V / 2 - t * u = -(u ^ 2 / (2 * V)) := by
    dsimp only [t]
    field_simp [hV.ne']
    <;> ring
  rw [he] at hplus hminus
  have hpoint (a : H) : (if u ≤ |X a| then p a else 0) ≤
      (if u ≤ X a then p a else 0) + (if u ≤ -X a then p a else 0) := by
    by_cases h0 : u ≤ |X a|
    · have hor : u ≤ X a ∨ u ≤ -X a := by
        by_cases hx : 0 ≤ X a
        · exact Or.inl (by simpa only [abs_of_nonneg hx] using h0)
        · exact Or.inr (by simpa only [abs_of_neg (lt_of_not_ge hx)] using h0)
      rcases hor with h | h <;> simp only [h0, ite_true, h] <;> split_ifs <;> linarith [hp a]
    · simp only [h0, ite_false]
      split_ifs <;> linarith [hp a]
  have hs := Finset.sum_le_sum (fun h (_ : h ∈ (univ : Finset H)) => hpoint h)
  rw [Finset.sum_add_distrib] at hs
  have hev : FiniteProcess.eventMass K T (fun h => u ≤ |pathSum Z h|) =
      ∑ h : H, if u ≤ |X h| then p h else 0 :=
    (Finset.sum_coe_sort H (fun h => if u ≤ |pathSum Z h| then historyWeight K h else 0)).symm
  rw [hev]
  calc
    _ ≤ (∑ h : H, if u ≤ X h then p h else 0) +
        ∑ h : H, if u ≤ -X h then p h else 0 := hs
    _ ≤ Real.exp (-(u ^ 2 / (2 * V))) + Real.exp (-(u ^ 2 / (2 * V))) :=
      add_le_add hplus hminus
    _ = _ := by ring

end KqR75.FiniteAzuma

#print axioms KqR75.FiniteAzuma.history_mgf
#print axioms KqR75.FiniteAzuma.tail
#print axioms KqR75.FiniteAzuma.centered_zero
