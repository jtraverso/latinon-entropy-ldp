module
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Distributions.Bernoulli

@[expose] public section
noncomputable section
namespace KqR75.ReserveTails

open Set MeasureTheory ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
variable {X : Ω → ℝ} {m : ℝ}

/-- A Bernoulli moment factor is bounded by the exponential of its linear term. -/
theorem bernoulli_factor_le (p s : ℝ) :
    1 + p * (Real.exp s - 1) ≤ Real.exp (p * (Real.exp s - 1)) := by
  simpa only [add_comm] using Real.add_one_le_exp (p * (Real.exp s - 1))

/-- Lower tail with a fixed fractional deviation, suitable both for cuts
and for rooted neighbourhoods after deleting the roots. -/
theorem lower (hm : 0 ≤ m)
    (hint : Integrable (fun ω => Real.exp ((-1 / 3 : ℝ) * X ω)) P)
    (hmgf : mgf X P (-1 / 3) ≤ Real.exp (m * (Real.exp (-1 / 3) - 1))) :
    P.real {ω | X ω ≤ (2 / 3) * m} ≤ Real.exp (-m / 36) := by
  have he : Real.exp (-1 / 3) ≤ (3 / 4 : ℝ) := by
    rw [show (-1 / 3 : ℝ) = -(1 / 3) by ring, Real.exp_neg, inv_le_iff_one_le_mul₀]
    · nlinarith only [Real.add_one_le_exp (1 / 3 : ℝ)]
    · positivity
  apply (measure_le_le_exp_mul_mgf ((2 / 3) * m) (by norm_num) hint).trans
  refine (mul_le_mul_of_nonneg_left hmgf (by positivity)).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left he hm]

/-- Upper tail at twice the Bernoulli mean. -/
theorem upper (hm : 0 ≤ m)
    (hint : Integrable (fun ω => Real.exp ((1 / 3 : ℝ) * X ω)) P)
    (hmgf : mgf X P (1 / 3) ≤ Real.exp (m * (Real.exp (1 / 3) - 1))) :
    P.real {ω | 2 * m ≤ X ω} ≤ Real.exp (-m / 6) := by
  have he : Real.exp (1 / 3) ≤ (3 / 2 : ℝ) := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (show (0 : ℝ) ≤ 1 / 3 by norm_num) (show (1 / 3 : ℝ) < 1 by norm_num)
    norm_num at h ⊢
    exact h
  apply (measure_ge_le_exp_mul_mgf (2 * m) (by norm_num) hint).trans
  refine (mul_le_mul_of_nonneg_left hmgf (by positivity)).trans ?_
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left he hm]

/-- The exponential moment estimate for a sum of independent Bernoulli variables. -/
theorem independent_bernoulli_sum {ι : Type*} {Y : ι → Ω → ℝ} (p : unitInterval)
    (s : Finset ι) (hI : iIndepFun Y P) (hM : ∀ i, Measurable (Y i))
    (hY : ∀ i, HasLaw (Y i) (bernoulliMeasure (1 : ℝ) 0 p) P) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * (∑ i ∈ s, Y i) ω)) P ∧
      mgf (∑ i ∈ s, Y i) P t ≤ Real.exp (((s.card : ℝ) * p) * (Real.exp t - 1)) := by
  have hmeas (i : ι) := (hY i).aemeasurable
  constructor
  · exact hI.integrable_exp_mul_sum hM (fun i _ =>
      (hY i).integrable_fun_comp (integrable_bernoulliMeasure (1 : ℝ) 0 p
        (fun z => Real.exp (t * z))))
  · rw [hI.mgf_sum₀ hmeas]
    calc
      _ ≤ ∏ _i ∈ s, Real.exp ((p : ℝ) * (Real.exp t - 1)) := by
        apply Finset.prod_le_prod₀ (fun i _ => mgf_nonneg)
        intro i _
        unfold mgf
        change P[(fun z => Real.exp (t * z)) ∘ Y i] ≤ _
        rw [(hY i).integral_comp (by fun_prop), integral_bernoulliMeasure]
        simp only [mul_one, mul_zero, Real.exp_zero, smul_eq_mul]
        convert bernoulli_factor_le (p : ℝ) t using 1; ring
      _ = _ := by
        rw [← Real.exp_sum, Finset.sum_const, nsmul_eq_mul, mul_assoc]

omit [IsFiniteMeasure P] in
/-- The same sample can satisfy every cut and root test when their total
failure budget is strictly below one. -/
theorem exists_avoiding {ι : Type*} [Fintype ι] [IsProbabilityMeasure P]
    (bad : ι → Set Ω) (e : ι → ℝ) (he : ∀ i, P.real (bad i) ≤ e i)
    (hs : ∑ i, e i < 1) : ∃ ω, ∀ i, ω ∉ bad i := by
  classical
  have hbound : P.real (⋃ i, bad i) < 1 :=
    ((measureReal_iUnion_fintype_le bad).trans (Finset.sum_le_sum (fun i _ => he i))).trans_lt hs
  by_contra! h
  have hu : (⋃ i, bad i) = univ := by
    apply eq_univ_of_forall
    intro ω
    obtain ⟨i, hi⟩ := h ω
    exact mem_iUnion.mpr ⟨i, hi⟩
  simp [hu] at hbound

end KqR75.ReserveTails

#print axioms KqR75.ReserveTails.lower
#print axioms KqR75.ReserveTails.upper
#print axioms KqR75.ReserveTails.independent_bernoulli_sum
#print axioms KqR75.ReserveTails.exists_avoiding
