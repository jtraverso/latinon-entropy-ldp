module
public import MeanEnergy

@[expose] public section
noncomputable section
namespace KqR75.GreedyMoments

open Finset
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

theorem error_zero_outside (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (k : ℝ) (e : E) (he : e ∉ WeightedGreedy.remaining I J h) :
    WeightedGreedy.error I μ J h k e = 0 := by
  simp only [WeightedGreedy.error, he, ite_false, sub_zero,
    WeightedGreedy.load_zero_outside I μ J h e he]

theorem sum_supported (S : Finset E) (f : E → ℝ) (hf : ∀ e, e ∉ S → f e = 0) :
    (∑ e ∈ S, f e) = ∑ e, f e :=
  Finset.sum_subset (Finset.subset_univ S) (fun e _ he => hf e he)

theorem error_variances (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (k : ℝ) :
    (∑ e, |WeightedGreedy.error I μ J h k e|) ^ 2 ≤
      ((WeightedGreedy.remaining I J h).card : ℝ) * WeightedGreedy.energy I μ J h k ∧
    (∑ e, WeightedGreedy.error I μ J h k e) ^ 2 ≤
      ((WeightedGreedy.remaining I J h).card : ℝ) * WeightedGreedy.energy I μ J h k := by
  let S := WeightedGreedy.remaining I J h
  let x := WeightedGreedy.error I μ J h k
  have hx (e : E) (he : e ∉ S) : x e = 0 := error_zero_outside I μ J h k e he
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq S (fun e => |x e|) (fun _ => (1 : ℝ))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq S x (fun _ => (1 : ℝ))
  have ha : (∑ e ∈ S, |x e|) = ∑ e, |x e| :=
    sum_supported S _ (fun e he => by rw [hx e he, abs_zero])
  have hs : (∑ e ∈ S, x e) = ∑ e, x e := sum_supported S x hx
  have hsq : (∑ e ∈ S, (x e) ^ 2) = ∑ e, (x e) ^ 2 :=
    sum_supported S _ (fun e he => by rw [hx e he]; norm_num)
  simp only [mul_one, one_pow, sq_abs, Finset.sum_const, nsmul_eq_mul, mul_one, ha, hs, hsq] at h1 h2
  constructor
  · simpa only [WeightedGreedy.energy, S, x, mul_comm] using h1
  · simpa only [WeightedGreedy.energy, S, x, mul_comm] using h2

theorem mass_error (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (r : ℕ) (hsize : ∀ b, (I b).card = r) (k : ℝ) :
    (∑ e, WeightedGreedy.error I μ J h k e) =
      (r : ℝ) * WeightedGreedy.totalWeight I μ J h - k * ((WeightedGreedy.remaining I J h).card : ℝ) := by
  have htest : (∑ e, if e ∈ WeightedGreedy.remaining I J h then k else 0) =
      ((WeightedGreedy.remaining I J h).card : ℝ) * k := by
    have hf : (univ.filter fun e => e ∈ WeightedGreedy.remaining I J h) =
        WeightedGreedy.remaining I J h := Finset.filter_mem_eq_of_subset (Finset.subset_univ _)
    rw [← Finset.sum_filter, hf]
    simp
  simp only [WeightedGreedy.error, Finset.sum_sub_distrib, htest,
    WeightedGreedy.sum_load I μ J r hsize h]
  ring

theorem load_error_moment (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (k : ℝ) :
    (∑ e, WeightedGreedy.load I μ J h e * WeightedGreedy.error I μ J h k e) =
      WeightedGreedy.energy I μ J h k + k * ∑ e, WeightedGreedy.error I μ J h k e := by
  simp_rw [MeanEnergy.load_error_product]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

theorem weighted_absolute_error (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (k : ℝ) :
    (∑ e, WeightedGreedy.load I μ J h e * |WeightedGreedy.error I μ J h k e|) ≤
      WeightedGreedy.energy I μ J h k + k * ∑ e, |WeightedGreedy.error I μ J h k e| := by
  have he (e : E) : WeightedGreedy.load I μ J h e * |WeightedGreedy.error I μ J h k e| ≤
      (WeightedGreedy.error I μ J h k e) ^ 2 + k * |WeightedGreedy.error I μ J h k e| := by
    by_cases hm : e ∈ WeightedGreedy.remaining I J h
    · have hd : WeightedGreedy.load I μ J h e = WeightedGreedy.error I μ J h k e + k := by
        simp only [WeightedGreedy.error, hm, ite_true]
        ring
      have hs := mul_le_mul_of_nonneg_right (le_abs_self (WeightedGreedy.error I μ J h k e))
        (abs_nonneg (WeightedGreedy.error I μ J h k e))
      rw [hd]
      nlinarith only [hs, sq_abs (WeightedGreedy.error I μ J h k e)]
    · rw [WeightedGreedy.load_zero_outside I μ J h e hm, error_zero_outside I μ J h k e hm]
      norm_num
  have hs := Finset.sum_le_sum (fun e (_ : e ∈ (univ : Finset E)) => he e)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, WeightedGreedy.energy] using hs

end KqR75.GreedyMoments

#print axioms KqR75.GreedyMoments.error_variances
#print axioms KqR75.GreedyMoments.weighted_absolute_error
