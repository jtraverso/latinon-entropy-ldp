module
public import KqCore

@[expose] public section
noncomputable section
namespace KqR75

open Finset

/-- Inclusion-exclusion for a separable sum over ordered distinct triples. -/
theorem distinct_triple_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g h : ι → ℝ) :
    (∑ i, ∑ j, ∑ k, if i ≠ j ∧ j ≠ k ∧ k ≠ i then f i * g j * h k else 0) =
      (∑ i, f i) * (∑ j, g j) * (∑ k, h k) -
      (∑ i, f i * g i) * (∑ k, h k) -
      (∑ j, g j * h j) * (∑ i, f i) -
      (∑ k, h k * f k) * (∑ j, g j) + 2 * ∑ i, f i * g i * h i := by
  have he (i j k : ι) :
      (if i ≠ j ∧ j ≠ k ∧ k ≠ i then f i * g j * h k else 0) =
        f i * g j * h k - (if j = i then f i * g j * h k else 0) -
        (if k = j then g j * h k * f i else 0) -
        (if k = i then h k * f i * g j else 0) +
        2 * (if j = i then if k = i then f i * g j * h k else 0 else 0) := by
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k; simp; ring
      · have hki : k ≠ i := Ne.symm hik
        simp [hik, hki] <;> ring
    · have hji : j ≠ i := Ne.symm hij
      by_cases hjk : j = k
      · subst k; simp [hij, hji] <;> ring
      · have hkj : k ≠ j := Ne.symm hjk
        by_cases hki : k = i
        · subst k; simp [hij, hji] <;> ring
        · simp [hij, hji, hjk, hkj, hki]
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, ← Finset.mul_sum,
    ← Finset.sum_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] <;> ring

/-- The three-variable inequality used to control the distinct-triple moment. -/
theorem triple_fraction_gap (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 ≤ a * b * c⁻¹ + b * c * a⁻¹ + c * a * b⁻¹ - a - b - c := by
  have hid : (a * b * c⁻¹ + b * c * a⁻¹ + c * a * b⁻¹ - a - b - c) *
      (2 * a * b * c) = (a * b - a * c) ^ 2 + (a * b - b * c) ^ 2 +
        (a * c - b * c) ^ 2 := by
    field_simp [ha.ne', hb.ne', hc.ne']
    <;> ring
  have hp : 0 < 2 * a * b * c := by positivity
  have hn : 0 ≤ (a * b * c⁻¹ + b * c * a⁻¹ + c * a * b⁻¹ - a - b - c) *
      (2 * a * b * c) := by rw [hid]; positivity
  exact nonneg_of_mul_nonneg_left hn hp

end KqR75

#print axioms KqR75.distinct_triple_sum
#print axioms KqR75.triple_fraction_gap
