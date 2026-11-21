/-
 R73: exact mean-degree identities for the Bernoulli typed-token lift.
 Algebraic P1 only; does not claim concentration or GJKKL integration.
-/
module
public import TypedClique.R72.P3Universal
@[expose] public section
namespace TypedClique.R73
open Finset
variable {Block Pair Color : Type*}
variable [DecidableEq Block] [DecidableEq Pair] [DecidableEq Color]

theorem token_weight_sum (a : ℕ) (ha : 0 < a) (d0 w : ℝ) :
    (∑ _j : Fin a, d0 * w / (a : ℝ)) = d0 * w := by
  classical
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  calc
    (∑ _j : Fin a, d0 * w / (a : ℝ)) =
        (a : ℝ) * (d0 * w / (a : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = d0 * w := by field_simp

theorem physical_expected_degree
    (pool : Finset Block) (footprint : Block → Finset Pair)
    (color : Block → Color) (capacity : Color → ℕ)
    (nu : Block → ℝ) (d0 : ℝ) (e : Pair)
    (hcapacity : ∀ b ∈ pool, 0 < capacity (color b))
    (hload : (∑ b ∈ pool, if e ∈ footprint b then nu b else 0) = 1) :
    (∑ b ∈ pool, if e ∈ footprint b then
      (∑ _j : Fin (capacity (color b)),
        d0 * nu b / (capacity (color b) : ℝ)) else 0) = d0 := by
  classical
  calc
    (∑ b ∈ pool, if e ∈ footprint b then
      (∑ _j : Fin (capacity (color b)),
        d0 * nu b / (capacity (color b) : ℝ)) else 0) =
      ∑ b ∈ pool, if e ∈ footprint b then d0 * nu b else 0 := by
        apply Finset.sum_congr rfl
        intro b hb
        by_cases he : e ∈ footprint b
        · simp [he, token_weight_sum (capacity (color b)) (hcapacity b hb) d0 (nu b)]
        · simp [he]
    _ = d0 * (∑ b ∈ pool, if e ∈ footprint b then nu b else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases he : e ∈ footprint b <;> simp [he]
    _ = d0 := by rw [hload]; ring

theorem token_expected_degree
    (pool : Finset Block) (color : Block → Color)
    (capacity : Color → ℕ) (nu : Block → ℝ)
    (d0 : ℝ) (i : Color) (j : Fin (capacity i)) :
    (∑ b ∈ pool, if color b = i then
       d0 * nu b / (capacity i : ℝ) else 0) =
       (d0 / (capacity i : ℝ)) *
         (∑ b ∈ pool, if color b = i then nu b else 0) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hi : color b = i
  · simp [hi]; ring
  · simp [hi]
end TypedClique.R73
