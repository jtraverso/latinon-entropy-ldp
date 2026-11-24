module
public import KqCore
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section
namespace KqR75.GradedColumns

open Finset

variable {D R : Type*} [Fintype D] [DecidableEq D] [CommRing R]

def combine (col : D → D → R) (a : D → R) (i : D) : R :=
  ∑ j, a j * col j i

/-- Eliminate the highest remaining grade at each step. The proof uses
only addition and multiplication, so it also produces integer coefficients. -/
theorem solve (degree : D → ℕ) (col : D → D → R)
    (hdiag : ∀ i, col i i = 1)
    (htri : ∀ i j, degree j ≤ degree i → j ≠ i → col j i = 0)
    (k : ℕ) (v : D → R) (hv : ∀ i, k ≤ degree i → v i = 0) :
    ∃ a : D → R, combine col a = v ∧ ∀ i, k ≤ degree i → a i = 0 := by
  classical
  induction k generalizing v with
  | zero =>
    refine ⟨0, ?_, fun _ _ => rfl⟩
    funext i
    simp [combine, hv i (Nat.zero_le _)]
  | succ k ih =>
    let b : D → R := fun i => if degree i = k then v i else 0
    have hb (i : D) (hi : k ≤ degree i) : combine col b i = v i := by
      have hoff (j : D) (hji : j ≠ i) : b j * col j i = 0 := by
        by_cases hj : degree j = k
        · rw [htri i j (by rwa [hj]) hji, mul_zero]
        · simp [b, hj]
      have hself : b i = v i := by
        by_cases hk : degree i = k
        · simp [b, hk]
        · have hi' : k + 1 ≤ degree i := by omega
          simp [b, hk, hv i hi']
      unfold combine
      rw [Finset.sum_eq_single i (fun j _ hji => hoff j hji) (by simp), hself, hdiag, mul_one]
    obtain ⟨a, ha, haz⟩ := ih (fun i => v i - combine col b i)
      (fun i hi => sub_eq_zero.mpr (hb i hi).symm)
    refine ⟨fun j => a j + b j, ?_, ?_⟩
    · funext i
      have hai := congrFun ha i
      change combine col a i = v i - combine col b i at hai
      unfold combine
      simp only [add_mul, Finset.sum_add_distrib]
      change combine col a i + combine col b i = v i
      rw [hai, sub_add_cancel]
    · intro i hi
      have hk : degree i ≠ k := by omega
      simp [b, hk, haz i (by omega)]

theorem solve_all (degree : D → ℕ) (col : D → D → R)
    (hdiag : ∀ i, col i i = 1)
    (htri : ∀ i j, degree j ≤ degree i → j ≠ i → col j i = 0)
    (v : D → R) : ∃ a : D → R, combine col a = v := by
  let k := univ.sup degree + 1
  have hv (i : D) (hi : k ≤ degree i) : v i = 0 := by
    have hh : degree i ≤ univ.sup degree := Finset.le_sup (f := degree) (mem_univ i)
    dsimp only [k] at hi
    omega
  obtain ⟨a, ha, _⟩ := solve degree col hdiag htri k v hv
  exact ⟨a, ha⟩

/-- Each right-inverse column is obtained by eliminating a coordinate
vector. These fixed columns can later be used for every histogram defect. -/
theorem right_inverse (degree : D → ℕ) (col : D → D → R)
    (hdiag : ∀ i, col i i = 1)
    (htri : ∀ i j, degree j ≤ degree i → j ≠ i → col j i = 0) :
    ∃ L : D → D → R, ∀ i j, combine col (L j) i = if i = j then 1 else 0 := by
  choose L hL using fun j : D =>
    solve_all degree col hdiag htri (fun i => if i = j then 1 else 0)
  exact ⟨L, fun i j => congrFun (hL j) i⟩

end KqR75.GradedColumns

#print axioms KqR75.GradedColumns.solve_all
#print axioms KqR75.GradedColumns.right_inverse
