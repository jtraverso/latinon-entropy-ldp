module
public import StoppedPhysical

@[expose] public section
noncomputable section
namespace KqR75.StoppingGuard

open StoppedPhysical
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- A bound on the integrated energy implies the physical regularity
guard. Only deterministic scale inequalities remain to be instantiated. -/
theorem regular_of_threshold (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (r : ℕ) (M : ℝ) (hr : 1 ≤ r) (hM : 0 < M) (n β u : ℝ) (hn : 1 ≤ n)
    (h : List (Option B)) (hv : WeightedGreedy.valid I J h)
    (hm : n ≤ mass M (WeightedGreedy.selectedCount h))
    (hsmall : 64 * (r : ℝ) ^ 2 * β ≤
      (mass M (WeightedGreedy.selectedCount h) / (M : ℝ)) ^ (r - 1))
    (hscale : 16 * (r : ℝ) * u ≤ (M : ℝ) *
      (mass M (WeightedGreedy.selectedCount h) / (M : ℝ)) ^ (4 * r - 1))
    (henergy : WeightedGreedy.stoppedEnergy I μ J (profile (r - 1) M) (profile (2 * r) M) h ≤ u) :
    regular I μ J r M n β h := by
  let i := WeightedGreedy.selectedCount h
  let m := mass M i
  let p := m / (M : ℝ)
  let k := profile (r - 1) M i
  let f := profile (2 * r) M i
  let X := WeightedGreedy.energy I μ J h k
  have hM0 : (0 : ℝ) < M := hM
  have hm0 : 0 < m := by dsimp only [m, i]; linarith only [hn, hm]
  have hi : (i : ℝ) ≤ M := by dsimp only [m, mass] at hm0; linarith only [hm0]
  have hp : 0 < p := div_pos hm0 hM0
  have hk : k = p ^ (r - 1) := profile_eq (r - 1) M i hM hi
  have hf : f = p ^ (2 * r) := profile_eq (2 * r) M i hM hi
  have hk0 : 0 < k := by rw [hk]; exact pow_pos hp _
  have hf0 : 0 < f := by rw [hf]; exact pow_pos hp _
  have hmass : m = (M : ℝ) * p := by dsimp only [p]; field_simp [hM0.ne']
  have hproduct : (m * k ^ 2) * f = (M : ℝ) * p ^ (4 * r - 1) := by
    rw [hmass, hk, hf]
    have hexp : 4 * r - 1 = 1 + (r - 1) * 2 + 2 * r := by omega
    rw [hexp]
    simp only [pow_add, pow_one, pow_mul]
    ring
  have he : (16 * (r : ℝ) * X) * f ≤ (m * k ^ 2) * f := by
    calc
      _ = 16 * (r : ℝ) * (f * X) := by ring
      _ ≤ 16 * (r : ℝ) * u := mul_le_mul_of_nonneg_left henergy (by positivity)
      _ ≤ (M : ℝ) * p ^ (4 * r - 1) := hscale
      _ = _ := hproduct.symm
  have hraw : 16 * (r : ℝ) * X ≤ m * k ^ 2 := le_of_mul_le_mul_right he hf0
  refine ⟨hv, hm, hk0, ?_, hraw⟩
  change 64 * (r : ℝ) ^ 2 * β ≤ k
  rw [hk]
  exact hsmall

end KqR75.StoppingGuard

#print axioms KqR75.StoppingGuard.regular_of_threshold
