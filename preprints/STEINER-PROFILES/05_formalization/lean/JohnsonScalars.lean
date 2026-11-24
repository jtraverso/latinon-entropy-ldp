module
public import KqCore

@[expose] public section
noncomputable section
namespace KqR75.Johnson

def s1 (n : ℝ) := 2 / (n - 2)
def s2 (n : ℝ) := 2 / ((n - 2) * (n - 3))
def u0 (n : ℝ) := (3 * n ^ 2 - 19 * n + 29) / (3 * (n - 5) * (n - 4))
def u1 (n : ℝ) := -(2 * n - 7) / (3 * (n - 5) * (n - 4))
def u2 (n : ℝ) := 1 / ((n - 5) * (n - 4))
def alpha (n : ℝ) := (17 * n ^ 2 - 97 * n + 132) / (6 * (n - 5) * (n - 4))

/-- Scalar orbit identities from the original R28 certificate.
The combinatorial orbit multiplicities and the matrix inverse remain separate obligations. -/
theorem orbit_identities (n : ℝ) (hn : 6 ≤ n) :
    u0 n + 2 * (n - 2) * s1 n * u1 n +
      (n - 2) * (n - 3) / 2 * s2 n * u2 n = 1 ∧
    u1 n + s1 n * u0 n + (n - 2) * s1 n * u1 n +
      (n - 3) * s1 n * u2 n + (n - 3) * s2 n * u1 n +
      (n - 3) * (n - 4) / 2 * s2 n * u2 n = 0 ∧
    u2 n + s2 n * u0 n + 4 * s1 n * u1 n +
      2 * (n - 4) * s1 n * u2 n + 2 * (n - 4) * s2 n * u1 n +
      (n - 4) * (n - 5) / 2 * s2 n * u2 n = 0 := by
  have h2 : n - 2 ≠ 0 := by linarith
  have h3 : n - 3 ≠ 0 := by linarith
  have h4 : n - 4 ≠ 0 := by linarith
  have h5 : n - 5 ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_⟩ <;> dsimp only [s1, s2, u0, u1, u2] <;>
    field_simp [h2, h3, h4, h5] <;> ring

theorem alpha_le_four (n : ℝ) (hn : 16 ≤ n) : alpha n ≤ 4 := by
  have h5 : 0 < n - 5 := by linarith
  have h4 : 0 < n - 4 := by linarith
  have hd : 0 < 6 * (n - 5) * (n - 4) := by positivity
  have hm : 0 ≤ n - 16 := by linarith
  dsimp only [alpha]
  apply (div_le_iff₀ hd).mpr
  nlinarith only [hm, sq_nonneg (n - 16)]

theorem alpha_le_three (n : ℝ) (hn : 1000 ≤ n) : alpha n ≤ 3 := by
  have h5 : 0 < n - 5 := by linarith
  have h4 : 0 < n - 4 := by linarith
  have hd : 0 < 6 * (n - 5) * (n - 4) := by positivity
  have hm : 0 ≤ n - 1000 := by linarith
  dsimp only [alpha]
  apply (div_le_iff₀ hd).mpr
  nlinarith only [hm, sq_nonneg (n - 1000)]

end KqR75.Johnson

#print axioms KqR75.Johnson.orbit_identities
#print axioms KqR75.Johnson.alpha_le_four
#print axioms KqR75.Johnson.alpha_le_three
