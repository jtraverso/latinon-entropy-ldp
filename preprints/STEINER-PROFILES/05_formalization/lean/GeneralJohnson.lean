module
public import KqCore

@[expose] public section
noncomputable section
namespace KqR75.GeneralJohnson

def s1 (q n : ℝ) := (q - 2) / (n - 2)
def s2 (q n : ℝ) := (q - 2) * (q - 3) / ((n - 2) * (n - 3))
def den (q n : ℝ) := q * (q - 1) * (n - q) * (n - q - 1)
def u0 (q n : ℝ) :=
  (q * (q - 1) * n ^ 2 - q * (7 * q - 9) * n +
    4 * (3 * q ^ 2 - 5 * q + 1)) / den q n
def u1 (q n : ℝ) := -(q - 2) * (q * n - 4 * q + 2) / den q n
def u2 (q n : ℝ) := 2 * (q - 2) / (q * (n - q) * (n - q - 1))

def alpha (q n : ℝ) := |u0 q n| + 2 * (n - 2) * |u1 q n| +
  (n - 2) * (n - 3) / 2 * |u2 q n|

def alphaNum (q n : ℝ) :=
  2 * (2 * n ^ 2 * q ^ 2 - 4 * n ^ 2 * q + n ^ 2 - 12 * n * q ^ 2 +
    26 * n * q - 9 * n + 17 * q ^ 2 - 39 * q + 16)

/-- A row-sum envelope using only the vertex-incidence Gram relations. -/
def envelope (q n : ℝ) := u0 q n - 2 * u1 q n + u2 q n -
  2 * (n - 1) * (u1 q n - u2 q n) + n * (n - 1) / 2 * u2 q n

def envelopeNum (q n : ℝ) :=
  2 * (2 * n ^ 2 * q ^ 2 - 4 * n ^ 2 * q + n ^ 2 - 6 * n * q ^ 2 +
    10 * n * q - n + 5 * q ^ 2 - 7 * q)

set_option maxHeartbeats 800000 in
/-- General-q scalar products for the three orbits of pairs of edges.
This does not itself prove the finite-set orbit counts or a matrix inverse. -/
theorem orbit_identities (q n : ℝ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) :
    u0 q n + 2 * (n - 2) * s1 q n * u1 q n +
      (n - 2) * (n - 3) / 2 * s2 q n * u2 q n = 1 ∧
    u1 q n + s1 q n * u0 q n + (n - 2) * s1 q n * u1 q n +
      (n - 3) * s1 q n * u2 q n + (n - 3) * s2 q n * u1 q n +
      (n - 3) * (n - 4) / 2 * s2 q n * u2 q n = 0 ∧
    u2 q n + s2 q n * u0 q n + 4 * s1 q n * u1 q n +
      2 * (n - 4) * s1 q n * u2 q n + 2 * (n - 4) * s2 q n * u1 q n +
      (n - 4) * (n - 5) / 2 * s2 q n * u2 q n = 0 := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  have h2 : n - 2 ≠ 0 := by linarith
  have h3 : n - 3 ≠ 0 := by linarith
  have ha : n - q ≠ 0 := by linarith
  have hb : n - q - 1 ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_⟩ <;> dsimp only [s1, s2, u0, u1, u2, den] <;>
    field_simp [hq0, hq1, h2, h3, ha, hb] <;> ring

/-- Signs of the inverse coefficients, beyond the nondegenerate incidence range. -/
theorem coefficient_signs (q n : ℝ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) :
    0 ≤ u0 q n ∧ u1 q n ≤ 0 ∧ 0 ≤ u2 q n := by
  have hu : 0 ≤ q - 3 := by linarith
  have hv : 0 ≤ n - q - 2 := by linarith
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have hq2 : 0 ≤ q - 2 := by linarith
  have ha : 0 < n - q := by linarith
  have hb : 0 < n - q - 1 := by linarith
  have hD : 0 < den q n := by dsimp [den]; positivity
  have hpoly : q * (q - 1) * n ^ 2 - q * (7 * q - 9) * n +
      4 * (3 * q ^ 2 - 5 * q + 1) =
      (q - 3 + 3) * (q - 3 + 2) * (n - q - 2) ^ 2 +
      (q - 3 + 3) * (2 * (q - 3) ^ 2 + 7 * (q - 3) + 8) * (n - q - 2) +
      (q - 3) ^ 4 + 8 * (q - 3) ^ 3 + 25 * (q - 3) ^ 2 + 36 * (q - 3) + 22 := by
    ring
  have hn4 : 0 ≤ n - 4 := by linarith
  have hqn : 0 ≤ q * n - 4 * q + 2 := by nlinarith [mul_nonneg hq0.le hn4]
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [u0]
    rw [hpoly]
    positivity
  · dsimp only [u1]
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by linarith)) hqn) hD.le
  · dsimp only [u2]
    positivity

theorem alpha_eq (q n : ℝ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) :
    alpha q n = alphaNum q n / den q n := by
  obtain ⟨h0, h1, h2⟩ := coefficient_signs q n hq hn
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  have ha : n - q ≠ 0 := by linarith
  have hb : n - q - 1 ≠ 0 := by linarith
  dsimp only [alpha]
  rw [abs_of_nonneg h0, abs_of_nonpos h1, abs_of_nonneg h2]
  dsimp only [u0, u1, u2, alphaNum, den]
  field_simp [hq0, hq1, ha, hb]
  <;> ring

/-- A uniform explicit bound for the column sum of the Johnson inverse coefficients. -/
theorem alpha_le_four (q n : ℝ) (hq : 3 ≤ q) (hn : 2 * q ^ 2 ≤ n) :
    alpha q n ≤ 4 := by
  have hu : 0 ≤ q - 3 := by linarith
  have hv : 0 ≤ n - 2 * q ^ 2 := sub_nonneg.mpr hn
  have hnq : q + 2 ≤ n := by nlinarith [sq_nonneg (q - 3)]
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have ha : 0 < n - q := by linarith
  have hb : 0 < n - q - 1 := by linarith
  have hD : 0 < den q n := by dsimp [den]; positivity
  have hid : 4 * den q n - alphaNum q n =
      52 * (q - 3) ^ 4 + 8 * (q - 3) ^ 3 * (n - 2 * q ^ 2) +
      528 * (q - 3) ^ 3 + 92 * (q - 3) ^ 2 * (n - 2 * q ^ 2) +
      1942 * (q - 3) ^ 2 + 4 * (q - 3) * (n - 2 * q ^ 2) ^ 2 +
      288 * (q - 3) * (n - 2 * q ^ 2) + 3090 * (q - 3) +
      10 * (n - 2 * q ^ 2) ^ 2 + 270 * (n - 2 * q ^ 2) + 1804 := by
    dsimp only [den, alphaNum]
    ring
  have hp : 0 ≤ 4 * den q n - alphaNum q n := by rw [hid]; positivity
  rw [alpha_eq q n hq hnq]
  exact (div_le_iff₀ hD).mpr (by linarith)

theorem envelope_eq (q n : ℝ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) :
    envelope q n = envelopeNum q n / den q n := by
  have hq0 : q ≠ 0 := by linarith
  have hq1 : q - 1 ≠ 0 := by linarith
  have ha : n - q ≠ 0 := by linarith
  have hb : n - q - 1 ≠ 0 := by linarith
  dsimp only [envelope, envelopeNum, u0, u1, u2, den]
  field_simp [hq0, hq1, ha, hb]
  <;> ring

theorem envelope_le_four (q n : ℝ) (hq : 3 ≤ q) (hn : 2 * q ^ 2 ≤ n) :
    envelope q n ≤ 4 := by
  have hu : 0 ≤ q - 3 := by linarith
  have hv : 0 ≤ n - 2 * q ^ 2 := sub_nonneg.mpr hn
  have hnq : q + 2 ≤ n := by nlinarith [sq_nonneg (q - 3)]
  have hq0 : 0 < q := by linarith
  have hq1 : 0 < q - 1 := by linarith
  have ha : 0 < n - q := by linarith
  have hb : 0 < n - q - 1 := by linarith
  have hD : 0 < den q n := by dsimp [den]; positivity
  have hid : 4 * den q n - envelopeNum q n =
      28 * (q - 3) ^ 4 + 8 * (q - 3) ^ 3 * (n - 2 * q ^ 2) +
      304 * (q - 3) ^ 3 + 80 * (q - 3) ^ 2 * (n - 2 * q ^ 2) +
      1214 * (q - 3) ^ 2 + 4 * (q - 3) * (n - 2 * q ^ 2) ^ 2 +
      248 * (q - 3) * (n - 2 * q ^ 2) + 2114 * (q - 3) +
      10 * (n - 2 * q ^ 2) ^ 2 + 242 * (n - 2 * q ^ 2) + 1356 := by
    dsimp only [den, envelopeNum]
    ring
  have hp : 0 ≤ 4 * den q n - envelopeNum q n := by rw [hid]; positivity
  rw [envelope_eq q n hq hnq]
  exact (div_le_iff₀ hD).mpr (by linarith)

end KqR75.GeneralJohnson

#print axioms KqR75.GeneralJohnson.orbit_identities
#print axioms KqR75.GeneralJohnson.alpha_le_four
#print axioms KqR75.GeneralJohnson.envelope_le_four
