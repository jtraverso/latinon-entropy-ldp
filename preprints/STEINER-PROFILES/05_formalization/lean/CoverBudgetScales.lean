module
public import CoverRatios

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

/-- Separate the pairs within each of two parts from the crossing pairs. -/
private theorem choose_two_add (l k : ℕ) :
    (l + k).choose 2 = l.choose 2 + k.choose 2 + l * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep (j : ℕ) : (j + 1).choose 2 = j + j.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' j 1
    rw [Nat.add_succ, hstep (l + k), hstep k, ih, Nat.mul_succ]
    omega

theorem star_edge_exponent {q : ℕ} (hq : 3 ≤ q) :
    2 * (q - 3) + (q - 3).choose 2 = (q - 1).choose 2 - 1 := by
  have he := choose_two_add (q - 3) 2
  rw [show q - 3 + 2 = q - 1 by omega] at he
  have htwo : (2 : ℕ).choose 2 = 1 := by decide
  rw [htwo] at he
  omega

theorem pair_lower_exponent {q : ℕ} (hq : 2 ≤ q) :
    2 * (q - 2) + (q - 2).choose 2 = q.choose 2 - 1 := by
  have he := choose_two_add (q - 2) 2
  rw [show q - 2 + 2 = q by omega] at he
  have htwo : (2 : ℕ).choose 2 = 1 := by decide
  rw [htwo] at he
  omega

theorem pair_vertex_exponent {q : ℕ} (hq : 3 ≤ q) :
    3 * (q - 3) + (q - 3).choose 2 = (q.choose 2 - 1) - 2 := by
  have he := choose_two_add (q - 3) 3
  rw [show q - 3 + 3 = q by omega] at he
  have hthree : (3 : ℕ).choose 2 = 3 := by decide
  rw [hthree] at he
  omega

theorem pair_edge_exponent {q : ℕ} (hq : 4 ≤ q) :
    4 * (q - 4) + (q - 4).choose 2 = (q.choose 2 - 1) - 5 := by
  have he := choose_two_add (q - 4) 4
  rw [show q - 4 + 4 = q by omega] at he
  have hfour : (4 : ℕ).choose 2 = 6 := by decide
  rw [hfour] at he
  omega

/-- The clique lower bound from the cut lemma at a given minimum
size, with all fixed factors displayed. -/
theorem star_candidate_scale (l : ℕ) {x α c S p : ℝ}
    (hx : 0 ≤ x) (hc : 0 ≤ c) (hp : 0 ≤ p) (hl : 0 < l)
    (hS : c * x ^ α ≤ S) :
    ((c / (4 * l)) ^ l / 2 ^ l.choose 2) * x ^ (α * (l : ℝ)) * p ^ l.choose 2 ≤
      (S / (4 * l)) ^ l * (p / 2) ^ l.choose 2 := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have h0 : 0 ≤ c * x ^ α / (4 * l) := by positivity
  have hle := div_le_div_of_nonneg_right hS (show 0 ≤ 4 * (l : ℝ) by positivity)
  calc
    _ = (c * x ^ α / (4 * l)) ^ l * (p / 2) ^ l.choose 2 := by
      rw [show c * x ^ α / (4 * l) = (c / (4 * l)) * x ^ α by ring, mul_pow,
        ← Real.rpow_natCast (x ^ α) l, ← Real.rpow_mul hx, div_pow p 2 (l.choose 2)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hle _) (by positivity)

/-- Express the rooted lower bound in the same scale used by the
obstruction ratios. -/
theorem pair_candidate_scale {q : ℕ} (hq : 3 ≤ q) (x p : ℝ) :
    let l := q - 2
    ((1 / (8 * l : ℝ)) ^ l / 2 ^ l.choose 2) * x ^ l * p ^ (q.choose 2 - 1) =
      (x * p ^ 2 / (8 * l)) ^ l * (p / 2) ^ l.choose 2 := by
  let l := q - 2
  change ((1 / (8 * l : ℝ)) ^ l / 2 ^ l.choose 2) * x ^ l * p ^ (q.choose 2 - 1) =
    (x * p ^ 2 / (8 * l)) ^ l * (p / 2) ^ l.choose 2
  have hmain : (x * p ^ 2 / (8 * l : ℝ)) ^ l =
      (1 / (8 * l : ℝ)) ^ l * x ^ l * p ^ (2 * l) := by
    rw [show x * p ^ 2 / (8 * l : ℝ) = (1 / (8 * l : ℝ)) * x * p ^ 2 by ring,
      mul_pow, mul_pow, ← pow_mul]
  rw [← pair_lower_exponent (by omega : 2 ≤ q), pow_add, show q - 2 = l by rfl,
    hmain, div_pow p 2 (l.choose 2)]
  ring

end KqR75.CoverDown

#print axioms KqR75.CoverDown.star_edge_exponent
#print axioms KqR75.CoverDown.pair_lower_exponent
#print axioms KqR75.CoverDown.pair_vertex_exponent
#print axioms KqR75.CoverDown.pair_edge_exponent
#print axioms KqR75.CoverDown.star_candidate_scale
#print axioms KqR75.CoverDown.pair_candidate_scale
