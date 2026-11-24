module
public import SeedLog

@[expose] public section
noncomputable section
namespace KqR75.ColouredCliques

open Finset

/-- The score accumulated by blocks of each type gives the relative
entropy correction with the sign in the counting formula. -/
theorem type_score_as_relative_entropy {τ : Type*} [Fintype τ]
    (m N : τ → ℝ) (b d : ℝ) (hb : 0 < b) (hd : 0 < d)
    (hN : ∀ t, 0 < N t) (hbt : ∑ t, m t = b) :
    -(∑ t, m t * Real.log (m t / N t)) =
      b * (Real.log d -
        ∑ t, (m t / b) * Real.log ((m t / b) / (N t / (b * d)))) := by
  let q := fun t => m t / b
  let p := fun t => N t / (b * d)
  have hratio (t : τ) : q t / p t = (m t / N t) * d := by
    dsimp [q, p]
    field_simp [hb.ne', hd.ne', (hN t).ne']
  have hterm (t : τ) : m t * Real.log (m t / N t) =
      m t * Real.log (q t / p t) - m t * Real.log d := by
    by_cases h : m t = 0
    · simp [h]
    · rw [hratio, Real.log_mul (div_ne_zero h (hN t).ne') hd.ne',
        mul_add, add_sub_cancel_right]
  simp_rw [hterm]
  rw [sum_sub_distrib, ← sum_mul, hbt, neg_sub, mul_sub, mul_sum]
  change b * Real.log d - (∑ t, m t * Real.log (q t / p t)) =
    b * Real.log d - ∑ t, b * (q t * Real.log (q t / p t))
  have he (t : τ) : b * (q t * Real.log (q t / p t)) = m t * Real.log (q t / p t) := by
    rw [← mul_assoc, mul_comm b, show q t * b = m t from div_mul_cancel₀ _ hb.ne']
  simp_rw [he]

end KqR75.ColouredCliques

#print axioms KqR75.ColouredCliques.type_score_as_relative_entropy
