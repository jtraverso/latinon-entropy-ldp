module
public import PrefixCount

@[expose] public section
noncomputable section
namespace KqR75.WeightedGreedy

open Finset LatinonEntropy

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- Count the outputs of an event of mass at least one half. The
history score includes the logarithm of the order multiplicity. -/
theorem log_outputs_of_history_score (I : B → Finset E) (J : Finset E)
    (hI : ∀ b, (I b).Nonempty) (K : FiniteKernel (Option B)) (T : ℕ)
    (good : List (Option B) → Prop) (outputs : Finset (Finset B))
    (complete : List (Option B) → Finset B) (Q : ℝ)
    (hmass : (1 : ℝ) / 2 ≤ FiniteProcess.eventMass K T good)
    (hgood : ∀ h ∈ histories (Option B) T, good h → 0 < historyWeight K h →
      valid I J h ∧ none ∉ h ∧ complete h ∈ outputs ∧
        (complete h).filter (fun b => I b ⊆ J) = picked h ∧
        Real.log (historyWeight K h) + Real.log (T.factorial : ℝ) ≤ Q) :
    0 < outputs.card ∧ -Q - Real.log 2 ≤ Real.log (outputs.card : ℝ) := by
  have hfac : 0 < (T.factorial : ℝ) := by positivity
  have hM : 0 < Real.exp Q / (T.factorial : ℝ) := div_pos (Real.exp_pos _) hfac
  have hcard := completions_of_probability_cap I J hI K T good outputs complete
    (Real.exp Q / (T.factorial : ℝ)) hM.le (fun h hh hg hp => by
      obtain ⟨hv, hn, ho, hr, hlog⟩ := hgood h hh hg hp
      refine ⟨hv, hn, ho, hr, (le_div_iff₀ hfac).mpr ?_⟩
      apply (Real.log_le_log_iff (mul_pos hp hfac) (Real.exp_pos _)).mp
      rw [Real.log_mul hp.ne' hfac.ne', Real.log_exp]
      exact hlog)
  have hle : (1 : ℝ) / 2 ≤ (outputs.card : ℝ) * Real.exp Q := by
    have ht := hmass.trans hcard
    rw [mul_assoc, mul_comm (T.factorial : ℝ), div_mul_cancel₀ _ hfac.ne'] at ht
    exact ht
  have hpos : 0 < (outputs.card : ℝ) :=
    pos_of_mul_pos_left (lt_of_lt_of_le (by norm_num) hle) (Real.exp_pos _).le
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hle
  rw [Real.log_mul hpos.ne' (Real.exp_ne_zero _), Real.log_exp,
    one_div, Real.log_inv] at hlog
  exact ⟨by exact_mod_cast hpos, by linarith only [hlog]⟩

end KqR75.WeightedGreedy

#print axioms KqR75.WeightedGreedy.log_outputs_of_history_score
