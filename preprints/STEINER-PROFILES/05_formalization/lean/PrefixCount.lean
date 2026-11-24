module
public import PrefixRecovery

@[expose] public section
noncomputable section
namespace KqR75.WeightedGreedy

open Finset LatinonEntropy
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- A positive history has the log probability obtained by summing
the actual logarithmic transition probabilities. -/
theorem log_historyWeight (K : FiniteKernel (Option B)) (h : List (Option B))
    (hp : 0 < historyWeight K h) :
    Real.log (historyWeight K h) =
      pathSum (fun p b => Real.log (K.transition p b)) h := by
  induction h with
  | nil => simp [historyWeight, pathSum]
  | cons b h ih =>
    change 0 < historyWeight K h * K.transition h b at hp
    have hprev : 0 < historyWeight K h := by
      by_contra! hneg
      exact not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg hneg (K.nonneg _ _)) hp
    have hnext : 0 < K.transition h b := by
      by_contra! hneg
      exact not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos hprev.le hneg) hp
    rw [historyWeight, pathSum, Real.log_mul hprev.ne' hnext.ne', ih hprev]

/-- A mass bound for good histories and a per-history probability cap
give a count of physical completions. The only multiplicity cost is T!. -/
theorem completions_of_probability_cap (I : B → Finset E) (J : Finset E)
    (hI : ∀ b, (I b).Nonempty) (K : FiniteKernel (Option B)) (T : ℕ)
    (good : List (Option B) → Prop) (outputs : Finset (Finset B))
    (complete : List (Option B) → Finset B) (M : ℝ) (hM : 0 ≤ M)
    (hgood : ∀ h ∈ histories (Option B) T, good h → 0 < historyWeight K h →
      valid I J h ∧ none ∉ h ∧ complete h ∈ outputs ∧
        (complete h).filter (fun b => I b ⊆ J) = picked h ∧ historyWeight K h ≤ M) :
    FiniteProcess.eventMass K T good ≤ (outputs.card : ℝ) * T.factorial * M := by
  classical
  let G := (histories (Option B) T).filter (fun h => good h ∧ 0 < historyWeight K h)
  have h1 : FiniteProcess.eventMass K T good = ∑ h ∈ G, historyWeight K h := by
    unfold FiniteProcess.eventMass
    rw [sum_filter]
    apply sum_congr rfl
    intro h _
    by_cases hp : good h
    · by_cases hpos : 0 < historyWeight K h
      · simp [hp, hpos]
      · have hz : historyWeight K h = 0 :=
          le_antisymm (le_of_not_gt hpos) (historyWeight_nonneg _ _)
        simp [hz]
    · simp [hp]
  have h2 (h : List (Option B)) (hh : h ∈ G) :=
    hgood h (mem_filter.mp hh).1 (mem_filter.mp hh).2.1 (mem_filter.mp hh).2.2
  have hf (P : Finset B) : (G.filter (fun h => complete h = P)).card ≤ T.factorial := by
    apply order_fibre_card I J hI T (P.filter (fun b => I b ⊆ J))
    intro h hh
    obtain ⟨hg, hp⟩ := mem_filter.mp hh
    obtain ⟨hv, hn, _, hr, _⟩ := h2 h hg
    rw [hp] at hr
    exact ⟨histories_length (mem_filter.mp hg).1, hv, hn, hr.symm⟩
  have h3 : G.card ≤ outputs.card * T.factorial := by
    rw [card_eq_sum_card_fiberwise (f := complete) (fun h hh => (h2 h hh).2.2.1)]
    exact (sum_le_sum (fun P _ => hf P)).trans_eq (by simp [Nat.nsmul_eq_mul])
  calc
    _ = ∑ h ∈ G, historyWeight K h := h1
    _ ≤ ∑ _h ∈ G, M := sum_le_sum (fun h hh => (h2 h hh).2.2.2.2)
    _ = (G.card : ℝ) * M := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast h3) hM

end KqR75.WeightedGreedy

#print axioms KqR75.WeightedGreedy.log_historyWeight
#print axioms KqR75.WeightedGreedy.completions_of_probability_cap
