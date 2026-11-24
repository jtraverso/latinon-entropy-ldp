module
public import TypeTails
public import GreedySchedule
public import TypeCounts

@[expose] public section
noncomputable section
namespace KqR75.PrefixTypeTests

open Finset LatinonEntropy

theorem mono_support {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (P Q : List Ω → Prop)
    (hPQ : ∀ h ∈ histories Ω T, 0 < historyWeight K h → P h → Q h) :
    FiniteProcess.eventMass K T P ≤ FiniteProcess.eventMass K T Q := by
  classical
  unfold FiniteProcess.eventMass
  apply sum_le_sum
  intro h hh
  by_cases hp : 0 < historyWeight K h
  · by_cases hP : P h
    · simp [hP, hPQ h hh hp hP]
    · by_cases hQ : Q h <;> simp [hP, hQ, historyWeight_nonneg]
  · have hz : historyWeight K h = 0 := le_antisymm (le_of_not_gt hp) (historyWeight_nonneg K h)
    simp [hz]

theorem prefix_union {Ω D : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (S : Finset D) (P : D → ℕ → List Ω → Prop) (δ : ℝ)
    (htail : ∀ d ∈ S, ∀ t ≤ T, FiniteProcess.eventMass K t (P d t) ≤ δ) :
    FiniteProcess.eventMass K T (fun h => ∃ d ∈ S, ∃ t ≤ T, P d t (h.drop (T - t))) ≤
      (S.card : ℝ) * (T + 1) * δ := by
  classical
  let U := S ×ˢ range (T + 1)
  let test := fun (j : D × ℕ) (h : List Ω) => P j.1 j.2 (h.drop (T - j.2))
  have hle := TypeTails.eventMass_exists_le K T U test
  have hsub : FiniteProcess.eventMass K T (fun h => ∃ d ∈ S, ∃ t ≤ T, P d t (h.drop (T - t))) ≤
      FiniteProcess.eventMass K T (fun h => ∃ j ∈ U, test j h) := by
    apply mono_support
    rintro h _ _ ⟨d, hd, t, ht, hp⟩
    exact ⟨(d,t), mem_product.mpr ⟨hd, mem_range.mpr (Nat.lt_succ_of_le ht)⟩, hp⟩
  refine hsub.trans (hle.trans ?_)
  calc
    _ ≤ ∑ _j ∈ U, δ := by
      apply sum_le_sum
      intro j hj
      obtain ⟨hd, ht⟩ := mem_product.mp hj
      have ht' : j.2 ≤ T := Nat.le_of_lt_succ (mem_range.mp ht)
      have he := TypeTails.eventMass_drop K j.2 (T - j.2) (P j.1 j.2)
      rw [Nat.add_sub_of_le ht'] at he
      exact he.trans_le (htail _ hd _ ht')
    _ = _ := by simp [U, card_product, nsmul_eq_mul, mul_assoc]

/-- Applying the terminal union bound to the two kinds of type tests
puts the count and proportion estimates on the same history law. -/
theorem counts_and_prefix_union {Ω D : Type*} [Fintype Ω] [DecidableEq Ω]
    (K : FiniteKernel Ω) (T : ℕ) (S : Finset D)
    (P : D → ℕ → List Ω → Prop) (Q : D → List Ω → Prop) (δ η : ℝ)
    (htail : ∀ d ∈ S, ∀ t ≤ T, FiniteProcess.eventMass K t (P d t) ≤ δ)
    (hcount : ∀ d ∈ S, FiniteProcess.eventMass K T (Q d) ≤ η) :
    FiniteProcess.eventMass K T (fun h =>
      (∃ d ∈ S, ∃ t ≤ T, P d t (h.drop (T - t))) ∨ (∃ d ∈ S, Q d h)) ≤
        (S.card : ℝ) * (T + 1) * δ + (S.card : ℝ) * η := by
  classical
  let P' := fun h : List Ω => ∃ d ∈ S, ∃ t ≤ T, P d t (h.drop (T - t))
  let Q' := fun h : List Ω => ∃ d ∈ S, Q d h
  have hp := prefix_union K T S P δ htail
  have hq : FiniteProcess.eventMass K T Q' ≤ (S.card : ℝ) * η := by
    refine (TypeTails.eventMass_exists_le K T S Q).trans ?_
    simpa only [sum_const, nsmul_eq_mul] using sum_le_sum hcount
  have hor : FiniteProcess.eventMass K T (fun h => P' h ∨ Q' h) ≤
      FiniteProcess.eventMass K T P' + FiniteProcess.eventMass K T Q' := by
    unfold FiniteProcess.eventMass
    rw [← sum_add_distrib]
    apply sum_le_sum
    intro h _
    by_cases hp : P' h <;> by_cases hq : Q' h <;> simp [hp, hq, historyWeight_nonneg]
  exact hor.trans (add_le_add hp hq)

end KqR75.PrefixTypeTests

#print axioms KqR75.PrefixTypeTests.prefix_union
#print axioms KqR75.PrefixTypeTests.counts_and_prefix_union
