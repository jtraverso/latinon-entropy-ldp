module
public import BankDefect
public import BankScales

@[expose] public section
noncomputable section
namespace KqR75.BankCapacity

open Finset CompleteJohnson CliqueGram ColouredCliques SparseGram

/-- Summing the degree envelope controls the number of removed edges. -/
theorem edge_card_of_degree {n : ℕ} (X : Finset (Edge n)) (D : ℝ)
    (h : ∀ v : Fin n, ∑ e : X, incidence 2 e v ≤ D) :
    (X.card : ℝ) ≤ (n : ℝ) * D / 2 := by
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset (Fin n))) => h v)
  rw [Finset.sum_comm] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have he (e : X) : (∑ v : Fin n, incidence 2 (e : Edge n) v) = 2 :=
    by simpa using (incidence_row_sum (V := Fin n) 2 (e : Edge n))
  simp_rw [he] at hsum
  simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul] at hsum
  linarith

/-- Counting one marked edge per block in a packing bounds its size by
the pool of marked edges. -/
theorem block_card_of_marking {n q : ℕ} (P : Finset (Clique n q)) (X : Finset (Edge n))
    (hpack : ∀ e : Edge n, (P.filter fun b => e ∈ resources n q b).card ≤ 1)
    (hmark : ∀ b ∈ P, ((resources n q b) ∩ X).Nonempty) : P.card ≤ X.card := by
  classical
  let F := fun b : Clique n q => resources n q b ∩ X
  have hdis : Set.PairwiseDisjoint (P : Set (Clique n q)) F := by
    intro b hb c hc hbc
    apply disjoint_left.mpr
    intro e heb hec
    have hb' : b ∈ P.filter (fun t => e ∈ resources n q t) :=
      mem_filter.mpr ⟨hb, (mem_inter.mp heb).1⟩
    have hc' : c ∈ P.filter (fun t => e ∈ resources n q t) :=
      mem_filter.mpr ⟨hc, (mem_inter.mp hec).1⟩
    exact hbc (card_le_one.mp (hpack e) b hb' c hc')
  calc
    _ = ∑ _b ∈ P, (1 : ℕ) := by simp
    _ ≤ ∑ b ∈ P, (F b).card := sum_le_sum (fun b hb => card_pos.mpr (hmark b hb))
    _ = (P.biUnion F).card := (card_biUnion hdis).symm
    _ ≤ _ := card_le_card <| biUnion_subset.mpr (fun _ _ => inter_subset_right)

/-- Fix the number of copies before the bank is built. The resulting
integer budget still has the exponent required for placement. -/
theorem capacity_rounding {n : ℕ} {B : ℤ} {D z : ℝ}
    (hn : 1 ≤ n) (hB : 0 ≤ B) (hD : 0 ≤ D) (hz : z ≤ 2) :
    let X := (n : ℝ) ^ (2 - z)
    let ε := ⌈D * X⌉₊
    let M := B.toNat * ε
    (B * (ε : ℤ) ≤ (M : ℤ)) ∧
      ((M : ℝ) ≤ (B : ℝ) * (D + 1) * X) ∧
      ∀ a : ℤ, |(a : ℝ)| ≤ D * X → |a| ≤ (ε : ℤ) := by
  let X := (n : ℝ) ^ (2 - z)
  let ε := ⌈D * X⌉₊
  let M := B.toNat * ε
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hX : 1 ≤ X := Real.one_le_rpow hn₁ (by linarith)
  have hbN : (B.toNat : ℤ) = B := Int.toNat_of_nonneg hB
  have hbR : (B.toNat : ℝ) = (B : ℝ) := by exact_mod_cast hbN
  have hε : (ε : ℝ) ≤ (D + 1) * X := by
    have hcl := Nat.ceil_lt_add_one (show 0 ≤ D * X by positivity)
    change (ε : ℝ) < D * X + 1 at hcl
    linarith only [hcl, hX]
  refine ⟨?_, ?_, ?_⟩
  · change B * (ε : ℤ) ≤ (M : ℤ)
    simp [M, hbN]
  · change (M : ℝ) ≤ _
    rw [show (M : ℝ) = (B.toNat : ℝ) * (ε : ℝ) by dsimp [M]; push_cast; rfl, hbR, mul_assoc]
    exact mul_le_mul_of_nonneg_left hε (by exact_mod_cast hB)
  · intro a ha
    have he : |(a : ℝ)| ≤ (ε : ℝ) := ha.trans (Nat.le_ceil _)
    exact_mod_cast he

end KqR75.BankCapacity

#print axioms KqR75.BankCapacity.edge_card_of_degree
#print axioms KqR75.BankCapacity.block_card_of_marking
#print axioms KqR75.BankCapacity.capacity_rounding
