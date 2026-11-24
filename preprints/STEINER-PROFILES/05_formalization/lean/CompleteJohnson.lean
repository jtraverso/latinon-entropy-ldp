module
public import CliqueGram
public import IncidenceAlgebra

@[expose] public section
noncomputable section
namespace KqR75.CompleteJohnson

open Finset GeneralJohnson CliqueGram
open scoped Matrix

abbrev Edge (n : ℕ) := ((univ : Finset (Fin n)).powersetCard 2)

def middle (n : ℕ) : Matrix (Edge n) (Edge n) ℝ :=
  incidence (V := Fin n) 2 * (incidence (V := Fin n) 2)ᵀ

def operator (n q : ℕ) : Matrix (Edge n) (Edge n) ℝ :=
  (1 - 2 * s1 q n + s2 q n) • 1 +
    (s1 q n - s2 q n) • middle n + s2 q n • IncidenceAlgebra.ones

def inverseOperator (n q : ℕ) : Matrix (Edge n) (Edge n) ℝ :=
  (u0 q n - 2 * u1 q n + u2 q n) • 1 +
    (u1 q n - u2 q n) • middle n + u2 q n • IncidenceAlgebra.ones

def normalizedGram (n q : ℕ) : Matrix (Edge n) (Edge n) ℝ :=
  (((n - 2).choose (q - 2) : ℝ))⁻¹ •
    (pairIncidence (V := Fin n) q * (pairIncidence (V := Fin n) q)ᵀ)

theorem operator_mul_inverse (n q : ℕ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) :
    operator n q * inverseOperator n q = 1 := by
  let T := incidence (V := Fin n) 2
  have hrow (e : Edge n) : ∑ v, T e v = 2 := incidence_row_sum 2 e
  have hn1 : 1 ≤ n := by omega
  have hcol (v : Fin n) : ∑ e, T e v = (n : ℝ) - 1 := by
    simpa only [Fintype.card_fin, Nat.cast_sub hn1, Nat.cast_one] using incidence_column_sum v
  have hones : Matrix.of (fun (_ : Fin n) (_ : Fin n) => (1 : ℝ)) =
      (IncidenceAlgebra.ones : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    rfl
  have hgram : Tᵀ * T = ((n : ℝ) - 2) • (1 : Matrix (Fin n) (Fin n) ℝ) +
      IncidenceAlgebra.ones := by
    simpa only [T, Fintype.card_fin, hones] using
      vertex_gram (V := Fin n) (by simpa only [Fintype.card_fin] using (show 2 ≤ n by omega))
  exact IncidenceAlgebra.inverse_from_incidence T q n
    (by exact_mod_cast hq) (by exact_mod_cast hn) (by simp) hrow hcol hgram

/-- The incidence-algebra operator is the normalized Gram of actual q-cliques. -/
theorem normalizedGram_eq_operator (n q : ℕ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) :
    normalizedGram n q = operator n q := by
  classical
  have hD : ((n - 2).choose (q - 2) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : q - 2 ≤ n - 2)).ne'
  ext e f
  have he : (e : Finset (Fin n)).card = 2 := (Finset.mem_powersetCard.mp e.property).2
  have hf : (f : Finset (Fin n)).card = 2 := (Finset.mem_powersetCard.mp f.property).2
  have hval : normalizedGram n q e f =
      (multiplicity q (e : Finset (Fin n)) (f : Finset (Fin n)) : ℝ) /
      ((n - 2).choose (q - 2) : ℝ) := by
    simp only [normalizedGram, Matrix.smul_apply, smul_eq_mul, pair_gram_entry, div_eq_mul_inv]
    ring
  have hop : operator n q e f =
      (1 - 2 * s1 q n + s2 q n) * (if e = f then 1 else 0) +
      (s1 q n - s2 q n) * (((e : Finset (Fin n)) ∩ (f : Finset (Fin n))).card : ℝ) +
      s2 q n := by
    simp only [operator, middle, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply, edge_gram_entry, IncidenceAlgebra.ones, mul_one]
  rw [hval, hop]
  by_cases hef : e = f
  · subst f
    have hm := multiplicity_eq_choose q (e : Finset (Fin n)) e (by simp [he]; omega)
    simp only [Finset.union_self, he, Fintype.card_fin] at hm
    rw [hm, div_self hD]
    simp only [ite_true, mul_one, Finset.inter_self, he, Nat.cast_ofNat]
    ring
  · have hi : ((e : Finset (Fin n)) ∩ (f : Finset (Fin n))).card ≤ 2 := by
      have hsub : (e : Finset (Fin n)) ∩ (f : Finset (Fin n)) ⊆ e := Finset.inter_subset_left
      simpa only [he] using Finset.card_le_card hsub
    have hi2 : ((e : Finset (Fin n)) ∩ (f : Finset (Fin n))).card ≠ 2 := by
      intro h
      have hsub : (e : Finset (Fin n)) ⊆ f := by
        have heq : (e : Finset (Fin n)) ∩ (f : Finset (Fin n)) = e :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
        exact Finset.inter_eq_left.mp heq
      apply hef
      apply Subtype.ext
      exact Finset.eq_of_subset_of_card_le hsub (by omega)
    have hu := Finset.card_union_add_card_inter (e : Finset (Fin n)) (f : Finset (Fin n))
    rw [he, hf] at hu
    simp only [if_neg hef, mul_zero, zero_add]
    by_cases hi1 : ((e : Finset (Fin n)) ∩ (f : Finset (Fin n))).card = 1
    · have hu3 : ((e : Finset (Fin n)) ∪ (f : Finset (Fin n))).card = 3 := by omega
      have hm := multiplicity_eq_choose q (e : Finset (Fin n)) f (by rw [hu3]; omega)
      simp only [hu3, Fintype.card_fin] at hm
      rw [hm, adjacent_ratio n q hq hn, hi1]
      simp [s1]
    · have hi0 : ((e : Finset (Fin n)) ∩ (f : Finset (Fin n))).card = 0 := by omega
      have hu4 : ((e : Finset (Fin n)) ∪ (f : Finset (Fin n))).card = 4 := by omega
      rw [hi0]
      simp only [Nat.cast_zero, mul_zero, zero_add]
      by_cases hq4 : 4 ≤ q
      · have hm := multiplicity_eq_choose q (e : Finset (Fin n)) f (by rw [hu4]; exact hq4)
        simp only [hu4, Fintype.card_fin] at hm
        rw [hm, disjoint_ratio n q hq4 hn]
        rfl
      · have hq3 : q = 3 := by omega
        subst q
        rw [multiplicity_eq_zero 3 (e : Finset (Fin n)) f (by rw [hu4]; omega)]
        simp [s2]

/-- An actual right inverse of the complete pair-versus-clique incidence Gram. -/
theorem normalizedGram_mul_inverse (n q : ℕ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) :
    normalizedGram n q * inverseOperator n q = 1 := by
  rw [normalizedGram_eq_operator n q hq hn]
  exact operator_mul_inverse n q hq hn

theorem normalizedGram_inverse (n q : ℕ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) :
    (normalizedGram n q)⁻¹ = inverseOperator n q :=
  Matrix.inv_eq_right_inv (normalizedGram_mul_inverse n q hq hn)

theorem middle_nonneg (n : ℕ) (e f : Edge n) : 0 ≤ middle n e f := by
  rw [middle, edge_gram_entry]
  positivity

theorem middle_row_sum (n : ℕ) (hn : 1 ≤ n) (e : Edge n) :
    (∑ f, middle n e f) = 2 * ((n : ℝ) - 1) := by
  apply IncidenceAlgebra.gram_row_sum
  · exact incidence_row_sum 2
  · intro v
    simpa only [Fintype.card_fin, Nat.cast_sub hn, Nat.cast_one] using
      (incidence_column_sum (V := Fin n) v)

theorem edge_card (n : ℕ) (hn : 1 ≤ n) :
    (Fintype.card (Edge n) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  apply IncidenceAlgebra.cardinality_of_incidence (incidence (V := Fin n) 2)
  · simp
  · exact incidence_row_sum 2
  · intro v
    simpa only [Fintype.card_fin, Nat.cast_sub hn, Nat.cast_one] using
      (incidence_column_sum (V := Fin n) v)

theorem inverseOperator_symmetric (n q : ℕ) (e f : Edge n) :
    inverseOperator n q e f = inverseOperator n q f e := by
  have hK : middle n e f = middle n f e := by
    simp only [middle, edge_gram_entry, Finset.inter_comm]
  simp only [inverseOperator, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, IncidenceAlgebra.ones]
  have hd : (if e = f then (1 : ℝ) else 0) = (if f = e then 1 else 0) := by
    simp only [eq_comm]
  rw [hK, hd]

/-- The coefficient estimate controls the actual matrix, including every edge. -/
theorem inverseOperator_rows_le_four (n q : ℕ) (hq : 3 ≤ q)
    (hn : 2 * q ^ 2 ≤ n) (e : Edge n) :
    (∑ f, |inverseOperator n q e f|) ≤ 4 := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hnR : 2 * (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hn
  have hnqR : (q : ℝ) + 2 ≤ n := by nlinarith [sq_nonneg ((q : ℝ) - 3)]
  obtain ⟨hu0, hu1, hu2⟩ := coefficient_signs q n hqR hnqR
  let a := u0 q n - 2 * u1 q n + u2 q n
  let b := u1 q n - u2 q n
  let c := u2 q n
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : b ≤ 0 := by dsimp [b]; linarith
  have hc : 0 ≤ c := hu2
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith)
  have hentry (f : Edge n) : |inverseOperator n q e f| ≤
      a * (if e = f then 1 else 0) + (-b) * middle n e f + c := by
    have hd : (0 : ℝ) ≤ if e = f then 1 else 0 := by split_ifs <;> norm_num
    have hK := middle_nonneg n e f
    change |a * (if e = f then 1 else 0) + b * middle n e f + c * 1| ≤ _
    rw [mul_one]
    calc
      _ ≤ |a * (if e = f then 1 else 0) + b * middle n e f| + |c| := abs_add_le _ _
      _ ≤ (|a * (if e = f then 1 else 0)| + |b * middle n e f|) + |c| :=
        add_le_add (abs_add_le _ _) (le_refl |c|)
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hd,
        abs_of_nonpos hb, abs_of_nonneg hK, abs_of_nonneg hc]
  calc
    _ ≤ ∑ f, (a * (if e = f then 1 else 0) + (-b) * middle n e f + c) :=
      Finset.sum_le_sum (fun f _ => hentry f)
    _ = a - 2 * ((n : ℝ) - 1) * b + (n : ℝ) * ((n : ℝ) - 1) / 2 * c := by
      have hd : (∑ f : Edge n, if e = f then (1 : ℝ) else 0) = 1 := by simp
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        nsmul_eq_mul, Finset.card_univ, middle_row_sum n hn1, edge_card n hn1, hd]
      <;> ring
    _ = envelope q n := by rfl
    _ ≤ 4 := envelope_le_four q n hqR hnR

theorem inverseOperator_cols_le_four (n q : ℕ) (hq : 3 ≤ q)
    (hn : 2 * q ^ 2 ≤ n) (e : Edge n) :
    (∑ f, |inverseOperator n q f e|) ≤ 4 := by
  simp_rw [inverseOperator_symmetric n q _ e]
  exact inverseOperator_rows_le_four n q hq hn e

theorem normalizedGram_inverse_rows_le_four (n q : ℕ) (hq : 3 ≤ q)
    (hn : 2 * q ^ 2 ≤ n) (e : Edge n) :
    (∑ f, |(normalizedGram n q)⁻¹ e f|) ≤ 4 := by
  have hnq : q + 2 ≤ n := by nlinarith
  rw [normalizedGram_inverse n q hq hnq]
  exact inverseOperator_rows_le_four n q hq hn e

end KqR75.CompleteJohnson

#print axioms KqR75.CompleteJohnson.operator_mul_inverse
#print axioms KqR75.CompleteJohnson.normalizedGram_eq_operator
#print axioms KqR75.CompleteJohnson.normalizedGram_mul_inverse
#print axioms KqR75.CompleteJohnson.normalizedGram_inverse
#print axioms KqR75.CompleteJohnson.inverseOperator_rows_le_four
#print axioms KqR75.CompleteJohnson.inverseOperator_cols_le_four
#print axioms KqR75.CompleteJohnson.normalizedGram_inverse_rows_le_four
