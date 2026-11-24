module
public import CodegreeLoss
public import SparseGram

@[expose] public section
noncomputable section
namespace KqR75.CliqueCodegrees

open Finset CliqueGram CompleteJohnson SparseGram GeneralJohnson

theorem codegree_eq_gram {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]
    (I : B → Finset E) (w : B → ℝ) (e f : E) :
    CodegreeLoss.codegree I w e f = DeletedGram.gram I w e f := by
  apply Finset.sum_congr rfl
  intro b _
  by_cases he : e ∈ I b <;> by_cases hf : f ∈ I b <;> simp [he, hf]

theorem normalizedGram_offdiag (n q : ℕ) (hq : 3 ≤ q) (hn : q + 2 ≤ n)
    (e f : Edge n) (hef : e ≠ f) : normalizedGram n q e f ≤ s1 q n := by
  have he : (e : Finset (Fin n)).card = 2 := (Finset.mem_powersetCard.mp e.property).2
  have hf : (f : Finset (Fin n)).card = 2 := (Finset.mem_powersetCard.mp f.property).2
  have hcard : ((e : Finset (Fin n)) ∩ (f : Finset (Fin n))).card ≤ 1 := by
    have hsub : (e : Finset (Fin n)) ∩ (f : Finset (Fin n)) ⊆ e := Finset.inter_subset_left
    have hc := Finset.card_le_card hsub
    rw [he] at hc
    have hne : ((e : Finset (Fin n)) ∩ (f : Finset (Fin n))).card ≠ 2 := by
      intro ht
      have hi : (e : Finset (Fin n)) ∩ (f : Finset (Fin n)) = e :=
        Finset.eq_of_subset_of_card_le hsub (by omega)
      have hef' : (e : Finset (Fin n)) ⊆ f := Finset.inter_eq_left.mp hi
      exact hef (Subtype.ext (Finset.eq_of_subset_of_card_le hef' (by omega)))
    omega
  have hcR : (((e : Finset (Fin n)) ∩ (f : Finset (Fin n))).card : ℝ) ≤ 1 := by exact_mod_cast hcard
  have hs := SparseGram.s1_sub_s2_nonneg q n (by exact_mod_cast hq) (by exact_mod_cast hn)
  rw [normalizedGram_eq_operator n q hq hn]
  simp only [operator, middle, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, hef, ite_false, mul_zero, zero_add, edge_gram_entry, IncidenceAlgebra.ones, mul_one]
  have hh := mul_le_mul_of_nonneg_left hcR hs
  linarith only [hh]

theorem codegree_le_complete (n q : ℕ) (C : ℝ)
    (w : ((univ : Finset (Fin n)).powersetCard q) → ℝ)
    (hw : ∀ b, w b ≤ C * ((n - 2).choose (q - 2) : ℝ)⁻¹) (e f : Edge n) :
    CodegreeLoss.codegree (resources n q) w e f ≤ C * normalizedGram n q e f := by
  rw [codegree_eq_gram, ← weightedGram_eq]
  dsimp only [DeletedGram.gram]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b _
  split_ifs
  · exact hw b
  · simp

/-- Every available state inherits the complete-graph codegree bound from
the fixed diffuse seed, independently of the number of deleted blocks. -/
theorem history_codegree_le (n q : ℕ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) (C : ℝ) (hC : 0 ≤ C)
    (μ : ((univ : Finset (Fin n)).powersetCard q) → ℝ)
    (hμ : ∀ b, μ b ≤ C * ((n - 2).choose (q - 2) : ℝ)⁻¹)
    (J : Finset (Edge n)) (h : List (Option ((univ : Finset (Fin n)).powersetCard q)))
    (e f : Edge n) (hef : e ≠ f) :
    CodegreeLoss.codegree (resources n q) (WeightedGreedy.availableWeight (resources n q) μ J h) e f ≤
      C * s1 q n := by
  have hw (b : ((univ : Finset (Fin n)).powersetCard q)) :
      WeightedGreedy.availableWeight (resources n q) μ J h b ≤
        C * ((n - 2).choose (q - 2) : ℝ)⁻¹ := by
    dsimp only [WeightedGreedy.availableWeight]
    split_ifs
    · exact hμ b
    · positivity
  exact (codegree_le_complete n q C _ hw e f).trans
    (mul_le_mul_of_nonneg_left (normalizedGram_offdiag n q hq hn e f hef) hC)

theorem history_codegree_rate (n q : ℕ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) (C : ℝ) (hC : 0 ≤ C)
    (μ : ((univ : Finset (Fin n)).powersetCard q) → ℝ)
    (hμ : ∀ b, μ b ≤ C * ((n - 2).choose (q - 2) : ℝ)⁻¹)
    (J : Finset (Edge n)) (h : List (Option ((univ : Finset (Fin n)).powersetCard q)))
    (e f : Edge n) (hef : e ≠ f) :
    CodegreeLoss.codegree (resources n q) (WeightedGreedy.availableWeight (resources n q) μ J h) e f ≤
      2 * C * (q : ℝ) / n := by
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hnR : (q : ℝ) + 2 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hn2 : 0 < (n : ℝ) - 2 := by linarith
  have hratio : s1 q n ≤ 2 * (q : ℝ) / n := by
    apply (div_le_div_iff₀ hn2 hn0).mpr
    have hp := mul_nonneg (show (0 : ℝ) ≤ q by linarith)
      (show 0 ≤ (n : ℝ) - 4 by linarith)
    nlinarith only [hp, hn0]
  calc
    _ ≤ C * s1 q n := history_codegree_le n q hq hn C hC μ hμ J h e f hef
    _ ≤ C * (2 * (q : ℝ) / n) := mul_le_mul_of_nonneg_left hratio hC
    _ = _ := by ring

end KqR75.CliqueCodegrees

#print axioms KqR75.CliqueCodegrees.normalizedGram_offdiag
#print axioms KqR75.CliqueCodegrees.history_codegree_le
#print axioms KqR75.CliqueCodegrees.history_codegree_rate
