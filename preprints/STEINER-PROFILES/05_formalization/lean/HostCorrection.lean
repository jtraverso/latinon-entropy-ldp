module
public import SparseGram
public import LoadCorrection

@[expose] public section
noncomputable section
namespace KqR75.HostCorrection

open Finset CliqueGram CompleteJohnson SparseGram
open scoped Matrix

abbrev Block (n q : ℕ) := ((univ : Finset (Fin n)).powersetCard q)

def availableBlocks (n q : ℕ) (J : Finset (Edge n)) : Finset (Block n q) :=
  univ.filter fun b => resources n q b ⊆ J

def hostIncidence (n q : ℕ) (J : Finset (Edge n)) :
    Matrix J (availableBlocks n q J) ℝ :=
  fun e b => if (e : Edge n) ∈ resources n q b then 1 else 0

def scale (n q : ℕ) : ℝ := ((n - 2).choose (q - 2) : ℝ)⁻¹

theorem hostIncidence_nonneg (n q : ℕ) (J : Finset (Edge n))
    (e : J) (b : availableBlocks n q J) : 0 ≤ hostIncidence n q J e b := by
  dsimp [hostIncidence]
  split_ifs <;> norm_num

theorem hostIncidence_col_sum_le (n q : ℕ) (J : Finset (Edge n))
    (b : availableBlocks n q J) :
    (∑ e, hostIncidence n q J e b) ≤ (q.choose 2 : ℝ) := by
  dsimp only [hostIncidence]
  rw [Finset.sum_coe_sort J (fun e : Edge n => if e ∈ resources n q b then (1 : ℝ) else 0)]
  calc
    _ ≤ ∑ e : Edge n, if e ∈ resources n q b then (1 : ℝ) else 0 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J)
        (fun e _ _ => by split_ifs <;> norm_num)
    _ = _ := by
      have hf : ((univ : Finset (Edge n)).filter fun e => e ∈ resources n q b) =
          resources n q b := Finset.filter_mem_eq_of_subset (Finset.subset_univ _)
      simp only [Finset.sum_boole, hf, resources_card]

theorem gram_eq_hostGram (n q : ℕ) (J : Finset (Edge n)) :
    LoadCorrection.gram (hostIncidence n q J) (scale n q) = hostGram n q J := by
  ext e f
  dsimp only [LoadCorrection.gram, hostGram, DeletedGram.prunedGram]
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul]
  dsimp only [hostIncidence]
  rw [Finset.sum_coe_sort (availableBlocks n q J)
    (fun b : Block n q =>
      (if (e : Edge n) ∈ resources n q b then (1 : ℝ) else 0) *
        (if (f : Edge n) ∈ resources n q b then 1 else 0))]
  simp only [availableBlocks, Finset.sum_filter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  dsimp only [scale]
  split_ifs <;> simp_all

theorem normalizedGram_diag (n q : ℕ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) (e : Edge n) :
    normalizedGram n q e e = 1 := by
  have he : (e : Finset (Fin n)).card = 2 := (Finset.mem_powersetCard.mp e.property).2
  rw [normalizedGram_eq_operator n q hq hn]
  simp [operator, middle, edge_gram_entry, Finset.inter_self, he, IncidenceAlgebra.ones]
  <;> ring

theorem normalized_row_cap (n q : ℕ) (hq : 3 ≤ q) (hn : q + 2 ≤ n)
    (J : Finset (Edge n)) (e : J) :
    scale n q * ∑ b, hostIncidence n q J e b ≤ 1 := by
  have hl := DeletedGram.loss_nonneg (resources n q)
    (fun _ => scale n q) (fun _ => by dsimp [scale]; positivity) J e e
  have hfull : DeletedGram.gram (resources n q) (fun _ => scale n q) = normalizedGram n q :=
    weightedGram_eq n q
  rw [hfull, normalizedGram_diag n q hq hn e] at hl
  have hdiag : LoadCorrection.gram (hostIncidence n q J) (scale n q) e e =
      scale n q * ∑ b, hostIncidence n q J e b := by
    dsimp only [LoadCorrection.gram]
    simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [hostIncidence]
    split_ifs <;> norm_num
  rw [gram_eq_hostGram] at hdiag
  change scale n q * ∑ b, hostIncidence n q J e b ≤ 1
  have hprune : DeletedGram.prunedGram (resources n q) (fun _ => scale n q) J e e =
      hostGram n q J e e := rfl
  rw [hprune, hdiag] at hl
  linarith only [hl]

/-- An exact solution of the load defect, with both norm bounds on the
physical surviving blocks. -/
theorem solve_defect (n q : ℕ) (hq : 3 ≤ q) (hn : 2 * q ^ 2 ≤ n)
    (J : Finset (Edge n)) (t u : ℝ) (hu : 0 ≤ u)
    (hdeg : ∀ v : Fin n, ∑ f : (Jᶜ : Finset (Edge n)), incidence 2 f v ≤ t)
    (hsmall : 4 * (1 + (q.choose 2 : ℝ)) * outsideBound n q t ≤ 1 / 2)
    (h : J → ℝ) (hh : ∀ e, |h e| ≤ u) :
    ∃ v : availableBlocks n q J → ℝ, hostIncidence n q J *ᵥ v = h ∧
      (∑ b, |v b|) ≤ 8 * ∑ e, |h e| ∧
      (∀ b, |v b| ≤ 8 * (q.choose 2 : ℝ) * scale n q * u) := by
  have hnq : q + 2 ≤ n := by nlinarith
  obtain ⟨hdet, hrows⟩ := host_inverse_rows_le_eight n q hq hn J t hdeg hsmall
  rw [← gram_eq_hostGram] at hdet hrows
  have hα : 0 ≤ scale n q := by dsimp [scale]; positivity
  let R := LoadCorrection.corrector (hostIncidence n q J) (scale n q)
  refine ⟨R *ᵥ h, ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, LoadCorrection.right_inverse _ _ hdet, Matrix.one_mulVec]
  · exact LoadCorrection.mulVec_l1_le R 8
      (LoadCorrection.corrector_cols_le_eight _ _ hα (hostIncidence_nonneg n q J)
        (normalized_row_cap n q hq hnq J) hrows) h
  · exact LoadCorrection.mulVec_pointwise_le R _ u hu
      (LoadCorrection.corrector_rows_le _ _ _ hα (hostIncidence_nonneg n q J)
        (hostIncidence_col_sum_le n q J) hrows) h hh

/-- Positive weights with exactly prescribed loads, on actual surviving cliques.
The only matrix-smallness condition is the explicit deleted-degree bound. -/
theorem repair_positive (n q : ℕ) (hq : 3 ≤ q) (hn : 2 * q ^ 2 ≤ n)
    (J : Finset (Edge n)) (t u δ : ℝ) (hu : 0 ≤ u) (hδ : 0 < δ)
    (hdeg : ∀ v : Fin n, ∑ f : (Jᶜ : Finset (Edge n)), incidence 2 f v ≤ t)
    (hsmall : 4 * (1 + (q.choose 2 : ℝ)) * outsideBound n q t ≤ 1 / 2)
    (μ : availableBlocks n q J → ℝ) (ν : J → ℝ) (hμ : ∀ b, δ ≤ μ b)
    (hdefect : ∀ e, |(ν - hostIncidence n q J *ᵥ μ) e| ≤ u)
    (hpositive : 8 * (q.choose 2 : ℝ) * scale n q * u ≤ δ / 2) :
    ∃ μ' : availableBlocks n q J → ℝ, hostIncidence n q J *ᵥ μ' = ν ∧
      (∀ b, 0 < μ' b) ∧
      (∀ b, |μ' b - μ b| ≤ 8 * (q.choose 2 : ℝ) * scale n q * u) := by
  obtain ⟨hdet, hrows⟩ := host_inverse_rows_le_eight n q hq hn J t hdeg hsmall
  rw [← gram_eq_hostGram] at hdet hrows
  exact LoadCorrection.repair_positive (hostIncidence n q J) (scale n q)
    (q.choose 2 : ℝ) u δ (by dsimp [scale]; positivity) hu hδ
    (hostIncidence_nonneg n q J) (hostIncidence_col_sum_le n q J) hdet hrows
    μ ν hμ hdefect hpositive

end KqR75.HostCorrection

#print axioms KqR75.HostCorrection.gram_eq_hostGram
#print axioms KqR75.HostCorrection.normalized_row_cap
#print axioms KqR75.HostCorrection.solve_defect
#print axioms KqR75.HostCorrection.repair_positive
