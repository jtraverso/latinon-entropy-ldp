module
public import CompleteJohnson
public import DeletedGram

@[expose] public section
noncomputable section
namespace KqR75.SparseGram

open Finset CliqueGram CompleteJohnson GeneralJohnson
open scoped Matrix

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]

theorem sparse_middle_bound (T : Matrix E V ℝ) (F : Finset E) (t : ℝ)
    (hT : ∀ e v, 0 ≤ T e v) (hrow : ∀ e, ∑ v, T e v = 2)
    (hdeg : ∀ v, ∑ f : F, T f v ≤ t) (e : E) :
    (∑ f : F, (T * Tᵀ) e f) ≤ 2 * t := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  calc
    _ ≤ ∑ v, T e v * t := Finset.sum_le_sum (fun v _ =>
      mul_le_mul_of_nonneg_left (hdeg v) (hT e v))
    _ = _ := by rw [← Finset.sum_mul, hrow]

theorem sparse_card_bound (T : Matrix E V ℝ) (F : Finset E) (t : ℝ)
    (hrow : ∀ e, ∑ v, T e v = 2) (hdeg : ∀ v, ∑ f : F, T f v ≤ t) :
    2 * (F.card : ℝ) ≤ (Fintype.card V : ℝ) * t := by
  have hh := Finset.sum_le_sum (s := (univ : Finset V)) (fun v _ => hdeg v)
  rw [Finset.sum_comm] at hh
  simpa [hrow, mul_comm] using hh

theorem s1_sub_s2_nonneg (q n : ℝ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) :
    0 ≤ s1 q n - s2 q n := by
  have hn2 : n - 2 ≠ 0 := by linarith
  have hn3 : n - 3 ≠ 0 := by linarith
  have he : s1 q n - s2 q n = (q - 2) * (n - q) / ((n - 2) * (n - 3)) := by
    dsimp [s1, s2]
    field_simp [hn2, hn3]
    <;> ring
  rw [he]
  have hq2 : 0 ≤ q - 2 := by linarith
  have hnq : 0 ≤ n - q := by linarith
  have hn2' : 0 < n - 2 := by linarith
  have hn3' : 0 < n - 3 := by linarith
  positivity

def outsideBound (n q : ℕ) (t : ℝ) : ℝ :=
  2 * t * (s1 q n - s2 q n) + (n : ℝ) * t / 2 * s2 q n

theorem outside_factor_le (q n : ℝ) (hq : 3 ≤ q) (hn : 6 ≤ n) :
    2 * (s1 q n - s2 q n) + n / 2 * s2 q n ≤ 4 * q ^ 2 / n := by
  have hn0 : 0 < n := by linarith
  have hn2 : 0 < n - 2 := by linarith
  have hn3 : 0 < n - 3 := by linarith
  have hden : 0 < 2 * (n - 2) * (n - 3) := by positivity
  have hid : 2 * (s1 q n - s2 q n) + n / 2 * s2 q n =
      (q - 2) * ((q + 1) * n - 4 * q) / (2 * (n - 2) * (n - 3)) := by
    dsimp [s1, s2]
    field_simp [hn2.ne', hn3.ne']
    <;> ring
  have hu : 0 ≤ q - 3 := by linarith
  have hv : 0 ≤ n - 6 := by linarith
  have hpoly : 8 * q ^ 2 * (n - 2) * (n - 3) -
      n * (q - 2) * ((q + 1) * n - 4 * q) =
      7 * (q - 3) ^ 2 * (n - 6) ^ 2 + 48 * (q - 3) ^ 2 * (n - 6) +
      84 * (q - 3) ^ 2 + 43 * (q - 3) * (n - 6) ^ 2 +
      292 * (q - 3) * (n - 6) + 492 * (q - 3) +
      68 * (n - 6) ^ 2 + 468 * (n - 6) + 792 := by ring
  have hnonneg : 0 ≤ 8 * q ^ 2 * (n - 2) * (n - 3) -
      n * (q - 2) * ((q + 1) * n - 4 * q) := by rw [hpoly]; positivity
  rw [hid]
  apply (div_le_div_iff₀ hden hn0).mpr
  nlinarith only [hnonneg]

theorem outsideBound_le (n q : ℕ) (hq : 3 ≤ q) (hn : 6 ≤ n)
    (t : ℝ) (ht : 0 ≤ t) : outsideBound n q t ≤ 4 * (q : ℝ) ^ 2 * t / n := by
  have hfactor := outside_factor_le q n (by exact_mod_cast hq) (by exact_mod_cast hn)
  calc
    _ = t * (2 * (s1 q n - s2 q n) + (n : ℝ) / 2 * s2 q n) := by
      dsimp [outsideBound]
      ring
    _ ≤ t * (4 * (q : ℝ) ^ 2 / n) := mul_le_mul_of_nonneg_left hfactor ht
    _ = _ := by ring

/-- The lost Gram mass is controlled by the maximum degree of the deleted graph. -/
theorem outside_mass_le (n q : ℕ) (hq : 3 ≤ q) (hn : q + 2 ≤ n)
    (F : Finset (Edge n)) (t : ℝ)
    (hdeg : ∀ v : Fin n, ∑ f : F, incidence 2 f v ≤ t)
    (e : Edge n) (he : e ∉ F) :
    (∑ f : F, normalizedGram n q e f) ≤ outsideBound n q t := by
  let T := incidence (V := Fin n) 2
  have hrow : ∀ e, ∑ v, T e v = 2 := incidence_row_sum 2
  have hT : ∀ e v, 0 ≤ T e v := by
    intro e v
    dsimp [T, incidence]
    split_ifs <;> norm_num
  have hmiddle := sparse_middle_bound T F t hT hrow hdeg e
  have hcard : (F.card : ℝ) ≤ (n : ℝ) * t / 2 := by
    have h := sparse_card_bound T F t hrow hdeg
    simp only [Fintype.card_fin] at h
    linarith only [h]
  have hqR : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hnR : (q : ℝ) + 2 ≤ n := by exact_mod_cast hn
  have hs := s1_sub_s2_nonneg q n hqR hnR
  have hq2 : 0 ≤ (q : ℝ) - 2 := by linarith
  have hq3 : 0 ≤ (q : ℝ) - 3 := by linarith
  have hn2 : 0 < (n : ℝ) - 2 := by linarith
  have hn3 : 0 < (n : ℝ) - 3 := by linarith
  have hs2 : 0 ≤ s2 q n := by
    dsimp [s2]
    positivity
  have hentry (f : F) : normalizedGram n q e f =
      (s1 q n - s2 q n) * middle n e f + s2 q n := by
    have hef : e ≠ (f : Edge n) := by intro h; exact he (h ▸ f.property)
    rw [normalizedGram_eq_operator n q hq hn]
    simp [operator, Matrix.one_apply, hef, IncidenceAlgebra.ones]
  simp_rw [hentry]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcardF : (Fintype.card F : ℝ) = F.card := by simp
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcardF]
  have hm : (s1 q n - s2 q n) * (∑ f : F, middle n e f) ≤
      2 * t * (s1 q n - s2 q n) := by
    simpa only [middle, T, mul_comm] using mul_le_mul_of_nonneg_left hmiddle hs
  exact add_le_add hm
    (mul_le_mul_of_nonneg_right hcard hs2)

def resources (n q : ℕ) (b : ((univ : Finset (Fin n)).powersetCard q)) : Finset (Edge n) :=
  univ.filter fun e => (e : Finset (Fin n)) ⊆ (b : Finset (Fin n))

theorem resources_card (n q : ℕ) (b : ((univ : Finset (Fin n)).powersetCard q)) :
    (resources n q b).card = q.choose 2 := by
  have hb : (b : Finset (Fin n)).card = q := (Finset.mem_powersetCard.mp b.property).2
  calc
    _ = ((b : Finset (Fin n)).powersetCard 2).card := by
      apply Finset.card_bij (fun (e : Edge n) _ => (e : Finset (Fin n)))
      · intro e he
        exact Finset.mem_powersetCard.mpr
          ⟨(Finset.mem_filter.mp he).2, (Finset.mem_powersetCard.mp e.property).2⟩
      · intro e he f hf hef
        exact Subtype.ext hef
      · intro f hf
        let e : Edge n := ⟨f, Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, (Finset.mem_powersetCard.mp hf).2⟩⟩
        exact ⟨e, Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_powersetCard.mp hf).1⟩, rfl⟩
    _ = _ := by rw [Finset.card_powersetCard, hb]

theorem weightedGram_eq (n q : ℕ) :
    DeletedGram.gram (resources n q) (fun _ => ((n - 2).choose (q - 2) : ℝ)⁻¹) =
      normalizedGram n q := by
  ext e f
  dsimp only [DeletedGram.gram, normalizedGram]
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [resources, Finset.mem_filter, mem_univ, true_and, pairIncidence]
  split_ifs <;> simp_all

def hostGram (n q : ℕ) (J : Finset (Edge n)) : Matrix J J ℝ :=
  fun e f => DeletedGram.prunedGram (resources n q)
    (fun _ => ((n - 2).choose (q - 2) : ℝ)⁻¹) J e f

/-- Invertibility and a uniform row bound for the actual surviving clique Gram. -/
theorem host_inverse_rows_le_eight (n q : ℕ) (hq : 3 ≤ q) (hn : 2 * q ^ 2 ≤ n)
    (J : Finset (Edge n)) (t : ℝ)
    (hdeg : ∀ v : Fin n, ∑ f : (Jᶜ : Finset (Edge n)), incidence 2 f v ≤ t)
    (hsmall : 4 * (1 + (q.choose 2 : ℝ)) * outsideBound n q t ≤ 1 / 2) :
    (hostGram n q J).det ≠ 0 ∧ ∀ i, ∑ j, |(hostGram n q J)⁻¹ i j| ≤ 8 := by
  have hnq : q + 2 ≤ n := by nlinarith
  apply DeletedGram.pruned_inverse_rows_le_eight (resources n q)
    (fun _ => ((n - 2).choose (q - 2) : ℝ)⁻¹) (fun _ => by positivity)
    (q.choose 2 : ℝ) (by positivity) (fun b => by rw [resources_card]) J
    (inverseOperator n q)
  · rw [weightedGram_eq]
    exact normalizedGram_mul_inverse n q hq hnq
  · exact inverseOperator_rows_le_four n q hq hn
  · intro e
    rw [weightedGram_eq]
    exact outside_mass_le n q hq hnq _ t hdeg e
      (by simpa only [Finset.mem_compl, not_not] using e.property)
  · exact hsmall

/-- A purely degree-based sufficient condition for the physical inverse bound. -/
theorem host_inverse_of_degree (n q : ℕ) (hq : 3 ≤ q) (hn : 2 * q ^ 2 ≤ n)
    (J : Finset (Edge n)) (t : ℝ) (ht : 0 ≤ t)
    (hdeg : ∀ v : Fin n, ∑ f : (Jᶜ : Finset (Edge n)), incidence 2 f v ≤ t)
    (hsmall : 32 * (1 + (q.choose 2 : ℝ)) * (q : ℝ) ^ 2 * t ≤ n) :
    (hostGram n q J).det ≠ 0 ∧ ∀ i, ∑ j, |(hostGram n q J)⁻¹ i j| ≤ 8 := by
  have hn6 : 6 ≤ n := by nlinarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  apply host_inverse_rows_le_eight n q hq hn J t hdeg
  calc
    _ ≤ 4 * (1 + (q.choose 2 : ℝ)) * (4 * (q : ℝ) ^ 2 * t / n) :=
      mul_le_mul_of_nonneg_left (outsideBound_le n q hq hn6 t ht) (by positivity)
    _ = (16 * (1 + (q.choose 2 : ℝ)) * (q : ℝ) ^ 2 * t) / n := by ring
    _ ≤ 1 / 2 := (div_le_iff₀ hnR).mpr (by nlinarith only [hsmall])

end KqR75.SparseGram

#print axioms KqR75.SparseGram.outside_mass_le
#print axioms KqR75.SparseGram.resources_card
#print axioms KqR75.SparseGram.host_inverse_rows_le_eight
#print axioms KqR75.SparseGram.outsideBound_le
#print axioms KqR75.SparseGram.host_inverse_of_degree
