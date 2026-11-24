module
public import DistinctTriples
public import SignedBlockScalar

@[expose] public section
noncomputable section
namespace KqR75.SignedBlock

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A moment inequality proved by summing the three-variable square certificate
over distinct ordered triples. Empty triple sums also cover cardinalities 1 and 2. -/
theorem moment (d : ι → ℝ) (hd : ∀ i, 0 < d i) :
    ((∑ i, d i) ^ 2 - ∑ i, (d i) ^ 2) * (∑ i, (d i)⁻¹) ≥
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) * (∑ i, d i) := by
  have hz (i : ι) : d i ≠ 0 := (hd i).ne'
  let F (f g h : ι → ℝ) : ℝ :=
    ∑ i, ∑ j, ∑ k, if i ≠ j ∧ j ≠ k ∧ k ≠ i then f i * g j * h k else 0
  have hnon : 0 ≤
      F d d (fun i => (d i)⁻¹) + F (fun i => (d i)⁻¹) d d +
      F d (fun i => (d i)⁻¹) d - F d (fun _ => 1) (fun _ => 1) -
      F (fun _ => 1) d (fun _ => 1) - F (fun _ => 1) (fun _ => 1) d := by
    have ht : 0 ≤ ∑ i, ∑ j, ∑ k,
        if i ≠ j ∧ j ≠ k ∧ k ≠ i then
          d i * d j * (d k)⁻¹ + d j * d k * (d i)⁻¹ + d k * d i * (d j)⁻¹ -
            d i - d j - d k else 0 := by
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      apply Finset.sum_nonneg
      intro k _
      split_ifs
      · exact KqR75.triple_fraction_gap _ _ _ (hd i) (hd j) (hd k)
      · exact le_rfl
    convert ht using 1
    dsimp only [F]
    simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> ring
  dsimp only [F] at hnon
  simp_rw [KqR75.distinct_triple_sum] at hnon
  simp [hz, mul_assoc] at hnon
  simp_rw [← pow_two] at hnon
  nlinarith only [hnon]

/-- The universal signed inequality, normalized to target load one. -/
theorem normalized (d : ι → ℝ) (hd : ∀ i, 0 < d i)
    (hr : 1 ≤ Fintype.card ι) :
    (∑ i, (d i - 1) ^ 2) - 2 * (∑ i, (d i - 1)) ^ 2 ≤
      (2 * (Fintype.card ι : ℝ) - 1) * ∑ i, (d i - 1) ^ 2 / d i := by
  let r : ℝ := Fintype.card ι
  let S : ℝ := ∑ i, d i
  let T : ℝ := ∑ i, (d i)⁻¹
  let U : ℝ := ∑ i, (d i) ^ 2
  have hr1 : 1 ≤ r := by dsimp only [r]; exact_mod_cast hr
  have hne : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  letI := hne
  have hS : 0 < S := Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty
  have hT : 0 < T := Finset.sum_pos (fun i _ => inv_pos.mpr (hd i)) Finset.univ_nonempty
  have hC : r ^ 2 ≤ S * T := by
    have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (univ : Finset ι)
      (f := d) (g := fun i => (d i)⁻¹) (r := fun _ => (1 : ℝ))
      (fun i _ => (hd i).le) (fun i _ => (inv_pos.mpr (hd i)).le)
      (fun i _ => by simp [(hd i).ne'])
    simpa [r, S, T] using hh
  have hM : (S ^ 2 - U) * T ≥ r * (r - 1) * S := moment d hd
  have hsum : (∑ i, (d i - 1)) = S - r := by
    simp [S, r, Finset.sum_sub_distrib]
  have hsq : (∑ i, (d i - 1) ^ 2) = U - 2 * S + r := by
    have he (i : ι) : (d i - 1) ^ 2 = (d i) ^ 2 - 2 * d i + 1 := by ring
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp [U, S, r, Finset.mul_sum]
  have hdiv : (∑ i, (d i - 1) ^ 2 / d i) = S - 2 * r + T := by
    have he (i : ι) : (d i - 1) ^ 2 / d i = d i - 2 + (d i)⁻¹ := by
      field_simp [(hd i).ne']
      <;> ring
    simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp [S, T, r, mul_comm]
  rw [hsum, hsq, hdiv]
  by_cases hsmall : S ≤ 2 * r - 1
  · have hpoint (i : ι) : (d i - 1) ^ 2 ≤
        (2 * r - 1) * ((d i - 1) ^ 2 / d i) := by
      have hdi : d i ≤ S := Finset.single_le_sum (fun j _ => (hd j).le) (mem_univ i)
      have hh := mul_le_mul_of_nonneg_right (hdi.trans hsmall)
        (div_nonneg (sq_nonneg (d i - 1)) (hd i).le)
      have he : d i * ((d i - 1) ^ 2 / d i) = (d i - 1) ^ 2 := by
        field_simp [(hd i).ne']
      rw [he] at hh
      exact hh
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) => hpoint i)
    rw [← Finset.mul_sum, hsq, hdiv] at hh
    nlinarith [sq_nonneg (S - r)]
  · have hp := polynomial_nonnegative r S T hr1 (le_of_not_ge hsmall) hC
    have hidentity :
        ((2 * r - 1) * (S - 2 * r + T) -
          (U - 2 * S + r - 2 * (S - r) ^ 2)) * T =
        polynomial r S T + ((S ^ 2 - U) * T - r * (r - 1) * S) := by
      dsimp only [polynomial]
      ring
    have hh : 0 ≤ ((2 * r - 1) * (S - 2 * r + T) -
        (U - 2 * S + r - 2 * (S - r) ^ 2)) * T := by
      rw [hidentity]
      linarith
    exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hh hT)

 /-- Homogeneous form of the signed block inequality for an arbitrary positive target load. -/
theorem universal (d : ι → ℝ) (hd : ∀ i, 0 < d i)
    (k : ℝ) (hk : 0 < k) (hr : 1 ≤ Fintype.card ι) :
    (∑ i, (d i - k) ^ 2) - 2 * (∑ i, (d i - k)) ^ 2 ≤
      (2 * (Fintype.card ι : ℝ) - 1) * k * ∑ i, (d i - k) ^ 2 / d i := by
  let v : ι → ℝ := fun i => d i / k
  have hv (i : ι) : 0 < v i := div_pos (hd i) hk
  have h := normalized v hv hr
  have he (i : ι) : d i - k = k * (v i - 1) := by
    dsimp [v]
    field_simp [hk.ne']
    <;> ring
  have hs : (∑ i, (d i - k)) = k * ∑ i, (v i - 1) := by
    simp_rw [he]
    exact (Finset.mul_sum _ _ _).symm
  have hsq : (∑ i, (d i - k) ^ 2) = k ^ 2 * ∑ i, (v i - 1) ^ 2 := by
    simp_rw [he, mul_pow]
    exact (Finset.mul_sum _ _ _).symm
  have hdiv : (∑ i, (d i - k) ^ 2 / d i) = k * ∑ i, (v i - 1) ^ 2 / v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [v]
    field_simp [(hd i).ne', hk.ne']
    <;> ring
  rw [hs, hsq, hdiv]
  convert mul_le_mul_of_nonneg_left h (sq_nonneg k) using 1 <;> ring

end KqR75.SignedBlock

#print axioms KqR75.SignedBlock.moment
#print axioms KqR75.SignedBlock.normalized
#print axioms KqR75.SignedBlock.universal
