module
public import UpperIntegralBound
public import UpperExceptionalWeight

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Finset ColouredCliques CompleteJohnson SparseGram PhysicalCompletion

variable {C : Type*} [Fintype C] [DecidableEq C]

private theorem reference_score_of_fibre {n q : ℕ} (colour : Fin n → C)
    (m : TypeProfile C q → ℤ) (P : Finset (Clique n q)) (hP : P ∈ designFibre colour m) :
    (∑ b ∈ P, Real.log (ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ)) b)) =
      ∑ t, (m t : ℝ) * Real.log ((m t : ℝ) /
        ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ)) := by
  classical
  rw [← sum_fiberwise P (cliqueType colour)]
  apply sum_congr rfl
  intro t _
  have he := ((mem_designFibre colour m P).mp hP).2 t
  have hh (b : Clique n q) (hb : b ∈ P.filter (fun b => cliqueType colour b = t)) :
      Real.log (ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ)) b) =
        Real.log ((m t : ℝ) / ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ)) := by
    simp only [ProfileWeights.weight, (mem_filter.mp hb).2]
  rw [sum_congr rfl hh, sum_const, nsmul_eq_mul]
  congr 1
  exact_mod_cast he

/-- Upper bound on the exact type fibre for a diffuse reference profile.
The fibre may contain some absent types; the proof uses positivity only
on realized blocks. -/
theorem log_designFibre_upper_with_envelope {n q : ℕ} (hq : 3 ≤ q) (hnq : q ≤ n)
    (colour : Fin n → C) (hclasses : ∀ i, q ≤ profile colour univ i)
    (m : TypeProfile C q → ℤ)
    (hmargin : ∀ e : Edge n, pairMargin colour (fun t => (m t : ℝ)) e =
      (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ))
    (hfibre : (designFibre colour m).Nonempty)
    (W : ℝ) (hW : 0 ≤ W) (hsize : 4 * (q.choose 3 : ℝ) * W + 1 ≤ n)
    (hw : ∀ b, ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ)) b ≤
      W / (n : ℝ) ^ (q - 2)) :
    let r := q.choose 2
    let s : ℝ := (r - 1 : ℕ)
    let B := (Fintype.card (Edge n) : ℝ) / (r : ℝ)
    let K := 4 * (q.choose 3 : ℝ) * W + 1
    Real.log ((designFibre colour m).card : ℝ) +
      (∑ t, (m t : ℝ) * Real.log ((m t : ℝ) /
        ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ))) ≤
      -s * B + (K ^ (1 / s) * (Real.log 2 + s + 1 / (s - 1))) * (n : ℝ) ^ (2 - 1 / s) := by
  classical
  let r := q.choose 2
  let s : ℝ := (r - 1 : ℕ)
  let K := 4 * (q.choose 3 : ℝ) * W + 1
  let δ := K / (n : ℝ)
  let w := ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ))
  let v : ℝ := ∑ t, (m t : ℝ) * Real.log ((m t : ℝ) /
    ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ))
  let E : ↥(designFibre colour m) ↪ FullPacking n q :=
    ⟨fun P => ⟨P.val, ((mem_designFibre colour m P.val).mp P.property).1⟩,
      fun _ _ he => Subtype.ext (congrArg (fun Q : FullPacking n q => Q.val) he)⟩
  let S := (designFibre colour m).attach.map E
  have hcard : S.card = (designFibre colour m).card := by simp [S]
  have hS : S.Nonempty := card_pos.mp (by rw [hcard]; exact hfibre.card_pos)
  have hmem (P : FullPacking n q) (hP : P ∈ S) : P.val ∈ designFibre colour m := by
    obtain ⟨Q, _, rfl⟩ := mem_map.mp hP
    exact Q.property
  obtain ⟨P, hP⟩ := hfibre
  obtain ⟨hwn, _, hload⟩ := profile_reference_properties colour hclasses m hmargin P hP
  have hpos (P : FullPacking n q) (hP : P ∈ S) : ∀ b ∈ P.val, 0 < w b :=
    (profile_reference_properties colour hclasses m hmargin P.val (hmem P hP)).2.1
  have hn : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hK : 0 < K := by dsimp [K]; positivity
  have hδ : 0 < δ := div_pos hK hn
  have hδ₁ : δ ≤ 1 := (div_le_one hn).mpr hsize
  have hmass (P : FullPacking n q) (_ : P ∈ S) (e : Edge n) :
      (∑ b ∈ exceptional P.val e, w b) ≤ δ :=
    (exceptional_weight_le hq (by omega) P.val P.property e w W hW hw).trans
      (div_le_div_of_nonneg_right (by dsimp [K]; linarith) hn.le)
  have hscore (P : FullPacking n q) (hP : P ∈ S) : v ≤ ∑ b ∈ P.val, Real.log (w b) :=
    (reference_score_of_fibre colour m P.val (hmem P hP)).ge
  have ht := weighted_upper_of_exceptional_mass hq hnq S hS w hwn hpos hload δ v hδ hδ₁ hmass hscore
  dsimp only at ht
  rw [hcard] at ht
  change Real.log ((designFibre colour m).card : ℝ) + v ≤ _
  refine ht.trans ?_
  let b := (Fintype.card (Edge n) : ℝ) / (r : ℝ)
  let A := Real.log 2 + s + 1 / (s - 1)
  have hr : 3 ≤ r := (show 3 ≤ (3 : ℕ).choose 2 by decide).trans (Nat.choose_le_choose 2 hq)
  have hs : 1 < s := by
    dsimp only [s]
    exact_mod_cast (by omega : 1 < r - 1)
  have hb : b ≤ (n : ℝ) ^ 2 := by
    have hN := CompleteJohnson.edge_card n (by omega)
    have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast (by omega : 1 ≤ r)
    calc
      b ≤ Fintype.card (Edge n) := div_le_self (Nat.cast_nonneg _) hr₁
      _ ≤ _ := by nlinarith only [hN, hn.le, sq_nonneg (n : ℝ)]
  have hA : 0 ≤ A := by
    dsimp [A]
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
    positivity
  have hδpow : δ ^ (1 / s) = K ^ (1 / s) * (n : ℝ) ^ (-(1 / s)) := by
    dsimp [δ]
    rw [Real.div_rpow hK.le hn.le, Real.rpow_neg hn.le, div_eq_mul_inv]
  change b * (-s + δ ^ (1 / s) * A) ≤ -s * b + (K ^ (1 / s) * A) * (n : ℝ) ^ (2 - 1 / s)
  rw [hδpow]
  calc
    _ = -s * b + (K ^ (1 / s) * A) * (b * (n : ℝ) ^ (-(1 / s))) := by ring
    _ ≤ -s * b + (K ^ (1 / s) * A) * ((n : ℝ) ^ 2 * (n : ℝ) ^ (-(1 / s))) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (by positivity))
        (mul_nonneg (Real.rpow_nonneg hK.le _) hA))
    _ = _ := by
      rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hn, Nat.cast_ofNat, sub_eq_add_neg]

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.log_designFibre_upper_with_envelope
