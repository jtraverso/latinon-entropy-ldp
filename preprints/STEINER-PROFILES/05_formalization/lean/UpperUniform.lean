module
public import UpperDesignFibre
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
noncomputable section
namespace KqR75.UpperCounting

open Filter Finset ColouredCliques CompleteJohnson SparseGram PhysicalCompletion
open scoped Topology

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Uniform second-order upper bound in the score normalization.
The constant depends on q, the palette, and the lower bound on
class proportions, including when some target types are absent. -/
theorem eventually_log_designFibre_upper (q : ℕ) (hq : 3 ≤ q) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ err : ℝ, 0 ≤ err ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (colour : Fin n → C) (m : TypeProfile C q → ℤ),
      (∀ c, ρ * (n : ℝ) ≤ (profile colour univ c : ℝ)) →
      (∀ e : Edge n, pairMargin colour (fun t => (m t : ℝ)) e =
        (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ)) →
      (designFibre colour m).Nonempty →
      let r := q.choose 2
      let s : ℝ := (r - 1 : ℕ)
      let B := (Fintype.card (Edge n) : ℝ) / (r : ℝ)
      Real.log ((designFibre colour m).card : ℝ) +
        (∑ t, (m t : ℝ) * Real.log ((m t : ℝ) /
          ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ))) ≤
        -s * B + err * (n : ℝ) ^ (2 - 1 / s) := by
  classical
  let a := ρ / 4
  let U := (q.factorial : ℝ) ^ Fintype.card C / a ^ q
  let F := (2 : ℝ) ^ (q - 2) * ((q - 2).factorial : ℝ)
  let W := U * F
  let K := 4 * (q.choose 3 : ℝ) * W + 1
  let r := q.choose 2
  let s : ℝ := (r - 1 : ℕ)
  let err := K ^ (1 / s) * (Real.log 2 + s + 1 / (s - 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hW : 0 ≤ W := mul_nonneg hU hF
  have hK : 0 < K := by dsimp [K]; positivity
  have hr : 3 ≤ r := (show 3 ≤ (3 : ℕ).choose 2 by decide).trans (Nat.choose_le_choose 2 hq)
  have hs : 1 < s := by
    dsimp only [s]
    exact_mod_cast (by omega : 1 < r - 1)
  have hA : 0 ≤ Real.log 2 + s + 1 / (s - 1) := by
    have hlog := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hdiff := sub_pos.mpr hs
    have hs' : 0 ≤ s := by linarith
    positivity
  refine ⟨err, mul_nonneg (Real.rpow_nonneg hK.le _) hA, ?_⟩
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 * q),
    (tendsto_atTop.1 hnat) (max K ((4 * ((q : ℝ) + 1)) / ρ))] with n hn hnc
  intro colour m hclasses hmarg hfibre
  have hnq : q ≤ n := by omega
  have hsize : K ≤ (n : ℝ) := (le_max_left _ _).trans hnc
  have hclassN : 4 * ((q : ℝ) + 1) ≤ ρ * (n : ℝ) := by
    have ht := (div_le_iff₀ hρ).mp ((le_max_right _ _).trans hnc)
    simpa only [mul_comm (n : ℝ) ρ] using ht
  let d : ℕ := ⌊ρ * (n : ℝ) / 2⌋₊
  have hdn : a * (n : ℝ) ≤ d := by
    have hd := Nat.lt_floor_add_one (ρ * (n : ℝ) / 2)
    change ρ * (n : ℝ) / 2 < (d : ℝ) + 1 at hd
    dsimp only [a]
    nlinarith only [hd, hclassN, Nat.cast_nonneg (α := ℝ) q]
  have hd (c : C) : d + q ≤ profile colour univ c := by
    have h := Nat.floor_le (show 0 ≤ ρ * (n : ℝ) / 2 by positivity)
    change (d : ℝ) ≤ ρ * (n : ℝ) / 2 at h
    exact_mod_cast (by nlinarith only [h, hclassN, hclasses c] :
      (d : ℝ) + q ≤ profile colour univ c)
  have hqclass (c : C) : q ≤ profile colour univ c := (Nat.le_add_left _ _).trans (hd c)
  obtain ⟨P, hP⟩ := hfibre
  obtain ⟨hpacks, hhist⟩ := (mem_designFibre colour m P).mp hP
  have hquota (t : TypeProfile C q) : |(m t : ℝ)| ≤ (n : ℝ) ^ 2 := by
    rw [← hhist t]
    unfold BankCapacity.integerHistogram
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (card_filter_le _ _).trans (blocks_le_square (by omega) hpacks)
  have hw (b : Clique n q) :
      ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ)) b ≤
        W / (n : ℝ) ^ (q - 2) := by
    have h := seed_weight_abs_le colour (by omega) hnq d a 1 ha zero_le_one hd hdn
      (fun t => (m t : ℝ)) (fun t => by simpa only [one_mul] using hquota t) b
    simp only [one_mul] at h
    refine (le_abs_self _).trans (h.trans ?_)
    change U * HostCorrection.scale n q ≤ _
    exact (mul_le_mul_of_nonneg_left (scale_le_power (by omega) hn) hU).trans_eq (by dsimp [W, F]; ring)
  exact log_designFibre_upper_with_envelope hq hnq colour hqclass m hmarg ⟨P, hP⟩ W hW hsize hw

end KqR75.UpperCounting

#print axioms KqR75.UpperCounting.eventually_log_designFibre_upper
