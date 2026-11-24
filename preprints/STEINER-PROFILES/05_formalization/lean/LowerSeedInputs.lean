module
public import RepairedHostSeed
public import LowerHostScales

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Filter Finset ColouredCliques CompleteJohnson SparseGram ProfileBalance CliqueGram
open scoped Topology

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The total seed mass is prescribed by the unit edge loads, before
any existence result for exact designs is used. -/
theorem profile_mass_of_unit_seed {n q : ℕ} (hq : 2 ≤ q)
    (colour : Fin n → C) (hclasses : ∀ i, q ≤ profile colour univ i)
    (m : TypeProfile C q → ℝ)
    (hload : ∀ e : Edge n,
      WeightedEnergy.load (resources n q) (ProfileWeights.weight (cliqueType colour) m) e = 1) :
    (∑ t, m t) = (Fintype.card (Edge n) : ℝ) / (q.choose 2 : ℝ) := by
  let w := ProfileWeights.weight (cliqueType colour) m
  have ht : (∑ t, m t) = ∑ b, w b := by
    rw [← sum_fiberwise univ (cliqueType colour) w]
    exact sum_congr rfl (fun t _ => (seed_mass colour hclasses m t).symm)
  have hi := WeightedEnergy.incidence_sum (resources n q) w (fun _ => (1 : ℝ))
  have hload' (e : Edge n) : WeightedEnergy.load (resources n q) w e = 1 := hload e
  simp only [hload', mul_one, sum_const, nsmul_eq_mul, card_univ, resources_card, ← sum_mul] at hi
  have hr : (0 : ℝ) < q.choose 2 := by exact_mod_cast Nat.choose_pos hq
  rw [ht]
  exact (eq_div_iff hr.ne').mpr hi

/-- The two normalized diffuse bounds of the unpruned seed, with
constants fixed by the class proportions and the interior margin. -/
theorem eventually_interior_seed (q : ℕ) (hq : 3 ≤ q) (ρ κ : ℝ)
    (hρ : 0 < ρ) (hκ : 0 < κ) :
    let s := ρ / 4
    let W := (q.factorial : ℝ) ^ Fintype.card C / s ^ q
    let ℓ := (κ / (4 * (q.choose 2 : ℝ))) /
      ((2 : ℝ) ^ (q - 2) * ((q - 2).factorial : ℝ))
    ∀ᶠ n : ℕ in atTop, ∀ (colour : Fin n → C) (m : TypeProfile C q → ℝ),
      (∀ i, ρ * (n : ℝ) ≤ (profile colour univ i : ℝ)) →
      (∀ t, κ * ((Fintype.card (Edge n) : ℝ) / (q.choose 2 : ℝ)) ≤ m t) →
      (∀ e : Edge n, pairMargin colour m e =
        (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ)) →
      ∃ d : ℕ, (∀ i, d + q ≤ profile colour univ i) ∧ s * (n : ℝ) ≤ d ∧
        (∀ b : Clique n q, ℓ * HostCorrection.scale n q ≤
          ProfileWeights.weight (cliqueType colour) m b) ∧
        (∀ b : Clique n q, |ProfileWeights.weight (cliqueType colour) m b| ≤
          W * HostCorrection.scale n q) ∧
        ∀ e : Edge n, WeightedEnergy.load (resources n q) (ProfileWeights.weight (cliqueType colour) m) e = 1 := by
  let s := ρ / 4
  let r := q.choose 2
  let B (n : ℕ) := (Fintype.card (Edge n) : ℝ) / (r : ℝ)
  let c := κ / (4 * (r : ℝ))
  have hq' : 2 ≤ q := by omega
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.choose_pos hq'
  have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast Nat.choose_pos hq'
  have hs : 0 < s := by dsimp [s]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2 * q),
    (tendsto_atTop.1 hnat) ((4 * ((q : ℝ) + 1)) / ρ)] with n hn hlarge
  intro colour m hclasses hm hmargin
  have hnq : q ≤ n := by omega
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
  have hlarge' : 4 * ((q : ℝ) + 1) ≤ ρ * (n : ℝ) := by
    simpa only [mul_comm (n : ℝ) ρ] using (div_le_iff₀ hρ).mp hlarge
  let d := ⌊ρ * (n : ℝ) / 2⌋₊
  have hdn : s * (n : ℝ) ≤ d := by
    have hf := Nat.lt_floor_add_one (ρ * (n : ℝ) / 2)
    change ρ * (n : ℝ) / 2 < (d : ℝ) + 1 at hf
    dsimp [s]
    linarith only [hf, hlarge', Nat.cast_nonneg (α := ℝ) q]
  have hd (i : C) : d + q ≤ profile colour univ i := by
    have hf := Nat.floor_le (show 0 ≤ ρ * (n : ℝ) / 2 by positivity)
    change (d : ℝ) ≤ ρ * (n : ℝ) / 2 at hf
    exact_mod_cast (by linarith only [hf, hlarge', hclasses i] :
      (d : ℝ) + q ≤ profile colour univ i)
  have hcls (i : C) : q ≤ profile colour univ i := (Nat.le_add_left _ _).trans (hd i)
  have hload := seed_load colour hcls m hmargin
  have hsum := profile_mass_of_unit_seed hq' colour hcls m hload
  have hb₁ : (n : ℝ) ^ 2 / (4 * (r : ℝ)) ≤ B n := by
    change _ ≤ (Fintype.card (Edge n) : ℝ) / (r : ℝ)
    rw [edge_card n (by omega)]
    rw [div_mul_eq_div_div]
    apply div_le_div_of_nonneg_right _ hr.le
    nlinarith only [mul_nonneg (show 0 ≤ (n : ℝ) - 2 by linarith) (by positivity : 0 ≤ (n : ℝ))]
  have hbn : 0 ≤ B n := div_nonneg (Nat.cast_nonneg _) hr.le
  have hb₂ : B n ≤ (n : ℝ) ^ 2 := by
    have hcard : Fintype.card (Edge n) = n.choose 2 := by
      rw [Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]
    dsimp only [B]
    rw [hcard]
    exact (div_le_self (Nat.cast_nonneg _) hr₁).trans (by exact_mod_cast Nat.choose_le_pow n 2)
  have hlow (t : TypeProfile C q) : c * (n : ℝ) ^ 2 ≤ m t := by
    refine le_trans ?_ (hm t)
    calc
      _ = κ * ((n : ℝ) ^ 2 / (4 * (r : ℝ))) := by dsimp [c]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb₁ hκ.le
  have hnonneg (t : TypeProfile C q) : 0 ≤ m t := le_trans (mul_nonneg hκ.le hbn) (hm t)
  have hu (t : TypeProfile C q) : |m t| ≤ 1 * (n : ℝ) ^ 2 := by
    rw [abs_of_nonneg (hnonneg t), one_mul]
    exact (single_le_sum (fun j _ => hnonneg j) (mem_univ t)).trans (hsum.trans_le hb₂)
  exact ⟨d, hd, hdn,
    seed_weight_lower colour hq' hn hcls c hc m hlow,
    (by simpa only [one_mul, HostCorrection.scale] using
      seed_weight_abs_le colour hq' hnq d s 1 hs zero_le_one hd hdn m hu),
    hload⟩

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.profile_mass_of_unit_seed
#print axioms KqR75.PhysicalCompletion.eventually_interior_seed
