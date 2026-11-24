module
public import ResidualSeed
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
noncomputable section
namespace KqR75.SeedScales

open Filter Finset ColouredCliques SlotProfiles CompleteJohnson SparseGram ProfileBalance CliqueGram
open scoped Matrix Topology

/-- Convert an absolute deletion bound to the relative scale used by
the seed repair, including its normalization at positive orders. -/
theorem relative_degree_bound {n : ℕ} (hn : 0 < n) {t D z : ℝ}
    (ht : t ≤ D * (n : ℝ) ^ (1 - z)) :
    t / (n : ℝ) ≤ D * (n : ℝ) ^ (-z) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (1 - z) = (n : ℝ) * (n : ℝ) ^ (-z) := by
    rw [sub_eq_add_neg, Real.rpow_add hn', Real.rpow_one]
  apply (div_le_iff₀ hn').2
  rw [hpow] at ht
  convert ht using 1
  ring

/-- The finite correction inequalities hold uniformly at large host
orders when deletion degree is bounded by a constant times n^(1-z). -/
theorem eventually_repair_after_packing {C : Type*} [Fintype C] [DecidableEq C]
    (q : ℕ) (hq : 3 ≤ q) (ref : C) (s G M a D z : ℝ)
    (hs : 0 < s) (hG : 0 ≤ G) (hM : 0 ≤ M) (ha : 0 < a) (hz : 0 < z) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (colour : Fin n → C) (d : ℕ),
        (∀ i, d + q ≤ profile colour univ i) → s * (n : ℝ) ≤ d →
      ∀ (g : High C q ref → TypeProfile C q → ℝ),
        (∀ j v, |g j v| ≤ G) →
        (∀ i j : High C q ref, g j i.val = if i = j then 1 else 0) →
        (∀ j i₁ i₂, ∑ v, g j v * (SlotPairMargins.orderedCount v i₁ i₂ : ℝ) = 0) →
      ∀ (P : Finset (Clique n q)) (J : Finset (Edge n)) (t : ℝ), 0 ≤ t →
        t ≤ D * (n : ℝ) ^ (1 - z) →
        (∀ e : Edge n, ((P.filter fun b => e ∈ resources n q b).card : ℝ) =
          if e ∈ J then 0 else 1) →
        (∀ v : Fin n, ∑ f : (Jᶜ : Finset (Edge n)), incidence 2 f v ≤ t) →
      ∀ (w : Clique n q → ℝ),
        (∀ b, |w b| ≤ M * HostCorrection.scale n q) →
        (∀ b, a * HostCorrection.scale n q ≤ w b) →
        (∀ e : Edge n, WeightedEnergy.load (resources n q) w e = 1) →
        ∃ w' : HostCorrection.availableBlocks n q J → ℝ,
          HostCorrection.hostIncidence n q J *ᵥ w' = (fun _ => 1) ∧
          hostHistogram colour J w' =
            (fun i => histogram colour w i - histogram colour (fun b => if b ∈ P then 1 else 0) i) ∧
          (∀ b, 0 < w' b) ∧
          ∀ b, |w' b - w b| ≤ HostCorrection.scale n q * (L * (n : ℝ) ^ (-z)) := by
  classical
  let B₀ := G * (q.factorial : ℝ) ^ Fintype.card C / s ^ q
  let k := (Fintype.card (High C q ref) : ℝ)
  let r := (q.choose 2 : ℝ)
  let A := 16 * (1 + r) * (q : ℝ) ^ 2
  let H := k * B₀ * (1 / 2 + 16 * (q : ℝ) ^ 2)
  let E := 32 * r * M * (q : ℝ) ^ 2 +
    8 * k * B₀ * (1 + 32 * r * (q : ℝ) ^ 2) * ((1 + M) / 2 + 16 * M * (q : ℝ) ^ 2)
  let R := 1 + A + H + E / a
  have hB₀ : 0 ≤ B₀ := by dsimp [B₀]; positivity
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hEa : 0 ≤ E / a := by positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hR₁ : 1 ≤ R := by dsimp [R]; linarith
  have hRA : A ≤ R := by dsimp [R]; linarith
  have hRH : H ≤ R := by dsimp [R]; linarith
  have hRE : E / a ≤ R := by dsimp [R]; linarith
  refine ⟨max 0 D * E, mul_nonneg (le_max_left _ _) hE, ?_⟩
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-z)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hz).comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => D * (n : ℝ) ^ (-z)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul D
  have hsmall : ∀ᶠ n : ℕ in atTop, D * (n : ℝ) ^ (-z) < 1 / (2 * R) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  filter_upwards [eventually_ge_atTop (2 * q ^ 2), hsmall] with n hn hnsmall
  intro colour d hclasses hdn g hg hcoord hmargin P J t ht ht' hpacking hdeg w hw hwpos hseed
  let ξ := t / (n : ℝ)
  let α := HostCorrection.scale n q
  have hnq : q ≤ n := by nlinarith
  have hn₀ : 0 < n := by omega
  have hξ : ξ ≤ D * (n : ℝ) ^ (-z) := relative_degree_bound hn₀ ht'
  have hξ₀ : 0 ≤ ξ := by dsimp [ξ]; positivity
  have hξR : R * ξ ≤ 1 / 2 := by
    have hh := (lt_div_iff₀ (show 0 < 2 * R by positivity)).mp (hξ.trans_lt hnsmall)
    nlinarith only [hh]
  have hξ₁ : ξ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hR₁ hξ₀
    linarith
  have hξA : A * ξ ≤ 1 / 2 := (mul_le_mul_of_nonneg_right hRA hξ₀).trans hξR
  have hξH : H * ξ ≤ 1 / 2 := (mul_le_mul_of_nonneg_right hRH hξ₀).trans hξR
  have hξE : ξ * E ≤ a / 2 := by
    have hh := (mul_le_mul_of_nonneg_right hRE hξ₀).trans hξR
    rw [div_mul_eq_mul_div] at hh
    have he := (div_le_iff₀ ha).mp hh
    linarith [mul_comm E ξ]
  have hα : 0 < α := by
    dsimp [α, HostCorrection.scale]
    apply inv_pos.mpr
    exact_mod_cast Nat.choose_pos (show q - 2 ≤ n - 2 by omega)
  have hδα : α * ξ * E ≤ a * α / 2 := by
    calc
      _ = α * (ξ * E) := mul_assoc _ _ _
      _ ≤ α * (a / 2) := mul_le_mul_of_nonneg_left hξE hα.le
      _ = _ := by ring
  obtain ⟨w', hload, hhist, hpositive, hpert⟩ :=
    ResidualSeed.repair_after_packing hq hn colour ref d s G hs hG hclasses hdn g hg hcoord hmargin
      P J t M (a * α) ht hM (mul_pos ha hα) hpacking hdeg w hw hwpos hseed hξ₁ hξA hξH hδα
  refine ⟨w', hload, hhist, hpositive, fun b => (hpert b).trans ?_⟩
  have hξ' : ξ ≤ max 0 D * (n : ℝ) ^ (-z) :=
    hξ.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  calc
    _ ≤ α * (max 0 D * (n : ℝ) ^ (-z)) * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hξ' hα.le) hE
    _ = _ := by ring

end KqR75.SeedScales

#print axioms KqR75.SeedScales.eventually_repair_after_packing
