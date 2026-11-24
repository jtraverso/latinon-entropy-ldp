module
public import GreedySchedule
public import TypeTracking

@[expose] public section
noncomputable section
namespace KqR75.TypeDriftEnvelope

private theorem rpow_sq {x : ℝ} (hx : 0 ≤ x) (s : ℝ) :
    (x ^ s) ^ 2 = x ^ (2 * s) := by
  rw [← Real.rpow_two, ← Real.rpow_mul hx, mul_comm s 2]

/-- Cauchy–Schwarz on the live resource set gives the absolute-error
scale before the integrated-energy crossing. -/
theorem absolute_error {n p r C A m X L : ℝ}
    (hn : 0 < n) (hp : 0 < p) (hr : 0 ≤ r) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (_hm : 0 ≤ m) (hX : 0 ≤ X) (hmul : m ≤ C * n ^ 2 * p)
    (henergy : X ≤ A * n * p ^ (-2 * r)) (hL : L ^ 2 ≤ r * m * X) :
    L ≤ Real.sqrt (r * C * A) * n ^ (3 / 2 : ℝ) * p ^ (1 / 2 - r) := by
  have hbase := mul_nonneg (mul_nonneg hr hC) hA
  have hL' : L ^ 2 ≤ (r * C * A) * n ^ 3 * p ^ (1 - 2 * r) := by
    calc
      _ ≤ r * m * X := hL
      _ ≤ r * (C * n ^ 2 * p) * (A * n * p ^ (-2 * r)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hmul hr) henergy hX (by positivity)
      _ = (r * C * A) * n ^ 3 * (p * p ^ (-2 * r)) := by ring
      _ = _ := by
        rw [show p * p ^ (-2 * r) = p ^ (1 - 2 * r) by
          rw [sub_eq_add_neg, Real.rpow_add hp, Real.rpow_one, neg_mul]]
  have hsquare :
      (Real.sqrt (r * C * A) * n ^ (3 / 2 : ℝ) * p ^ (1 / 2 - r)) ^ 2 =
        (r * C * A) * n ^ 3 * p ^ (1 - 2 * r) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hbase, rpow_sq hn.le, rpow_sq hp.le]
    rw [show 2 * (3 / 2 : ℝ) = 3 by norm_num, show (3 : ℝ) = (↑(3 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, show 2 * (1 / 2 - r) = 1 - 2 * r by ring]
  by_contra! h
  have hnonneg : 0 ≤ Real.sqrt (r * C * A) * n ^ (3 / 2 : ℝ) * p ^ (1 / 2 - r) := by positivity
  have hprod := mul_pos (sub_pos.mpr h)
    (show 0 < L + Real.sqrt (r * C * A) * n ^ (3 / 2 : ℝ) * p ^ (1 / 2 - r) by linarith)
  nlinarith only [hL'.trans_eq hsquare.symm, hprod]

/-- The nonlinear type drift splits into four power envelopes at a
regular history. The lower bound for available mass absorbs both
denominators before summation. -/
theorem drift {n p r c C A X L Z γ b : ℝ}
    (hn : 0 < n) (hp : 0 < p) (_hr : 0 ≤ r) (hc : 0 < c)
    (hA : 0 ≤ A) (hb : 0 ≤ b) (_hX : 0 ≤ X) (_hL : 0 ≤ L) (_hγ : 0 ≤ γ)
    (henergy : X ≤ A * n * p ^ (-2 * r))
    (herror : L ≤ Real.sqrt (r * C * A) * n ^ (3 / 2 : ℝ) * p ^ (1 / 2 - r))
    (hmass : c / 2 * n ^ 2 * p ^ r ≤ Z) (hcodeg : γ ≤ r ^ 2 * b / n) :
    (X + p ^ (r - 1) * L) / Z ^ 2 + γ / Z + 2 * r ^ 2 / Z ^ 2 ≤
      (2 / c) ^ 2 * A * (n ^ (-3 : ℝ) * p ^ (-4 * r)) +
      (2 / c) ^ 2 * Real.sqrt (r * C * A) * (n ^ (-5 / 2 : ℝ) * p ^ (-2 * r - 1 / 2)) +
      (2 / c) * r ^ 2 * b * (n ^ (-3 : ℝ) * p ^ (-r)) +
      (2 / c) ^ 2 * (2 * r ^ 2) * (n ^ (-4 : ℝ) * p ^ (-2 * r)) := by
  let W := (2 / c) * n ^ (-2 : ℝ) * p ^ (-r)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hZ : 0 < Z := (show 0 < c / 2 * n ^ 2 * p ^ r by positivity).trans_le hmass
  have hInv : Z⁻¹ ≤ W := by
    calc
      _ ≤ (c / 2 * n ^ 2 * p ^ r)⁻¹ :=
        (inv_le_inv₀ hZ (by positivity)).mpr hmass
      _ = _ := by
        dsimp [W]
        rw [Real.rpow_neg hn.le, Real.rpow_two, Real.rpow_neg hp.le]
        field_simp
  have hSq : (Z ^ 2)⁻¹ ≤ W ^ 2 := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (by positivity) hInv _
  have hWsq : W ^ 2 = (2 / c) ^ 2 * n ^ (-4 : ℝ) * p ^ (-2 * r) := by
    dsimp [W]
    rw [mul_pow, mul_pow, rpow_sq hn.le, rpow_sq hp.le]
    rw [show 2 * (-2 : ℝ) = -4 by norm_num, show 2 * (-r) = -2 * r by ring]
  have hpowN : n * n ^ (-4 : ℝ) = n ^ (-3 : ℝ) := by
    rw [show (-3 : ℝ) = 1 + (-4) by norm_num, Real.rpow_add hn, Real.rpow_one]
  have hpowX : n ^ (3 / 2 : ℝ) * n ^ (-4 : ℝ) = n ^ (-5 / 2 : ℝ) := by
    rw [← Real.rpow_add hn]
    congr 1
    norm_num
  have hpowL : p ^ (r - 1) * p ^ (1 / 2 - r) * p ^ (-2 * r) = p ^ (-2 * r - 1 / 2) := by
    rw [← Real.rpow_add hp, ← Real.rpow_add hp]
    congr 1
    ring
  have hpowP : p ^ (-2 * r) * p ^ (-2 * r) = p ^ (-4 * r) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  have hnDiv : n⁻¹ * n ^ (-2 : ℝ) = n ^ (-3 : ℝ) := by
    rw [show n⁻¹ = n ^ (-1 : ℝ) by rw [Real.rpow_neg hn.le, Real.rpow_one],
      ← Real.rpow_add hn, show (-1 : ℝ) + (-2) = -3 by norm_num]
  calc
    _ = X * (Z ^ 2)⁻¹ + (p ^ (r - 1) * L) * (Z ^ 2)⁻¹ + γ * Z⁻¹ + (2 * r ^ 2) * (Z ^ 2)⁻¹ := by
      simp only [div_eq_mul_inv, add_mul]
    _ ≤ (A * n * p ^ (-2 * r)) * W ^ 2 +
        (p ^ (r - 1) * (Real.sqrt (r * C * A) * n ^ (3 / 2 : ℝ) * p ^ (1 / 2 - r))) * W ^ 2 +
        (r ^ 2 * b / n) * W + (2 * r ^ 2) * W ^ 2 := by
      have h1 := mul_le_mul henergy hSq (by positivity) (by positivity)
      have h2 := mul_le_mul (mul_le_mul_of_nonneg_left herror (show 0 ≤ p ^ (r - 1) by positivity)) hSq
        (by positivity) (by positivity)
      have h3 := mul_le_mul hcodeg hInv (by positivity) (by positivity)
      have h4 := mul_le_mul_of_nonneg_left hSq (show 0 ≤ 2 * r ^ 2 by positivity)
      exact add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by
      have ha : (A * n * p ^ (-2 * r)) * W ^ 2 =
          (2 / c) ^ 2 * A * ((n * n ^ (-4 : ℝ)) * (p ^ (-2 * r) * p ^ (-2 * r))) := by
        rw [hWsq]; ring
      have hl : (p ^ (r - 1) * (Real.sqrt (r * C * A) * n ^ (3 / 2 : ℝ) *
          p ^ (1 / 2 - r))) * W ^ 2 =
          (2 / c) ^ 2 * Real.sqrt (r * C * A) *
            ((n ^ (3 / 2 : ℝ) * n ^ (-4 : ℝ)) * (p ^ (r - 1) * p ^ (1 / 2 - r) * p ^ (-2 * r))) := by
        rw [hWsq]; ring
      have hc' : (r ^ 2 * b / n) * W =
          (2 / c) * r ^ 2 * b * ((n⁻¹ * n ^ (-2 : ℝ)) * p ^ (-r)) := by
        dsimp [W]; ring
      rw [ha, hl, hc', hpowN, hpowP, hpowX, hpowL, hnDiv, hWsq]
      ring

open Finset

theorem count_eq_length {B : Type*} (h : List (Option B)) (hh : none ∉ h) :
    WeightedGreedy.selectedCount h = h.length := by
  induction h with
  | nil => simp [WeightedGreedy.selectedCount]
  | cons x h ih =>
    have hn : none ∉ h := fun he => hh (List.mem_cons_of_mem _ he)
    cases x with
    | none => exact (hh List.mem_cons_self).elim
    | some w => simp only [WeightedGreedy.selectedCount, List.length_cons, ih hn]

/-- Instantiate the four envelopes with the actual predictable
increment of any type proportion on an active history. -/
theorem active_bound {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]
    (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (S : Finset B) (guard : List (Option B) → Prop)
    (r T : ℕ) (M n β b c C A : ℝ) (hr : 1 ≤ r) (hn : 1 ≤ n)
    (hc : 0 < c) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hMₗ : c * n ^ 2 ≤ M) (hMᵤ : M ≤ C * n ^ 2) (hT : (T : ℝ) < M)
    (hsize : ∀ w, (I w).card = r) (hJ : (J.card : ℝ) = (r : ℝ) * M)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (hβ : 0 ≤ β) (hb : 0 ≤ b) (hβrate : β ≤ b / n)
    (hcodeg : ∀ e f, e ≠ f → CodegreeLoss.codegree I μ e f ≤ β)
    (h : List (Option B)) (hl : WeightedGreedy.live I μ J guard h)
    (hlen : h.length ≤ T) (hreg : StoppedPhysical.regular I μ J r M n β h)
    (hY : WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
      (StoppedPhysical.profile (2 * r) M) h ≤ A * n)
    (hZ : 2 * (r : ℝ) ≤ WeightedGreedy.totalWeight I μ J h) :
    let p := (M - (WeightedGreedy.selectedCount h : ℝ)) / M
    |∑ x, (WeightedGreedy.kernel I μ hμ J guard).transition h x *
        TypeMartingale.increment I μ J S guard h x| ≤
      (2 / c) ^ 2 * A * (n ^ (-3 : ℝ) * p ^ (-4 * (r : ℝ))) +
      (2 / c) ^ 2 * Real.sqrt ((r : ℝ) * C * A) * (n ^ (-5 / 2 : ℝ) * p ^ (-2 * (r : ℝ) - 1 / 2)) +
      (2 / c) * (r : ℝ) ^ 2 * b * (n ^ (-3 : ℝ) * p ^ (-(r : ℝ))) +
      (2 / c) ^ 2 * (2 * (r : ℝ) ^ 2) * (n ^ (-4 : ℝ) * p ^ (-2 * (r : ℝ))) := by
  let i := WeightedGreedy.selectedCount h
  let m := StoppedPhysical.mass M i
  let p := m / M
  let k := StoppedPhysical.profile (r - 1) M i
  let X := WeightedGreedy.energy I μ J h k
  let L := ∑ e, |WeightedGreedy.error I μ J h k e|
  let Z := WeightedGreedy.totalWeight I μ J h
  let γ := (r : ℝ) ^ 2 * β
  have hn₀ : 0 < n := by linarith
  have hM₀ : 0 < M := (mul_pos hc (by positivity)).trans_le hMₗ
  have hi : i = h.length := count_eq_length h hl.1
  have hv := hreg.1
  have hm := hreg.2.1
  have hk := hreg.2.2.1
  change n ≤ m at hm
  have hm₀ := hn₀.trans_le hm
  have hp : 0 < p := div_pos hm₀ hM₀
  have hiM : (i : ℝ) ≤ M := by dsimp [m, StoppedPhysical.mass] at hm₀; linarith
  have hmk : M * p = m := by rw [mul_comm]; exact div_mul_cancel₀ _ hM₀.ne'
  have hk_eq : k = p ^ ((r : ℝ) - 1) := by
    rw [show (r : ℝ) - 1 = (↑(r - 1) : ℝ) by rw [Nat.cast_sub hr, Nat.cast_one], Real.rpow_natCast]
    exact StoppedPhysical.profile_eq (r - 1) M i hM₀ hiM
  have hcoverage : ((WeightedGreedy.remaining I J h).card : ℝ) = (r : ℝ) * m := by
    have hh := WeightedGreedy.resource_count I J r hsize h hv
    have hh' : ((WeightedGreedy.remaining I J h).card : ℝ) + (r : ℝ) * i = J.card := by exact_mod_cast hh
    rw [hJ] at hh'
    dsimp [m, StoppedPhysical.mass]
    linarith only [hh']
  have hXX : 0 ≤ X := sum_nonneg (fun _ _ => sq_nonneg _)
  have hLY := (GreedyMoments.error_variances I μ J h k).1
  rw [hcoverage] at hLY
  have hYX : X ≤ A * n * p ^ (-2 * (r : ℝ)) := by
    have hfactor : StoppedPhysical.profile (2 * r) M i = p ^ (2 * (r : ℝ)) := by
      rw [StoppedPhysical.profile_eq _ _ _ hM₀ hiM, ← Real.rpow_natCast, Nat.cast_mul]
      norm_num [p, m]
    change StoppedPhysical.profile (2 * r) M i * X ≤ A * n at hY
    rw [hfactor] at hY
    rw [show -2 * (r : ℝ) = -(2 * (r : ℝ)) by ring, Real.rpow_neg hp.le, ← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos hp _)).mpr (by linarith only [hY, mul_comm X (p ^ (2 * (r : ℝ)))])
  have hL : L ≤ Real.sqrt ((r : ℝ) * C * A) * n ^ (3 / 2 : ℝ) * p ^ (1 / 2 - (r : ℝ)) :=
    absolute_error hn₀ hp (by positivity) hC hA hm₀.le hXX
      (by rw [← hmk]; gcongr) hYX hLY
  have hZₗ : c / 2 * n ^ 2 * p ^ (r : ℝ) ≤ Z := by
    rw [Real.rpow_natCast]
    calc
      _ = (c * n ^ 2) / 2 * p ^ r := by ring
      _ ≤ M / 2 * p ^ r := by gcongr
      _ = GreedySchedule.denominator M T r h.length := by
        rw [GreedySchedule.denominator, min_eq_left hlen, ← hi]
        rfl
      _ ≤ _ := GreedySchedule.denominator_le_available I μ J r T M n β hr hn hM₀ hsize hJ h hreg hlen hT
  have hover (w : B) : OverlapDrift.overcount I (WeightedGreedy.availableWeight I μ J h) w ≤ γ :=
    CodegreeLoss.overcount_le I _ (WeightedGreedy.availableWeight_nonneg I μ hμ J h) r hsize β hβ
      (fun e f hef => (StoppedPhysical.codegree_le_initial I μ hμ J h e f).trans (hcodeg e f hef)) w
  have hmean := TypeTracking.active_mean_bound I μ hμ J S guard h hl r hr hsize hload k γ
    hk.le (by dsimp [γ]; positivity) hover hZ
  change _ ≤ (X + k * L) / Z ^ 2 + γ / Z + 2 * (r : ℝ) ^ 2 / Z ^ 2 at hmean
  rw [hk_eq] at hmean
  exact hmean.trans (drift hn₀ hp (by positivity) hc hA hb hXX
    (sum_nonneg (fun _ _ => abs_nonneg _)) (by dsimp [γ]; positivity) hYX hL hZₗ
    (by dsimp [γ]; rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hβrate (by positivity)))

end KqR75.TypeDriftEnvelope

#print axioms KqR75.TypeDriftEnvelope.absolute_error
#print axioms KqR75.TypeDriftEnvelope.drift
#print axioms KqR75.TypeDriftEnvelope.active_bound
