module
public import TimeEnergy
public import CodegreeLoss
public import GreedyMoments
public import ScalarDrift
public import GreedyProfile

@[expose] public section
noncomputable section
namespace KqR75.PhysicalDrift

open Finset
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- Uniform one-step energy drift on the actual physical greedy kernel.
Every analytic hypothesis is an explicit state/schedule inequality; no drift
inequality, stochastic-process conclusion, or final counting theorem is assumed. -/
theorem energy_drift (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop) (h : List (Option B))
    (hlive : WeightedGreedy.live I μ J guard h)
    (r : ℕ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (m k η C β : ℝ) (hm : 1 ≤ m) (hk : 0 < k) (hk1 : k ≤ 1) (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hcard : ((WeightedGreedy.remaining I J h).card : ℝ) = (r : ℝ) * m)
    (hcodeg : ∀ e f, e ≠ f →
      CodegreeLoss.codegree I (WeightedGreedy.availableWeight I μ J h) e f ≤ β)
    (hsmall : 64 * (r : ℝ) ^ 2 * β ≤ k)
    (hZ : m * k / 2 ≤ WeightedGreedy.totalWeight I μ J h)
    (hnear : (2 * (r : ℝ) - 1) * k * m ≤
      (2 * (r : ℝ) - 1 / 2) * WeightedGreedy.totalWeight I μ J h)
    (hη0 : 0 ≤ η) (hη : η ≤ ((r : ℝ) - 1) * k / m)
    (hprofile : ((r : ℝ) - 1) * k / m - η ≤ C * k / m ^ 2) :
    (∑ a, (WeightedGreedy.kernel I μ hμ J guard).transition h a *
      (WeightedGreedy.energy I μ J (a :: h) (k - η) - WeightedGreedy.energy I μ J h k)) ≤
      2 * (r : ℝ) * WeightedGreedy.energy I μ J h k / m +
        32 * (r : ℝ) * (((r : ℝ) ^ 2 * β) ^ 2) +
        (r : ℝ) * (2 * C + 4 * ((r : ℝ) - 1)) ^ 2 / m ^ 2 +
        (r : ℝ) * ((r : ℝ) - 1) ^ 2 / m + (r : ℝ) ^ 3 * β := by
  let w := WeightedGreedy.availableWeight I μ J h
  let x := WeightedGreedy.error I μ J h k
  let Z := WeightedGreedy.totalWeight I μ J h
  let X := WeightedGreedy.energy I μ J h k
  let s := ∑ e, x e
  let L := ∑ e, |x e|
  let M := ∑ e, WeightedGreedy.load I μ J h e * x e
  let A := ∑ e, WeightedGreedy.load I μ J h e * (x e) ^ 2
  let Q := ∑ b, w b * (∑ e ∈ I b, x e) ^ 2
  let R := ∑ e, OverlapDrift.correction I w e * x e
  let W := ∑ c, w c * MeanEnergy.squareLoss I w c
  let H := ∑ c, w c * TimeEnergy.remainingLoss I w c
  let γ := (r : ℝ) ^ 2 * β
  let D := ∑ a, (WeightedGreedy.kernel I μ hμ J guard).transition h a *
    (WeightedGreedy.energy I μ J (a :: h) (k - η) - WeightedGreedy.energy I μ J h k)
  have hw (b : B) : 0 ≤ w b := WeightedGreedy.availableWeight_nonneg I μ hμ J h b
  have hZ0 : 0 < Z := hlive.2.2
  have hm0 : 0 < m := by linarith
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hγ0 : 0 ≤ γ := by dsimp [γ]; positivity
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun e _ => sq_nonneg _)
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun e _ => abs_nonneg _)
  obtain ⟨hvarL, hvarS⟩ := GreedyMoments.error_variances I μ J h k
  rw [hcard] at hvarL hvarS
  have hmass : s = (r : ℝ) * (Z - m * k) := by
    have ht := GreedyMoments.mass_error I μ J h r hsize k
    rw [hcard] at ht
    change s = (r : ℝ) * Z - k * ((r : ℝ) * m) at ht
    nlinarith only [ht]
  have hM : M = X + k * s := GreedyMoments.load_error_moment I μ J h k
  have hsigned : A - 2 * Q ≤ (2 * (r : ℝ) - 1) * k * X :=
    WeightedGreedy.signed_energy I μ hμ J r hr hsize h k hk
  have hR : R ≤ γ * (X + k * L) := by
    have hρ (e : E) := OverlapDrift.correction_bounds I w hw γ
      (CodegreeLoss.overcount_le I w hw r hsize β hβ hcodeg) e
    have hp (e : E) : OverlapDrift.correction I w e * x e ≤
        γ * (WeightedGreedy.load I μ J h e * |x e|) := by
      calc
        _ ≤ OverlapDrift.correction I w e * |x e| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (hρ e).1
        _ ≤ (γ * WeightedGreedy.load I μ J h e) * |x e| :=
          mul_le_mul_of_nonneg_right (hρ e).2 (abs_nonneg _)
        _ = _ := by ring
    calc
      _ ≤ ∑ e, γ * (WeightedGreedy.load I μ J h e * |x e|) := Finset.sum_le_sum (fun e _ => hp e)
      _ = γ * ∑ e, WeightedGreedy.load I μ J h e * |x e| := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (GreedyMoments.weighted_absolute_error I μ J h k) hγ0
  have hW : W / Z ≤ (r : ℝ) ^ 3 * β := by
    have hb (c : B) : MeanEnergy.squareLoss I w c ≤ (r : ℝ) ^ 3 * β :=
      CodegreeLoss.square_loss_le I w hw r hsize β hβ hcodeg
        (fun e => (WeightedGreedy.load_le_initial I μ hμ J h e).trans (hload e)) c
    have hs := Finset.sum_le_sum (fun c (_ : c ∈ (univ : Finset B)) =>
      mul_le_mul_of_nonneg_left (hb c) (hw c))
    rw [← Finset.sum_mul] at hs
    have hzsum : (∑ c, w c) = Z := rfl
    rw [hzsum] at hs
    exact (div_le_iff₀ hZ0).mpr (hs.trans_eq (mul_comm _ _))
  have hH : 0 ≤ H := Finset.sum_nonneg (fun c _ => mul_nonneg (hw c)
    (Finset.sum_nonneg (fun e _ => by
      split_ifs
      · exact le_rfl
      · exact CodegreeLoss.loss_nonneg I w hw c e)))
  have hD : D = (A - 2 * Q) / Z + 2 * R / Z +
      (-2 * ((r : ℝ) - 1) * k * (X + k * s) / Z + 2 * η * (s - (X + k * s) / Z)) +
        W / Z - 2 * η * H / Z + (r : ℝ) * η ^ 2 * (m - 1) := by
    have ha := TimeEnergy.live_average I μ hμ J guard h hlive
      (fun a => WeightedGreedy.energy I μ J (a :: h) (k - η) - WeightedGreedy.energy I μ J h k)
    have ht := TimeEnergy.physical_mean_drift I μ J h r hsize k η
    change (∑ c, w c * (WeightedGreedy.energy I μ J (some c :: h) (k - η) - X)) =
      A - 2 * Q - 2 * ((r : ℝ) - 1) * k * M + 2 * R + W +
        2 * η * (Z * s - M - H) + η ^ 2 * (Z * (((WeightedGreedy.remaining I J h).card : ℝ) - r)) at ht
    change D = (∑ c, w c * (WeightedGreedy.energy I μ J (some c :: h) (k - η) - X)) / Z at ha
    rw [ht, hM, hcard] at ha
    rw [ha]
    field_simp [hZ0.ne']
    <;> ring
  have hraw : D ≤ (2 * (r : ℝ) - 1) * k * X / Z + 2 * γ * (X + k * L) / Z +
      (2 * |s| * (((r : ℝ) - 1) * k / m - η) + 2 * η * k * |s| / Z) +
        (r : ℝ) ^ 3 * β + (r : ℝ) * η ^ 2 * (m - 1) := by
    rw [hD]
    have h1 := div_le_div_of_nonneg_right hsigned hZ0.le
    have h2 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 2)) hZ0.le
    have h2' : 2 * R / Z ≤ 2 * γ * (X + k * L) / Z := by
      convert h2 using 1 <;> ring
    have h3 := ScalarDrift.temporal_upper r m k Z X s η hrR hm0 hk hZ0 hX0 hη0
      (sub_nonneg.mpr hη) hmass hvarS
    have h4 : 0 ≤ 2 * η * H / Z := by positivity
    linarith only [h1, h2', h3, hW, h4]
  exact ScalarDrift.close_budget r m k Z γ X L s C (((r : ℝ) - 1) * k / m - η) η
    ((r : ℝ) ^ 3 * β) D hrR hm hk hk1 hZ hnear hγ0
    (by dsimp only [γ]; nlinarith only [hsmall]) hX0 hL0 hvarL hvarS hC hprofile hη0 hη hraw

/-- Natural greedy schedule. The denominator guards follow from small total
energy, and the schedule remainder is proved algebraically. -/
theorem energy_drift_regular (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop) (h : List (Option B))
    (hlive : WeightedGreedy.live I μ J guard h)
    (r : ℕ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (m k β : ℝ) (hm : 1 ≤ m) (hk : 0 < k) (hk1 : k ≤ 1) (hβ : 0 ≤ β)
    (hcard : ((WeightedGreedy.remaining I J h).card : ℝ) = (r : ℝ) * m)
    (hcodeg : ∀ e f, e ≠ f →
      CodegreeLoss.codegree I (WeightedGreedy.availableWeight I μ J h) e f ≤ β)
    (hsmall : 64 * (r : ℝ) ^ 2 * β ≤ k)
    (henergy : 16 * (r : ℝ) * WeightedGreedy.energy I μ J h k ≤ m * k ^ 2) :
    let η := k * (1 - (1 - 1 / m) ^ (r - 1))
    (∑ a, (WeightedGreedy.kernel I μ hμ J guard).transition h a *
      (WeightedGreedy.energy I μ J (a :: h) (k - η) - WeightedGreedy.energy I μ J h k)) ≤
      2 * (r : ℝ) * WeightedGreedy.energy I μ J h k / m +
        32 * (r : ℝ) * (((r : ℝ) ^ 2 * β) ^ 2) +
        (r : ℝ) * (2 * ((r : ℝ) - 1) ^ 2 + 4 * ((r : ℝ) - 1)) ^ 2 / m ^ 2 +
        (r : ℝ) * ((r : ℝ) - 1) ^ 2 / m + (r : ℝ) ^ 3 * β := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hm0 : 0 < m := by linarith
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr, Nat.cast_one]
  have hs := GreedyProfile.schedule_bounds (r - 1) m k hm hk.le
  dsimp only at hs
  rw [hcast] at hs
  have hmass : (∑ e, WeightedGreedy.error I μ J h k e) =
      (r : ℝ) * (WeightedGreedy.totalWeight I μ J h - m * k) := by
    have ht := GreedyMoments.mass_error I μ J h r hsize k
    rw [hcard] at ht
    nlinarith only [ht]
  have hvar := (GreedyMoments.error_variances I μ J h k).2
  rw [hcard] at hvar
  obtain ⟨hZ, hnear⟩ := ScalarDrift.regularity r m k (WeightedGreedy.totalWeight I μ J h)
    (WeightedGreedy.energy I μ J h k) (∑ e, WeightedGreedy.error I μ J h k e)
    hrR hm0 hk hmass hvar henergy
  exact energy_drift I μ hμ J guard h hlive r hr hsize hload
    m k (k * (1 - (1 - 1 / m) ^ (r - 1))) (((r : ℝ) - 1) ^ 2) β
    hm hk hk1 (sq_nonneg _) hβ hcard hcodeg hsmall hZ hnear hs.1 hs.2.1 hs.2.2.2

def noiseConstant (r : ℕ) (b : ℝ) : ℝ :=
  32 * (r : ℝ) ^ 5 * b ^ 2 +
    (r : ℝ) * (2 * ((r : ℝ) - 1) ^ 2 + 4 * ((r : ℝ) - 1)) ^ 2 +
    (r : ℝ) * ((r : ℝ) - 1) ^ 2 + (r : ℝ) ^ 3 * b

/-- The requested uniform B/n rate. The constant depends on the block size
and the diffuse-codegree constant, and not on the energy stopping parameter. -/
theorem energy_drift_rate (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop) (h : List (Option B))
    (hlive : WeightedGreedy.live I μ J guard h)
    (r : ℕ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (hload : ∀ e, WeightedEnergy.load I μ e ≤ 1)
    (n m k β b : ℝ) (hn : 1 ≤ n) (hm : n ≤ m) (hk : 0 < k) (hk1 : k ≤ 1)
    (hβ : 0 ≤ β) (hb : 0 ≤ b) (hβrate : β ≤ b / n)
    (hcard : ((WeightedGreedy.remaining I J h).card : ℝ) = (r : ℝ) * m)
    (hcodeg : ∀ e f, e ≠ f →
      CodegreeLoss.codegree I (WeightedGreedy.availableWeight I μ J h) e f ≤ β)
    (hsmall : 64 * (r : ℝ) ^ 2 * β ≤ k)
    (henergy : 16 * (r : ℝ) * WeightedGreedy.energy I μ J h k ≤ m * k ^ 2) :
    let η := k * (1 - (1 - 1 / m) ^ (r - 1))
    (∑ a, (WeightedGreedy.kernel I μ hμ J guard).transition h a *
      (WeightedGreedy.energy I μ J (a :: h) (k - η) - WeightedGreedy.energy I μ J h k)) ≤
      2 * (r : ℝ) * WeightedGreedy.energy I μ J h k / m + noiseConstant r b / n := by
  have hs := energy_drift_regular I μ hμ J guard h hlive r hr hsize hload
    m k β (hn.trans hm) hk hk1 hβ hcard hcodeg hsmall henergy
  have he := ScalarDrift.noise_rate r
    (2 * ((r : ℝ) - 1) ^ 2 + 4 * ((r : ℝ) - 1)) b β m n
    (by positivity) hb hβ hn hm hβrate
  dsimp only at hs ⊢
  dsimp only [noiseConstant]
  linarith only [hs, he]

end KqR75.PhysicalDrift

#print axioms KqR75.PhysicalDrift.energy_drift
#print axioms KqR75.PhysicalDrift.energy_drift_regular
#print axioms KqR75.PhysicalDrift.energy_drift_rate
