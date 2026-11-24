module
public import MeanEnergy

@[expose] public section
noncomputable section
namespace KqR75.TimeEnergy

open Finset

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

def remainingLoss (I : B → Finset E) (w : B → ℝ) (c : B) : ℝ :=
  ∑ e, if e ∈ I c then 0 else OverlapDrift.loss I w c e

theorem sum_complement (S : Finset E) (f : E → ℝ) :
    (∑ e, if e ∈ S then 0 else f e) = (∑ e, f e) - ∑ e ∈ S, f e := by
  have hpoint (e : E) : (if e ∈ S then 0 else f e) = f e - (if e ∈ S then f e else 0) := by
    split_ifs <;> ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [← Finset.sum_filter]
  simp

theorem profile_shift (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (k η : ℝ) :
    WeightedGreedy.energy I μ J h (k - η) - WeightedGreedy.energy I μ J h k =
      2 * η * (∑ e, WeightedGreedy.error I μ J h k e) +
        η ^ 2 * ((WeightedGreedy.remaining I J h).card : ℝ) := by
  have he (e : E) : (WeightedGreedy.error I μ J h (k - η) e) ^ 2 -
      (WeightedGreedy.error I μ J h k e) ^ 2 =
      2 * η * WeightedGreedy.error I μ J h k e +
        (if e ∈ WeightedGreedy.remaining I J h then η ^ 2 else 0) := by
    by_cases hm : e ∈ WeightedGreedy.remaining I J h
    · simp only [WeightedGreedy.error, hm, ite_true]
      ring
    · simp [WeightedGreedy.error, hm, WeightedGreedy.load_zero_outside I μ J h e hm]
  dsimp only [WeightedGreedy.energy]
  rw [← Finset.sum_sub_distrib]
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_filter]
  simp [mul_comm]

theorem sum_error_after (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (c : B) (k : ℝ) :
    (∑ e, WeightedGreedy.error I μ J (some c :: h) k e) =
      (∑ e, WeightedGreedy.error I μ J h k e) - (∑ e ∈ I c, WeightedGreedy.error I μ J h k e) -
        remainingLoss I (WeightedGreedy.availableWeight I μ J h) c := by
  have he (e : E) : WeightedGreedy.error I μ J (some c :: h) k e =
      (if e ∈ I c then 0 else WeightedGreedy.error I μ J h k e) -
        (if e ∈ I c then 0 else OverlapDrift.loss I (WeightedGreedy.availableWeight I μ J h) c e) := by
    have he := WeightedGreedy.error_after I μ J h c k 0 e
    simp only [sub_zero, ite_self, add_zero] at he
    rw [he, OverlapDrift.loss_eq_history]
    by_cases hm : e ∈ I c <;> simp [hm]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, sum_complement]
  rfl

theorem mean_error_after (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (k : ℝ) :
    (∑ c, WeightedGreedy.availableWeight I μ J h c * ∑ e, WeightedGreedy.error I μ J (some c :: h) k e) =
      WeightedGreedy.totalWeight I μ J h * (∑ e, WeightedGreedy.error I μ J h k e) -
        (∑ e, WeightedGreedy.load I μ J h e * WeightedGreedy.error I μ J h k e) -
        ∑ c, WeightedGreedy.availableWeight I μ J h c *
          remainingLoss I (WeightedGreedy.availableWeight I μ J h) c := by
  simp_rw [sum_error_after, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
    WeightedEnergy.incidence_sum]
  rfl

theorem mean_card_after (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (r : ℕ) (hsize : ∀ b, (I b).card = r) :
    (∑ c, WeightedGreedy.availableWeight I μ J h c *
      ((WeightedGreedy.remaining I J (some c :: h)).card : ℝ)) =
      WeightedGreedy.totalWeight I μ J h *
        (((WeightedGreedy.remaining I J h).card : ℝ) - r) := by
  have hc (c : B) : WeightedGreedy.availableWeight I μ J h c *
      ((WeightedGreedy.remaining I J (some c :: h)).card : ℝ) =
      WeightedGreedy.availableWeight I μ J h c *
        (((WeightedGreedy.remaining I J h).card : ℝ) - r) := by
    by_cases hw : WeightedGreedy.availableWeight I μ J h c = 0
    · simp [hw]
    have hs : I c ⊆ WeightedGreedy.remaining I J h := by
      by_contra hn
      simp [WeightedGreedy.availableWeight, hn] at hw
    have ht := Finset.card_sdiff_add_card_eq_card hs
    rw [hsize] at ht
    have htR : (((WeightedGreedy.remaining I J h \ I c).card : ℕ) : ℝ) + r =
        (WeightedGreedy.remaining I J h).card := by exact_mod_cast ht
    have he : ((WeightedGreedy.remaining I J (some c :: h)).card : ℝ) =
        ((WeightedGreedy.remaining I J h).card : ℝ) - r := by
      change ((WeightedGreedy.remaining I J h \ I c).card : ℝ) = _
      linarith only [htR]
    rw [he]
  simp_rw [hc]
  rw [← Finset.sum_mul]
  rfl

/-- The full physical numerator, including the change of k and the crossing step. -/
theorem physical_mean_drift (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (r : ℕ) (hsize : ∀ b, (I b).card = r) (k η : ℝ) :
    let w := WeightedGreedy.availableWeight I μ J h
    let x := WeightedGreedy.error I μ J h k
    let Z := WeightedGreedy.totalWeight I μ J h
    let M := ∑ e, WeightedGreedy.load I μ J h e * x e
    (∑ c, w c * (WeightedGreedy.energy I μ J (some c :: h) (k - η) - WeightedGreedy.energy I μ J h k)) =
      (∑ e, WeightedGreedy.load I μ J h e * (x e) ^ 2) -
        2 * (∑ b, w b * (∑ e ∈ I b, x e) ^ 2) - 2 * ((r : ℝ) - 1) * k * M +
        2 * (∑ e, OverlapDrift.correction I w e * x e) + ∑ c, w c * MeanEnergy.squareLoss I w c +
        2 * η * (Z * (∑ e, x e) - M - ∑ c, w c * remainingLoss I w c) +
        η ^ 2 * (Z * (((WeightedGreedy.remaining I J h).card : ℝ) - r)) := by
  dsimp only
  have hc (c : B) :
      WeightedGreedy.energy I μ J (some c :: h) (k - η) - WeightedGreedy.energy I μ J h k =
      (WeightedGreedy.energy I μ J (some c :: h) k - WeightedGreedy.energy I μ J h k) +
        2 * η * (∑ e, WeightedGreedy.error I μ J (some c :: h) k e) +
        η ^ 2 * ((WeightedGreedy.remaining I J (some c :: h)).card : ℝ) := by
    have hs := profile_shift I μ J (some c :: h) k η
    linarith only [hs]
  have hstep :
      (∑ c, WeightedGreedy.availableWeight I μ J h c *
        (WeightedGreedy.energy I μ J (some c :: h) (k - η) - WeightedGreedy.energy I μ J h k)) =
      (∑ c, WeightedGreedy.availableWeight I μ J h c *
        (WeightedGreedy.energy I μ J (some c :: h) k - WeightedGreedy.energy I μ J h k)) +
        2 * η * (∑ c, WeightedGreedy.availableWeight I μ J h c *
          ∑ e, WeightedGreedy.error I μ J (some c :: h) k e) +
        η ^ 2 * (∑ c, WeightedGreedy.availableWeight I μ J h c *
          ((WeightedGreedy.remaining I J (some c :: h)).card : ℝ)) := by
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · congr 1
      apply Finset.sum_congr rfl
      intro c _
      ring
    · apply Finset.sum_congr rfl
      intro c _
      ring
  rw [hstep, MeanEnergy.physical_fixed_drift I μ J h r hsize k,
    mean_error_after, mean_card_after I μ J h r hsize]

theorem live_average (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop) (h : List (Option B))
    (hl : WeightedGreedy.live I μ J guard h) (F : Option B → ℝ) :
    (∑ a, (WeightedGreedy.kernel I μ hμ J guard).transition h a * F a) =
      (∑ c, WeightedGreedy.availableWeight I μ J h c * F (some c)) / WeightedGreedy.totalWeight I μ J h := by
  simp only [WeightedGreedy.kernel, hl, ite_true]
  rw [univ_option, Finset.sum_insertNone]
  simp only [zero_mul, zero_add]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  ring

end KqR75.TimeEnergy

#print axioms KqR75.TimeEnergy.physical_mean_drift
#print axioms KqR75.TimeEnergy.live_average
