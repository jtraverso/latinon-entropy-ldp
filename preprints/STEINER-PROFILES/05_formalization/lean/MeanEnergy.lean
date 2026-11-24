module
public import OverlapDrift

@[expose] public section
noncomputable section
namespace KqR75.MeanEnergy

open Finset

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

def squareLoss (I : B → Finset E) (w : B → ℝ) (c : B) : ℝ :=
  ∑ e, if e ∈ I c then 0 else (OverlapDrift.loss I w c e) ^ 2

def fixedChange (I : B → Finset E) (w : B → ℝ) (x : E → ℝ) (c : B) : ℝ :=
  ∑ e, if e ∈ I c then -(x e) ^ 2 else
    -2 * x e * OverlapDrift.loss I w c e + (OverlapDrift.loss I w c e) ^ 2

theorem mean_fixed_change (I : B → Finset E) (w : B → ℝ) (x : E → ℝ) :
    (∑ c, w c * fixedChange I w x c) =
      -(∑ e, WeightedEnergy.load I w e * (x e) ^ 2) -
        2 * ((∑ b, w b * (∑ e ∈ I b, x e) * (∑ e ∈ I b, WeightedEnergy.load I w e)) -
          (∑ e, OverlapDrift.correction I w e * x e) -
          ∑ e, (WeightedEnergy.load I w e) ^ 2 * x e) +
        ∑ c, w c * squareLoss I w c := by
  have hpoint (c : B) (e : E) :
      w c * (if e ∈ I c then -(x e) ^ 2 else
        -2 * x e * OverlapDrift.loss I w c e + (OverlapDrift.loss I w c e) ^ 2) =
        -((if e ∈ I c then w c else 0) * (x e) ^ 2) -
          2 * (w c * (if e ∈ I c then 0 else OverlapDrift.loss I w c e) * x e) +
          w c * (if e ∈ I c then 0 else (OverlapDrift.loss I w c e) ^ 2) := by
    by_cases he : e ∈ I c <;> simp only [he, ite_true, ite_false] <;> ring
  have he (e : E) :
      (∑ c, w c * (if e ∈ I c then -(x e) ^ 2 else
        -2 * x e * OverlapDrift.loss I w c e + (OverlapDrift.loss I w c e) ^ 2)) =
        -(WeightedEnergy.load I w e * (x e) ^ 2) -
          2 * (((∑ c, w c * OverlapDrift.loss I w c e) - (WeightedEnergy.load I w e) ^ 2) * x e) +
          ∑ c, w c * (if e ∈ I c then 0 else (OverlapDrift.loss I w c e) ^ 2) := by
    have hsel : (∑ c, (if e ∈ I c then w c else 0) * (x e) ^ 2) =
        WeightedEnergy.load I w e * (x e) ^ 2 := by rw [← Finset.sum_mul]; rfl
    have hout : (∑ c, w c * (if e ∈ I c then 0 else OverlapDrift.loss I w c e) * x e) =
        ((∑ c, w c * OverlapDrift.loss I w c e) - (WeightedEnergy.load I w e) ^ 2) * x e := by
      rw [← Finset.sum_mul, OverlapDrift.weighted_outside_loss]
    calc
      _ = -(∑ c, (if e ∈ I c then w c else 0) * (x e) ^ 2) -
          2 * (∑ c, w c * (if e ∈ I c then 0 else OverlapDrift.loss I w c e) * x e) +
          ∑ c, w c * (if e ∈ I c then 0 else (OverlapDrift.loss I w c e) ^ 2) := by
        simp_rw [hpoint]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
          ← Finset.mul_sum]
      _ = _ := by rw [hsel, hout]
  have hloss : (∑ e, (∑ c, w c * OverlapDrift.loss I w c e) * x e) =
      (∑ b, w b * (∑ e ∈ I b, x e) * (∑ e ∈ I b, WeightedEnergy.load I w e)) -
        ∑ e, OverlapDrift.correction I w e * x e := by
    calc
      _ = ∑ c, ∑ e, (w c * OverlapDrift.loss I w c e) * x e := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
      _ = ∑ c, w c * ∑ e, OverlapDrift.loss I w c e * x e := by
        apply Finset.sum_congr rfl
        intro c _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = _ := OverlapDrift.weighted_loss I w x
  have hW : (∑ e, ∑ c, w c * (if e ∈ I c then 0 else (OverlapDrift.loss I w c e) ^ 2)) =
      ∑ c, w c * squareLoss I w c := by
    rw [Finset.sum_comm]
    simp only [squareLoss, Finset.mul_sum]
  calc
    _ = ∑ e, ∑ c, w c * (if e ∈ I c then -(x e) ^ 2 else
        -2 * x e * OverlapDrift.loss I w c e + (OverlapDrift.loss I w c e) ^ 2) := by
      dsimp only [fixedChange]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [he]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        ← Finset.mul_sum]
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, hloss, hW]

theorem load_error_product (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (k : ℝ) (e : E) :
    WeightedGreedy.load I μ J h e * WeightedGreedy.error I μ J h k e =
      (WeightedGreedy.error I μ J h k e) ^ 2 + k * WeightedGreedy.error I μ J h k e := by
  by_cases he : e ∈ WeightedGreedy.remaining I J h
  · simp only [WeightedGreedy.error, he, ite_true]
    ring
  · rw [WeightedGreedy.load_zero_outside I μ J h e he]
    simp [WeightedGreedy.error, he, WeightedGreedy.load_zero_outside I μ J h e he]

theorem load_square_error (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (k : ℝ) (e : E) :
    (WeightedGreedy.load I μ J h e) ^ 2 * WeightedGreedy.error I μ J h k e =
      WeightedGreedy.load I μ J h e * (WeightedGreedy.error I μ J h k e) ^ 2 +
        k * (WeightedGreedy.load I μ J h e * WeightedGreedy.error I μ J h k e) := by
  by_cases he : e ∈ WeightedGreedy.remaining I J h
  · simp only [WeightedGreedy.error, he, ite_true]
    ring
  · simp [WeightedGreedy.load_zero_outside I μ J h e he]

theorem block_load_error (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (r : ℕ) (hsize : ∀ b, (I b).card = r) (k : ℝ) :
    (∑ b, WeightedGreedy.availableWeight I μ J h b *
      (∑ e ∈ I b, WeightedGreedy.error I μ J h k e) *
        (∑ e ∈ I b, WeightedGreedy.load I μ J h e)) =
      (∑ b, WeightedGreedy.availableWeight I μ J h b *
        (∑ e ∈ I b, WeightedGreedy.error I μ J h k e) ^ 2) +
        (r : ℝ) * k * ∑ e, WeightedGreedy.load I μ J h e * WeightedGreedy.error I μ J h k e := by
  have hb (b : B) : WeightedGreedy.availableWeight I μ J h b *
      (∑ e ∈ I b, WeightedGreedy.error I μ J h k e) *
        (∑ e ∈ I b, WeightedGreedy.load I μ J h e) =
      WeightedGreedy.availableWeight I μ J h b * (∑ e ∈ I b, WeightedGreedy.error I μ J h k e) ^ 2 +
        (r : ℝ) * k * (WeightedGreedy.availableWeight I μ J h b *
          ∑ e ∈ I b, WeightedGreedy.error I μ J h k e) := by
    by_cases hw : WeightedGreedy.availableWeight I μ J h b = 0
    · simp [hw]
    have hs : I b ⊆ WeightedGreedy.remaining I J h := by
      by_contra hn
      simp [WeightedGreedy.availableWeight, hn] at hw
    have he (e : E) (he : e ∈ I b) : WeightedGreedy.load I μ J h e =
        WeightedGreedy.error I μ J h k e + k := by
      simp only [WeightedGreedy.error, hs he, ite_true]
      ring
    have hl : (∑ e ∈ I b, WeightedGreedy.load I μ J h e) =
        (∑ e ∈ I b, WeightedGreedy.error I μ J h k e) + (r : ℝ) * k := by
      rw [Finset.sum_congr rfl he, Finset.sum_add_distrib]
      simp [hsize]
    rw [hl]
    ring
  simp_rw [hb]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, WeightedEnergy.incidence_sum]
  rfl

/-- The exact fixed-profile part of the physical mean energy drift.
No pointwise d_e=O(k) hypothesis is used. -/
theorem physical_fixed_drift (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (r : ℕ) (hsize : ∀ b, (I b).card = r) (k : ℝ) :
    let w := WeightedGreedy.availableWeight I μ J h
    let x := WeightedGreedy.error I μ J h k
    (∑ c, w c * (WeightedGreedy.energy I μ J (some c :: h) k - WeightedGreedy.energy I μ J h k)) =
      (∑ e, WeightedGreedy.load I μ J h e * (x e) ^ 2) -
        2 * (∑ b, w b * (∑ e ∈ I b, x e) ^ 2) -
        2 * ((r : ℝ) - 1) * k * (∑ e, WeightedGreedy.load I μ J h e * x e) +
        2 * (∑ e, OverlapDrift.correction I w e * x e) + ∑ c, w c * squareLoss I w c := by
  dsimp only
  have hfixed (c : B) :
      WeightedGreedy.energy I μ J (some c :: h) k - WeightedGreedy.energy I μ J h k =
      fixedChange I (WeightedGreedy.availableWeight I μ J h) (WeightedGreedy.error I μ J h k) c := by
    have he := WeightedGreedy.energy_after I μ J h c k 0
    simpa only [sub_zero, mul_zero, zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero,
      ite_self, ← OverlapDrift.loss_eq_history, fixedChange] using he
  simp_rw [hfixed]
  rw [mean_fixed_change]
  have hblock := block_load_error I μ J h r hsize k
  simp only [WeightedGreedy.load] at hblock
  rw [hblock]
  have hd : (∑ e, (WeightedGreedy.load I μ J h e) ^ 2 * WeightedGreedy.error I μ J h k e) =
      (∑ e, WeightedGreedy.load I μ J h e * (WeightedGreedy.error I μ J h k e) ^ 2) +
        k * ∑ e, WeightedGreedy.load I μ J h e * WeightedGreedy.error I μ J h k e := by
    simp_rw [load_square_error]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  change -(∑ e, WeightedGreedy.load I μ J h e * (WeightedGreedy.error I μ J h k e) ^ 2) -
    2 * (((∑ b, WeightedGreedy.availableWeight I μ J h b * (∑ e ∈ I b, WeightedGreedy.error I μ J h k e) ^ 2) +
      (r : ℝ) * k * ∑ e, WeightedGreedy.load I μ J h e * WeightedGreedy.error I μ J h k e) -
      (∑ e, OverlapDrift.correction I (WeightedGreedy.availableWeight I μ J h) e * WeightedGreedy.error I μ J h k e) -
      (∑ e, (WeightedGreedy.load I μ J h e) ^ 2 * WeightedGreedy.error I μ J h k e)) + _ = _
  rw [hd]
  ring

end KqR75.MeanEnergy

#print axioms KqR75.MeanEnergy.mean_fixed_change
#print axioms KqR75.MeanEnergy.physical_fixed_drift
