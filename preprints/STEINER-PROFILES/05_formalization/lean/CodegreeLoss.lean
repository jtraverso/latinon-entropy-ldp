module
public import MeanEnergy

@[expose] public section
noncomputable section
namespace KqR75.CodegreeLoss

open Finset

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

def codegree (I : B → Finset E) (w : B → ℝ) (e f : E) : ℝ :=
  WeightedEnergy.load I (fun b => if e ∈ I b then w b else 0) f

theorem codegree_diag (I : B → Finset E) (w : B → ℝ) (e : E) :
    codegree I w e e = WeightedEnergy.load I w e := by
  apply Finset.sum_congr rfl
  intro b _
  change (if e ∈ I b then (if e ∈ I b then w b else 0) else 0) = _
  by_cases he : e ∈ I b <;> simp [he]

theorem quadratic_intersections (I : B → Finset E) (w : B → ℝ) (b : B) :
    (∑ e ∈ I b, ∑ f ∈ I b, codegree I w e f) =
      ∑ c, w c * ((I b ∩ I c).card : ℝ) ^ 2 := by
  have hi (e : E) : (∑ f ∈ I b, codegree I w e f) =
      ∑ c, (if e ∈ I c then w c else 0) * ((I b ∩ I c).card : ℝ) :=
    OverlapDrift.intersection_load I (fun c => if e ∈ I c then w c else 0) b
  simp_rw [hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_mul]
  have hc : (∑ e ∈ I b, if e ∈ I c then w c else 0) = ((I b ∩ I c).card : ℝ) * w c := by
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.sum_const, nsmul_eq_mul]
  rw [hc]
  ring

theorem off_diagonal_intersections (I : B → Finset E) (w : B → ℝ) (b : B) :
    (∑ e ∈ I b, ∑ f ∈ I b, if e = f then 0 else codegree I w e f) =
      (∑ c, w c * ((I b ∩ I c).card : ℝ) ^ 2) -
        ∑ c, w c * ((I b ∩ I c).card : ℝ) := by
  have hr (e : E) (he : e ∈ I b) :
      (∑ f ∈ I b, if e = f then 0 else codegree I w e f) =
        (∑ f ∈ I b, codegree I w e f) - WeightedEnergy.load I w e := by
    have hf (f : E) : (if e = f then 0 else codegree I w e f) =
        codegree I w e f - (if e = f then codegree I w e e else 0) := by
      by_cases hef : e = f
      · subst f; simp
      · simp [hef]
    simp_rw [hf]
    rw [Finset.sum_sub_distrib]
    have hsel : (∑ f ∈ I b, if e = f then WeightedEnergy.load I w e else 0) =
        WeightedEnergy.load I w e := by
      have hh : (∑ f ∈ I b, if e = f then WeightedEnergy.load I w e else 0) =
          (if e = e then WeightedEnergy.load I w e else 0) := by
        apply Finset.sum_eq_single e
        · intro f _ hfe
          simp [Ne.symm hfe]
        · intro hn
          exact (hn he).elim
      simpa only [ite_true] using hh
    rw [codegree_diag, hsel]
  rw [Finset.sum_congr rfl hr, Finset.sum_sub_distrib,
    quadratic_intersections, OverlapDrift.intersection_load]

/-- Multiple intersections are controlled by the same off-diagonal codegree
as the quadratic loss. A coarse r² constant suffices for the uniform drift. -/
theorem overcount_le (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b)
    (r : ℕ) (hsize : ∀ b, (I b).card = r) (β : ℝ) (hβ : 0 ≤ β)
    (hcodeg : ∀ e f, e ≠ f → codegree I w e f ≤ β) (b : B) :
    OverlapDrift.overcount I w b ≤ (r : ℝ) ^ 2 * β := by
  have hex (c : B) : OverlapDrift.excess I b c ≤
      ((I b ∩ I c).card : ℝ) ^ 2 - ((I b ∩ I c).card : ℝ) := by
    by_cases hd : Disjoint (I b) (I c)
    · have hi := Finset.disjoint_iff_inter_eq_empty.mp hd
      simp [OverlapDrift.excess, hd, hi]
    · simp only [OverlapDrift.excess, hd, ite_false]
      nlinarith only [sq_nonneg (((I b ∩ I c).card : ℝ) - 1)]
  calc
    _ ≤ ∑ c, w c * (((I b ∩ I c).card : ℝ) ^ 2 - ((I b ∩ I c).card : ℝ)) :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hex c) (hw c))
    _ = ∑ e ∈ I b, ∑ f ∈ I b, if e = f then 0 else codegree I w e f := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      exact (off_diagonal_intersections I w b).symm
    _ ≤ ∑ _e ∈ I b, ∑ _f ∈ I b, β := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro f _
      by_cases hef : e = f
      · simpa only [hef, ite_true] using hβ
      · simpa only [hef, ite_false] using hcodeg e f hef
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hsize]; ring

theorem overcount_nonneg (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) (c : B) :
    0 ≤ OverlapDrift.overcount I w c :=
  Finset.sum_nonneg (fun b _ => mul_nonneg (hw b) (OverlapDrift.excess_nonneg I c b))

theorem loss_nonneg (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) (c : B) (e : E) :
    0 ≤ OverlapDrift.loss I w c e := by
  apply Finset.sum_nonneg
  intro b _
  change 0 ≤ (if e ∈ I b then (if Disjoint (I b) (I c) then 0 else w b) else 0)
  split_ifs <;> first | exact hw b | norm_num

theorem loss_le_codegrees (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b)
    (c : B) (e : E) : OverlapDrift.loss I w c e ≤ ∑ f ∈ I c, codegree I w e f := by
  let v : B → ℝ := fun b => if e ∈ I b then w b else 0
  have hv (b : B) : 0 ≤ v b := by dsimp [v]; split_ifs; exact hw b; exact le_rfl
  have hi := OverlapDrift.overcount_identity I v c
  have hn := overcount_nonneg I v hv c
  have he : (∑ b, if Disjoint (I c) (I b) then 0 else v b) = OverlapDrift.loss I w c e := by
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [v]
    by_cases hm : e ∈ I b <;> by_cases hd : Disjoint (I c) (I b) <;>
      simp only [hm, hd, disjoint_comm, ite_true, ite_false]
  rw [he] at hi
  change OverlapDrift.loss I w c e ≤ ∑ f ∈ I c, WeightedEnergy.load I v f
  linarith only [hi, hn]

theorem loss_le_card_mul (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b)
    (β : ℝ) (hcodeg : ∀ e f, e ≠ f → codegree I w e f ≤ β) (c : B) (e : E)
    (he : e ∉ I c) : OverlapDrift.loss I w c e ≤ ((I c).card : ℝ) * β := by
  calc
    _ ≤ ∑ f ∈ I c, codegree I w e f := loss_le_codegrees I w hw c e
    _ ≤ ∑ _f ∈ I c, β := Finset.sum_le_sum (fun f hf => hcodeg e f
      (fun hef => he (by simpa only [hef] using hf)))
    _ = _ := by simp

theorem total_loss_le (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b)
    (r : ℕ) (hsize : ∀ b, (I b).card = r)
    (hload : ∀ e, WeightedEnergy.load I w e ≤ 1) (c : B) :
    (∑ e, OverlapDrift.loss I w c e) ≤ (r : ℝ) ^ 2 := by
  let v : B → ℝ := fun b => if Disjoint (I b) (I c) then 0 else w b
  have hmass : (∑ b, v b) ≤ (r : ℝ) := by
    have hi := OverlapDrift.overcount_identity I w c
    have hn := overcount_nonneg I w hw c
    have hd : (∑ e ∈ I c, WeightedEnergy.load I w e) ≤ (r : ℝ) := by
      calc
        _ ≤ ∑ _e ∈ I c, (1 : ℝ) := Finset.sum_le_sum (fun e _ => hload e)
        _ = _ := by simp [hsize]
    have he : (∑ b, if Disjoint (I c) (I b) then 0 else w b) = ∑ b, v b := by
      simp only [v, disjoint_comm]
    rw [he] at hi
    linarith only [hi, hn, hd]
  have hi := WeightedEnergy.incidence_sum I v (fun _ => (1 : ℝ))
  have he : (∑ e, OverlapDrift.loss I w c e) = (∑ b, v b) * (r : ℝ) := by
    simpa only [OverlapDrift.loss, v, Finset.sum_const, nsmul_eq_mul, hsize, mul_one,
      ← Finset.sum_mul] using hi.symm
  rw [he]
  have hs := mul_le_mul_of_nonneg_right hmass (show (0 : ℝ) ≤ r by positivity)
  nlinarith only [hs]

/-- All quadratic losses are O(codegree), without separate adjacent/disjoint
resource counts. The estimate is uniform over every available state. -/
theorem square_loss_le (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b)
    (r : ℕ) (hsize : ∀ b, (I b).card = r) (β : ℝ) (hβ : 0 ≤ β)
    (hcodeg : ∀ e f, e ≠ f → codegree I w e f ≤ β)
    (hload : ∀ e, WeightedEnergy.load I w e ≤ 1) (c : B) :
    MeanEnergy.squareLoss I w c ≤ (r : ℝ) ^ 3 * β := by
  have he (e : E) : (if e ∈ I c then 0 else (OverlapDrift.loss I w c e) ^ 2) ≤
      ((r : ℝ) * β) * OverlapDrift.loss I w c e := by
    have hl := loss_nonneg I w hw c e
    by_cases hm : e ∈ I c
    · simp only [hm, ite_true]
      positivity
    · have hx := loss_le_card_mul I w hw β hcodeg c e hm
      rw [hsize] at hx
      simp only [hm, ite_false]
      nlinarith only [mul_nonneg (sub_nonneg.mpr hx) hl]
  calc
    _ ≤ ∑ e, ((r : ℝ) * β) * OverlapDrift.loss I w c e := Finset.sum_le_sum (fun e _ => he e)
    _ = ((r : ℝ) * β) * ∑ e, OverlapDrift.loss I w c e := (Finset.mul_sum _ _ _).symm
    _ ≤ ((r : ℝ) * β) * (r : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (total_loss_le I w hw r hsize hload c) (by positivity)
    _ = _ := by ring

end KqR75.CodegreeLoss

#print axioms KqR75.CodegreeLoss.loss_le_codegrees
#print axioms KqR75.CodegreeLoss.square_loss_le
#print axioms KqR75.CodegreeLoss.overcount_le
