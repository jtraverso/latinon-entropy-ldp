module
public import CodegreeLoss

@[expose] public section
noncomputable section
namespace KqR75.TypeWeights

open Finset
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

def marked (S : Finset B) (w : B → ℝ) (b : B) : ℝ := if b ∈ S then w b else 0

def removed (I : B → Finset E) (w : B → ℝ) (c : B) : ℝ :=
  ∑ b, if Disjoint (I b) (I c) then 0 else w b

theorem marked_bounds (S : Finset B) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) (b : B) :
    0 ≤ marked S w b ∧ marked S w b ≤ w b := by
  dsimp only [marked]
  split_ifs
  · exact ⟨hw b, le_rfl⟩
  · exact ⟨le_rfl, hw b⟩

theorem removed_nonneg (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) (c : B) :
    0 ≤ removed I w c := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs <;> first | exact le_rfl | exact hw b

theorem removed_mono (I : B → Finset E) (v w : B → ℝ) (hvw : ∀ b, v b ≤ w b) (c : B) :
    removed I v c ≤ removed I w c := by
  apply Finset.sum_le_sum
  intro b _
  split_ifs <;> first | exact le_rfl | exact hvw b

theorem removed_le (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b)
    (r : ℕ) (hsize : ∀ b, (I b).card = r)
    (hload : ∀ e, WeightedEnergy.load I w e ≤ 1) (c : B) : removed I w c ≤ r := by
  have hi := OverlapDrift.overcount_identity I w c
  have hn := CodegreeLoss.overcount_nonneg I w hw c
  have hd : (∑ e ∈ I c, WeightedEnergy.load I w e) ≤ (r : ℝ) := by
    calc
      _ ≤ ∑ _e ∈ I c, (1 : ℝ) := Finset.sum_le_sum (fun e _ => hload e)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hsize, mul_one]
  have he : (∑ b, if Disjoint (I c) (I b) then 0 else w b) = removed I w c := by
    simp only [removed, disjoint_comm]
  rw [he] at hi
  linarith only [hi, hn, hd]

/-- The first moment of a type loss, with its multiple-intersection
correction retained exactly. No independence approximation is used. -/
theorem mean_removed (I : B → Finset E) (w v : B → ℝ) :
    (∑ c, w c * removed I v c) =
      (∑ e, WeightedEnergy.load I v e * WeightedEnergy.load I w e) -
        ∑ b, v b * OverlapDrift.overcount I w b := by
  have hb (b : B) : (∑ c, w c * (if Disjoint (I b) (I c) then 0 else v b)) =
      v b * ((∑ e ∈ I b, WeightedEnergy.load I w e) - OverlapDrift.overcount I w b) := by
    have hi := OverlapDrift.overcount_identity I w b
    have hm : (∑ e ∈ I b, WeightedEnergy.load I w e) - OverlapDrift.overcount I w b =
        ∑ c, if Disjoint (I b) (I c) then 0 else w c := by linarith only [hi]
    rw [hm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> ring
  calc
    _ = ∑ c, ∑ b, w c * (if Disjoint (I b) (I c) then 0 else v b) := by
      simp only [removed, Finset.mul_sum]
    _ = ∑ b, ∑ c, w c * (if Disjoint (I b) (I c) then 0 else v b) := Finset.sum_comm
    _ = ∑ b, v b * ((∑ e ∈ I b, WeightedEnergy.load I w e) - OverlapDrift.overcount I w b) :=
      Finset.sum_congr rfl (fun b _ => hb b)
    _ = _ := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [WeightedEnergy.incidence_sum]

theorem available_marked (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (S : Finset B) :
    WeightedGreedy.availableWeight I (marked S μ) J h = marked S (WeightedGreedy.availableWeight I μ J h) := by
  funext b
  dsimp only [marked, WeightedGreedy.availableWeight]
  split_ifs <;> rfl

theorem total_after (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (c : B) :
    WeightedGreedy.totalWeight I μ J (some c :: h) = WeightedGreedy.totalWeight I μ J h -
      removed I (WeightedGreedy.availableWeight I μ J h) c := by
  dsimp only [WeightedGreedy.totalWeight, removed]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [WeightedGreedy.availableWeight_after]
  split_ifs <;> ring

theorem total_marked (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (S : Finset B) :
    WeightedGreedy.totalWeight I (marked S μ) J h =
      ∑ b, marked S (WeightedGreedy.availableWeight I μ J h) b := by
  simp only [WeightedGreedy.totalWeight, available_marked]

def proportion (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (S : Finset B) (h : List (Option B)) : ℝ :=
  WeightedGreedy.totalWeight I (marked S μ) J h / WeightedGreedy.totalWeight I μ J h

theorem proportion_none (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (S : Finset B) (h : List (Option B)) :
    proportion I μ J S (none :: h) = proportion I μ J S h := rfl

end KqR75.TypeWeights

#print axioms KqR75.TypeWeights.mean_removed
#print axioms KqR75.TypeWeights.removed_le
#print axioms KqR75.TypeWeights.total_after
