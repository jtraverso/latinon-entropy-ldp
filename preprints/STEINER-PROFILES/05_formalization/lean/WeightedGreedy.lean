module
public import FiniteProcess
public import WeightedEnergy
public import Mathlib.Data.Fintype.Option
public import Mathlib.Algebra.BigOperators.Option

@[expose] public section
noncomputable section
namespace KqR75.WeightedGreedy

open Finset LatinonEntropy

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- Outcomes are real blocks, or the absorbing stopped outcome `none`. -/
def remaining (I : B → Finset E) (J : Finset E) : List (Option B) → Finset E
  | [] => J
  | none :: h => remaining I J h
  | some b :: h => remaining I J h \ I b

def selectedCount : List (Option B) → ℕ
  | [] => 0
  | none :: h => selectedCount h
  | some _ :: h => selectedCount h + 1

def valid (I : B → Finset E) (J : Finset E) : List (Option B) → Prop
  | [] => True
  | none :: h => valid I J h
  | some b :: h => valid I J h ∧ I b ⊆ remaining I J h

def availableWeight (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (b : B) : ℝ :=
  if I b ⊆ remaining I J h then μ b else 0

def totalWeight (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) : ℝ := ∑ b, availableWeight I μ J h b

def live (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (guard : List (Option B) → Prop) (h : List (Option B)) : Prop :=
  none ∉ h ∧ guard h ∧ 0 < totalWeight I μ J h

theorem availableWeight_nonneg (I : B → Finset E) (μ : B → ℝ)
    (hμ : ∀ b, 0 ≤ μ b) (J : Finset E) (h : List (Option B)) (b : B) :
    0 ≤ availableWeight I μ J h b := by
  dsimp only [availableWeight]
  split_ifs
  · exact hμ b
  · exact le_rfl

/-- The physical weighted greedy kernel, stopped by a predictable guard.
Its normalization and support are proved from finite sums. -/
def kernel (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop) : FiniteKernel (Option B) := by
  classical
  exact {
    transition := fun h a => if live I μ J guard h then
      match a with
      | none => 0
      | some b => availableWeight I μ J h b / totalWeight I μ J h
      else if a = none then 1 else 0
    nonneg := by
      intro h a
      by_cases hl : live I μ J guard h
      · simp only [hl, ite_true]
        cases a with
        | none => exact le_rfl
        | some b => exact div_nonneg (availableWeight_nonneg I μ hμ J h b) hl.2.2.le
      · simp only [hl, ite_false]
        split_ifs <;> norm_num
    total := by
      intro h
      by_cases hl : live I μ J guard h
      · simp only [hl, ite_true]
        rw [univ_option, Finset.sum_insertNone]
        simp only [zero_add]
        rw [← Finset.sum_div]
        exact div_self hl.2.2.ne'
      · simp [hl] }

theorem stopped_transition (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop) (h : List (Option B))
    (hnone : none ∈ h) (b : B) : (kernel I μ hμ J guard).transition h (some b) = 0 := by
  have hl : ¬ live I μ J guard h := fun h => h.1 hnone
  simp [kernel, hl]

theorem positive_some_available (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop) (h : List (Option B)) (b : B)
    (hp : 0 < (kernel I μ hμ J guard).transition h (some b)) :
    I b ⊆ remaining I J h := by
  by_cases hl : live I μ J guard h
  · by_contra hn
    simp [kernel, hl, availableWeight, hn] at hp
  · simp [kernel, hl] at hp

/-- Positive-probability histories select only edge-disjoint physical blocks. -/
theorem positive_history_valid (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop) (h : List (Option B))
    (hp : 0 < historyWeight (kernel I μ hμ J guard) h) : valid I J h := by
  revert hp
  induction h with
  | nil => intro _; trivial
  | cons a h ih =>
    intro hp
    let K := kernel I μ hμ J guard
    change 0 < historyWeight K h * K.transition h a at hp
    have hh : 0 < historyWeight K h := by
      by_contra hn
      have hz : historyWeight K h = 0 :=
        le_antisymm (le_of_not_gt hn) (historyWeight_nonneg K h)
      simp only [hz, zero_mul, lt_self_iff_false] at hp
    have ha : 0 < K.transition h a := by
      by_contra hn
      have hz : K.transition h a = 0 :=
        le_antisymm (le_of_not_gt hn) (K.nonneg h a)
      simp only [hz, mul_zero, lt_self_iff_false] at hp
    cases a with
    | none => exact ih hh
    | some b => exact ⟨ih hh, positive_some_available I μ hμ J guard h b ha⟩

theorem resource_count (I : B → Finset E) (J : Finset E) (r : ℕ)
    (hsize : ∀ b, (I b).card = r) (h : List (Option B)) (hv : valid I J h) :
    (remaining I J h).card + r * selectedCount h = J.card := by
  revert hv
  induction h with
  | nil => intro _; simp [remaining, selectedCount]
  | cons a h ih =>
    intro hv
    cases a with
    | none => exact ih hv
    | some b =>
      have hc := Finset.card_sdiff_add_card_eq_card hv.2
      rw [hsize b] at hc
      have hi := ih hv.1
      simp only [remaining, selectedCount]
      nlinarith only [hc, hi]

def load (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (e : E) : ℝ :=
  WeightedEnergy.load I (availableWeight I μ J h) e

def error (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (k : ℝ) (e : E) : ℝ :=
  load I μ J h e - if e ∈ remaining I J h then k else 0

theorem load_nonneg (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (h : List (Option B)) (e : E) : 0 ≤ load I μ J h e := by
  apply Finset.sum_nonneg
  intro b _
  split_ifs
  · exact availableWeight_nonneg I μ hμ J h b
  · exact le_rfl

theorem load_le_initial (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (h : List (Option B)) (e : E) :
    load I μ J h e ≤ WeightedEnergy.load I μ e := by
  apply Finset.sum_le_sum
  intro b _
  dsimp only [availableWeight]
  split_ifs <;> first | exact le_rfl | exact hμ b

theorem resource_selection_prob (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop) (h : List (Option B))
    (hl : live I μ J guard h) (e : E) :
    (∑ a : Option B, (kernel I μ hμ J guard).transition h a *
      (match a with | none => 0 | some b => if e ∈ I b then 1 else 0)) =
      load I μ J h e / totalWeight I μ J h := by
  simp only [kernel, hl, ite_true]
  rw [univ_option, Finset.sum_insertNone]
  simp only [zero_mul, zero_add]
  have hterm (b : B) : availableWeight I μ J h b / totalWeight I μ J h *
      (if e ∈ I b then 1 else 0) =
      (if e ∈ I b then availableWeight I μ J h b else 0) / totalWeight I μ J h := by
    split_ifs <;> simp
  simp_rw [hterm]
  rw [← Finset.sum_div]
  rfl

theorem load_zero_outside (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (e : E) (he : e ∉ remaining I J h) :
    load I μ J h e = 0 := by
  apply Finset.sum_eq_zero
  intro b _
  by_cases heb : e ∈ I b
  · have hn : ¬ I b ⊆ remaining I J h := fun hs => he (hs heb)
    simp [availableWeight, heb, hn]
  · simp [heb]

theorem availableWeight_after (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (C b : B) :
    availableWeight I μ J (some C :: h) b =
      if Disjoint (I b) (I C) then availableWeight I μ J h b else 0 := by
  have hs : I b ⊆ remaining I J h \ I C ↔
      I b ⊆ remaining I J h ∧ Disjoint (I b) (I C) := by
    constructor
    · intro hsub
      refine ⟨fun e he => (Finset.mem_sdiff.mp (hsub he)).1, ?_⟩
      exact Finset.disjoint_left.mpr (fun e heb heC => (Finset.mem_sdiff.mp (hsub heb)).2 heC)
    · rintro ⟨hsub, hd⟩ e he
      exact Finset.mem_sdiff.mpr ⟨hsub he, fun heC => Finset.disjoint_left.mp hd he heC⟩
  by_cases hd : Disjoint (I b) (I C)
  · by_cases hsub : I b ⊆ remaining I J h
    · have hn : I b ⊆ remaining I J (some C :: h) := hs.mpr ⟨hsub, hd⟩
      simp only [availableWeight, hn, hsub, hd, ite_true]
    · have hn : ¬ I b ⊆ remaining I J (some C :: h) := fun hn => hsub (hs.mp hn).1
      simp only [availableWeight, hn, hsub, hd, ite_false, ite_true]
  · have hn : ¬ I b ⊆ remaining I J (some C :: h) := fun hn => hd (hs.mp hn).2
    simp only [availableWeight, hn, hd, ite_false]

def loss (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (C : B) (e : E) : ℝ :=
  ∑ b, if e ∈ I b ∧ ¬ Disjoint (I b) (I C) then availableWeight I μ J h b else 0

/-- Exact physical update, before any approximation or drift estimate. -/
theorem load_after (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (C : B) (e : E) :
    load I μ J (some C :: h) e = load I μ J h e - loss I μ J h C e := by
  change (∑ b, if e ∈ I b then availableWeight I μ J (some C :: h) b else 0) =
    (∑ b, if e ∈ I b then availableWeight I μ J h b else 0) -
      ∑ b, if e ∈ I b ∧ ¬ Disjoint (I b) (I C) then availableWeight I μ J h b else 0
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  rw [availableWeight_after]
  by_cases he : e ∈ I b <;> by_cases hd : Disjoint (I b) (I C) <;> simp [he, hd]

theorem loss_on_selected (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (C : B) (e : E) (he : e ∈ I C) :
    loss I μ J h C e = load I μ J h e := by
  apply Finset.sum_congr rfl
  intro b _
  by_cases heb : e ∈ I b
  · have hd : ¬ Disjoint (I b) (I C) := fun hd => Finset.disjoint_left.mp hd heb he
    simp only [heb, hd, not_false_eq_true, and_self, ite_true]
  · simp only [heb, false_and, ite_false]

theorem error_after (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (C : B) (k η : ℝ) (e : E) :
    error I μ J (some C :: h) (k - η) e =
      if e ∈ I C then 0 else error I μ J h k e - loss I μ J h C e +
        if e ∈ remaining I J h then η else 0 := by
  by_cases he : e ∈ I C
  · have hl := loss_on_selected I μ J h C e he
    simp [error, load_after, remaining, he, hl]
  · simp only [error, load_after, remaining, Finset.mem_sdiff, he, not_false_eq_true,
      and_true, ite_false]
    by_cases hr : e ∈ remaining I J h <;> simp only [hr, ite_true, ite_false] <;> ring

def energy (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (k : ℝ) : ℝ := ∑ e, (error I μ J h k e) ^ 2

/-- Time is the number of selected blocks, so the whole functional freezes
after the absorbing outcome, including the value of a crossing step. -/
def stoppedEnergy (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (k factor : ℕ → ℝ) (h : List (Option B)) : ℝ :=
  factor (selectedCount h) * energy I μ J h (k (selectedCount h))

theorem stoppedEnergy_none (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (k factor : ℕ → ℝ) (h : List (Option B)) :
    stoppedEnergy I μ J k factor (none :: h) = stoppedEnergy I μ J k factor h := rfl

theorem stoppedEnergy_nonneg (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (k factor : ℕ → ℝ) (hf : ∀ i, 0 ≤ factor i) (h : List (Option B)) :
    0 ≤ stoppedEnergy I μ J k factor h :=
  mul_nonneg (hf _) (Finset.sum_nonneg (fun e _ => sq_nonneg _))

theorem stoppedEnergy_step (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop) (k factor : ℕ → ℝ)
    (h : List (Option B)) (hl : ¬ live I μ J guard h) :
    (∑ a, (kernel I μ hμ J guard).transition h a *
      stoppedEnergy I μ J k factor (a :: h)) = stoppedEnergy I μ J k factor h := by
  simp only [kernel, hl, ite_false, ite_mul, one_mul, zero_mul]
  simpa using stoppedEnergy_none I μ J k factor h

theorem stoppedEnergy_drift_bound (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (guard : List (Option B) → Prop) (k factor b : ℕ → ℝ)
    (hb : ∀ i, 0 ≤ b i)
    (hactive : ∀ h, live I μ J guard h →
      (∑ a, (kernel I μ hμ J guard).transition h a * stoppedEnergy I μ J k factor (a :: h)) ≤
        stoppedEnergy I μ J k factor h + b h.length) (T : ℕ) :
    historyExpectation (kernel I μ hμ J guard) T (stoppedEnergy I μ J k factor) ≤
      stoppedEnergy I μ J k factor [] + ∑ s ∈ range T, b s := by
  apply FiniteProcess.drift_bound
  intro h
  by_cases hl : live I μ J guard h
  · exact hactive h hl
  · rw [stoppedEnergy_step I μ hμ J guard k factor h hl]
    linarith only [hb h.length]

/-- Exact one-step energy expansion for the physical block deletion.
The geometric and conditional-mean bounds are separate later obligations. -/
theorem energy_after (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (h : List (Option B)) (C : B) (k η : ℝ) :
    energy I μ J (some C :: h) (k - η) - energy I μ J h k =
      ∑ e, if e ∈ I C then -(error I μ J h k e) ^ 2 else
        -2 * error I μ J h k e * loss I μ J h C e + (loss I μ J h C e) ^ 2 +
          if e ∈ remaining I J h then
            2 * η * (error I μ J h k e - loss I μ J h C e) + η ^ 2 else 0 := by
  dsimp only [energy]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [error_after]
  by_cases he : e ∈ I C
  · simp only [he, ite_true]
    ring
  · simp only [he, ite_false]
    by_cases hr : e ∈ remaining I J h <;> simp only [hr, ite_true, ite_false] <;> ring

theorem sum_load (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (r : ℕ) (hsize : ∀ b, (I b).card = r) (h : List (Option B)) :
    (∑ e, load I μ J h e) = (r : ℝ) * totalWeight I μ J h := by
  have hs := WeightedEnergy.incidence_sum I (availableWeight I μ J h) (fun _ => (1 : ℝ))
  have he : (∑ e, load I μ J h e) = (∑ b, availableWeight I μ J h b) * (r : ℝ) := by
    simpa only [load, Finset.sum_const, nsmul_eq_mul, hsize, mul_one,
      ← Finset.sum_mul] using hs.symm
  calc
    _ = _ := he
    _ = _ := by dsimp only [totalWeight]; ring

/-- The signed energy inequality is instantiated at every actual greedy history,
including histories containing resources of zero available load. -/
theorem signed_energy (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ b, 0 ≤ μ b)
    (J : Finset E) (r : ℕ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (h : List (Option B)) (k : ℝ) (hk : 0 < k) :
    (∑ e, load I μ J h e * (error I μ J h k e) ^ 2) -
      2 * (∑ b, availableWeight I μ J h b * (∑ e ∈ I b, error I μ J h k e) ^ 2) ≤
      (2 * (r : ℝ) - 1) * k * ∑ e, (error I μ J h k e) ^ 2 := by
  apply WeightedEnergy.signed_quadratic I (availableWeight I μ J h)
    (availableWeight_nonneg I μ hμ J h) r hr hsize k hk
  intro e he
  have hm : e ∈ remaining I J h := by
    by_contra hn
    have hz := load_zero_outside I μ J h e hn
    change 0 < load I μ J h e at he
    rw [hz] at he
    exact (lt_irrefl 0) he
  simp only [error, hm, ite_true, load]

end KqR75.WeightedGreedy

#print axioms KqR75.WeightedGreedy.kernel
#print axioms KqR75.WeightedGreedy.positive_history_valid
#print axioms KqR75.WeightedGreedy.resource_count
#print axioms KqR75.WeightedGreedy.sum_load
#print axioms KqR75.WeightedGreedy.resource_selection_prob
#print axioms KqR75.WeightedGreedy.load_after
#print axioms KqR75.WeightedGreedy.error_after
#print axioms KqR75.WeightedGreedy.energy_after
#print axioms KqR75.WeightedGreedy.stoppedEnergy_drift_bound
#print axioms KqR75.WeightedGreedy.signed_energy
