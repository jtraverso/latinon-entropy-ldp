module
public import TypeCounts
public import TypeTails
public import GreedyHorizon
public import PrefixTypeTests

@[expose] public section
noncomputable section
namespace KqR75.TypeCountHorizon

open Finset LatinonEntropy

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- If the prefix proportions stay within η of their starting value,
the predictable count differs from the initial proportion times the
length by at most length · η. -/
theorem compensator_error (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ w, 0 ≤ μ w)
    (J : Finset E) (S : Finset B) (guard : List (Option B) → Prop) (η : ℝ)
    (h : List (Option B))
    (hlive : ∀ j < h.length, WeightedGreedy.live I μ J guard (h.drop (h.length - j)))
    (hprop : ∀ j < h.length,
      |TypeWeights.proportion I μ J S (h.drop (h.length - j)) -
        TypeWeights.proportion I μ J S []| ≤ η) :
    |pathSum (fun g _ => ∑ w, (WeightedGreedy.kernel I μ hμ J guard).transition g w *
        TypeCounts.indicator S w) h -
      (h.length : ℝ) * TypeWeights.proportion I μ J S []| ≤ h.length * η := by
  let f := fun (g : List (Option B)) (_ : Option B) =>
    ∑ w, (WeightedGreedy.kernel I μ hμ J guard).transition g w * TypeCounts.indicator S w
  let p := TypeWeights.proportion I μ J S []
  change |pathSum f h - (h.length : ℝ) * p| ≤ h.length * η
  induction h with
  | nil => simp [pathSum]
  | cons w g ih =>
    have hh (j : ℕ) (hj : j ≤ g.length) :
        (w :: g).drop ((w :: g).length - j) = g.drop (g.length - j) := by
      rw [List.length_cons, show g.length + 1 - j = (g.length - j) + 1 by omega, List.drop_succ_cons]
    have hgl (j : ℕ) (hj : j < g.length) :=
      hlive j (by simp only [List.length_cons]; omega)
    have hgp (j : ℕ) (hj : j < g.length) :=
      hprop j (by simp only [List.length_cons]; omega)
    have htail := ih (fun j hj => by simpa only [hh j hj.le] using hgl j hj)
      (fun j hj => by simpa only [hh j hj.le] using hgp j hj)
    have hl : WeightedGreedy.live I μ J guard g := by
      simpa only [hh g.length le_rfl, Nat.sub_self, List.drop_zero] using
        hlive g.length (by simp only [List.length_cons]; omega)
    have hμ' : |f g w - p| ≤ η := by
      rw [show f g w = TypeWeights.proportion I μ J S g by
        exact TypeCounts.live_mean I μ hμ J S guard g hl]
      simpa only [hh g.length le_rfl, Nat.sub_self, List.drop_zero] using
        hprop g.length (by simp only [List.length_cons]; omega)
    rw [pathSum, List.length_cons, Nat.cast_add, Nat.cast_one]
    rw [show pathSum f g + f g w - ((g.length : ℝ) + 1) * p =
      (pathSum f g - (g.length : ℝ) * p) + (f g w - p) by ring]
    calc
      _ ≤ |pathSum f g - (g.length : ℝ) * p| + |f g w - p| := abs_add_le _ _
      _ ≤ (g.length : ℝ) * η + η := add_le_add htail hμ'
      _ = _ := by ring

theorem drop_support {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (K : FiniteKernel Ω)
    (h : List Ω) (k : ℕ) (hp : 0 < historyWeight K h) :
    0 < historyWeight K (h.drop k) := by
  induction k generalizing h with
  | zero => simpa using hp
  | succ k ih =>
    cases h with
    | nil => simpa using hp
    | cons w g =>
      change 0 < historyWeight K g * K.transition g w at hp
      have hg := pos_of_mul_pos_left hp (K.nonneg g w)
      simpa only [List.drop_succ_cons] using ih g hg

theorem drop_no_cross {Ω : Type*} (Y : List Ω → ℝ) (u : ℝ) (h : List Ω) (k : ℕ)
    (hh : ¬ EnergyExit.crossed Y u h) : ¬ EnergyExit.crossed Y u (h.drop k) := by
  induction k generalizing h with
  | zero => simpa using hh
  | succ k ih =>
    cases h with
    | nil => simpa using hh
    | cons w g => simpa only [List.drop_succ_cons] using ih g (fun hg => hh (Or.inr hg))

theorem below_of_not_crossed {Ω : Type*} (Y : List Ω → ℝ) (u : ℝ)
    (h : List Ω) (hh : ¬ EnergyExit.crossed Y u h) : Y h < u := by
  apply lt_of_not_ge
  cases h with
  | nil => exact hh
  | cons a h => exact fun he => hh (Or.inl he)

/-- At probability cost at most the energy-exit budget plus the
two type-test budgets, the stopped history reaches the horizon
and its actual selected counts follow the prescribed profile. -/
theorem simultaneous {D : Type*} (I : B → Finset E) (μ : B → ℝ) (hμ : ∀ w, 0 ≤ μ w)
    (J : Finset E) (S : Finset D) (F : D → Finset B)
    (r T : ℕ) (M n β u η v δ ε : ℝ) (hr : 1 ≤ r) (hn : 1 ≤ n)
    (hM : 0 < M) (hT : (T : ℝ) < M) (hsize : ∀ w, (I w).card = r)
    (hJ : (J.card : ℝ) = (r : ℝ) * M)
    (hguards : ∀ h : List (Option B), h.length < T → WeightedGreedy.valid I J h →
      WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
        (StoppedPhysical.profile (2 * r) M) h < u →
      StoppedPhysical.regular I μ J r M n β h) :
    let Y := WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
      (StoppedPhysical.profile (2 * r) M)
    let guard := fun h : List (Option B) =>
      StoppedPhysical.regular I μ J r M n β h ∧ (h.length < T ∧ Y h < u)
    let K := WeightedGreedy.kernel I μ hμ J guard
    FiniteProcess.eventMass K T (EnergyExit.crossed Y u) ≤ 1 / 4 →
    (∀ d ∈ S, ∀ t ≤ T, FiniteProcess.eventMass K t (fun h =>
      η < |TypeWeights.proportion I μ J (F d) h - TypeWeights.proportion I μ J (F d) []|) ≤ δ) →
    (∀ d ∈ S, FiniteProcess.eventMass K T (fun h => v < |(TypeCounts.count (F d) h : ℝ) -
      pathSum (fun g _ => ∑ w, K.transition g w * TypeCounts.indicator (F d) w) h|) ≤ ε) →
    (S.card : ℝ) * (T + 1) * δ + (S.card : ℝ) * ε ≤ 1 / 4 →
    1 / 2 ≤ FiniteProcess.eventMass K T (fun h =>
      none ∉ h ∧ WeightedGreedy.valid I J h ∧ ¬EnergyExit.crossed Y u h ∧
      ∀ d ∈ S, |(TypeCounts.count (F d) h : ℝ) -
        (T : ℝ) * TypeWeights.proportion I μ J (F d) []| ≤ v + (T : ℝ) * η) := by
  classical
  dsimp only
  intro hcross htail hcount hbudget
  let Y := WeightedGreedy.stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
    (StoppedPhysical.profile (2 * r) M)
  let guard := fun h : List (Option B) =>
    StoppedPhysical.regular I μ J r M n β h ∧ (h.length < T ∧ Y h < u)
  let K := WeightedGreedy.kernel I μ hμ J guard
  let P := fun d (_ : ℕ) h => η < |TypeWeights.proportion I μ J (F d) h -
    TypeWeights.proportion I μ J (F d) []|
  let Q := fun d h => v < |(TypeCounts.count (F d) h : ℝ) -
    pathSum (fun g _ => ∑ w, K.transition g w * TypeCounts.indicator (F d) w) h|
  let bad := fun h => (∃ d ∈ S, ∃ t ≤ T, P d t (h.drop (T - t))) ∨ (∃ d ∈ S, Q d h)
  have hbad : FiniteProcess.eventMass K T bad ≤ 1 / 4 :=
    (PrefixTypeTests.counts_and_prefix_union K T S P Q δ ε htail hcount).trans hbudget
  let tests := fun j : Bool => if j then (fun h => ¬EnergyExit.crossed Y u h) else fun h => ¬bad h
  have hmass := TypeTails.eventMass_all_ge K T (univ : Finset Bool) tests
  have he : (∑ j : Bool, FiniteProcess.eventMass K T (fun h => ¬tests j h)) ≤ 1 / 2 := by
    have heq : (∑ j : Bool, FiniteProcess.eventMass K T (fun h => ¬tests j h)) =
        FiniteProcess.eventMass K T (EnergyExit.crossed Y u) + FiniteProcess.eventMass K T bad := by
      rw [Fintype.sum_bool]
      simp [tests]
    rw [heq]
    exact (add_le_add hcross hbad).trans (by norm_num)
  refine (show (1 : ℝ) / 2 ≤ 1 - (∑ j : Bool, FiniteProcess.eventMass K T (fun h => ¬tests j h))
    by linarith).trans (hmass.trans ?_)
  apply PrefixTypeTests.mono_support
  intro h hh hp hgood
  have hc : ¬EnergyExit.crossed Y u h := by simpa [tests] using hgood true (mem_univ _)
  have hb : ¬bad h := by simpa [tests] using hgood false (mem_univ _)
  have ht : h.length = T := histories_length hh
  have hvalid := WeightedGreedy.positive_history_valid I μ hμ J guard h hp
  have hnone := GreedyHorizon.no_stop_without_exit I μ hμ J r T M n β u hr hn hM hT hsize hJ
    hguards h ht.le hp hc
  refine ⟨hnone, hvalid, hc, ?_⟩
  intro d hd
  have hcp : |(TypeCounts.count (F d) h : ℝ) -
      pathSum (fun g _ => ∑ w, K.transition g w * TypeCounts.indicator (F d) w) h| ≤ v :=
    le_of_not_gt (fun he => hb (Or.inr ⟨d, hd, he⟩))
  have hlive (j : ℕ) (hj : j < h.length) : WeightedGreedy.live I μ J guard (h.drop (h.length - j)) := by
    let g := h.drop (h.length - j)
    have hlen : g.length < T := by dsimp [g]; rw [List.length_drop]; omega
    have hg := drop_support K h (h.length - j) hp
    have hgc : ¬EnergyExit.crossed Y u g := drop_no_cross Y u h (h.length - j) hc
    have hy := below_of_not_crossed Y u g hgc
    have hv := WeightedGreedy.positive_history_valid I μ hμ J guard g hg
    have hreg := hguards g hlen hv hy
    have hden := GreedySchedule.denominator_le_available I μ J r T M n β hr hn hM
      hsize hJ g hreg hlen.le hT
    exact ⟨fun hm => hnone (List.mem_of_mem_drop hm), ⟨hreg, hlen, hy⟩,
      (GreedySchedule.denominator_pos hM hT r g.length).trans_le hden⟩
  have hhprop (j : ℕ) (hj : j < h.length) :
      |TypeWeights.proportion I μ J (F d) (h.drop (h.length - j)) -
        TypeWeights.proportion I μ J (F d) []| ≤ η := by
    rw [ht]
    exact le_of_not_gt (fun he => hb (Or.inl ⟨d, hd, j, (hj.trans_eq ht).le, he⟩))
  have hcomp := compensator_error I μ hμ J (F d) guard η h hlive hhprop
  rw [ht] at hcomp
  exact (abs_sub_le _ _ _).trans (add_le_add hcp hcomp)

end KqR75.TypeCountHorizon

#print axioms KqR75.TypeCountHorizon.compensator_error
#print axioms KqR75.TypeCountHorizon.simultaneous
