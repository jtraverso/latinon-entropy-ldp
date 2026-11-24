module
public import GreedySchedule

@[expose] public section
noncomputable section
namespace KqR75.GreedySchedule

open Finset WeightedGreedy

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- Integrated energy controls the relative error in the transition
normalizer at any valid prefix. -/
theorem relative_mass_error (I : B → Finset E) (μ : B → ℝ) (J : Finset E)
    (r : ℕ) (hr : 1 ≤ r) (hsize : ∀ b, (I b).card = r)
    (M : ℝ) (hM : 0 < M) (hJ : (J.card : ℝ) = (r : ℝ) * M)
    (h : List (Option B)) (hv : valid I J h) (hi : (selectedCount h : ℝ) < M)
    (ε : ℝ) (hε : 0 ≤ ε) :
    let p := (M - (selectedCount h : ℝ)) / M
    stoppedEnergy I μ J (StoppedPhysical.profile (r - 1) M)
        (StoppedPhysical.profile (2 * r) M) h ≤
      ε ^ 2 * ((r : ℝ) * M * p ^ (4 * r - 1)) →
    |totalWeight I μ J h - M * p ^ r| ≤ ε * (M * p ^ r) := by
  let i := selectedCount h
  let m := M - (i : ℝ)
  let p := m / M
  let k := StoppedPhysical.profile (r - 1) M i
  let X := energy I μ J h k
  let Z := totalWeight I μ J h
  dsimp only
  intro hY
  have hm : 0 < m := sub_pos.mpr hi
  have hp : 0 < p := div_pos hm hM
  have hrR : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hk : k = p ^ (r - 1) := StoppedPhysical.profile_eq (r - 1) M i hM hi.le
  have hf : StoppedPhysical.profile (2 * r) M i = p ^ (2 * r) :=
    StoppedPhysical.profile_eq (2 * r) M i hM hi.le
  have hm' : M * p = m := by
    dsimp [p]
    rw [mul_comm, div_mul_cancel₀ _ hM.ne']
  have hmk : M * p ^ r = m * k := by
    have hexp : r = r - 1 + 1 := by omega
    rw [hk, show p ^ r = p ^ (r - 1) * p from (congrArg (fun j : ℕ => p ^ j) hexp).trans
      (pow_succ _ _), ← hm']
    ring
  have hprod : (r : ℝ) * M * p ^ (4 * r - 1) =
      ((r : ℝ) * m * k ^ 2) * p ^ (2 * r) := by
    have hexp : 4 * r - 1 = 1 + (r - 1) * 2 + 2 * r := by omega
    rw [hexp, hk, ← hm']
    simp only [pow_add, pow_one, pow_mul]
    ring
  change StoppedPhysical.profile (2 * r) M i * X ≤ _ at hY
  rw [hf, hprod] at hY
  have hX : X ≤ ε ^ 2 * ((r : ℝ) * m * k ^ 2) := by
    have hf₀ : 0 < p ^ (2 * r) := pow_pos hp _
    apply le_of_mul_le_mul_right _ hf₀
    nlinarith only [hY]
  have hc : ((remaining I J h).card : ℝ) = (r : ℝ) * m := by
    have hh : ((remaining I J h).card : ℝ) + (r : ℝ) * i = J.card :=
      by exact_mod_cast resource_count I J r hsize h hv
    rw [hJ] at hh
    dsimp [m]
    linarith only [hh]
  let s := ∑ e, error I μ J h k e
  have hmass : s = (r : ℝ) * (Z - m * k) := by
    have hh := GreedyMoments.mass_error I μ J h r hsize k
    rw [hc] at hh
    dsimp [s, Z]
    linarith only [hh]
  have hv' : s ^ 2 ≤ ((r : ℝ) * m) * X := by
    simpa only [hc] using (GreedyMoments.error_variances I μ J h k).2
  have hs : s ^ 2 ≤ ((r : ℝ) * (ε * (m * k))) ^ 2 := by
    calc
      _ ≤ ((r : ℝ) * m) * X := hv'
      _ ≤ ((r : ℝ) * m) * (ε ^ 2 * ((r : ℝ) * m * k ^ 2)) :=
        mul_le_mul_of_nonneg_left hX (mul_nonneg hrR.le hm.le)
      _ = _ := by ring
  have habs : |s| ≤ (r : ℝ) * (ε * (m * k)) := by
    by_contra! hb
    have hdiff : 0 < |s| - (r : ℝ) * (ε * (m * k)) := sub_pos.mpr hb
    have hpos : 0 < |s| := lt_of_le_of_lt
      (by rw [hk]; positivity) hb
    have hsum : 0 < |s| + (r : ℝ) * (ε * (m * k)) := by rw [hk]; positivity
    nlinarith only [mul_pos hdiff hsum, hs, sq_abs s]
  rw [hmass, abs_mul, abs_of_pos hrR] at habs
  change |Z - M * p ^ r| ≤ ε * (M * p ^ r)
  rw [hmk]
  exact le_of_mul_le_mul_left habs hrR

end KqR75.GreedySchedule

#print axioms KqR75.GreedySchedule.relative_mass_error
