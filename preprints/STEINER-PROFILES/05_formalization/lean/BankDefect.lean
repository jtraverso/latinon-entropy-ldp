module
public import ProfileBalance

@[expose] public section
noncomputable section
namespace KqR75.BankCapacity

open Finset ColouredCliques SlotPairMargins CompleteJohnson SparseGram

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The exact type histogram of a finite family of physical cliques. -/
def integerHistogram {n q : ℕ} (colour : Fin n → C) (P : Finset (Clique n q))
    (t : TypeProfile C q) : ℤ :=
  ((P.filter (fun b => cliqueType colour b = t)).card : ℤ)

/-- The weighted histogram specializes to the integer histogram for a packing. -/
theorem histogram_indicator {n q : ℕ} (colour : Fin n → C) (P : Finset (Clique n q))
    (t : TypeProfile C q) :
    ProfileBalance.histogram colour (fun b => if b ∈ P then 1 else 0) t =
      (integerHistogram colour P t : ℝ) := by
  classical
  have he : ((univ.filter (fun b : Clique n q => cliqueType colour b = t)).filter (· ∈ P)) =
      P.filter (fun b => cliqueType colour b = t) := by
    ext b
    simp [and_comm]
  unfold ProfileBalance.histogram integerHistogram ProfileWeights.fibre
  rw [sum_boole, he]
  norm_cast

theorem load_indicator {n q : ℕ} (P : Finset (Clique n q)) (e : Edge n) :
    WeightedEnergy.load (resources n q) (fun b => if b ∈ P then 1 else 0) e =
      ((P.filter (fun b => e ∈ resources n q b)).card : ℝ) := by
  classical
  unfold WeightedEnergy.load
  calc
    _ = ∑ b : Clique n q, if b ∈ P ∧ e ∈ resources n q b then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro b _
      by_cases hb : b ∈ P <;> by_cases he : e ∈ resources n q b <;> simp [hb, he]
    _ = _ := by
      have he : (univ.filter (fun b : Clique n q => b ∈ P ∧ e ∈ resources n q b)) =
          P.filter (fun b => e ∈ resources n q b) := by
        ext b
        simp
      rw [sum_boole, he]

/-- The difference between two histograms with the complete host's
margins lies in the integer kernel required by the bank. -/
theorem defect_in_kernel {n q : ℕ} (colour : Fin n → C)
    (hclasses : ∀ i, 2 ≤ profile colour univ i) (P : Finset (Clique n q))
    (m : TypeProfile C q → ℤ)
    (hdecomp : ∀ e : Edge n, (P.filter (fun b => e ∈ resources n q b)).card = 1)
    (hmargin : ∀ e : Edge n, pairMargin colour (fun t => (m t : ℝ)) e =
      ∑ f : Edge n,
        if profile colour (f : Finset (Fin n)) = profile colour (e : Finset (Fin n)) then 1 else 0) :
    ∀ i j : C, ∑ t, (m t - integerHistogram colour P t) * (orderedCount t i j : ℤ) = 0 := by
  classical
  let w : TypeProfile C q → ℝ := fun t => (m t : ℝ) - (integerHistogram colour P t : ℝ)
  have hP (e : Edge n) : pairMargin colour (fun t => (integerHistogram colour P t : ℝ)) e =
      ∑ f : Edge n,
        if profile colour (f : Finset (Fin n)) = profile colour (e : Finset (Fin n)) then 1 else 0 := by
    simp_rw [← histogram_indicator]
    rw [ProfileBalance.margin_histogram]
    simp_rw [load_indicator, hdecomp, Nat.cast_one, one_mul]
  have hw (e : Edge n) : pairMargin colour w e = 0 := by
    change pairMargin colour (fun t => (m t : ℝ) - (integerHistogram colour P t : ℝ)) e = 0
    unfold pairMargin
    simp only [mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr ((hmargin e).trans (hP e).symm)
  intro i j
  have h := ((ordered_margins_zero_iff colour hclasses w).mpr hw) i j
  dsimp only [w] at h
  exact_mod_cast h

end KqR75.BankCapacity

namespace KqR75.BankCapacity

/-- The deficit from the prefixed number of steps costs at most the
unused mass of the initial distribution. -/
theorem prefix_defect {k h m T ε : ℝ}
    (hm : 0 < m) (hh : 0 ≤ h) (hhm : h ≤ m) (hT : T ≤ m)
    (htrack : |k - T * (h / m)| ≤ ε) :
    |k - h| ≤ ε + (m - T) := by
  have hp₀ : 0 ≤ h / m := div_nonneg hh hm.le
  have hp₁ : h / m ≤ 1 := (div_le_one hm).mpr hhm
  have hEq : T * (h / m) - h = -((m - T) * (h / m)) := by field_simp; ring
  calc
    _ = |(k - T * (h / m)) + (T * (h / m) - h)| := by congr 1; ring
    _ ≤ |k - T * (h / m)| + |T * (h / m) - h| := abs_add_le _ _
    _ ≤ _ := by
      rw [hEq, abs_neg, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hT) hp₀)]
      have he : (m - T) * (h / m) ≤ (m - T) * 1 :=
        mul_le_mul_of_nonneg_left hp₁ (sub_nonneg.mpr hT)
      rw [mul_one] at he
      exact add_le_add htrack he

/-- The basal bank cancels before estimating the defect. Only the seed
repair, the pickedMass, and the other completion pieces enter the bound. -/
theorem completed_defect {m bank basalAbs repaired pickedMass cover absorbed ε₁ ε₂ : ℝ}
    (hrepair : |m - bank - basalAbs - repaired| ≤ ε₁)
    (hprefix : |repaired - pickedMass| ≤ ε₂)
    (hbasal : 0 ≤ basalAbs) (hcover : 0 ≤ cover) (habs : 0 ≤ absorbed) :
    |m - (bank + pickedMass + cover + absorbed)| ≤ ε₁ + ε₂ + basalAbs + cover + absorbed := by
  have he : m - (bank + pickedMass + cover + absorbed) =
      ((m - bank - basalAbs - repaired) + (repaired - pickedMass)) + (basalAbs - cover - absorbed) := by ring
  rw [he]
  have h₁ := abs_add_le (m - bank - basalAbs - repaired) (repaired - pickedMass)
  have h₂ : |basalAbs - cover - absorbed| ≤ basalAbs + cover + absorbed := by
    apply abs_le.mpr
    constructor <;> linarith
  exact (abs_add_le _ _).trans (by linarith)

end KqR75.BankCapacity

#print axioms KqR75.BankCapacity.defect_in_kernel
#print axioms KqR75.BankCapacity.prefix_defect
#print axioms KqR75.BankCapacity.completed_defect
