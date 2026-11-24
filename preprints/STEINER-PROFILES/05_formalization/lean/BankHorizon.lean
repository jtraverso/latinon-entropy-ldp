module
public import BankBudget
public import PrefixPacking

@[expose] public section
noncomputable section
namespace KqR75.BankCapacity

open Finset ColouredCliques CompleteJohnson SparseGram
open scoped Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Each type weight is at most the total remaining block mass. -/
theorem host_histogram_bounds {n q : ℕ} (hq : 2 ≤ q) (J : Finset (Edge n))
    (colour : Fin n → C) (w : HostCorrection.availableBlocks n q J → ℝ)
    (hw : ∀ b, 0 ≤ w b) (hload : HostCorrection.hostIncidence n q J *ᵥ w = (fun _ => 1))
    (t : TypeProfile C q) :
    0 ≤ ProfileBalance.hostHistogram colour J w t ∧
      ProfileBalance.hostHistogram colour J w t ≤ (J.card : ℝ) / (q.choose 2 : ℝ) := by
  classical
  let μ := ProfileBalance.extend J w
  have hμ := PhysicalHorizonCounts.extend_nonneg J w hw
  have htotal := WeightedEnergy.incidence_sum (resources n q) μ (fun _ => (1 : ℝ))
  have hload' (e : Edge n) : WeightedEnergy.load (resources n q) μ e = if e ∈ J then 1 else 0 := by
    change WeightedEnergy.load (resources n q) (ProfileBalance.extend J w) e = _
    rw [ProfileBalance.load_extend, hload]
    split_ifs <;> rfl
  have hl : (∑ b, μ b * ∑ _e ∈ resources n q b, (1 : ℝ)) =
      (∑ b, μ b) * (q.choose 2 : ℝ) := by
    simp only [sum_const, nsmul_eq_mul, resources_card, mul_one, sum_mul]
  have hr : (∑ e, WeightedEnergy.load (resources n q) μ e * 1) = (J.card : ℝ) := by
    simp_rw [hload', mul_one]
    rw [sum_boole, filter_mem_eq_of_subset (subset_univ J)]
  rw [hl, hr] at htotal
  have hq' : (0 : ℝ) < q.choose 2 := by exact_mod_cast Nat.choose_pos hq
  have hm : (∑ b, μ b) = (J.card : ℝ) / (q.choose 2 : ℝ) :=
    (eq_div_iff hq'.ne').mpr htotal
  change 0 ≤ ∑ b ∈ ProfileWeights.fibre (cliqueType colour) t, μ b ∧
    (∑ b ∈ ProfileWeights.fibre (cliqueType colour) t, μ b) ≤ _
  exact ⟨sum_nonneg (fun b _ => hμ b), hm ▸
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun b _ _ => hμ b)⟩

/-- The unused horizon mass has an envelope with a coefficient
independent of the bank and of the reserve. -/
theorem horizon_loss_bound {n : ℕ} {M a z : ℝ} (hn : 1 ≤ n) (hM : 0 < M)
    (hMup : M ≤ (n : ℝ) ^ 2) (ha : 0 ≤ a) (hz : z ≤ 2) (haz : z ≤ a) :
    M - (GreedyScales.horizon M n a : ℝ) ≤ 2 * (n : ℝ) ^ (2 - z) := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) < n := by linarith
  have hX : 1 ≤ (n : ℝ) ^ (2 - z) := Real.one_le_rpow hn₁ (by linarith)
  have hpow : (n : ℝ) ^ (-a) ≤ (n : ℝ) ^ (-z) :=
    Real.rpow_le_rpow_of_exponent_le hn₁ (by linarith)
  have hmult : M * (n : ℝ) ^ (-a) ≤ (n : ℝ) ^ (2 - z) := by
    calc
      _ ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ (-z) :=
        mul_le_mul hMup hpow (by positivity) (by positivity)
      _ = _ := by
        rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_add hn₀]
        congr 1
  exact (GreedyScales.horizon_bounds M n a hM hn ha).2.1.trans (by linarith)

/-- Convert the type event for the greedy history into a discrepancy
between the actual prefix histogram and the repaired weight. -/
theorem prefix_histogram_bound {n q : ℕ} (hq : 3 ≤ q) (hn : 1 ≤ n)
    (J : Finset (Edge n)) (hJ : 0 < J.card)
    (colour : Fin n → C) (w : HostCorrection.availableBlocks n q J → ℝ)
    (hw : ∀ b, 0 ≤ w b) (hload : HostCorrection.hostIncidence n q J *ᵥ w = (fun _ => 1))
    (a z D : ℝ) (ha : 0 ≤ a) (hz : z ≤ 2) (haz : z ≤ a)
    (h : List (Option (Clique n q))) (hv : WeightedGreedy.valid (resources n q) J h)
    (hh : h.length = GreedyScales.horizon ((J.card : ℝ) / (q.choose 2 : ℝ)) n a)
    (hcount : ∀ t : TypeProfile C q,
      |(TypeCounts.count (PhysicalHorizonCounts.fibre colour t) h : ℝ) -
        (h.length : ℝ) * TypeWeights.proportion (resources n q) (ProfileBalance.extend J w) J
          (PhysicalHorizonCounts.fibre colour t) []| ≤ D * (n : ℝ) ^ (2 - z)) :
    ∀ t : TypeProfile C q, |(integerHistogram colour (WeightedGreedy.picked h) t : ℝ) -
      ProfileBalance.hostHistogram colour J w t| ≤ (D + 2) * (n : ℝ) ^ (2 - z) := by
  classical
  let M : ℝ := (J.card : ℝ) / (q.choose 2 : ℝ)
  have hr : (1 : ℝ) ≤ q.choose 2 := by exact_mod_cast Nat.choose_pos (by omega : 2 ≤ q)
  have hM : 0 < M := div_pos (by exact_mod_cast hJ) (by linarith)
  have hMup : M ≤ (n : ℝ) ^ 2 := by
    have h1 : (J.card : ℝ) ≤ Fintype.card (Edge n) := by exact_mod_cast card_le_univ J
    have h2 : (Fintype.card (Edge n) : ℝ) ≤ (n : ℝ) ^ 2 := by
      have hh : Fintype.card (Edge n) = n.choose 2 := by
        rw [Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]
      rw [hh]
      exact_mod_cast Nat.choose_le_pow n 2
    exact (div_le_self (Nat.cast_nonneg _) hr).trans (h1.trans h2)
  have hI (b : Clique n q) : (resources n q b).Nonempty := by
    apply card_pos.mp
    rw [resources_card]
    exact Nat.choose_pos (by omega)
  have hT : (h.length : ℝ) ≤ M := by
    rw [hh]
    exact (GreedyScales.horizon_bounds M n a hM hn ha).1.le
  intro t
  obtain ⟨hpos, hup⟩ := host_histogram_bounds (by omega : 2 ≤ q) J colour w hw hload t
  have ht := hcount t
  rw [PhysicalHorizonCounts.initial_proportion (by omega : 2 ≤ q) J colour w hload t] at ht
  have he := (WeightedGreedy.picked_partition (resources n q) J hI h hv).2
    (PhysicalHorizonCounts.fibre colour t)
  have htally : integerHistogram colour (WeightedGreedy.picked h) t =
      (TypeCounts.count (PhysicalHorizonCounts.fibre colour t) h : ℤ) := by
    dsimp [integerHistogram]
    exact_mod_cast (by simpa [PhysicalHorizonCounts.fibre] using he)
  rw [htally, Int.cast_natCast]
  refine (prefix_defect hM hpos hup hT ht).trans ?_
  rw [hh]
  have hrem := horizon_loss_bound hn hM hMup ha hz haz
  linarith only [hrem]

end KqR75.BankCapacity

#print axioms KqR75.BankCapacity.host_histogram_bounds
#print axioms KqR75.BankCapacity.horizon_loss_bound
#print axioms KqR75.BankCapacity.prefix_histogram_bound
