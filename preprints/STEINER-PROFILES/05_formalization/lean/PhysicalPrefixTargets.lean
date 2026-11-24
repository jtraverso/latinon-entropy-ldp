module
public import BankHorizon
public import PhysicalPrefixScore

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Finset ColouredCliques CompleteJohnson SparseGram WeightedGreedy ProfileBalance
open BankCapacity (integerHistogram)
open scoped Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Prefix frequencies compared with the original target. For this
comparison the basal packing contributes its size, while the signed
correction of the completed design cancels its bank contribution. -/
theorem prefix_counts_close_to_target {n q : ℕ} (hq : 3 ≤ q) (hn : 1 ≤ n)
    (colour : Fin n → C) (J : Finset (Edge n)) (hJ : 0 < J.card)
    (P : Finset (Clique n q)) (m : TypeProfile C q → ℝ)
    (w : HostCorrection.availableBlocks n q J → ℝ) (hw : ∀ b, 0 ≤ w b)
    (hload : HostCorrection.hostIncidence n q J *ᵥ w = (fun _ => 1))
    (a z D K U : ℝ) (ha : 0 ≤ a) (hz : z ≤ 2) (haz : z ≤ a)
    (h : List (Option (Clique n q))) (hv : valid (resources n q) J h)
    (hh : h.length = GreedyScales.horizon ((J.card : ℝ) / (q.choose 2 : ℝ)) n a)
    (hcount : ∀ t : TypeProfile C q,
      |(TypeCounts.count (PhysicalHorizonCounts.fibre colour t) h : ℝ) -
        (h.length : ℝ) * TypeWeights.proportion (resources n q) (extend J w) J
          (PhysicalHorizonCounts.fibre colour t) []| ≤ D * (n : ℝ) ^ (2 - z))
    (hrepair : ∀ t, |m t - (integerHistogram colour P t : ℝ) - hostHistogram colour J w t| ≤
      K * (n : ℝ) ^ (2 - z))
    (hP : (P.card : ℝ) ≤ U * (n : ℝ) ^ (2 - z)) :
    ∀ t : TypeProfile C q,
      |(TypeCounts.count (PhysicalHorizonCounts.fibre colour t) h : ℝ) - m t| ≤
        (D + 2 + K + U) * (n : ℝ) ^ (2 - z) := by
  classical
  have hp := BankCapacity.prefix_histogram_bound hq hn J hJ colour w hw hload a z D ha hz haz
    h hv hh hcount
  intro t
  let ν := TypeCounts.count (PhysicalHorizonCounts.fibre colour t) h
  let A := (integerHistogram colour P t : ℝ)
  let b := hostHistogram colour J w t
  have hI (C : Clique n q) : (resources n q C).Nonempty := by
    apply card_pos.mp
    rw [resources_card]
    exact Nat.choose_pos (by omega)
  have he := (picked_partition (resources n q) J hI h hv).2 (PhysicalHorizonCounts.fibre colour t)
  have hν : (integerHistogram colour (picked h) t : ℝ) = (ν : ℝ) := by
    simp only [integerHistogram, Int.cast_natCast, Nat.cast_inj, ν]
    simpa [PhysicalHorizonCounts.fibre] using he
  have h₁ := hp t
  rw [hν] at h₁
  have h₂ := hrepair t
  have hA : |A| ≤ (P.card : ℝ) := by
    dsimp [A, integerHistogram]
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _), Nat.cast_le]
    exact card_filter_le _ _
  change |(ν : ℝ) - m t| ≤ _
  rw [show (ν : ℝ) - m t = ((ν : ℝ) - b) - (m t - A - b) - A by ring]
  have abs_diff (x y : ℝ) : |x - y| ≤ |x| + |y| := by
    simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le x 0 y
  calc
    _ ≤ |(ν : ℝ) - b| + |m t - A - b| + |A| :=
      (abs_diff _ _).trans (add_le_add (abs_diff _ _) le_rfl)
    _ ≤ (D + 2 + K + U) * (n : ℝ) ^ (2 - z) := by
      nlinarith only [h₁, h₂, hA.trans hP]

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.prefix_counts_close_to_target
