module
public import CoverDegrees

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex is saturated if the proposed degree increase would exceed
the current allowance. -/
def saturated (f : V → ℕ) (cap step : ℕ) : Finset V :=
  univ.filter (fun v => cap < f v + step)

theorem saturated_card (f : V → ℕ) (cap step : ℕ) (hstep : step ≤ cap) :
    (saturated f cap step).card * (cap - step + 1) ≤ ∑ v : V, f v := by
  have hsub : saturated f cap step ⊆ univ.filter (fun v => cap - step + 1 ≤ f v) := by
    intro v hv
    have h := (mem_filter.mp hv).2
    exact mem_filter.mpr ⟨mem_univ _, by omega⟩
  exact (Nat.mul_le_mul_right _ (card_le_card hsub)).trans (card_large f (cap - step + 1))

/-- The vertex potential used in the second phase. -/
def potential (q : ℕ) (L Y : Finset (Finset V)) (v : V) : ℕ :=
  degree Y v + (q - 2) * degree L v

theorem sum_potential (q : ℕ) (L Y : Finset (Finset V))
    (hL : ∀ e ∈ L, e.card = 2) (hY : ∀ e ∈ Y, e.card = 2) :
    (∑ v : V, potential q L Y v) = 2 * (Y.card + (q - 2) * L.card) := by
  unfold potential
  rw [sum_add_distrib, ← mul_sum, sum_degrees Y hY, sum_degrees L hL]
  ring

/-- The first phase loses at most the number of saturated vertices
from the neighbour set of the star centre. -/
theorem star_candidates_card (L Y : Finset (Finset V)) (u : V) (cap step : ℕ)
    (hL : ∀ e ∈ L, e.card = 2) :
    degree L u ≤
      (adjacentVertices L u \ saturated (degree Y) cap step).card +
        (saturated (degree Y) cap step).card := by
  rw [← adjacentVertices_card L u hL]
  exact card_le_card_sdiff_add_card

/-- Apart from the saturated vertices, the second phase forbids at most
two current reserve degrees' worth of auxiliary vertices. -/
theorem pair_forbidden_card (q : ℕ) (L Y : Finset (Finset V)) (cap step : ℕ)
    (u v : V) (hY : ∀ e ∈ Y, e.card = 2)
    (hcap : ∀ w, potential q L Y w ≤ cap) :
    ((saturated (potential q L Y) cap step ∪ adjacentVertices Y u) ∪ adjacentVertices Y v).card ≤
      (saturated (potential q L Y) cap step).card + 2 * cap := by
  have hu : (adjacentVertices Y u).card ≤ cap :=
    (adjacentVertices_card Y u hY).trans_le ((Nat.le_add_right _ _).trans (hcap u))
  have hv : (adjacentVertices Y v).card ≤ cap :=
    (adjacentVertices_card Y v hY).trans_le ((Nat.le_add_right _ _).trans (hcap v))
  have h₁ := card_union_le (saturated (potential q L Y) cap step) (adjacentVertices Y u)
  have h₂ := card_union_le
    (saturated (potential q L Y) cap step ∪ adjacentVertices Y u) (adjacentVertices Y v)
  omega

end KqR75.CoverDown

#print axioms KqR75.CoverDown.saturated_card
#print axioms KqR75.CoverDown.sum_potential
#print axioms KqR75.CoverDown.star_candidates_card
#print axioms KqR75.CoverDown.pair_forbidden_card
