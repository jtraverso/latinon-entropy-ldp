module
public import WeightedEnergy
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section
noncomputable section
namespace KqR75.ProfileWeights

open Finset

/-- Impossible prescribed vertices contribute zero, rather than using
truncated natural subtraction as though a completion existed. -/
def completionChoices (n k s : ℕ) : ℕ :=
  if s ≤ k then (n - s).choose (k - s) else 0

theorem choose_completion (n k s : ℕ) :
    n.choose s * completionChoices n k s = n.choose k * k.choose s := by
  by_cases hs : s ≤ k
  · simpa only [completionChoices, hs, ite_true] using (Nat.choose_mul (n := n) hs).symm
  · simp only [completionChoices, hs, ite_false, mul_zero,
      Nat.choose_eq_zero_of_lt (lt_of_not_ge hs)]

theorem completion_ratio (n k s : ℕ) (hk : 0 < n.choose k) (hs : 0 < n.choose s) :
    (completionChoices n k s : ℝ) / (n.choose k : ℝ) = (k.choose s : ℝ) / (n.choose s : ℝ) := by
  have hkR : (0 : ℝ) < n.choose k := by exact_mod_cast hk
  have hsR : (0 : ℝ) < n.choose s := by exact_mod_cast hs
  have he : (n.choose s : ℝ) * completionChoices n k s = (n.choose k : ℝ) * k.choose s := by
    exact_mod_cast choose_completion n k s
  field_simp [hkR.ne', hsR.ne']
  nlinarith only [he]

variable {E B T : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]
  [Fintype T] [DecidableEq T]

def fibre (typeOf : B → T) (t : T) : Finset B := univ.filter fun b => typeOf b = t

def weight (typeOf : B → T) (m : T → ℝ) (b : B) : ℝ :=
  m (typeOf b) / ((fibre typeOf (typeOf b)).card : ℝ)

def incidenceCount (I : B → Finset E) (typeOf : B → T) (e : E) (t : T) : ℕ :=
  ((fibre typeOf t).filter fun b => e ∈ I b).card

theorem positive (typeOf : B → T) (m : T → ℝ) (hm : ∀ t, 0 < m t) (b : B) :
    0 < weight typeOf m b := by
  have hc : 0 < (fibre typeOf (typeOf b)).card :=
    Finset.card_pos.mpr ⟨b, by simp [fibre]⟩
  exact div_pos (hm _) (by exact_mod_cast hc)

/-- Exact prescribed mass on every nonempty physical type fibre. -/
theorem fibre_mass (typeOf : B → T) (m : T → ℝ) (t : T)
    (ht : 0 < (fibre typeOf t).card) :
    (∑ b ∈ fibre typeOf t, weight typeOf m b) = m t := by
  have hs : (∑ b ∈ fibre typeOf t, weight typeOf m b) =
      ∑ _b ∈ fibre typeOf t, m t / ((fibre typeOf t).card : ℝ) := by
    apply Finset.sum_congr rfl
    intro b hb
    have he := (Finset.mem_filter.mp hb).2
    dsimp only [weight]
    rw [he]
  rw [hs, Finset.sum_const, nsmul_eq_mul]
  have htR : (0 : ℝ) < (fibre typeOf t).card := by exact_mod_cast ht
  field_simp [htR.ne']

/-- Grouping actual resource loads by the finite block-type fibres. -/
theorem load_by_types (I : B → Finset E) (typeOf : B → T) (m : T → ℝ) (e : E) :
    WeightedEnergy.load I (weight typeOf m) e =
      ∑ t, (incidenceCount I typeOf e t : ℝ) * (m t / ((fibre typeOf t).card : ℝ)) := by
  change (∑ b, if e ∈ I b then weight typeOf m b else 0) = _
  rw [← Finset.sum_fiberwise univ typeOf (fun b => if e ∈ I b then weight typeOf m b else 0)]
  apply Finset.sum_congr rfl
  intro t _
  change (∑ b ∈ fibre typeOf t, if e ∈ I b then weight typeOf m b else 0) = _
  calc
    _ = ∑ b ∈ fibre typeOf t, if e ∈ I b then m t / ((fibre typeOf t).card : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      have he := (Finset.mem_filter.mp hb).2
      simp only [weight, he]
    _ = ∑ _b ∈ (fibre typeOf t).filter (fun b => e ∈ I b), m t / ((fibre typeOf t).card : ℝ) :=
      (Finset.sum_filter _ _).symm
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; rfl

/-- The load equals the margin divided by the number of edges of that type.
The same identity applies to signed changes of the histogram. -/
theorem load_eq_margin (I : B → Finset E) (typeOf : B → T) (m a : T → ℝ) (e : E)
    (N : ℝ) (hN : 0 < N) (ht : ∀ t, 0 < (fibre typeOf t).card)
    (hcount : ∀ t, (incidenceCount I typeOf e t : ℝ) * N = a t * ((fibre typeOf t).card : ℝ)) :
    WeightedEnergy.load I (weight typeOf m) e = (∑ t, a t * m t) / N := by
  have hratio (t : T) : (incidenceCount I typeOf e t : ℝ) / ((fibre typeOf t).card : ℝ) = a t / N := by
    have htR : (0 : ℝ) < (fibre typeOf t).card := by exact_mod_cast ht t
    field_simp [htR.ne', hN.ne']
    nlinarith only [hcount t]
  rw [load_by_types]
  calc
    _ = ∑ t, (a t * m t) / N := by
      apply Finset.sum_congr rfl
      intro t _
      calc
        _ = ((incidenceCount I typeOf e t : ℝ) / ((fibre typeOf t).card : ℝ)) * m t := by ring
        _ = (a t / N) * m t := by rw [hratio]
        _ = _ := by ring
    _ = (∑ t, a t * m t) / N := by simp only [div_eq_mul_inv, Finset.sum_mul]

theorem unit_load (I : B → Finset E) (typeOf : B → T) (m a : T → ℝ) (e : E)
    (N : ℝ) (hN : 0 < N) (ht : ∀ t, 0 < (fibre typeOf t).card)
    (hcount : ∀ t, (incidenceCount I typeOf e t : ℝ) * N = a t * ((fibre typeOf t).card : ℝ))
    (hmargin : (∑ t, a t * m t) = N) :
    WeightedEnergy.load I (weight typeOf m) e = 1 := by
  rw [load_eq_margin I typeOf m a e N hN ht hcount, hmargin, div_self hN.ne']

end KqR75.ProfileWeights

#print axioms KqR75.ProfileWeights.fibre_mass
#print axioms KqR75.ProfileWeights.completion_ratio
#print axioms KqR75.ProfileWeights.load_by_types
#print axioms KqR75.ProfileWeights.unit_load
