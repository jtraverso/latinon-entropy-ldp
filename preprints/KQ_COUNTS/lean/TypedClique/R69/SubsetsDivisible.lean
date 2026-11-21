/-
 R69: exact arithmetic adapter for Delcourt-Postle r=2 divisibility.

 The predicate IsPairSubsetDivisible below intentionally has the SAME
 defining formula as RefinedAbsorption.IsDivisible q 2 E:
   forall S with card S < 2, choose(q-card S, 2-card S) divides
   the number of edges containing S.
 This source proves equivalence to R65's ZMod signature for all q.

 It does not import the external absorbed theorem or assert its existence.
-/
module
public import TypedClique.R68.PackingDivisible
@[expose] public section

namespace TypedClique.R69

open Finset

variable {Vertex : Type*} [DecidableEq Vertex]

/-- Subset-divisibility predicate used by the external Delcourt-Postle
 theorem, specialized to two-uniform edge sets. -/
def IsPairSubsetDivisible (q : ℕ) (E : Finset (Finset Vertex)) : Prop :=
  ∀ S : Finset Vertex, S.card < 2 →
    Nat.choose (q - S.card) (2 - S.card) ∣
      (E.filter fun e => S ⊆ e).card

/-- The external subset-divisibility predicate at r=2 is exactly
 the modular edge-count/vertex-degree signature of R65. -/
theorem subset_divisible_iff_signature (q : ℕ) (E : Finset (Finset Vertex)) :
    IsPairSubsetDivisible q E ↔ TypedClique.R65.IsPairDivisible q E := by
  classical
  constructor
  · intro h
    constructor
    · have he := h (∅ : Finset Vertex) (by simp)
      have hdvd : Nat.choose q 2 ∣ E.card := by
        simpa using he
      have hz : ((E.card : ℕ) : ZMod (Nat.choose q 2)) = 0 :=
        ZMod.natCast_eq_zero_iff.mpr hdvd
      simpa using hz
    · intro v
      have he := h ({v} : Finset Vertex) (by simp)
      have hdvd : (q - 1) ∣ (E.filter fun e => v ∈ e).card := by
        simpa using he
      have hz : (((E.filter fun e => v ∈ e).card : ℕ) :
          ZMod (q - 1)) = 0 := ZMod.natCast_eq_zero_iff.mpr hdvd
      calc
        (∑ e ∈ E, if v ∈ e then (1 : ZMod (q - 1)) else 0) =
          ((E.filter fun e => v ∈ e).card : ZMod (q - 1)) := by
            simp [Finset.sum_filter]
        _ = 0 := hz
  · intro h
    rcases h with ⟨hcount, hdeg⟩
    intro S hS
    have hcases : S.card = 0 ∨ S.card = 1 := by omega
    rcases hcases with hzero | hone
    · have hS0 : S = ∅ := Finset.card_eq_zero.mp hzero
      subst S
      have hcountNat : ((E.card : ℕ) : ZMod (Nat.choose q 2)) = 0 := by
        simpa using hcount
      have hdvd : Nat.choose q 2 ∣ E.card :=
        ZMod.natCast_eq_zero_iff.mp hcountNat
      simpa using hdvd
    · obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hone
      subst S
      have hdegNat : (((E.filter fun e => v ∈ e).card : ℕ) :
          ZMod (q - 1)) = 0 := by
        simpa [Finset.sum_filter] using hdeg v
      have hdvd : (q - 1) ∣ (E.filter fun e => v ∈ e).card :=
        ZMod.natCast_eq_zero_iff.mp hdegNat
      simpa using hdvd

end TypedClique.R69
