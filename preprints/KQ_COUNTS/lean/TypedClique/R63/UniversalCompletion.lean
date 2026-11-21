/-
 R63: finite universal completion and weighted transfer.

 This does NOT assume the existence of a completion construction
 for all packings in an asymptotic family; it makes that quantified
 hypothesis explicit. In particular, the theorem cannot prove KL
 by postulating the existence claim as an axiom.
-/
module
public import TypedClique.R54.Disjointness
@[expose] public section

namespace TypedClique.R63

open Finset

variable {Packing Design : Type*} [DecidableEq Packing] [DecidableEq Design]

/-- A single fixed family of designs can complete every packing in the
 fixed admissible family; the recovery left inverse yields a cardinal bound. -/
theorem universal_completion_card_bound
    (Ps : Finset Packing) (Ds : Finset Design)
    (recover : Design → Packing)
    (hAll : ∀ P ∈ Ps, ∃ D ∈ Ds, recover D = P) :
    Ps.card ≤ Ds.card := by
  classical
  let completion : {P : Packing // P ∈ Ps} → {D : Design // D ∈ Ds} :=
    fun P =>
      ⟨Classical.choose (hAll P.1 P.2),
       (Classical.choose_spec (hAll P.1 P.2)).1⟩
  have hleft : ∀ P : {P : Packing // P ∈ Ps},
      recover (completion P).1 = P.1 := by
    intro P
    exact (Classical.choose_spec (hAll P.1 P.2)).2
  have hinj : Function.Injective completion := by
    intro P Q h
    apply Subtype.ext
    calc
      P.1 = recover (completion P).1 := (hleft P).symm
      _ = recover (completion Q).1 := congrArg (fun d => recover d.1) h
      _ = Q.1 := hleft Q
  have hc := Fintype.card_le_of_injective completion hinj
  simpa using hc

/-- Finite weighted transport: if every packing has a completion in the
 SAME pre-fixed design family, and every individual weight is bounded
 above by B, then the weighted partition sum is at most (#designs)*B.
 A genuine R60.2 instance follows by specifying B as its type-weight cap. -/
theorem universal_weighted_transfer
    (Ps : Finset Packing) (Ds : Finset Design)
    (recover : Design → Packing) (weight : Packing → ℝ) (B : ℝ)
    (hAll : ∀ P ∈ Ps, ∃ D ∈ Ds, recover D = P)
    (hB : 0 ≤ B)
    (hWeight : ∀ P ∈ Ps, weight P ≤ B) :
    (∑ P ∈ Ps, weight P) ≤ (Ds.card : ℝ) * B := by
  classical
  have hcard : Ps.card ≤ Ds.card :=
    universal_completion_card_bound Ps Ds recover hAll
  have hsum : (∑ P ∈ Ps, weight P) ≤ (Ps.card : ℝ) * B := by
    calc
      (∑ P ∈ Ps, weight P) ≤ ∑ P ∈ Ps, B := by
        apply Finset.sum_le_sum
        intro P hP
        exact hWeight P hP
      _ = (Ps.card : ℝ) * B := by simp
  calc
    (∑ P ∈ Ps, weight P) ≤ (Ps.card : ℝ) * B := hsum
    _ ≤ (Ds.card : ℝ) * B := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hB

end TypedClique.R63
