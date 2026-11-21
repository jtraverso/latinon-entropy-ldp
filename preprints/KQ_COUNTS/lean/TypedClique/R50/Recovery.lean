/-
  R50.1: Finite recovery and injectivity for typed clique completions.
  This code is a draft pending a genuine Lean kernel build.
-/
module
public import Mathlib
@[expose] public section

namespace TypedClique.R50

open Finset

/-- Filtering the finished decomposition by footprints inside J recovers P,
provided every newly inserted block uses an edge outside J. -/
theorem recover_eq
    {Block Edge : Type*} [DecidableEq Block] [DecidableEq Edge]
    (footprint : Block → Finset Edge) (J : Finset Edge) (D P : Finset Block)
    (hPD : P ⊆ D)
    (hInside : ∀ Q ∈ P, footprint Q ⊆ J)
    (hOutside : ∀ Q ∈ D \ P, ¬ footprint Q ⊆ J) :
    D.filter (fun Q => footprint Q ⊆ J) = P := by
  classical
  ext Q
  constructor
  · intro hQ
    have hQD : Q ∈ D := (Finset.mem_filter.mp hQ).1
    have hQJ : footprint Q ⊆ J := (Finset.mem_filter.mp hQ).2
    by_contra hQP
    exact hOutside Q (Finset.mem_sdiff.mpr ⟨hQD, hQP⟩) hQJ
  · intro hQP
    exact Finset.mem_filter.mpr ⟨hPD hQP, hInside Q hQP⟩

/-- Any deterministic completion with a left inverse is injective. -/
theorem complete_injective
    {S T : Type*} (complete : S → T) (recover : T → S)
    (h : ∀ s, recover (complete s) = s) :
    Function.Injective complete := by
  intro a b hab
  calc
    a = recover (complete a) := (h a).symm
    _ = recover (complete b) := congrArg recover hab
    _ = b := h b

end TypedClique.R50
