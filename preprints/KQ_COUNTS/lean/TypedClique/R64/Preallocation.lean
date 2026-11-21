/-
 R64: finite algebraic contracts for the order of quantifiers:
   reserve X -> omniabsorber A -> preallocate budgets -> bank B ->
   GJKKL horizon T and any admissible packing P.

 No new asymptotic existence theorem is assumed or asserted.
-/
module
public import TypedClique.R63.UniversalCompletion
@[expose] public section

namespace TypedClique.R64

/-- The matching horizon cannot create a circular dependence
 of the residual budget on bank B. M stands for the floor of bJ.
 In applications r=choose(q,2), theta=d^(-epsilon^3),
 and bStar is the number of full-graph blocks. -/
theorem horizon_gap_before_bank
    (r bJ bStar θ M T : ℝ)
    (hr : 0 ≤ r) (hM : M ≤ bJ) (hMlt : bJ < M + 1)
    (hθ : 0 ≤ θ) (hb : bJ ≤ bStar) (hTle : T ≤ M)
    (hTfloor : (1 - θ) * ((r * bJ + M) / (r + 1)) < T + 1) :
    0 ≤ bJ - T ∧ bJ - T < θ * bStar + 2 := by
  have hden : 0 < r + 1 := by linarith
  let x : ℝ := (r * bJ + M) / (r + 1)
  have hxle : x ≤ bJ := by
    dsimp [x]
    apply (div_le_iff₀ hden).2
    nlinarith [hM]
  have hxlow : bJ - 1 < x := by
    dsimp [x]
    apply (lt_div_iff₀ hden).2
    nlinarith [hMlt, hr]
  have hmul : θ * x ≤ θ * bJ :=
    mul_le_mul_of_nonneg_left hxle hθ
  constructor
  · linarith
  · change (1 - θ) * x < T + 1 at hTfloor
    have hpart : bJ - (1 - θ) * x < 1 + θ * bJ := by
      nlinarith [hxlow, hmul]
    have hthetale : θ * bJ ≤ θ * bStar :=
      mul_le_mul_of_nonneg_left hb hθ
    linarith

/-- A bank budget determined before bank B and packing P is known
 controls the integer defect, given R49's pointwise defect inequality. -/
theorem bank_defect_under_preallocated_budget
    (bStar θ hA X acoef r s Dstar gap normDefect : ℝ)
    (hgap : gap ≤ θ * bStar + 2)
    (hdefect : normDefect ≤
      2 * gap + 2 * hA / r + (acoef + 1 / r) * X + s)
    (hreserve : 2 * (θ * bStar + 2) +
      2 * hA / r + (acoef + 1 / r) * X + s ≤ Dstar) :
    normDefect ≤ Dstar := by
  linarith

/-- The total size of completion is independent of the number Y
 of reserve edges consumed by the coverdown algorithm. -/
theorem consumed_reserve_cancels
    (r L Y A X : ℝ) (hr : r ≠ 0) :
    (L + Y) / r + (A + X - Y) / r = (L + A + X) / r := by
  field_simp
  ring

end TypedClique.R64
