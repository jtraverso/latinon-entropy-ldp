module
public import LowerAssembly
public import UpperEntropyRate
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Algebra.Field.ZMod

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Filter Finset ColouredCliques CompleteJohnson

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Quantitative two-sided enumeration of labelled clique decompositions
with an interior profile, once the physical omni-absorber is supplied. -/
theorem eventually_designFibre_bilateral_of_omni (q : ℕ) (hq : 3 ≤ q) (ρ κ : ℝ)
    (hρ : 0 < ρ) (hκ : 0 < κ)
    (homni : PhysicalOmniPlacement q (GreedyScales.criticalExponent q)) :
    ∃ lowerErr upperErr : ℝ, 0 ≤ lowerErr ∧ 0 ≤ upperErr ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (colour : Fin n → C) (m : TypeProfile C q → ℤ),
      (∀ c, ρ * (n : ℝ) ≤ (profile colour univ c : ℝ)) →
      (∀ e : Edge n, pairMargin colour (fun t => (m t : ℝ)) e =
        (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ)) →
      (∀ t, κ * ((Fintype.card (Edge n) : ℝ) / (q.choose 2 : ℝ)) ≤ (m t : ℝ)) →
      q.choose 2 ∣ n.choose 2 → q - 1 ∣ n - 1 →
      let r := q.choose 2
      let z := GreedyScales.criticalExponent q
      let s : ℝ := (r - 1 : ℕ)
      let B := (Fintype.card (Edge n) : ℝ) / (r : ℝ)
      let N := fun t : TypeProfile C q => ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ)
      let K := ∑ t, ((m t : ℝ) / B) * Real.log (((m t : ℝ) / B) / (N t / (n.choose q : ℝ)))
      let main := B * (Real.log ((n - 2).choose (q - 2)) - s - K)
      0 < (designFibre colour m).card ∧
        main - lowerErr * ((n : ℝ) ^ (2 - z) * Real.log n) ≤
          Real.log ((designFibre colour m).card : ℝ) ∧
        Real.log ((designFibre colour m).card : ℝ) ≤
          main + upperErr * (n : ℝ) ^ (2 - 1 / s) := by
  classical
  let ref : C := Classical.choice (inferInstance : Nonempty C)
  obtain ⟨p, hp, hp'⟩ := Nat.exists_infinite_primes q
  letI : Fact p.Prime := ⟨hp'⟩
  haveI : NeZero p := ⟨hp'.ne_zero⟩
  let emb : Fin q ↪ Fin p :=
    ⟨fun i => ⟨i.val, i.isLt.trans_le hp⟩, fun _ _ hi => Fin.ext (congrArg (fun i : Fin p => i.val) hi)⟩
  let s : Fin q ↪ ZMod p := emb.trans (ZMod.finEquiv p).toEquiv.toEmbedding
  obtain ⟨L, hL, hl⟩ := eventually_lower_of_omni q hq ρ κ hρ hκ ref s s.injective homni
  obtain ⟨U, hU, hu⟩ := UpperCounting.eventually_card_designFibre_upper_entropy (C := C) q hq ρ hρ
  refine ⟨L, U, hL, hU, ?_⟩
  have hnlim : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hl, hu, eventually_ge_atTop q, (tendsto_atTop.1 hnlim) ((q : ℝ) / ρ)]
    with n hlow hupp hnq hlarge
  intro colour m hcls hmargin hm hsize hdeg
  have hclasses (c : C) : q ≤ profile colour univ c := by
    have hh := (div_le_iff₀ hρ).mp hlarge
    rw [mul_comm] at hh
    exact_mod_cast hh.trans (hcls c)
  have hq' : 2 ≤ q := by omega
  obtain ⟨hpos, hlow'⟩ := hlow colour m hcls hmargin hm hsize hdeg
  obtain ⟨P, hP⟩ := card_pos.mp hpos
  have he := designFibre_type_score_as_entropy hq' hnq colour hclasses m P hP
  have hupp' := hupp colour m hcls hmargin
  have hs : ((q.choose 2 - 1 : ℕ) : ℝ) = (q.choose 2 : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.choose_pos hq'), Nat.cast_one]
  dsimp only at he hupp' ⊢
  refine ⟨hpos, ?_, ?_⟩
  · rw [he] at hlow'
    rw [hs]
    linarith only [hlow']
  · exact (Real.log_le_iff_le_exp (by exact_mod_cast hpos)).mpr hupp'

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.eventually_designFibre_bilateral_of_omni
