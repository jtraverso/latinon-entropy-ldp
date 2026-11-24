module
public import ReserveTails
public import ReserveUpper
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Fintype.Powerset

@[expose] public section
noncomputable section
namespace KqR75.ReserveRandom

open Finset MeasureTheory ProbabilityTheory
open scoped Sym2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Independent coins on unordered pairs. Diagonal coins are ignored by adjacency. -/
def law (V : Type*) [Fintype V] (p : unitInterval) : Measure (Sym2 V → Bool) :=
  Measure.pi (fun _ => bernoulliMeasure true false p)

instance (p : unitInterval) : IsProbabilityMeasure (law V p) := by
  unfold law
  infer_instance

def adj (ω : Sym2 V → Bool) (u v : V) : Prop := u ≠ v ∧ ω s(u, v) = true

instance (ω : Sym2 V → Bool) : DecidableRel (adj ω) :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ ω s(u, v) = true))

instance (ω : Sym2 V → Bool) : Std.Symm (adj ω) :=
  ⟨fun _ _ h => ⟨h.1.symm, by exact (congrArg ω Sym2.eq_swap).trans h.2⟩⟩

omit [Fintype V] [DecidableEq V] in
/-- In a disjoint cut, the vertices in its two parts index distinct unordered pairs. -/
private theorem cut_injective {U W : Finset V} (hd : Disjoint U W) :
    Set.InjOn (fun x : V × V => s(x.1, x.2)) ↑(U ×ˢ W) := by
  rintro ⟨u, w⟩ hx ⟨u', w'⟩ hy he
  obtain ⟨hu, hw⟩ := mem_product.mp (mem_coe.mp hx)
  obtain ⟨hu', hw'⟩ := mem_product.mp (mem_coe.mp hy)
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact (disjoint_left.mp hd hu hw').elim

def coin (e : Sym2 V) (ω : Sym2 V → Bool) : ℝ := if ω e = true then 1 else 0

private theorem coin_map_measurable : Measurable (fun b : Bool => if b = true then (1 : ℝ) else 0) :=
  measurable_of_countable _

omit [Fintype V] [DecidableEq V] in
theorem coin_measurable (e : Sym2 V) : Measurable (coin e) :=
  coin_map_measurable.comp (measurable_pi_apply e)

omit [DecidableEq V] in
theorem coin_independent (p : unitInterval) : iIndepFun (coin (V := V)) (law V p) := by
  unfold law coin
  exact iIndepFun_pi (fun _ => coin_map_measurable.aemeasurable)

omit [DecidableEq V] in
theorem coin_law (p : unitInterval) (e : Sym2 V) :
    HasLaw (coin e) (bernoulliMeasure (1 : ℝ) 0 p) (law V p) := by
  let f := fun b : Bool => if b = true then (1 : ℝ) else 0
  have hm := measurePreserving_eval (fun _ : Sym2 V => bernoulliMeasure true false p) e
  refine ⟨(coin_measurable e).aemeasurable, ?_⟩
  change (law V p).map (f ∘ fun ω => ω e) = _
  rw [← Measure.map_map coin_map_measurable (measurable_pi_apply e)]
  change ((Measure.pi (fun _ : Sym2 V => bernoulliMeasure true false p)).map
    (Function.eval e)).map f = _
  rw [hm.map_eq]
  simp [f]

omit [Fintype V] in
/-- The real sum of cut degrees is the sum of the coins on the unordered
pairs crossing the cut. -/
theorem cut_sum_eq (ω : Sym2 V → Bool) (U W : Finset V) (hd : Disjoint U W) :
    (∑ u ∈ U, ((ReserveCuts.neighbours (adj ω) W u).card : ℝ)) =
      (∑ e ∈ (U ×ˢ W).image (fun x => s(x.1, x.2)), coin e) ω := by
  classical
  rw [Finset.sum_apply, sum_image (cut_injective hd), sum_product]
  apply sum_congr rfl
  intro u hu
  unfold ReserveCuts.neighbours
  rw [← sum_boole]
  apply sum_congr rfl
  intro v hv
  have huv : u ≠ v := fun h => disjoint_left.mp hd (h ▸ hu) hv
  simp [coin, adj, huv]

/-- Failure of the half-density cut test is exponentially small in the
expected number of crossing edges. -/
theorem cut_tail (p : unitInterval) (U W : Finset V) (hd : Disjoint U W) :
    (law V p).real {ω | (∑ u ∈ U, ((ReserveCuts.neighbours (adj ω) W u).card : ℝ)) <
      ((p : ℝ) / 2) * U.card * W.card} ≤
      Real.exp (-((p : ℝ) * U.card * W.card) / 36) := by
  classical
  let s := (U ×ˢ W).image (fun x => s(x.1, x.2))
  let m : ℝ := (s.card : ℝ) * p
  have hcard : s.card = U.card * W.card := by
    dsimp [s]
    rw [card_image_of_injOn (cut_injective hd), card_product]
  have hm : m = (p : ℝ) * U.card * W.card := by
    dsimp [m]
    rw [hcard, Nat.cast_mul]
    ring
  have hm0 : 0 ≤ m := mul_nonneg (Nat.cast_nonneg _) p.2.1
  obtain ⟨hint, hmgf⟩ := ReserveTails.independent_bernoulli_sum p s
    (coin_independent p) coin_measurable (coin_law p) (-1 / 3)
  rw [← hm]
  refine (measureReal_mono (s₂ := {ω | (∑ e ∈ s, coin e) ω ≤ (2 / 3) * m}) ?_).trans
    (ReserveTails.lower hm0 hint hmgf)
  intro ω hω
  have hc := cut_sum_eq ω U W hd
  change (∑ u ∈ U, ((ReserveCuts.neighbours (adj ω) W u).card : ℝ)) <
    ((p : ℝ) / 2) * U.card * W.card at hω
  change (∑ e ∈ s, coin e) ω ≤ (2 / 3) * m
  rw [← hc]
  linarith only [hω, hm, hm0]

/-- Simultaneous cut estimate. Indexing all pairs of subsets costs at most
four choices per vertex. -/
theorem cut_failure (p : unitInterval) (t : ℕ) :
    (law V p).real {ω | ¬ ReserveCuts.cutLower (adj ω) (p : ℝ) t} ≤
      (4 : ℝ) ^ Fintype.card V * Real.exp (-((p : ℝ) * t ^ 2) / 36) := by
  classical
  let bad : Finset V × Finset V → Set (Sym2 V → Bool) := fun (U, W) =>
    if Disjoint U W ∧ t ≤ U.card ∧ t ≤ W.card then
      {ω | (∑ u ∈ U, ((ReserveCuts.neighbours (adj ω) W u).card : ℝ)) <
        ((p : ℝ) / 2) * U.card * W.card}
    else ∅
  have hsub : {ω | ¬ ReserveCuts.cutLower (adj ω) (p : ℝ) t} ⊆ ⋃ a, bad a := by
    intro ω hω
    change ¬ ReserveCuts.cutLower (adj ω) (p : ℝ) t at hω
    unfold ReserveCuts.cutLower at hω
    push Not at hω
    obtain ⟨U, W, hd, htU, htW, h⟩ := hω
    apply Set.mem_iUnion.mpr
    have hg : Disjoint U W ∧ t ≤ U.card ∧ t ≤ W.card := ⟨hd, htU, htW⟩
    exact ⟨(U, W), by simpa only [bad, ite_eq_left hg, Set.mem_ofPred_eq] using h⟩
  let e := Real.exp (-((p : ℝ) * t ^ 2) / 36)
  have hbad (a : Finset V × Finset V) : (law V p).real (bad a) ≤ e := by
    obtain ⟨U, W⟩ := a
    dsimp only [bad]
    split
    next h =>
      refine (cut_tail p U W h.1).trans ?_
      apply Real.exp_le_exp.mpr
      have hU : (t : ℝ) ≤ U.card := by exact_mod_cast h.2.1
      have hW : (t : ℝ) ≤ W.card := by exact_mod_cast h.2.2
      have hprod := mul_le_mul hU hW (Nat.cast_nonneg t) (Nat.cast_nonneg U.card)
      have hmul := mul_le_mul_of_nonneg_left hprod p.2.1
      nlinarith only [hmul]
    next => simp [e, (Real.exp_pos _).le]
  calc
    _ ≤ (law V p).real (⋃ a, bad a) := measureReal_mono hsub
    _ ≤ ∑ a, (law V p).real (bad a) := measureReal_iUnion_fintype_le bad
    _ ≤ ∑ _a : Finset V × Finset V, e := sum_le_sum (fun a _ => hbad a)
    _ = _ := by
      rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_prod, Fintype.card_finset, Nat.cast_mul,
        Nat.cast_pow]
      norm_num
      rw [← mul_pow]
      norm_num [e]

end KqR75.ReserveRandom

#print axioms KqR75.ReserveRandom.cut_tail
#print axioms KqR75.ReserveRandom.cut_failure
