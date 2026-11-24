module

public import DesignFibreMass
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
noncomputable section

namespace KqR75.ProfileLDP

open Finset Filter Topology ColouredCliques CompleteJohnson
open SparseGram (resources)

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The number of blocks in a decomposition when the order is admissible. -/
def blockMass (n q : ℕ) : ℝ :=
  (Fintype.card (Edge n) : ℝ) / (q.choose 2 : ℝ)

/-- The type of a uniformly drawn q-clique of the complete graph. -/
def finiteTypeLaw {n q : ℕ} (colour : Fin n → C) (t : TypeProfile C q) : ℝ :=
  ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ) / (n.choose q : ℝ)

/-- The type law of q independent colours. -/
def multinomialTypeLaw {q : ℕ} (p : C → ℝ) (t : TypeProfile C q) : ℝ :=
  (q.factorial : ℝ) * ∏ c, p c ^ (t.val c : ℕ) / ((t.val c : ℕ).factorial : ℝ)

theorem finiteTypeLaw_nonneg {n q : ℕ} (colour : Fin n → C) (t : TypeProfile C q) :
    0 ≤ finiteTypeLaw colour t := by unfold finiteTypeLaw; positivity

omit [DecidableEq C] in
theorem multinomialTypeLaw_pos {q : ℕ} {p : C → ℝ} (hp : ∀ c, 0 < p c)
    (t : TypeProfile C q) : 0 < multinomialTypeLaw p t := by
  unfold multinomialTypeLaw
  exact mul_pos (by positivity) (prod_pos fun c _ => div_pos (pow_pos (hp c) _) (by positivity))

theorem sum_finiteTypeLaw {n q : ℕ} (hn : q ≤ n) (colour : Fin n → C) :
    ∑ t : TypeProfile C q, finiteTypeLaw colour t = 1 := by
  classical
  have hcard : Fintype.card (Clique n q) = n.choose q := by
    simp [Fintype.card_coe]
  have hs : (∑ t : TypeProfile C q, ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ)) =
      (n.choose q : ℝ) := by
    have h := sum_fiberwise (univ : Finset (Clique n q)) (cliqueType colour)
      (fun _ => (1 : ℝ))
    simpa only [ProfileWeights.fibre, sum_const, nsmul_eq_mul, mul_one, card_univ, hcard] using h
  simp only [finiteTypeLaw, ← sum_div, hs]
  exact div_self (by exact_mod_cast (Nat.choose_pos hn).ne')

private theorem uniform_load {n q : ℕ} (hq : 2 ≤ q) (hn : q ≤ n) (e : Edge n) :
    WeightedEnergy.load (resources n q)
        (fun _ : Clique n q => 1 / ((n - 2).choose (q - 2) : ℝ)) e = 1 := by
  classical
  have he : (e : Finset (Fin n)).card = 2 := (mem_powersetCard.mp e.property).2
  have hm := CliqueGram.multiplicity_eq_choose q (e : Finset (Fin n)) e (by
    simpa only [union_idempotent, he] using hq)
  simp only [CliqueGram.multiplicity, and_self, union_idempotent, he, Fintype.card_fin] at hm
  have hd : (0 : ℝ) < ((n - 2).choose (q - 2) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : q - 2 ≤ n - 2)
  change (∑ b : Clique n q,
    if e ∈ resources n q b then 1 / ((n - 2).choose (q - 2) : ℝ) else 0) = 1
  simp only [resources, mem_filter, mem_univ, true_and]
  rw [sum_coe_sort ((univ : Finset (Fin n)).powersetCard q)
    (fun b : Finset (Fin n) => if (e : Finset (Fin n)) ⊆ b then
      (1 : ℝ) / ((n - 2).choose (q - 2) : ℝ) else 0), ← sum_filter]
  simp only [sum_const, nsmul_eq_mul, hm, one_div, mul_inv_cancel₀ hd.ne']

/-- Scaling the uniform clique law by the block mass gives the host's
exact unordered pair margins, expressed using a representative edge. -/
theorem finiteTypeLaw_physical_margin {n q : ℕ} (hq : 2 ≤ q) (hn : q ≤ n)
    (colour : Fin n → C) (e : Edge n) :
    pairMargin colour (fun t : TypeProfile C q => blockMass n q * finiteTypeLaw colour t) e =
      (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ) := by
  classical
  let d : ℝ := ((n - 2).choose (q - 2) : ℝ)
  have hscale : blockMass n q * d = (n.choose q : ℝ) :=
    PhysicalCompletion.complete_clique_mass hq
  have hd : 0 < d := by
    dsimp only [d]
    exact_mod_cast Nat.choose_pos (by omega : q - 2 ≤ n - 2)
  have hnq : (0 : ℝ) < n.choose q := by exact_mod_cast Nat.choose_pos hn
  have hw : (fun t => blockMass n q * finiteTypeLaw colour t) =
      ProfileBalance.histogram colour (fun _ : Clique n q => 1 / d) := by
    funext t
    simp only [finiteTypeLaw, ProfileBalance.histogram, sum_const, nsmul_eq_mul]
    rw [← mul_div_assoc, ← mul_div_assoc, mul_one]
    apply (div_eq_div_iff hnq.ne' hd.ne').mpr
    rw [← hscale]
    ring
  rw [hw, ProfileBalance.margin_histogram]
  simp_rw [show ∀ f : Edge n, WeightedEnergy.load (resources n q)
      (fun _ : Clique n q => 1 / d) f = 1 from uniform_load hq hn, one_mul, sum_boole]
  have hf : (univ.filter fun f : Edge n => profile colour (f : Finset (Fin n)) =
      profile colour (e : Finset (Fin n))) = ProfileWeights.fibre (cliqueType colour) (cliqueType colour e) := by
    ext f
    simp only [ProfileWeights.fibre, mem_filter, mem_univ, true_and]
    exact (cliqueType_eq colour f (cliqueType colour e)).symm
  rw [hf, fibre_card]
  rfl

/-- The matrix identity used to transport a limiting profile to the
finite affine space of compatible quotas. -/
theorem finiteTypeLaw_pair_margins {n q : ℕ} (hq : 2 ≤ q) (hn : q ≤ n)
    (colour : Fin n → C) (hclasses : ∀ c, 2 ≤ profile colour univ c) (i j : C) :
    ∑ t : TypeProfile C q, ((∏ c, (t.val c : ℕ).choose (SlotPairMargins.demand i j c) : ℕ) : ℝ) *
      (blockMass n q * finiteTypeLaw colour t) = (cliques colour univ (SlotPairMargins.demand i j) : ℝ) := by
  obtain ⟨e, he⟩ := SlotPairMargins.exists_edge_demand colour hclasses i j
  simpa only [pairMargin, he] using finiteTypeLaw_physical_margin hq hn colour e

/-- The same identity for the ordered pair counts used by quota rounding. -/
theorem finiteTypeLaw_ordered_margins {n q : ℕ} (hq : 2 ≤ q) (hn : q ≤ n)
    (colour : Fin n → C) (hclasses : ∀ c, 2 ≤ profile colour univ c) (i j : C) :
    ∑ t : TypeProfile C q, (blockMass n q * finiteTypeLaw colour t) *
      (SlotPairMargins.orderedCount t i j : ℝ) =
      ((if i = j then 2 else 1 : ℕ) : ℝ) *
        (cliques colour univ (SlotPairMargins.demand i j) : ℝ) := by
  obtain ⟨e, he⟩ := SlotPairMargins.exists_edge_demand colour hclasses i j
  rw [← SlotPairMargins.physical_margin_mul colour _ e i j he,
    finiteTypeLaw_physical_margin hq hn, he]

/-- A fixed lower index in a binomial coefficient gives a polynomial
limit after dividing by the corresponding power of the ambient size. -/
theorem tendsto_scaled_choose_of_le {l : Filter ℕ} (hl : l ≤ atTop)
    (a : ℕ → ℕ) (k : ℕ) {p : ℝ} (hp : 0 < p)
    (h : Tendsto (fun n => (a n : ℝ) / n) l (𝓝 p)) :
    Tendsto (fun n : ℕ => (Nat.choose (a n) k : ℝ) / (n : ℝ) ^ k)
      l (𝓝 (p ^ k / (k.factorial : ℝ))) := by
  have ha : ∀ᶠ n in l, k ≤ a n := by
    filter_upwards [(tendsto_order.1 h).1 (p / 2) (by linarith),
      hl (eventually_ge_atTop (max 1 ⌈(k : ℝ) / (p / 2)⌉₊))] with n hn hlarge
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      ((le_max_left _ _).trans hlarge))
    have hkn : (k : ℝ) / (p / 2) ≤ n := (Nat.le_ceil _).trans (by
      exact_mod_cast (le_max_right _ _).trans hlarge)
    have hka : (k : ℝ) ≤ (a n : ℝ) :=
      ((div_le_iff₀ (by positivity)).mp hkn).trans
        (by simpa only [mul_comm] using ((lt_div_iff₀ hn0).mp hn).le)
    exact_mod_cast hka
  have hfactor : Tendsto
      (fun n : ℕ => ∏ i ∈ range k, ((a n : ℝ) / n - (i : ℝ) / n))
      l (𝓝 (p ^ k)) := by
    have hh := tendsto_finsetProd (range k) (fun i _ =>
      h.sub ((tendsto_const_div_atTop_nhds_zero_nat (i : ℝ)).mono_left hl))
    simpa only [sub_zero, prod_const, card_range] using hh
  apply (hfactor.div_const (k.factorial : ℝ)).congr'
  filter_upwards [ha] with n hn
  have hprod : (∏ i ∈ range k, ((a n : ℝ) - (i : ℝ))) =
      (k.factorial : ℝ) * (Nat.choose (a n) k : ℝ) := by
    rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
      Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    apply prod_congr rfl
    intro i hi
    exact (Nat.cast_sub ((mem_range.mp hi).le.trans hn)).symm
  simp_rw [← sub_div]
  rw [prod_div_distrib, prod_const, card_range, hprod]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  rw [mul_div_assoc, mul_comm (k.factorial : ℝ), mul_div_assoc, div_self hk, mul_one]

/-- The finite coloured clique law converges to the multinomial law when
the class proportions converge to strictly positive limits. -/
theorem tendsto_finiteTypeLaw_of_le {l : Filter ℕ} (hl : l ≤ atTop) {q : ℕ}
    (colour : (n : ℕ) → Fin n → C) (p : C → ℝ)
    (hp : ∀ c, 0 < p c) (h : ∀ c, Tendsto (fun n =>
      (profile (colour n) univ c : ℝ) / n) l (𝓝 (p c))) :
    Tendsto (fun n => finiteTypeLaw (q := q) (colour n)) l
      (𝓝 (multinomialTypeLaw p)) := by
  apply tendsto_pi_nhds.mpr
  intro t
  have hnum := tendsto_finsetProd (univ : Finset C) (fun c _ =>
    tendsto_scaled_choose_of_le hl (fun n => profile (colour n) univ c) (t.val c) (hp c) (h c))
  have hn : Tendsto (fun n : ℕ => (n : ℝ) / n) l (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hl (eventually_ne_atTop 0)] with n hn
    exact (div_self (by exact_mod_cast hn : (n : ℝ) ≠ 0)).symm
  have hden := tendsto_scaled_choose_of_le hl id q one_pos hn
  simp only [id_eq, one_pow] at hden
  have hfac : (q.factorial : ℝ) ≠ 0 := by positivity
  have hlim := hnum.div hden (one_div_ne_zero hfac)
  have hlim' : Tendsto (fun n : ℕ => (∏ c,
      (Nat.choose (profile (colour n) univ c) (t.val c) : ℝ) / (n : ℝ) ^ (t.val c : ℕ)) /
      ((n.choose q : ℝ) / (n : ℝ) ^ q)) l (𝓝 (multinomialTypeLaw p t)) := by
    convert hlim using 1
    unfold multinomialTypeLaw
    rw [div_div_eq_mul_div, div_one, mul_comm]
  apply hlim'.congr'
  filter_upwards [hl (eventually_ne_atTop 0)] with n hn
  unfold finiteTypeLaw
  rw [fibre_card, cliques, Nat.cast_prod, prod_div_distrib, prod_pow_eq_pow_sum, t.property]
  exact div_div_div_cancel_right₀ (pow_ne_zero q (by exact_mod_cast hn : (n : ℝ) ≠ 0)) _ _

theorem tendsto_scaled_choose (a : ℕ → ℕ) (k : ℕ) {p : ℝ} (hp : 0 < p)
    (h : Tendsto (fun n => (a n : ℝ) / n) atTop (𝓝 p)) :
    Tendsto (fun n : ℕ => (Nat.choose (a n) k : ℝ) / (n : ℝ) ^ k)
      atTop (𝓝 (p ^ k / (k.factorial : ℝ))) :=
  tendsto_scaled_choose_of_le le_rfl a k hp h

theorem tendsto_finiteTypeLaw {q : ℕ} (colour : (n : ℕ) → Fin n → C) (p : C → ℝ)
    (hp : ∀ c, 0 < p c) (h : ∀ c, Tendsto (fun n =>
      (profile (colour n) univ c : ℝ) / n) atTop (𝓝 (p c))) :
    Tendsto (fun n => finiteTypeLaw (q := q) (colour n)) atTop (𝓝 (multinomialTypeLaw p)) :=
  tendsto_finiteTypeLaw_of_le le_rfl colour p hp h

end KqR75.ProfileLDP

#print axioms KqR75.ProfileLDP.finiteTypeLaw_nonneg
#print axioms KqR75.ProfileLDP.multinomialTypeLaw_pos
#print axioms KqR75.ProfileLDP.sum_finiteTypeLaw
#print axioms KqR75.ProfileLDP.finiteTypeLaw_physical_margin
#print axioms KqR75.ProfileLDP.finiteTypeLaw_pair_margins
#print axioms KqR75.ProfileLDP.finiteTypeLaw_ordered_margins
#print axioms KqR75.ProfileLDP.tendsto_scaled_choose
#print axioms KqR75.ProfileLDP.tendsto_finiteTypeLaw
