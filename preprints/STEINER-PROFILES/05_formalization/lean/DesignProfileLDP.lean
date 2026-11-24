module
public import DesignProfileRates
public import QuotaRounding

@[expose] public section
noncomputable section
namespace KqR75.ProfileLDP

open Finset Filter Topology ColouredCliques CompleteJohnson PhysicalCompletion SlotPairMargins

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The pair-margin matrix with ordered pairs, including twice the same-colour margin. -/
def orderedMargins (q : ℕ) : (TypeProfile C q → ℝ) →ₗ[ℝ] (C → C → ℝ) where
  toFun Q i j := ∑ t, Q t * (orderedCount t i j : ℝ)
  map_add' X Y := by
    funext i j
    simp [add_mul, sum_add_distrib]
  map_smul' a X := by
    funext i j
    simp [mul_assoc, Finset.mul_sum]

theorem continuous_orderedMargins (q : ℕ) :
    Continuous (orderedMargins q : (TypeProfile C q → ℝ) → C → C → ℝ) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact continuous_finsetSum _ fun t _ => (continuous_apply t).mul continuous_const

/-- Equality of ordered margins is the pair-multiset equation of the manuscript. -/
theorem orderedMargins_eq_iff {q : ℕ} (P Q : TypeProfile C q → ℝ) :
    orderedMargins q Q = orderedMargins q P ↔
      ∀ i j : C, (∑ t, Q t * ((∏ c, (t.val c : ℕ).choose (demand i j c) : ℕ) : ℝ)) =
        ∑ t, P t * ((∏ c, (t.val c : ℕ).choose (demand i j c) : ℕ) : ℝ) := by
  have hrow (X : TypeProfile C q → ℝ) (i j : C) :
      orderedMargins q X i j =
        ((if i = j then 2 else 1 : ℕ) : ℝ) *
          ∑ t, X t * ((∏ c, (t.val c : ℕ).choose (demand i j c) : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro t _
    have he : ((if i = j then 2 else 1 : ℕ) : ℝ) *
        ((∏ c, (t.val c : ℕ).choose (demand i j c) : ℕ) : ℝ) = (orderedCount t i j : ℝ) := by
      exact_mod_cast orderedCount_demand t i j
    rw [← he]
    ring
  constructor
  · intro h i j
    have he := congrFun (congrFun h i) j
    rw [hrow, hrow] at he
    have hn : ((if i = j then 2 else 1 : ℕ) : ℝ) ≠ 0 := by split_ifs <;> norm_num
    exact mul_left_cancel₀ hn he
  · intro h
    funext i j
    rw [hrow, hrow, h i j]

/-- Probability profiles with the same pair margins as the limiting reference law. -/
def feasible {q : ℕ} (P : TypeProfile C q → ℝ) : Set (TypeProfile C q → ℝ) :=
  {Q | Q ∈ Set.Icc 0 1 ∧ (∑ t, Q t) = 1 ∧ orderedMargins q Q = orderedMargins q P}

private def defect {q : ℕ} (P Q : TypeProfile C q → ℝ) : ℝ :=
  |(∑ t, Q t) - 1| + ‖orderedMargins q Q - orderedMargins q P‖

private theorem continuous_defect {q : ℕ} (P : TypeProfile C q → ℝ) : Continuous (defect P) :=
  ((continuous_finsetSum _ fun t _ => continuous_apply t).sub continuous_const).abs.add
    ((continuous_orderedMargins q).sub continuous_const).norm

private theorem defect_nonneg {q : ℕ} (P Q : TypeProfile C q → ℝ) : 0 ≤ defect P Q :=
  add_nonneg (abs_nonneg _) (norm_nonneg _)

private theorem mem_feasible_iff {q : ℕ} {P Q : TypeProfile C q → ℝ} :
    Q ∈ feasible P ↔ Q ∈ Set.Icc 0 1 ∧ defect P Q = 0 := by
  unfold feasible defect
  simp only [Set.mem_ofPred_eq, add_eq_zero_iff_of_nonneg (abs_nonneg _) (norm_nonneg _),
    abs_eq_zero, norm_eq_zero, sub_eq_zero]

private theorem feasible_mix {q : ℕ} {P Q : TypeProfile C q → ℝ}
    (hP : P ∈ feasible P) (hQ : Q ∈ feasible P) {s : ℝ} (hs : 0 ≤ s) (hs' : s ≤ 1) :
    (fun t => (1 - s) * Q t + s * P t) ∈ feasible P := by
  rcases hP with ⟨hPb, hPsum, _⟩
  rcases hQ with ⟨hQb, hQsum, hQm⟩
  have hs₁ : 0 ≤ 1 - s := sub_nonneg.mpr hs'
  refine ⟨⟨fun t => add_nonneg (mul_nonneg hs₁ (hQb.1 t)) (mul_nonneg hs (hPb.1 t)),
    fun t => ?_⟩, ?_, ?_⟩
  · linarith [mul_le_mul_of_nonneg_left (hQb.2 t) hs₁, mul_le_mul_of_nonneg_left (hPb.2 t) hs]
  · simp only [sum_add_distrib, ← mul_sum, hPsum, hQsum, mul_one, sub_add_cancel]
  · change orderedMargins q ((1 - s) • Q + s • P) = _
    rw [map_add, map_smul, map_smul, hQm, ← add_smul, sub_add_cancel, one_smul]

private theorem eventually_classes {q : ℕ} {colour : (n : ℕ) → Fin n → C} {p : C → ℝ}
    (hp : ∀ c, 0 < p c)
    (hcolour : ∀ c, Tendsto (fun n => (profile (colour n) univ c : ℝ) / n)
      (admissibleOrders q) (𝓝 (p c))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ n : ℕ in admissibleOrders q,
      (∀ c, ρ * (n : ℝ) ≤ (profile (colour n) univ c : ℝ)) ∧
      ∀ c, q ≤ profile (colour n) univ c := by
  classical
  have hpos : ∃ ρ : ℝ, 0 < ρ ∧ ∀ c, ρ < p c := by
    by_cases hC : Nonempty C
    · let _ := hC
      obtain ⟨c, _, hc⟩ := exists_min_image univ p univ_nonempty
      exact ⟨p c / 2, half_pos (hp c), fun i => (half_lt_self (hp c)).trans_le
        (hc i (mem_univ i))⟩
    · exact ⟨1, one_pos, fun c => (hC ⟨c⟩).elim⟩
  obtain ⟨ρ, hρ, hρp⟩ := hpos
  have hρn : ∀ᶠ n in admissibleOrders q, ∀ c, ρ < (profile (colour n) univ c : ℝ) / n :=
    eventually_all.mpr fun c => (hcolour c).eventually (Ioi_mem_nhds (hρp c))
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl : admissibleOrders q ≤ atTop := inf_le_left
  refine ⟨ρ, hρ, ?_⟩
  filter_upwards [hρn, hl (eventually_ge_atTop 1),
    hl ((tendsto_atTop.mp hnat) ((q : ℝ) / ρ))] with n hc hn hnρ
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hclass (c : C) : ρ * (n : ℝ) ≤ (profile (colour n) univ c : ℝ) :=
    ((lt_div_iff₀ hn').mp (hc c)).le
  refine ⟨hclass, fun c => ?_⟩
  have hq' : (q : ℝ) ≤ ρ * n := by
    simpa only [mul_comm] using (div_le_iff₀ hρ).mp hnρ
  exact_mod_cast hq'.trans (hclass c)

private theorem histogram_ordered {n q : ℕ} (colour : Fin n → C) {D : Finset (Clique n q)}
    (hD : D ∈ designs q n) (hclass : ∀ c, 2 ≤ profile colour univ c) (i j : C) :
    orderedMargins q (fun t => (BankCapacity.integerHistogram colour D t : ℝ)) i j =
      ((if i = j then 2 else 1 : ℕ) : ℝ) * (cliques colour univ (demand i j) : ℝ) := by
  obtain ⟨e, he⟩ := exists_edge_demand colour hclass i j
  change (∑ t, (BankCapacity.integerHistogram colour D t : ℝ) * (orderedCount t i j : ℝ)) = _
  rw [← physical_margin_mul colour _ e i j he, histogram_margin colour hD, he]

private theorem profileOf_ordered {n q : ℕ} (q₂ : 2 ≤ q) (hn : q ≤ n) (colour : Fin n → C)
    {D : Finset (Clique n q)} (hD : D ∈ designs q n)
    (hclass : ∀ c, 2 ≤ profile colour univ c) :
    orderedMargins q (profileOf colour D) = orderedMargins q (finiteTypeLaw colour) := by
  funext i j
  have hB := blockMass_pos (q₂.trans hn) q₂
  apply (mul_right_inj' hB.ne').mp
  calc
    _ = orderedMargins q (fun t => (BankCapacity.integerHistogram colour D t : ℝ)) i j := by
      change blockMass n q * (∑ t, profileOf colour D t * (orderedCount t i j : ℝ)) = _
      rw [Finset.mul_sum]
      simp only [profileOf, normalizedQuota, orderedMargins, LinearMap.coe_mk, AddHom.coe_mk]
      exact sum_congr rfl fun t _ => by rw [← mul_assoc, mul_div_cancel₀ _ hB.ne']
    _ = _ := by
      rw [histogram_ordered colour hD hclass]
      simpa only [orderedMargins, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum, mul_assoc] using
        (finiteTypeLaw_ordered_margins q₂ hn colour hclass i j).symm

private theorem recover_quotas {q : ℕ} (hq : 3 ≤ q) [Nonempty C]
    (colour : (n : ℕ) → Fin n → C) {P Q : TypeProfile C q → ℝ}
    (hP : Tendsto (fun n => finiteTypeLaw (colour n)) (admissibleOrders q) (𝓝 P))
    (hQ : Q ∈ feasible P)
    (hclasses : ∀ᶠ n in admissibleOrders q, ∀ c, 2 ≤ profile (colour n) univ c) :
    ∃ m : ℕ → TypeProfile C q → ℤ,
      Tendsto (fun n => normalizedQuota n (m n)) (admissibleOrders q) (𝓝 Q) ∧
      ∀ᶠ n in admissibleOrders q, ExactPairMargins (colour n) (m n) := by
  classical
  have hq₂ : 2 ≤ q := by omega
  let ref : C := Classical.choice (inferInstance : Nonempty C)
  obtain ⟨p, hqp, hp⟩ := Nat.exists_infinite_primes q
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let emb : Fin q ↪ Fin p :=
    ⟨fun i => ⟨i.val, i.isLt.trans_le hqp⟩, fun _ _ hi => Fin.ext (congrArg (fun i : Fin p => i.val) hi)⟩
  let s := emb.trans (ZMod.finEquiv p).toEquiv.toEmbedding
  obtain ⟨L, hL, hround⟩ := round_quotas hq₂ s s.injective ref
  let q' (n : ℕ) (t : TypeProfile C q) := finiteTypeLaw (colour n) t + (Q t - P t)
  let x (n : ℕ) (t : TypeProfile C q) := blockMass n q * q' n t
  let Good (n : ℕ) (m : TypeProfile C q → ℤ) :=
    ExactPairMargins (colour n) m ∧ ∀ t, |(m t : ℝ) - x n t| ≤ L
  have hex : ∀ᶠ n in admissibleOrders q, ∃ m, Good n m := by
    filter_upwards [eventually_total_designs hq one_pos, hclasses,
      (show admissibleOrders q ≤ atTop from inf_le_left) (eventually_ge_atTop q)] with n hn hclass hnq
    obtain ⟨D, hD⟩ := card_pos.mp hn.1
    let m₀ := BankCapacity.integerHistogram (colour n) D
    have hsame : orderedMargins q (x n) = orderedMargins q (fun t => (m₀ t : ℝ)) := by
      change orderedMargins q (blockMass n q • (finiteTypeLaw (colour n) + (Q - P))) = _
      rw [map_smul, map_add, map_sub, hQ.2.2, sub_self, add_zero]
      funext i j
      exact (by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [histogram_ordered (colour n) hD hclass]
        simpa only [orderedMargins, LinearMap.coe_mk, AddHom.coe_mk, Finset.mul_sum, mul_assoc] using
          finiteTypeLaw_ordered_margins hq₂ hnq (colour n) hclass i j)
    have hzero (i j : C) :
        ∑ t, (x n t - (m₀ t : ℝ)) * (orderedCount t i j : ℝ) = 0 := by
      change orderedMargins q (x n - fun t => (m₀ t : ℝ)) i j = _
      rw [map_sub, hsame, sub_self]
      rfl
    obtain ⟨m, hm, hdiff⟩ := hround m₀ (x n) hzero
    refine ⟨m, (exactPairMargins_iff (colour n) m hclass).mpr fun e => ?_, hdiff⟩
    have he : pairMargin (colour n) (fun t => ((m t - m₀ t : ℤ) : ℝ)) e = 0 :=
      physical_margin_zero _ _ (fun i j => by exact_mod_cast hm i j) e
    have hlinear : pairMargin (colour n) (fun t => (m t : ℝ)) e -
        pairMargin (colour n) (fun t => (m₀ t : ℝ)) e = 0 := by
      simpa only [pairMargin, Int.cast_sub, mul_sub, sum_sub_distrib] using he
    exact (sub_eq_zero.mp hlinear).trans (histogram_margin (colour n) hD e)
  let m (n : ℕ) := if h : ∃ m, Good n m then h.choose else 0
  have hm : ∀ᶠ n in admissibleOrders q, Good n (m n) :=
    hex.mono fun n hn => by simpa only [m, dite_eq_left hn] using hn.choose_spec
  refine ⟨m, tendsto_pi_nhds.mpr fun t => ?_, hm.mono fun _ hn => hn.1⟩
  have hlim : Tendsto (fun n => q' n t) (admissibleOrders q) (𝓝 (Q t)) := by
    have he : P t + (Q t - P t) = Q t := by ring
    simpa only [q', he] using (tendsto_pi_nhds.mp hP t).add_const (Q t - P t)
  have hLlim : Tendsto (fun n => L / blockMass n q) (admissibleOrders q) (𝓝 0) :=
    (tendsto_blockMass hq₂).const_div_atTop L |>.mono_left inf_le_left
  have hdiff : ∀ᶠ n in admissibleOrders q, |normalizedQuota n (m n) t - q' n t| ≤ L / blockMass n q := by
    filter_upwards [hm, (show admissibleOrders q ≤ atTop from inf_le_left) (eventually_ge_atTop 2)]
      with n hn hn₂
    have hB := blockMass_pos hn₂ hq₂
    have he : ((m n t : ℝ) - x n t) / blockMass n q = normalizedQuota n (m n) t - q' n t := by
      change ((m n t : ℝ) - blockMass n q * q' n t) / blockMass n q = _
      rw [sub_div, mul_div_cancel_left₀ _ hB.ne']
      rfl
    rw [← he, abs_div, abs_of_pos hB]
    exact div_le_div_of_nonneg_right (hn.2 t) hB.le
  have hl := hlim.sub hLlim
  have hu := hlim.add hLlim
  simp only [sub_zero, add_zero] at hl hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
    (hdiff.mono fun n hn => by linarith [(abs_le.mp hn).1])
    (hdiff.mono fun n hn => by linarith [(abs_le.mp hn).2])

private theorem reference_feasible {q : ℕ} (hq : 2 ≤ q)
    (colour : (n : ℕ) → Fin n → C) {P : TypeProfile C q → ℝ}
    (hP : Tendsto (fun n => finiteTypeLaw (colour n)) (admissibleOrders q) (𝓝 P))
    (hpos : ∀ t, 0 < P t) : P ∈ feasible P := by
  let _ := admissibleOrders_neBot q hq
  have hsum : (∑ t, P t) = 1 := by
    apply tendsto_nhds_unique (tendsto_finsetSum _ fun t _ => tendsto_pi_nhds.mp hP t)
    apply tendsto_const_nhds.congr'
    filter_upwards [(show admissibleOrders q ≤ atTop from inf_le_left) (eventually_ge_atTop q)] with n hn
    exact (sum_finiteTypeLaw hn (colour n)).symm
  refine ⟨⟨fun t => (hpos t).le, fun t => ?_⟩, hsum, rfl⟩
  exact (single_le_sum (fun i _ => (hpos i).le) (mem_univ t)).trans_eq hsum

private theorem eventually_reference_pos {q : ℕ}
    (colour : (n : ℕ) → Fin n → C) {P : TypeProfile C q → ℝ}
    (hP : Tendsto (fun n => finiteTypeLaw (colour n)) (admissibleOrders q) (𝓝 P))
    (hpos : ∀ t, 0 < P t) :
    ∀ᶠ n in admissibleOrders q, ∀ t : TypeProfile C q, 0 < finiteTypeLaw (colour n) t :=
  eventually_all.mpr fun t => (tendsto_pi_nhds.mp hP t).eventually (Ioi_mem_nhds (hpos t))

private theorem eventually_upper_profiles {q : ℕ} (hq : 3 ≤ q)
    (colour : (n : ℕ) → Fin n → C) {P : TypeProfile C q → ℝ}
    (hP : Tendsto (fun n => finiteTypeLaw (colour n)) (admissibleOrders q) (𝓝 P))
    (hpos : ∀ t, 0 < P t) {ρ : ℝ} (hρ : 0 < ρ)
    (hclasses : ∀ᶠ n : ℕ in admissibleOrders q, ∀ c, ρ * (n : ℝ) ≤ (profile (colour n) univ c : ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in admissibleOrders q, ∀ Q ∈ profiles (colour n),
      profileCount (colour n) {Q} ≤ ((designs q n).card : ℝ) *
        Real.exp (-(blockMass n q * (KL Q P - ε))) := by
  have hq₂ : 2 ≤ q := by omega
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨L, _, hUp⟩ := UpperCounting.eventually_card_designFibre_upper_entropy (C := C) q hq ρ hρ
  have hl : admissibleOrders q ≤ atTop := inf_le_left
  filter_upwards [hl hUp, hclasses, hl (eventually_ge_atTop 2),
    hl (eventually_upper_budget hq L hδ), eventually_total_designs hq hδ,
    eventually_reference_pos colour hP hpos, eventually_sum_log_le hP (fun t => (hpos t).ne') hδ]
    with n hu hclass hn hbudget htotal hPn hlog
  intro Q hQ
  obtain ⟨D, hD, rfl⟩ := mem_profiles.mp hQ
  let m := BankCapacity.integerHistogram (colour n) D
  let Q := profileOf (colour n) D
  have hB := blockMass_pos hn hq₂
  have hv := hu (colour n) m hclass (histogram_margin (colour n) hD)
  change ((designFibre (colour n) m).card : ℝ) ≤ Real.exp
    (blockMass n q * (baseline q n - KL Q (finiteTypeLaw (colour n))) +
      L * (n : ℝ) ^ (2 - 1 / ((q.choose 2 - 1 : ℕ) : ℝ))) at hv
  have hdiff : KL Q P ≤ KL Q (finiteTypeLaw (colour n)) + δ := by
    rw [KL_eq_KLf (fun t => (hpos t).ne'), KL_eq_KLf (fun t => (hPn t).ne')]
    have h := (abs_KLf_sub_le (profileOf_box hq₂ hn (colour n) hD) P
      (finiteTypeLaw (colour n))).trans hlog
    linarith only [(abs_le.mp h).1]
  change profileCount (colour n) {normalizedQuota n m} ≤ _
  rw [profileCount_singleton _ _ hB.ne']
  refine hv.trans ?_
  calc
    _ ≤ Real.exp (blockMass n q * (baseline q n - δ)) *
        Real.exp (-(blockMass n q * (KL Q P - ε))) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hh := mul_le_mul_of_nonneg_left hdiff hB.le
      dsimp only [δ] at hh hbudget ⊢
      linarith only [hh, hbudget]
    _ ≤ _ := mul_le_mul_of_nonneg_right htotal.2.1 (Real.exp_pos _).le

private theorem eventually_lower_profiles {q : ℕ} (hq : 3 ≤ q) [Nonempty C]
    (colour : (n : ℕ) → Fin n → C) {P Q : TypeProfile C q → ℝ}
    (hP : Tendsto (fun n => finiteTypeLaw (colour n)) (admissibleOrders q) (𝓝 P))
    (hpos : ∀ t, 0 < P t) {ρ : ℝ} (hρ : 0 < ρ)
    (hclasses : ∀ᶠ n : ℕ in admissibleOrders q,
      (∀ c, ρ * (n : ℝ) ≤ (profile (colour n) univ c : ℝ)) ∧
      ∀ c, q ≤ profile (colour n) univ c)
    (hQ : Q ∈ feasible P) (hQpos : ∀ t, 0 < Q t)
    {ε : ℝ} (hε : 0 < ε) {V : Set (TypeProfile C q → ℝ)} (hV : V ∈ 𝓝 Q) :
    ∀ᶠ n in admissibleOrders q, ∃ Q' ∈ profiles (colour n), Q' ∈ V ∧
      ((designs q n).card : ℝ) * Real.exp (-(blockMass n q * (KL Q P + ε))) ≤
        profileCount (colour n) {Q'} := by
  classical
  let δ := ε / 3
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let _ : Nonempty (TypeProfile C q) := ⟨SlotProfiles.slotType fun _ =>
    Classical.choice (inferInstance : Nonempty C)⟩
  obtain ⟨t₀, _, ht₀⟩ := exists_min_image univ Q univ_nonempty
  let κ := Q t₀ / 2
  have hκ : 0 < κ := half_pos (hQpos t₀)
  have hκQ (t : TypeProfile C q) : κ < Q t :=
    (half_lt_self (hQpos t₀)).trans_le (ht₀ t (mem_univ t))
  obtain ⟨m, hm, hmarg⟩ := recover_quotas hq colour hP hQ
    (hclasses.mono fun _ hn c => (by omega : 2 ≤ q).trans (hn.2 c))
  obtain ⟨L, _, hLow⟩ := eventually_designFibre_bilateral (C := C) q hq ρ κ hρ hκ
  have hκm : ∀ᶠ n in admissibleOrders q, ∀ t, κ < normalizedQuota n (m n) t :=
    eventually_all.mpr fun t => (tendsto_pi_nhds.mp hm t).eventually (Ioi_mem_nhds (hκQ t))
  have hKL := (tendsto_KLf hm hP (fun t => (hpos t).ne')).eventually
    (Iio_mem_nhds (show KLf Q P < KLf Q P + δ by linarith))
  have hl : admissibleOrders q ≤ atTop := inf_le_left
  have had : ∀ᶠ n in admissibleOrders q, admissible q n :=
    eventually_inf_principal.mpr (Eventually.of_forall fun _ h => h)
  filter_upwards [hl hLow, hclasses, hmarg, hκm, hl (eventually_ge_atTop 2), had,
    hl (eventually_lower_budget hq L hδ), eventually_total_designs hq hδ,
    eventually_reference_pos colour hP hpos, hKL, hm.eventually hV]
    with n hc hclass hmargin hκ' hn hnAd hbudget htotal hPn hEnt hmem
  have hB := blockMass_pos (q := q) hn (by omega)
  have hκm' : ∀ t, κ * blockMass n q ≤ (m n t : ℝ) :=
    fun t => ((lt_div_iff₀ hB).mp (hκ' t)).le
  obtain ⟨hp, hlo, _⟩ := hc (colour n) (m n) hclass.1 hmargin hκm' hnAd.1 hnAd.2
  let Q' := normalizedQuota n (m n)
  change blockMass n q * (baseline q n - KL Q' (finiteTypeLaw (colour n))) -
    L * ((n : ℝ) ^ (2 - GreedyScales.criticalExponent q) * Real.log n) ≤
      Real.log ((designFibre (colour n) (m n)).card : ℝ) at hlo
  obtain ⟨D, hD⟩ := card_pos.mp hp
  obtain ⟨hpacks, hhist⟩ := (mem_designFibre _ _ _).mp hD
  have hQ' : profileOf (colour n) D = Q' := by
    funext t
    simp only [Q', profileOf, normalizedQuota, hhist t]
  have hpR : 0 < ((designFibre (colour n) (m n)).card : ℝ) := by exact_mod_cast hp
  refine ⟨Q', mem_profiles.mpr ⟨D, mem_designs.mpr hpacks, hQ'⟩, hmem, ?_⟩
  rw [profileCount_singleton _ _ hB.ne']
  calc
    _ ≤ Real.exp (blockMass n q * (baseline q n + δ)) *
        Real.exp (-(blockMass n q * (KL Q P + ε))) :=
      mul_le_mul_of_nonneg_right htotal.2.2 (Real.exp_pos _).le
    _ ≤ Real.exp (blockMass n q * (baseline q n - KL Q' (finiteTypeLaw (colour n))) -
        L * ((n : ℝ) ^ (2 - GreedyScales.criticalExponent q) * Real.log n)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have ht : KL Q' (finiteTypeLaw (colour n)) ≤ KL Q P + δ := by
        rw [KL_eq_KLf (fun t => (hPn t).ne'), KL_eq_KLf (fun t => (hpos t).ne')]
        exact hEnt.le
      have hh := mul_le_mul_of_nonneg_left ht hB.le
      dsimp only [δ] at hh hbudget ⊢
      linarith only [hh, hbudget]
    _ ≤ _ := (Real.le_log_iff_exp_le hpR).mp hlo

/-- Corollary 10.1. The uniform measure on labelled designs has a profile LDP
at speed blockMass. The counting inequalities give the probability inequalities
by eventual positivity of the total count. -/
theorem designProfileLDP {q : ℕ} (hq : 3 ≤ q) [Nonempty C]
    (colour : (n : ℕ) → Fin n → C) (p : C → ℝ) (hp : ∀ c, 0 < p c)
    (hcolour : ∀ c, Tendsto (fun n => (profile (colour n) univ c : ℝ) / n)
      (admissibleOrders q) (𝓝 (p c))) :
    let P : TypeProfile C q → ℝ := multinomialTypeLaw p
    CountLDP (admissible q) (fun n => (designs q n).card)
      (fun n => profileCount (colour n)) (fun n => blockMass n q) (feasible P) (fun Q => KL Q P) ∧
    (∀ᶠ n in admissibleOrders q, 0 < (designs q n).card) ∧
    ∀ a : ℝ, IsCompact {Q | Q ∈ feasible P ∧ KL Q P ≤ a} := by
  classical
  intro P
  have hq₂ : 2 ≤ q := by omega
  have hpos (t : TypeProfile C q) : 0 < P t := multinomialTypeLaw_pos hp t
  have hP : Tendsto (fun n => finiteTypeLaw (colour n)) (admissibleOrders q) (𝓝 P) :=
    tendsto_finiteTypeLaw_of_le inf_le_left colour p hp hcolour
  have hPF := reference_feasible hq₂ colour hP hpos
  have hI := continuous_KL_left (fun t => (hpos t).ne')
  obtain ⟨ρ, hρ, hclasses⟩ := eventually_classes hp hcolour
  have hclass : ∀ᶠ n in admissibleOrders q, ∀ c, q ≤ profile (colour n) univ c :=
    hclasses.mono fun _ h => h.2
  refine ⟨?_, (eventually_total_designs hq one_pos).mono fun _ h => h.1, fun a => ?_⟩
  · apply countLDP_of_bounds (P := P) (fun n => profiles (colour n)) (fun n Q => profileCount (colour n) {Q})
      (defect P) hI (continuous_defect P) (defect_nonneg P)
      (fun Q hbox hd => mem_feasible_iff.mpr ⟨hbox, hd⟩)
      (fun n => blockMass_nonneg n q) (fun _ => Nat.cast_nonneg _)
    · intro n A
      exact (profileCount_sum (colour n) A).le
    · intro n A Q _ hQA
      exact profileCount_mono (colour n) (Set.singleton_subset_iff.mpr hQA)
    · intro ε hε
      exact (eventually_profiles_subexponential q hq₂ colour hε).mono fun _ h _ => h
    · intro ε hε
      have hlim : Tendsto (fun n => ‖orderedMargins q (finiteTypeLaw (colour n)) - orderedMargins q P‖)
          (admissibleOrders q) (𝓝 0) := by
        simpa only [Function.comp_apply, sub_self, norm_zero] using
          ((((continuous_orderedMargins q).tendsto P).comp hP).sub_const (orderedMargins q P)).norm
      apply eventually_inf_principal.mp
      have hl : admissibleOrders q ≤ atTop := inf_le_left
      filter_upwards [hlim.eventually (ge_mem_nhds hε), hclass, hl (eventually_ge_atTop q)]
        with n hn hc hnq
      intro Q hQ
      obtain ⟨D, hD, rfl⟩ := mem_profiles.mp hQ
      exact ⟨profileOf_box hq₂ (hq₂.trans hnq) (colour n) hD, by
        rwa [defect, profileOf_sum hq₂ (hq₂.trans hnq) (colour n) hD, sub_self, abs_zero, zero_add,
          profileOf_ordered hq₂ hnq (colour n) hD (fun c => hq₂.trans (hc c))]⟩
    · intro ε hε
      exact eventually_inf_principal.mp
        (eventually_upper_profiles hq colour hP hpos hρ (hclasses.mono fun _ h => h.1) hε)
    · intro Q hQ hQpos ε hε V hV
      exact eventually_inf_principal.mp
        (eventually_lower_profiles hq colour hP hpos hρ hclasses hQ hQpos hε hV)
    · exact hpos
    · exact fun Q hQ _ hs hs' => feasible_mix hPF hQ hs hs'
    · exact fun Q hQ t => hQ.1.1 t
  · have hclosed : IsClosed (feasible P) := by
      have he : feasible P = Set.Icc 0 1 ∩ (defect P) ⁻¹' {0} :=
        Set.ext fun Q => by simp only [mem_feasible_iff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      rw [he]
      exact isClosed_Icc.inter (isClosed_singleton.preimage (continuous_defect P))
    exact isCompact_rate_sublevel hclosed (fun _ h => h.1) hI a

/-- Closed and open bounds for the probability of the normalized histogram
under the uniform law on the labelled designs. -/
theorem designProfileLDP_probability {q : ℕ} (hq : 3 ≤ q) [Nonempty C]
    (colour : (n : ℕ) → Fin n → C) (p : C → ℝ) (hp : ∀ c, 0 < p c)
    (hcolour : ∀ c, Tendsto (fun n => (profile (colour n) univ c : ℝ) / n)
      (admissibleOrders q) (𝓝 (p c))) :
    let P : TypeProfile C q → ℝ := multinomialTypeLaw p
    (∀ F : Set (TypeProfile C q → ℝ), IsClosed F → ∀ r : ℝ,
      (∀ Q ∈ F, Q ∈ feasible P → r < KL Q P) →
      ∀ᶠ n in admissibleOrders q, profileCount (colour n) F / (designs q n).card ≤
        Real.exp (-(blockMass n q * r))) ∧
    (∀ G : Set (TypeProfile C q → ℝ), IsOpen G → ∀ Q ∈ G, Q ∈ feasible P → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in admissibleOrders q, Real.exp (-(blockMass n q * (KL Q P + ε))) ≤
        profileCount (colour n) G / (designs q n).card) ∧
    ∀ a : ℝ, IsCompact {Q | Q ∈ feasible P ∧ KL Q P ≤ a} := by
  intro P
  obtain ⟨⟨hupper, hlower⟩, hpositive, hcompact⟩ := designProfileLDP hq colour p hp hcolour
  refine ⟨?_, ?_, hcompact⟩
  · intro F hF r hr
    filter_upwards [hpositive, eventually_inf_principal.mpr (hupper F hF r hr)] with n hn hcount
    have hn' : (0 : ℝ) < (designs q n).card := by exact_mod_cast hn
    exact (div_le_iff₀ hn').mpr (by simpa only [mul_comm] using hcount)
  · intro G hG Q hQ hQF ε hε
    filter_upwards [hpositive, eventually_inf_principal.mpr (hlower G hG Q hQ hQF ε hε)]
      with n hn hcount
    have hn' : (0 : ℝ) < (designs q n).card := by exact_mod_cast hn
    exact (le_div_iff₀ hn').mpr (by simpa only [mul_comm] using hcount)

end KqR75.ProfileLDP

#print axioms KqR75.ProfileLDP.designProfileLDP
#print axioms KqR75.ProfileLDP.designProfileLDP_probability
