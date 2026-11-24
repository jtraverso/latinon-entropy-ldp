module
public import SeedScales

@[expose] public section
noncomputable section
namespace KqR75.ReserveDeletion

open Filter Finset ColouredCliques CompleteJohnson CliqueGram SparseGram ProfileBalance
open scoped Matrix Topology

/-- Delete the reserve from an already repaired host. The inverse uses
the total deleted degree, while the load defect and histogram loss
depend only on the newly deleted reserve. -/
theorem repair_loads {C : Type*} [Fintype C] [DecidableEq C] {n q : ℕ}
    (hq : 3 ≤ q) (hn : 2 * q ^ 2 ≤ n) (colour : Fin n → C)
    (J₀ X : Finset (Edge n)) (t tX M δ : ℝ)
    (htX : 0 ≤ tX) (hM : 0 ≤ M)
    (hdeg : ∀ v : Fin n, ∑ e : ((J₀ ∩ Xᶜ)ᶜ : Finset (Edge n)), incidence 2 e v ≤ t)
    (hdegX : ∀ v : Fin n, ∑ e : X, incidence 2 e v ≤ tX)
    (hsmall : 4 * (1 + (q.choose 2 : ℝ)) * outsideBound n q t ≤ 1 / 2)
    (w₀ : HostCorrection.availableBlocks n q J₀ → ℝ)
    (hw : ∀ b, |w₀ b| ≤ M * HostCorrection.scale n q) (hwpos : ∀ b, δ ≤ w₀ b)
    (hload : HostCorrection.hostIncidence n q J₀ *ᵥ w₀ = (fun _ => 1)) :
    let J := J₀ ∩ Xᶜ
    let u := M * (4 * (q : ℝ) ^ 2 * tX / n)
    let c := 8 * (q.choose 2 : ℝ) * HostCorrection.scale n q * u
    c ≤ δ / 2 →
    ∃ w' : HostCorrection.availableBlocks n q J → ℝ,
      HostCorrection.hostIncidence n q J *ᵥ w' = (fun _ => 1) ∧
      (∀ b, δ / 2 ≤ w' b) ∧
      (∀ b, |w' b - extend J₀ w₀ b| ≤ c) ∧
      ∀ i, |hostHistogram colour J₀ w₀ i - hostHistogram colour J w' i| ≤
        M * (X.card : ℝ) + 8 * (J.card : ℝ) * u := by
  classical
  dsimp only
  intro hpos
  let J := J₀ ∩ Xᶜ
  let u := M * (4 * (q : ℝ) ^ 2 * tX / n)
  let c := 8 * (q.choose 2 : ℝ) * HostCorrection.scale n q * u
  let w := extend J₀ w₀
  let wX : HostCorrection.availableBlocks n q Xᶜ → ℝ := fun b => w b
  let μ : HostCorrection.availableBlocks n q J → ℝ := fun b => w b
  have hwext (b : Clique n q) : |w b| ≤ M * HostCorrection.scale n q := by
    by_cases hb : resources n q b ⊆ J₀
    · simpa only [w, extend, dite_eq_left hb] using hw ⟨b, mem_filter.mpr ⟨mem_univ _, hb⟩⟩
    · simp only [w, extend, dite_eq_right hb, abs_zero]
      unfold HostCorrection.scale
      positivity
  have hbridge : extend Xᶜ wX = extend J μ := by
    funext b
    have hJ : resources n q b ⊆ J ↔ resources n q b ⊆ J₀ ∧ resources n q b ⊆ Xᶜ :=
      subset_inter_iff
    by_cases h₀ : resources n q b ⊆ J₀ <;> by_cases hX : resources n q b ⊆ Xᶜ <;>
      simp [extend, hJ, wX, μ, w, h₀, hX]
  have hdegreeX (v : Fin n) : (∑ e : ((Xᶜ)ᶜ : Finset (Edge n)), incidence 2 e v) ≤ tX := by
    rw [compl_compl]
    exact hdegX v
  have hnq : q + 2 ≤ n := by nlinarith
  have hn6 : 6 ≤ n := by nlinarith
  have hu : 0 ≤ u := by dsimp [u]; positivity
  let h : J → ℝ := (fun _ => 1) - HostCorrection.hostIncidence n q J *ᵥ μ
  have hdef (e : J) : |h e| ≤ u := by
    have he₀ : (e : Edge n) ∈ J₀ := (mem_inter.mp e.property).1
    have heX : (e : Edge n) ∈ Xᶜ := (mem_inter.mp e.property).2
    have hh := PrunedWeights.host_load_defect hq hnq Xᶜ tX M hM hdegreeX w hwext ⟨e, heX⟩
    have h₀ : WeightedEnergy.load (resources n q) w (e : Edge n) = 1 := by
      change WeightedEnergy.load (resources n q) (extend J₀ w₀) (e : Edge n) = 1
      rw [load_extend, dite_eq_left he₀, hload]
    have h₁ := congrArg (fun v => WeightedEnergy.load (resources n q) v (e : Edge n)) hbridge
    rw [load_extend, load_extend, dite_eq_left heX, dite_eq_left e.property] at h₁
    change |WeightedEnergy.load (resources n q) w e -
      (HostCorrection.hostIncidence n q Xᶜ *ᵥ wX) ⟨e, heX⟩| ≤ _ at hh
    rw [h₀, h₁] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (outsideBound_le n q hq hn6 tX htX) hM)
  obtain ⟨v, hv, hl₁, hvabs⟩ := HostCorrection.solve_defect n q hq hn J t u hu hdeg hsmall h hdef
  have hsum : ∑ b, |v b| ≤ 8 * (J.card : ℝ) * u := by
    refine hl₁.trans ?_
    calc
      _ ≤ 8 * (∑ _e : J, u) := mul_le_mul_of_nonneg_left (sum_le_sum (fun e _ => hdef e)) (by norm_num)
      _ = _ := by simp only [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul]; ring
  refine ⟨μ + v, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mulVec_add, hv]
    change (HostCorrection.hostIncidence n q J *ᵥ μ) +
      ((fun _ => 1) - HostCorrection.hostIncidence n q J *ᵥ μ) = _
    abel
  · intro b
    have hb₀ : resources n q (b : Clique n q) ⊆ J₀ :=
      (mem_filter.mp b.property).2.trans inter_subset_left
    have hb : δ ≤ μ b := by
      change δ ≤ extend J₀ w₀ b
      rw [extend, dite_eq_left hb₀]
      exact hwpos _
    have hv' := (abs_le.mp (hvabs b)).1
    change δ / 2 ≤ μ b + v b
    linarith only [hb, hv', hpos]
  · intro b
    change |μ b + v b - μ b| ≤ c
    rw [add_sub_cancel_left]
    exact hvabs b
  · intro i
    have hremoved := PrunedWeights.type_mass_defect hq hnq Xᶜ M hM w hwext
      (ProfileWeights.fibre (cliqueType colour) i)
    have hmid : (∑ b : HostCorrection.availableBlocks n q Xᶜ,
        if (b : Clique n q) ∈ ProfileWeights.fibre (cliqueType colour) i then w b else 0) =
        hostHistogram colour J μ i := by
      calc
        _ = hostHistogram colour Xᶜ wX i := by rw [histogram_extend]; simp [wX, ProfileWeights.fibre]
        _ = _ := by simp only [hostHistogram, hbridge]
    rw [hmid, compl_compl] at hremoved
    have hchange : |hostHistogram colour J μ i - hostHistogram colour J (μ + v) i| ≤ ∑ b, |v b| := by
      simp only [histogram_extend, ← sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun b _ => ?_)
      split_ifs <;> simp
    exact (abs_sub_le _ _ _).trans (add_le_add hremoved (hchange.trans hsum))

/-- At the R75 scale the inverse threshold may depend on the whole
bank, but the error constant for type masses depends only on the
reserve degree and the fixed weight envelope. -/
theorem eventually_repair_loads {C : Type*} [Fintype C] [DecidableEq C]
    (q : ℕ) (hq : 3 ≤ q) (M a D Dₓ z : ℝ)
    (hM : 0 ≤ M) (ha : 0 < a) (hD : 0 ≤ D) (hDₓ : 0 ≤ Dₓ) (hz : 0 < z) :
    ∀ᶠ n : ℕ in atTop, ∀ (colour : Fin n → C) (J₀ X : Finset (Edge n)) (t tX : ℝ),
      0 ≤ t → 0 ≤ tX → t ≤ D * (n : ℝ) ^ (1 - z) → tX ≤ Dₓ * (n : ℝ) ^ (1 - z) →
      (∀ v : Fin n, ∑ e : ((J₀ ∩ Xᶜ)ᶜ : Finset (Edge n)), incidence 2 e v ≤ t) →
      (∀ v : Fin n, ∑ e : X, incidence 2 e v ≤ tX) →
      ∀ w₀ : HostCorrection.availableBlocks n q J₀ → ℝ,
        (∀ b, |w₀ b| ≤ M * HostCorrection.scale n q) →
        (∀ b, a * HostCorrection.scale n q ≤ w₀ b) →
        HostCorrection.hostIncidence n q J₀ *ᵥ w₀ = (fun _ => 1) →
        let J := J₀ ∩ Xᶜ
        let α := HostCorrection.scale n q
        ∃ w' : HostCorrection.availableBlocks n q J → ℝ,
          HostCorrection.hostIncidence n q J *ᵥ w' = (fun _ => 1) ∧
          (∀ b, a * α / 2 ≤ w' b) ∧
          (∀ b, |w' b - extend J₀ w₀ b| ≤
            α * (32 * (q.choose 2 : ℝ) * M * (q : ℝ) ^ 2 * Dₓ * (n : ℝ) ^ (-z))) ∧
          ∀ i, |hostHistogram colour J₀ w₀ i - hostHistogram colour J w' i| ≤
            (M * (1 / 2 + 16 * (q : ℝ) ^ 2) * Dₓ) * (n : ℝ) ^ (2 - z) := by
  classical
  let A := 16 * (1 + (q.choose 2 : ℝ)) * (q : ℝ) ^ 2
  let E := 32 * (q.choose 2 : ℝ) * M * (q : ℝ) ^ 2
  let R := 1 + A + E / a
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hEa : 0 ≤ E / a := by positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hRA : A ≤ R := by dsimp [R]; linarith
  have hRE : E / a ≤ R := by dsimp [R]; linarith
  have hp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-z)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hz).comp tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ => (D + Dₓ) * (n : ℝ) ^ (-z)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul (D + Dₓ)
  have hsmall : ∀ᶠ n : ℕ in atTop, (D + Dₓ) * (n : ℝ) ^ (-z) < 1 / (2 * R) :=
    hlim.eventually (gt_mem_nhds (by positivity))
  filter_upwards [eventually_ge_atTop (2 * q ^ 2), hsmall] with n hn hnsmall
  intro colour J₀ X t tX ht htX htD htDₓ hdeg hdegX w₀ hw hwpos hload
  let J := J₀ ∩ Xᶜ
  let α := HostCorrection.scale n q
  let ξ := t / (n : ℝ)
  let ξX := tX / (n : ℝ)
  have hn₀ : 0 < n := by nlinarith
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn₀
  have hξ : ξ ≤ D * (n : ℝ) ^ (-z) := SeedScales.relative_degree_bound hn₀ htD
  have hξX : ξX ≤ Dₓ * (n : ℝ) ^ (-z) := SeedScales.relative_degree_bound hn₀ htDₓ
  have hsmall' {x : ℝ} (hx : x ≤ (D + Dₓ) * (n : ℝ) ^ (-z)) : R * x ≤ 1 / 2 := by
    have hh := (lt_div_iff₀ (show 0 < 2 * R by positivity)).mp (hx.trans_lt hnsmall)
    nlinarith only [hh]
  have hξR : R * ξ ≤ 1 / 2 := hsmall' (hξ.trans
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity)))
  have hξXR : R * ξX ≤ 1 / 2 := hsmall' (hξX.trans
    (mul_le_mul_of_nonneg_right (by linarith) (by positivity)))
  have hξA : A * ξ ≤ 1 / 2 := (mul_le_mul_of_nonneg_right hRA (by dsimp [ξ]; positivity)).trans hξR
  have hξE : E * ξX ≤ a / 2 := by
    have hh := (mul_le_mul_of_nonneg_right hRE (by dsimp [ξX]; positivity)).trans hξXR
    rw [div_mul_eq_mul_div] at hh
    linarith only [(div_le_iff₀ ha).mp hh]
  have hα : 0 ≤ α := by dsimp [α, HostCorrection.scale]; positivity
  have hgram : 4 * (1 + (q.choose 2 : ℝ)) * outsideBound n q t ≤ 1 / 2 := by
    calc
      _ ≤ 4 * (1 + (q.choose 2 : ℝ)) * (4 * (q : ℝ) ^ 2 * t / n) :=
        mul_le_mul_of_nonneg_left (outsideBound_le n q hq (by nlinarith) t ht) (by positivity)
      _ = A * ξ := by dsimp [A, ξ]; ring
      _ ≤ _ := hξA
  let u := M * (4 * (q : ℝ) ^ 2 * tX / n)
  have hc : 8 * (q.choose 2 : ℝ) * α * u = α * (E * ξX) := by dsimp [u, E, ξX]; ring
  have hpos : 8 * (q.choose 2 : ℝ) * α * u ≤ a * α / 2 := by
    rw [hc]
    exact (mul_le_mul_of_nonneg_left hξE hα).trans_eq (by ring)
  obtain ⟨w', hloads, hpositive, hchange, hmass⟩ := repair_loads hq hn colour J₀ X t tX M (a * α)
    htX hM hdeg hdegX hgram w₀ hw hwpos hload hpos
  refine ⟨w', hloads, hpositive, ?_, ?_⟩
  · intro b
    refine (hchange b).trans ?_
    change 8 * (q.choose 2 : ℝ) * α * u ≤ _
    rw [hc]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hξX hE) hα).trans_eq (by dsimp [E]; ring)
  · intro i
    have hX : (X.card : ℝ) ≤ (n : ℝ) * tX / 2 := by
      have hh := sparse_card_bound (incidence (V := Fin n) 2) X tX (incidence_row_sum 2) hdegX
      simp only [Fintype.card_fin] at hh
      linarith only [hh]
    have hJ : (J.card : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
      have hh : (J.card : ℝ) ≤ Fintype.card (Edge n) := by exact_mod_cast J.card_le_univ
      rw [edge_card n (by omega)] at hh
      nlinarith only [hh, hn']
    have hP : (n : ℝ) * (n : ℝ) ^ (1 - z) = (n : ℝ) ^ (2 - z) := by
      calc
        _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 - z) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hn']; congr 1; ring
    refine (hmass i).trans ?_
    calc
      _ ≤ M * ((n : ℝ) * tX / 2) + 8 * ((n : ℝ) ^ 2 / 2) * u :=
        add_le_add (mul_le_mul_of_nonneg_left hX hM)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ (by norm_num))
            (by dsimp [u]; positivity))
      _ = (M * (1 / 2 + 16 * (q : ℝ) ^ 2) * (n : ℝ)) * tX := by
        dsimp [u]
        field_simp
        ring
      _ ≤ (M * (1 / 2 + 16 * (q : ℝ) ^ 2) * (n : ℝ)) * (Dₓ * (n : ℝ) ^ (1 - z)) :=
        mul_le_mul_of_nonneg_left htDₓ (by positivity)
      _ = (M * (1 / 2 + 16 * (q : ℝ) ^ 2) * Dₓ) * ((n : ℝ) * (n : ℝ) ^ (1 - z)) := by ring
      _ = _ := by rw [hP]

end KqR75.ReserveDeletion

#print axioms KqR75.ReserveDeletion.repair_loads
#print axioms KqR75.ReserveDeletion.eventually_repair_loads
