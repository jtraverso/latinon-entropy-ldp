module
public import ProfileBalance
public import PhysicalProfileLifts

@[expose] public section
noncomputable section
namespace KqR75.ResidualSeed

open Finset ColouredCliques SlotProfiles CompleteJohnson SparseGram ProfileBalance CliqueGram
open scoped Matrix

variable {C : Type*} [Fintype C] [DecidableEq C]

private theorem packing_load {n q : ℕ} (P : Finset (Clique n q)) (e : Edge n) :
    WeightedEnergy.load (resources n q) (fun b => if b ∈ P then 1 else 0) e =
      ((P.filter fun b => e ∈ resources n q b).card : ℝ) := by
  classical
  calc
    _ = ∑ b ∈ univ.filter (fun b => b ∈ P ∧ e ∈ resources n q b), (1 : ℝ) := by
      rw [WeightedEnergy.load, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : b ∈ P <;> by_cases he : e ∈ resources n q b <;> simp [hb, he]
    _ = _ := by
      have heq : univ.filter (fun b => b ∈ P ∧ e ∈ resources n q b) =
          P.filter (fun b => e ∈ resources n q b) := by ext b; simp
      rw [heq]
      simp

/-- The number of removed edges is the number of basal blocks times the
number of edges in each block. The maximum removed degree then bounds
the number of basal blocks independently of their colour profile. -/
theorem basal_card_le_of_degree {n q : ℕ} (hq : 2 ≤ q)
    (P : Finset (Clique n q)) (J : Finset (Edge n)) (t : ℝ)
    (hpacking : ∀ e : Edge n,
      ((P.filter fun b => e ∈ resources n q b).card : ℝ) = if e ∈ J then 0 else 1)
    (hdeg : ∀ v : Fin n, ∑ f : (Jᶜ : Finset (Edge n)), incidence 2 f v ≤ t) :
    (P.card : ℝ) ≤ (n : ℝ) * t / 2 := by
  classical
  let w : Clique n q → ℝ := fun b => if b ∈ P then 1 else 0
  have hload (e : Edge n) : WeightedEnergy.load (resources n q) w e =
      if e ∈ J then 0 else 1 := (packing_load P e).trans (hpacking e)
  have hmass := WeightedEnergy.incidence_sum (resources n q) w (fun _ => 1)
  have hrow (b : Clique n q) :
      (∑ _e ∈ resources n q b, (1 : ℝ)) = (q.choose 2 : ℝ) := by
    simp [resources_card]
  simp only [hrow, hload, mul_one] at hmass
  have hsum : (∑ b : Clique n q, w b * (q.choose 2 : ℝ)) =
      (P.card : ℝ) * (q.choose 2 : ℝ) := by
    rw [← Finset.sum_mul]
    congr 1
    simp only [w, ← Finset.sum_filter]
    rw [Finset.filter_mem_eq_of_subset (Finset.subset_univ P)]
    simp
  have hcomp : (∑ f : Edge n, if f ∈ J then (0 : ℝ) else 1) =
      ((Jᶜ : Finset (Edge n)).card : ℝ) := by
    classical
    rw [← show (∑ f ∈ (Jᶜ : Finset (Edge n)), (1 : ℝ)) =
      ((Jᶜ : Finset (Edge n)).card : ℝ) by simp]
    rw [← Finset.filter_mem_eq_of_subset (Finset.subset_univ (Jᶜ : Finset (Edge n)))]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : f ∈ J <;> simp [hf]
  rw [hsum, hcomp] at hmass
  have hcount := sparse_card_bound (incidence (V := Fin n) 2) (Jᶜ : Finset (Edge n))
    t (incidence_row_sum 2) hdeg
  have hr : (1 : ℝ) ≤ q.choose 2 := by
    exact_mod_cast (Nat.choose_pos hq)
  have hp : (P.card : ℝ) ≤ (P.card : ℝ) * (q.choose 2 : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ P.card by positivity)
  simp only [Fintype.card_fin] at hcount
  linarith only [hmass, hcount, hp]

/-- Subtracting the basal histogram from a unit-load seed gives the
prescribed pair margins on the actual leave of an edge-disjoint packing. -/
theorem compatible_after_packing {n q : ℕ} (colour : Fin n → C)
    (w : Clique n q → ℝ) (P : Finset (Clique n q)) (J : Finset (Edge n))
    (hseed : ∀ e : Edge n, WeightedEnergy.load (resources n q) w e = 1)
    (hpacking : ∀ e : Edge n,
      ((P.filter fun b => e ∈ resources n q b).card : ℝ) = if e ∈ J then 0 else 1) :
    compatible colour J
      (fun i => histogram colour w i - histogram colour (fun b => if b ∈ P then 1 else 0) i)
      (fun _ => 1) := by
  classical
  let v : Clique n q → ℝ := fun b => if b ∈ P then 1 else 0
  have hv (e : Edge n) : WeightedEnergy.load (resources n q) v e =
      if e ∈ J then 0 else 1 := (packing_load P e).trans (hpacking e)
  have hh (i : TypeProfile C q) : histogram colour (fun b => w b - v b) i =
      histogram colour w i - histogram colour v i := by
    simp only [histogram, Finset.sum_sub_distrib]
  intro e
  change pairMargin colour (fun i => histogram colour w i - histogram colour v i) e = _
  rw [show (fun i => histogram colour w i - histogram colour v i) =
    histogram colour (fun b => w b - v b) from funext (fun i => (hh i).symm),
    margin_histogram]
  have hload (f : Edge n) : WeightedEnergy.load (resources n q) (fun b => w b - v b) f =
      if f ∈ J then 1 else 0 := by
    have hsub : WeightedEnergy.load (resources n q) (fun b => w b - v b) f =
        WeightedEnergy.load (resources n q) w f - WeightedEnergy.load (resources n q) v f := by
      simp only [WeightedEnergy.load, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp
    rw [hsub, hseed, hv]
    split_ifs <;> norm_num
  let g (f : Edge n) : ℝ := if profile colour (f : Finset (Fin n)) =
    profile colour (e : Finset (Fin n)) then 1 else 0
  simp_rw [hload, one_mul]
  change (∑ f : Edge n, (if f ∈ J then (1 : ℝ) else 0) * g f) = ∑ f : J, g f
  rw [Finset.sum_coe_sort J g]
  have hf : univ.filter (fun f : Edge n => f ∈ J) = J :=
    Finset.filter_mem_eq_of_subset (Finset.subset_univ J)
  conv_rhs => rw [← hf, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f _
  split_ifs <;> simp

theorem basal_histogram_le_card {n q : ℕ} (colour : Fin n → C)
    (P : Finset (Clique n q)) (i : TypeProfile C q) :
    |histogram colour (fun b => if b ∈ P then 1 else 0) i| ≤ (P.card : ℝ) := by
  classical
  let w : Clique n q → ℝ := fun b => if b ∈ P then 1 else 0
  have hw (b : Clique n q) : 0 ≤ w b := by dsimp [w]; split_ifs <;> norm_num
  change |∑ b ∈ ProfileWeights.fibre (cliqueType colour) i, w b| ≤ _
  rw [abs_of_nonneg (sum_nonneg (fun b _ => hw b))]
  calc
    _ ≤ ∑ b : Clique n q, w b :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun b _ _ => hw b)
    _ = _ := by
      rw [show (∑ b : Clique n q, w b) =
        ∑ b ∈ univ.filter (fun b : Clique n q => b ∈ P), (1 : ℝ) by simp only [sum_filter, w],
        filter_mem_eq_of_subset (subset_univ P)]
      simp

/-- Restricted seeds have explicit defect bounds in terms of deletion.
The target may also differ from the full seed histogram by a prescribed
amount per type. -/
theorem repair_after_deletion {n q : ℕ} (hq : 3 ≤ q) (hn : 2 * q ^ 2 ≤ n)
    (colour : Fin n → C) (ref : C) (d : ℕ) (s G : ℝ)
    (hs : 0 < s) (hG : 0 ≤ G) (hclasses : ∀ i, d + q ≤ profile colour univ i)
    (hdn : s * (n : ℝ) ≤ d)
    (g : High C q ref → TypeProfile C q → ℝ) (hg : ∀ j v, |g j v| ≤ G)
    (hcoord : ∀ i j : High C q ref, g j i.val = if i = j then 1 else 0)
    (hmargin : ∀ j i₁ i₂, ∑ v, g j v * (SlotPairMargins.orderedCount v i₁ i₂ : ℝ) = 0)
    (J : Finset (Edge n)) (t M D δ : ℝ)
    (ht : 0 ≤ t) (hM : 0 ≤ M) (hD : 0 ≤ D) (hδ : 0 < δ)
    (hdeg : ∀ v : Fin n, ∑ f : (Jᶜ : Finset (Edge n)), incidence 2 f v ≤ t)
    (hsmall : 4 * (1 + (q.choose 2 : ℝ)) * outsideBound n q t ≤ 1 / 2)
    (w : Clique n q → ℝ) (m : TypeProfile C q → ℝ)
    (hw : ∀ b, |w b| ≤ M * HostCorrection.scale n q) (hwpos : ∀ b, δ ≤ w b)
    (hseed : ∀ e : Edge n, WeightedEnergy.load (resources n q) w e = 1)
    (hcompat : compatible colour J m (fun _ => 1))
    (htarget : ∀ i : High C q ref, |m i.val - histogram colour w i.val| ≤ D) :
    let α := HostCorrection.scale n q
    let Q := (G * (q.factorial : ℝ) ^ Fintype.card C / s ^ q) / (n : ℝ) ^ 2
    let u := M * (4 * (q : ℝ) ^ 2 * t / n)
    let v := Q * (4 * (q : ℝ) ^ 2 * t / n)
    let r := (q.choose 2 : ℝ)
    let k := (Fintype.card (High C q ref) : ℝ)
    let B := k * (Q * α + 8 * r * α * v)
    let T := D + M * ((Jᶜ : Finset (Edge n)).card : ℝ) + 8 * (J.card : ℝ) * u
    let E := 8 * r * α * u + B * (8 * T)
    k * (Q * ((Jᶜ : Finset (Edge n)).card : ℝ) + 8 * (J.card : ℝ) * v) ≤ 1 / 2 →
    E ≤ δ / 2 →
    ∃ w' : HostCorrection.availableBlocks n q J → ℝ,
      HostCorrection.hostIncidence n q J *ᵥ w' = (fun _ => 1) ∧
      hostHistogram colour J w' = m ∧
      (∀ b, 0 < w' b) ∧ (∀ b, |w' b - w b| ≤ E) := by
  classical
  dsimp only
  intro hnear herror
  let α := HostCorrection.scale n q
  let Q := (G * (q.factorial : ℝ) ^ Fintype.card C / s ^ q) / (n : ℝ) ^ 2
  let u := M * (4 * (q : ℝ) ^ 2 * t / n)
  let v := Q * (4 * (q : ℝ) ^ 2 * t / n)
  let r := (q.choose 2 : ℝ)
  let k := (Fintype.card (High C q ref) : ℝ)
  let B := k * (Q * α + 8 * r * α * v)
  let T := D + M * ((Jᶜ : Finset (Edge n)).card : ℝ) + 8 * (J.card : ℝ) * u
  let A := HostCorrection.hostIncidence n q J
  let R := LoadCorrection.corrector A α
  let H := highIncidence (q := q) colour ref J
  let μ : HostCorrection.availableBlocks n q J → ℝ := fun b => w b
  let h : J → ℝ := (fun _ => 1) - A *ᵥ μ
  have hnq : q + 2 ≤ n := by nlinarith
  have hn6 : 6 ≤ n := by nlinarith
  have hα : 0 ≤ α := by dsimp [α, HostCorrection.scale]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hcls (i : C) : 2 ≤ profile colour univ i := by have := hclasses i; omega
  obtain ⟨hdet, hrows⟩ := host_inverse_rows_le_eight n q hq hn J t hdeg hsmall
  rw [← HostCorrection.gram_eq_hostGram] at hdet hrows
  have hR : A * R = 1 := LoadCorrection.right_inverse A α hdet
  have hRR : ∀ b, ∑ e, |R b e| ≤ 8 * r * α :=
    LoadCorrection.corrector_rows_le A α r hα (HostCorrection.hostIncidence_nonneg n q J)
      (HostCorrection.hostIncidence_col_sum_le n q J) hrows
  have hRC : ∀ e, ∑ b, |R b e| ≤ 8 :=
    LoadCorrection.corrector_cols_le_eight A α hα (HostCorrection.hostIncidence_nonneg n q J)
      (HostCorrection.normalized_row_cap n q hq hnq J) hrows
  have hdef (e : J) : |h e| ≤ u := by
    have he := PrunedWeights.host_load_defect hq hnq J t M hM hdeg w hw e
    rw [hseed e] at he
    exact he.trans (mul_le_mul_of_nonneg_left (outsideBound_le n q hq hn6 t ht) hM)
  have hl1 : (∑ b, |(R *ᵥ h) b|) ≤ 8 * (J.card : ℝ) * u := by
    have hb : (∑ e, |h e|) ≤ ∑ _e : J, u := sum_le_sum (fun e _ => hdef e)
    exact (LoadCorrection.mulVec_l1_le R 8 hRC h).trans
      (by simp only [sum_const, nsmul_eq_mul, card_univ, Fintype.card_coe] at hb
          linarith)
  have hloadType (i : High C q ref) : |(H *ᵥ (R *ᵥ h)) i| ≤ 8 * (J.card : ℝ) * u := by
    change |∑ b, H i b * (R *ᵥ h) b| ≤ _
    refine le_trans (abs_sum_le_sum_abs _ _) (le_trans (sum_le_sum fun b _ => ?_) hl1)
    dsimp only [H, highIncidence]
    split_ifs <;> simp
  have htype (i : High C q ref) :
      |m i.val - (H *ᵥ μ) i - (H *ᵥ (R *ᵥ h)) i| ≤ T := by
    have hmass := PrunedWeights.type_mass_defect hq hnq J M hM w hw
      (ProfileWeights.fibre (cliqueType colour) i.val)
    have hm : |histogram colour w i.val - (H *ᵥ μ) i| ≤
        M * ((Jᶜ : Finset (Edge n)).card : ℝ) := by
      simpa [histogram, H, highIncidence, Matrix.mulVec, dotProduct, μ,
        ProfileWeights.fibre, ite_mul] using hmass
    calc
      _ = |(m i.val - histogram colour w i.val) +
          (histogram colour w i.val - (H *ᵥ μ) i) - (H *ᵥ (R *ᵥ h)) i| := by ring_nf
      _ ≤ _ := by
        dsimp only [T]
        have htri := abs_add_le ((m i.val - histogram colour w i.val) +
          (histogram colour w i.val - (H *ᵥ μ) i)) (-((H *ᵥ (R *ᵥ h)) i))
        rw [← sub_eq_add_neg, abs_neg] at htri
        exact htri.trans (add_le_add
          ((abs_add_le _ _).trans (add_le_add (htarget i) hm)) (hloadType i))
  obtain ⟨L, hL, hpert, hentry⟩ := PhysicalProfileLifts.host_columns
    hq hn colour ref d s G hs hG hclasses hdn g hg hcoord hmargin J t ht hdeg hsmall
  have hclose (i : High C q ref) :
      (∑ j, |(1 : Matrix (High C q ref) (High C q ref) ℝ) i j - (H * L) i j|) ≤ 1 / 2 := by
    exact (hpert i).trans hnear
  have hRL (b : HostCorrection.availableBlocks n q J) : (∑ j, |L b j|) ≤ B := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hcoef : G / (n : ℝ) ^ 2 * (q.factorial : ℝ) ^ Fintype.card C / s ^ q = Q := by
      dsimp [Q]
      ring
    calc
      _ ≤ ∑ _j : High C q ref, (Q * α + 8 * r * α * v) := by
        apply sum_le_sum
        intro j _
        have hgj (z : TypeProfile C q) : |g j z| ≤ G / (n : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
          rw [div_mul_cancel₀ _ (pow_ne_zero _ hn0)]
          exact hg j z
        have hf := seed_weight_abs_le colour (show 2 ≤ q by omega) (show q ≤ n by omega)
          d s (G / (n : ℝ) ^ 2) hs (by positivity) hclasses hdn (g j) hgj b
        rw [hcoef] at hf
        have htriangle := abs_add_le (L b j - ProfileWeights.weight (cliqueType colour) (g j) b)
          (ProfileWeights.weight (cliqueType colour) (g j) b)
        rw [sub_add_cancel] at htriangle
        exact (htriangle.trans (add_le_add (hentry b j) hf)).trans_eq (add_comm _ _)
      _ = B := by simp only [sum_const, card_univ, nsmul_eq_mul, B, k]
  exact repair_full_histogram (show 2 ≤ q by omega) colour hcls ref J R L
    hR hL hclose _ B u T δ hu hT hδ hRR hRL μ (fun _ => 1) m hcompat
    (fun b => hwpos b) hdef htype herror

/-- Convert the three finite repair bounds to conditions on the ratio of
deleted degree to host order. All coefficients of that ratio are fixed
once the profile and the coordinate directions have been bounded. -/
theorem thresholds_of_degree {n q : ℕ} (hn : 6 ≤ n) (hq : 3 ≤ q)
    (J : Finset (Edge n)) (t B₀ k M D : ℝ)
    (ht : 0 ≤ t) (hB₀ : 0 ≤ B₀) (hk : 0 ≤ k) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hdeg : ∀ v : Fin n, ∑ f : (Jᶜ : Finset (Edge n)), incidence 2 f v ≤ t)
    (hDcard : D ≤ (n : ℝ) * t / 2) :
    let ξ := t / (n : ℝ)
    let α := HostCorrection.scale n q
    let Q := B₀ / (n : ℝ) ^ 2
    let u := M * (4 * (q : ℝ) ^ 2 * t / n)
    let v := Q * (4 * (q : ℝ) ^ 2 * t / n)
    let r := (q.choose 2 : ℝ)
    let B := k * (Q * α + 8 * r * α * v)
    let T := D + M * ((Jᶜ : Finset (Edge n)).card : ℝ) + 8 * (J.card : ℝ) * u
    ξ ≤ 1 →
      4 * (1 + r) * outsideBound n q t ≤ 16 * (1 + r) * (q : ℝ) ^ 2 * ξ ∧
      k * (Q * ((Jᶜ : Finset (Edge n)).card : ℝ) + 8 * (J.card : ℝ) * v) ≤
        k * B₀ * (1 / 2 + 16 * (q : ℝ) ^ 2) * ξ ∧
      8 * r * α * u + B * (8 * T) ≤ α * ξ * (32 * r * M * (q : ℝ) ^ 2 +
        8 * k * B₀ * (1 + 32 * r * (q : ℝ) ^ 2) * ((1 + M) / 2 + 16 * M * (q : ℝ) ^ 2)) := by
  classical
  let ξ := t / (n : ℝ)
  let α := HostCorrection.scale n q
  let Q := B₀ / (n : ℝ) ^ 2
  let u := M * (4 * (q : ℝ) ^ 2 * t / n)
  let v := Q * (4 * (q : ℝ) ^ 2 * t / n)
  let r := (q.choose 2 : ℝ)
  let B := k * (Q * α + 8 * r * α * v)
  let T := D + M * ((Jᶜ : Finset (Edge n)).card : ℝ) + 8 * (J.card : ℝ) * u
  change ξ ≤ 1 → 4 * (1 + r) * outsideBound n q t ≤ 16 * (1 + r) * (q : ℝ) ^ 2 * ξ ∧
    k * (Q * ((Jᶜ : Finset (Edge n)).card : ℝ) + 8 * (J.card : ℝ) * v) ≤
      k * B₀ * (1 / 2 + 16 * (q : ℝ) ^ 2) * ξ ∧
    8 * r * α * u + B * (8 * T) ≤ α * ξ * (32 * r * M * (q : ℝ) ^ 2 +
      8 * k * B₀ * (1 + 32 * r * (q : ℝ) ^ 2) * ((1 + M) / 2 + 16 * M * (q : ℝ) ^ 2))
  intro hξ
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hα : 0 ≤ α := by dsimp [α, HostCorrection.scale]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hB : 0 ≤ B := by dsimp [B, r]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hξ0 : 0 ≤ ξ := by dsimp [ξ]; positivity
  have hd : ((Jᶜ : Finset (Edge n)).card : ℝ) ≤ (n : ℝ) * t / 2 := by
    have hh := sparse_card_bound (incidence (V := Fin n) 2) (Jᶜ : Finset (Edge n))
      t (incidence_row_sum 2) hdeg
    simp only [Fintype.card_fin] at hh
    linarith only [hh]
  have hj : (J.card : ℝ) ≤ (n : ℝ) ^ 2 / 2 := by
    have hc : (J.card : ℝ) ≤ Fintype.card (Edge n) := by exact_mod_cast J.card_le_univ
    rw [edge_card n (by omega)] at hc
    nlinarith only [hc, hnpos]
  have hu_eq : u = M * (4 * (q : ℝ) ^ 2 * ξ) := by dsimp [u, ξ]; ring
  have hv_eq : v = Q * (4 * (q : ℝ) ^ 2 * ξ) := by dsimp [v, ξ]; ring
  have hQ_eq : Q * (n : ℝ) ^ 2 = B₀ := div_mul_cancel₀ _ (pow_ne_zero _ hnpos.ne')
  have hnξ : (n : ℝ) * ξ = t := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hnpos.ne'
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ 4 * (1 + r) * (4 * (q : ℝ) ^ 2 * t / n) :=
        mul_le_mul_of_nonneg_left (outsideBound_le n q hq hn t ht) (by positivity)
      _ = _ := by dsimp [ξ]; ring
  · calc
      _ ≤ k * (Q * ((n : ℝ) * t / 2) + 8 * ((n : ℝ) ^ 2 / 2) * v) := by
        exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hd hQ)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj (by norm_num)) hv)) hk
      _ = k * (Q * (n : ℝ) ^ 2) * (1 / 2 + 16 * (q : ℝ) ^ 2) * ξ := by
        rw [hv_eq, ← hnξ]
        ring
      _ = _ := by rw [hQ_eq]
  · have hB_bound : B ≤ k * Q * α * (1 + 32 * r * (q : ℝ) ^ 2) := by
      have hv' : v ≤ Q * (4 * (q : ℝ) ^ 2) := by
        rw [hv_eq, ← mul_assoc]
        simpa using mul_le_mul_of_nonneg_left hξ (show 0 ≤ Q * (4 * (q : ℝ) ^ 2) by positivity)
      calc
        _ ≤ k * (Q * α + 8 * r * α * (Q * (4 * (q : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_left
            (add_le_add (le_refl (Q * α))
              (mul_le_mul_of_nonneg_left hv' (show 0 ≤ 8 * r * α by positivity))) hk
        _ = _ := by ring
    have hT_bound : T ≤ (n : ℝ) ^ 2 * ξ * ((1 + M) / 2 + 16 * M * (q : ℝ) ^ 2) := by
      calc
        _ ≤ (n : ℝ) * t / 2 + M * ((n : ℝ) * t / 2) + 8 * ((n : ℝ) ^ 2 / 2) * u :=
          add_le_add (add_le_add hDcard (mul_le_mul_of_nonneg_left hd hM))
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hj (by norm_num)) hu)
        _ = _ := by rw [hu_eq, ← hnξ]; ring
    calc
      _ ≤ 8 * r * α * u + (k * Q * α * (1 + 32 * r * (q : ℝ) ^ 2)) *
          (8 * ((n : ℝ) ^ 2 * ξ * ((1 + M) / 2 + 16 * M * (q : ℝ) ^ 2))) := by
        exact add_le_add (le_refl (8 * r * α * u)) (mul_le_mul hB_bound
          (mul_le_mul_of_nonneg_left hT_bound (by norm_num)) (by positivity) (by positivity))
      _ = α * ξ * (32 * r * M * (q : ℝ) ^ 2 +
          8 * k * (Q * (n : ℝ) ^ 2) * (1 + 32 * r * (q : ℝ) ^ 2) *
            ((1 + M) / 2 + 16 * M * (q : ℝ) ^ 2)) := by rw [hu_eq]; ring
      _ = _ := by rw [hQ_eq]

/-- A basal packing with small deleted degree admits a positive seed with
the exact residual type histogram and unit loads on all remaining edges. -/
theorem repair_after_packing {n q : ℕ} (hq : 3 ≤ q) (hn : 2 * q ^ 2 ≤ n)
    (colour : Fin n → C) (ref : C) (d : ℕ) (s G : ℝ)
    (hs : 0 < s) (hG : 0 ≤ G) (hclasses : ∀ i, d + q ≤ profile colour univ i)
    (hdn : s * (n : ℝ) ≤ d)
    (g : High C q ref → TypeProfile C q → ℝ) (hg : ∀ j v, |g j v| ≤ G)
    (hcoord : ∀ i j : High C q ref, g j i.val = if i = j then 1 else 0)
    (hmargin : ∀ j i₁ i₂, ∑ v, g j v * (SlotPairMargins.orderedCount v i₁ i₂ : ℝ) = 0)
    (P : Finset (Clique n q)) (J : Finset (Edge n)) (t M δ : ℝ)
    (ht : 0 ≤ t) (hM : 0 ≤ M) (hδ : 0 < δ)
    (hpacking : ∀ e : Edge n,
      ((P.filter fun b => e ∈ resources n q b).card : ℝ) = if e ∈ J then 0 else 1)
    (hdeg : ∀ v : Fin n, ∑ f : (Jᶜ : Finset (Edge n)), incidence 2 f v ≤ t)
    (w : Clique n q → ℝ)
    (hw : ∀ b, |w b| ≤ M * HostCorrection.scale n q) (hwpos : ∀ b, δ ≤ w b)
    (hseed : ∀ e : Edge n, WeightedEnergy.load (resources n q) w e = 1) :
    let ξ := t / (n : ℝ)
    let α := HostCorrection.scale n q
    let B₀ := G * (q.factorial : ℝ) ^ Fintype.card C / s ^ q
    let k := (Fintype.card (High C q ref) : ℝ)
    let r := (q.choose 2 : ℝ)
    let E := α * ξ * (32 * r * M * (q : ℝ) ^ 2 +
      8 * k * B₀ * (1 + 32 * r * (q : ℝ) ^ 2) * ((1 + M) / 2 + 16 * M * (q : ℝ) ^ 2))
    ξ ≤ 1 →
    16 * (1 + r) * (q : ℝ) ^ 2 * ξ ≤ 1 / 2 →
    k * B₀ * (1 / 2 + 16 * (q : ℝ) ^ 2) * ξ ≤ 1 / 2 →
    E ≤ δ / 2 →
    ∃ w' : HostCorrection.availableBlocks n q J → ℝ,
      HostCorrection.hostIncidence n q J *ᵥ w' = (fun _ => 1) ∧
      hostHistogram colour J w' =
        (fun i => histogram colour w i - histogram colour (fun b => if b ∈ P then 1 else 0) i) ∧
      (∀ b, 0 < w' b) ∧ (∀ b, |w' b - w b| ≤ E) := by
  classical
  dsimp only
  intro hξ hgram hcoord_small hpos
  let B₀ := G * (q.factorial : ℝ) ^ Fintype.card C / s ^ q
  let k := (Fintype.card (High C q ref) : ℝ)
  let D := (P.card : ℝ)
  let m (i : TypeProfile C q) :=
    histogram colour w i - histogram colour (fun b => if b ∈ P then 1 else 0) i
  have hn6 : 6 ≤ n := by nlinarith
  have hDcard := basal_card_le_of_degree (show 2 ≤ q by omega) P J t hpacking hdeg
  obtain ⟨hsmall, hnear, herror⟩ := thresholds_of_degree hn6 hq J t B₀ k M D
    ht (by dsimp [B₀]; positivity) (by dsimp [k]; positivity) hM
    (by dsimp [D]; positivity) hdeg hDcard hξ
  have htarget (i : High C q ref) : |m i.val - histogram colour w i.val| ≤ D := by
    have heq : m i.val - histogram colour w i.val =
        -histogram colour (fun b => if b ∈ P then 1 else 0) i.val := by dsimp [m]; ring
    rw [heq, abs_neg]
    exact basal_histogram_le_card colour P i.val
  obtain ⟨w', hload, hhist, hpositive, hbound⟩ :=
    repair_after_deletion hq hn colour ref d s G hs hG hclasses hdn g hg hcoord hmargin
      J t M D δ ht hM (by dsimp [D]; positivity) hδ hdeg (hsmall.trans hgram)
      w m hw hwpos hseed (compatible_after_packing colour w P J hseed hpacking)
      htarget (hnear.trans hcoord_small) (herror.trans hpos)
  exact ⟨w', hload, hhist, hpositive, fun b => (hbound b).trans herror⟩

end KqR75.ResidualSeed

#print axioms KqR75.ResidualSeed.compatible_after_packing
#print axioms KqR75.ResidualSeed.basal_histogram_le_card
#print axioms KqR75.ResidualSeed.basal_card_le_of_degree
#print axioms KqR75.ResidualSeed.repair_after_deletion
#print axioms KqR75.ResidualSeed.thresholds_of_degree
#print axioms KqR75.ResidualSeed.repair_after_packing
