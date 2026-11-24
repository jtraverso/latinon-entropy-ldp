module
public import ReserveDeletion
public import PackingJoin

@[expose] public section
noncomputable section
namespace KqR75.SeedScales

open Filter Finset ColouredCliques SlotProfiles CompleteJohnson SparseGram ProfileBalance CliqueGram
open scoped Matrix Topology

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Repair the seed after removing the basal packings and the reserve.
The final diffuse envelope and reserve histogram-loss coefficient are
independent of the degree bound on the basal packings. -/
theorem eventually_repaired_host (q : ℕ) (hq : 3 ≤ q) (ref : C)
    (s G W a D U z : ℝ) (hs : 0 < s) (hG : 0 ≤ G) (hW : 0 ≤ W) (ha : 0 < a)
    (hD : 0 ≤ D) (hU : 0 ≤ U) (hz : 0 < z) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (colour : Fin n → C) (d : ℕ),
        (∀ i, d + q ≤ profile colour univ i) → s * (n : ℝ) ≤ d →
      ∀ (g : High C q ref → TypeProfile C q → ℝ),
        (∀ j v, |g j v| ≤ G) →
        (∀ i j : High C q ref, g j i.val = if i = j then 1 else 0) →
        (∀ j i₁ i₂, ∑ v, g j v * (SlotPairMargins.orderedCount v i₁ i₂ : ℝ) = 0) →
      ∀ (P : Finset (Clique n q)) (J₀ X : Finset (Edge n)) (t tX : ℝ),
        0 ≤ t → 0 ≤ tX → t ≤ D * (n : ℝ) ^ (1 - z) → tX ≤ U * (n : ℝ) ^ (1 - z) →
        PhysicalCompletion.packs P J₀ᶜ →
        (∀ v : Fin n, ∑ e : ((J₀ ∩ Xᶜ)ᶜ : Finset (Edge n)), incidence 2 e v ≤ t) →
        (∀ v : Fin n, ∑ e : X, incidence 2 e v ≤ tX) →
      ∀ (w : Clique n q → ℝ),
        (∀ b, |w b| ≤ W * HostCorrection.scale n q) →
        (∀ b, a * HostCorrection.scale n q ≤ w b) →
        (∀ e : Edge n, WeightedEnergy.load (resources n q) w e = 1) →
        let J := J₀ ∩ Xᶜ
        let α := HostCorrection.scale n q
        ∃ w' : HostCorrection.availableBlocks n q J → ℝ,
          HostCorrection.hostIncidence n q J *ᵥ w' = (fun _ => 1) ∧
          (∀ b, a * α / 4 ≤ w' b ∧ w' b ≤ (W + 1) * α) ∧
          (∀ b, |w' b - w b| ≤ α * (E * (n : ℝ) ^ (-z))) ∧
          ∀ i, |histogram colour w i - (BankCapacity.integerHistogram colour P i : ℝ) -
            hostHistogram colour J w' i| ≤
            ((W + 1) * (1 / 2 + 16 * (q : ℝ) ^ 2) * U) * (n : ℝ) ^ (2 - z) := by
  obtain ⟨L, hL, hfirst⟩ := eventually_repair_after_packing q hq ref s G W a D z
    hs hG hW ha hz
  let F := 32 * (q.choose 2 : ℝ) * (W + 1) * (q : ℝ) ^ 2 * U
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let E := L + F
  have hE : 0 ≤ E := add_nonneg hL hF
  have hsecond := ReserveDeletion.eventually_repair_loads (C := C) q hq
    (W + 1) (a / 2) D U z (by positivity) (by positivity) hD hU hz
  have htend : Tendsto (fun n : ℕ => E * (n : ℝ) ^ (-z)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using
      ((tendsto_rpow_neg_atTop hz).comp tendsto_natCast_atTop_atTop).const_mul E
  have hsmall := htend.eventually_lt_const (lt_min zero_lt_one (half_pos ha))
  refine ⟨E, hE, ?_⟩
  filter_upwards [hfirst, hsecond, hsmall] with n hf hs' hsmall
  intro colour d hclasses hdn g hg hcoord hmargin P J₀ X t tX ht htX htD htU hP hdeg hdegX
    w hw hwa hload
  let J := J₀ ∩ Xᶜ
  let α := HostCorrection.scale n q
  have hα : 0 ≤ α := by dsimp [α, HostCorrection.scale]; positivity
  have hnz : 0 ≤ (n : ℝ) ^ (-z) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hLsmall : L * (n : ℝ) ^ (-z) ≤ min 1 (a / 2) :=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hF) hnz).trans hsmall.le
  have hP' (e : Edge n) : ((P.filter (fun b => e ∈ resources n q b)).card : ℝ) =
      if e ∈ J₀ then 0 else 1 := by
    have he := hP e
    change (P.filter (fun b => e ∈ resources n q b)).card = _ at he
    by_cases hm : e ∈ J₀
    · simp [hm] at he ⊢
      exact_mod_cast he
    · simp [hm] at he ⊢
      exact_mod_cast he
  have hdeg₀ (v : Fin n) : ∑ e : (J₀ᶜ : Finset (Edge n)), incidence 2 e v ≤ t := by
    refine le_trans ?_ (hdeg v)
    rw [sum_coe_sort J₀ᶜ (fun e : Edge n => incidence 2 e v),
      sum_coe_sort Jᶜ (fun e : Edge n => incidence 2 e v)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro e he
      simp only [mem_compl] at he ⊢
      exact fun hj => he (mem_inter.mp hj).1
    · intro e _ _
      simp [incidence]
      split_ifs <;> norm_num
  obtain ⟨w₀, hl₀, hhist₀, _, hpert₀⟩ :=
    hf colour d hclasses hdn g hg hcoord hmargin P J₀ t ht htD hP' hdeg₀ w hw hwa hload
  have hdiff₀ (b : HostCorrection.availableBlocks n q J₀) :
      |w₀ b - w b| ≤ α * min 1 (a / 2) :=
    (hpert₀ b).trans (mul_le_mul_of_nonneg_left hLsmall hα)
  have hupper₀ (b : HostCorrection.availableBlocks n q J₀) : |w₀ b| ≤ (W + 1) * α := by
    rw [show w₀ b = (w₀ b - w b) + w b by ring]
    have hδ : |w₀ b - w b| ≤ α := (hdiff₀ b).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (min_le_left 1 (a / 2)) hα)
    exact (abs_add_le _ _).trans ((add_le_add hδ (hw b)).trans_eq (by ring))
  have hlower₀ (b : HostCorrection.availableBlocks n q J₀) : (a / 2) * α ≤ w₀ b := by
    have hg := (hdiff₀ b).trans (mul_le_mul_of_nonneg_left (min_le_right 1 (a / 2)) hα)
    have hneg := (abs_le.mp hg).1
    nlinarith only [hneg, hwa b]
  obtain ⟨w', hl', ha', hp', hh'⟩ :=
    hs' colour J₀ X t tX ht htX htD htU hdeg hdegX w₀ hupper₀ hlower₀ hl₀
  have hcomp (b : HostCorrection.availableBlocks n q J) :
      |w' b - w b| ≤ α * (E * (n : ℝ) ^ (-z)) := by
    have hj : resources n q (b : Clique n q) ⊆ J := (mem_filter.mp b.property).2
    let b₀ : HostCorrection.availableBlocks n q J₀ :=
      ⟨b.val, mem_filter.mpr ⟨mem_univ _, hj.trans inter_subset_left⟩⟩
    have hb₀ : extend J₀ w₀ b = w₀ b₀ := extend_coe J₀ w₀ b₀
    have he := hp' b
    rw [hb₀] at he
    have h₀ := hpert₀ b₀
    calc
      _ ≤ |w' b - w₀ b₀| + |w₀ b₀ - w b| := abs_sub_le _ _ _
      _ ≤ α * (F * (n : ℝ) ^ (-z)) + α * (L * (n : ℝ) ^ (-z)) := add_le_add he h₀
      _ = _ := by dsimp [E]; ring
  refine ⟨w', hl', fun b => ⟨?_, ?_⟩, hcomp, ?_⟩
  · linarith only [ha' b]
  · have hδ := (hcomp b).trans (mul_le_mul_of_nonneg_left
      (hsmall.le.trans (min_le_left 1 (a / 2))) hα)
    nlinarith only [(abs_le.mp hδ).2, (le_abs_self _).trans (hw b)]
  · intro i
    have hb := congrFun hhist₀ i
    rw [BankCapacity.histogram_indicator] at hb
    rw [← hb]
    exact hh' i

end KqR75.SeedScales

#print axioms KqR75.SeedScales.eventually_repaired_host
