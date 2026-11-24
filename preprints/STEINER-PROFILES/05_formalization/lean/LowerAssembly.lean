module
public import LowerGeometry
public import LowerSeedInputs
public import LowerHostEvent
public import RepairedHostSeed

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Filter Finset ColouredCliques CompleteJohnson CliqueGram SparseGram SlotProfiles
open WeightedGreedy ProfileBalance CoverDown
open PhysicalBank (basalBlocks)
open BankCapacity (integerHistogram edge_card_of_degree)

variable {C K : Type*} [Fintype C] [DecidableEq C] [Field K] [Fintype K] [DecidableEq K]

private theorem remaining_subset_host {n q : ℕ} (J : Finset (Edge n))
    (h : List (Option (Clique n q))) : remaining (resources n q) J h ⊆ J := by
  induction h with
  | nil => exact Subset.rfl
  | cons b h ih =>
    cases b with
    | none => exact ih
    | some b => exact sdiff_subset.trans ih

theorem eventually_lower_of_omni (q : ℕ) (hq : 3 ≤ q) (ρ κ : ℝ)
    (hρ : 0 < ρ) (hκ : 0 < κ) (ref : C) (s : Fin q → K) (hs : Function.Injective s)
    (homni : PhysicalOmniPlacement q (GreedyScales.criticalExponent q)) :
    ∃ err : ℝ, 0 ≤ err ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (colour : Fin n → C) (m : TypeProfile C q → ℤ),
      (∀ c, ρ * (n : ℝ) ≤ (profile colour univ c : ℝ)) →
      (∀ e : Edge n, pairMargin colour (fun t => (m t : ℝ)) e =
        (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ)) →
      (∀ t, κ * ((Fintype.card (Edge n) : ℝ) / (q.choose 2 : ℝ)) ≤ (m t : ℝ)) →
      q.choose 2 ∣ n.choose 2 → q - 1 ∣ n - 1 →
      let r := q.choose 2
      let z := GreedyScales.criticalExponent q
      let B := (Fintype.card (Edge n) : ℝ) / (r : ℝ)
      0 < (designFibre colour m).card ∧
        -(∑ t, (m t : ℝ) * Real.log ((m t : ℝ) /
          ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ))) -
        ((r : ℝ) - 1) * B - err * ((n : ℝ) ^ (2 - z) * Real.log n) ≤
          Real.log ((designFibre colour m).card : ℝ) := by
  classical
  let r := q.choose 2
  let z := GreedyScales.criticalExponent q
  let a := (2 * (q : ℝ) - 1) * z
  let s₀ := ρ / 4
  let W := (q.factorial : ℝ) ^ Fintype.card C / s₀ ^ q
  let ℓ := (κ / (4 * (r : ℝ))) / ((2 : ℝ) ^ (q - 2) * ((q - 2).factorial : ℝ))
  have hq' : 2 ≤ q := by omega
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.choose_pos hq'
  have hr₁ : (1 : ℝ) ≤ r := by exact_mod_cast Nat.choose_pos hq'
  have hs₀ : 0 < s₀ := by dsimp [s₀]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hℓ : 0 < ℓ := by dsimp [ℓ]; positivity
  obtain ⟨hz, _, hza, ha, _, _⟩ := critical_completion_scales q hq
  have hzle : z ≤ 2 := by linarith
  have ha₀ : 0 ≤ a := hz.le.trans hza
  have ha₂ : a ≤ 2 := ha.trans (by norm_num)
  have hin := eventually_interior_seed (C := C) q hq ρ κ hρ hκ
  obtain ⟨D, hD, hcount⟩ := eventually_lower_with_recovering_host (C := C) q hq ℓ
    (W + 1) hℓ (by positivity)
  obtain ⟨tag, j, B, _, hB, hcomplete⟩ := complete_with_capacity hq s hs ref
  let coeff : ℝ := (W + 1) * (1 / 2 + 16 * (q : ℝ) ^ 2)
  have hcoeff : 0 ≤ coeff := by dsimp [coeff]; positivity
  obtain ⟨U, G, T, hU, hG, hT, hgeometry⟩ := eventually_lower_geometry q hq ρ hρ
    ref s hs tag j B hB coeff (D + 2) hcoeff (by linarith) homni
  obtain ⟨L, hL, g, hgb, hgc, hgm⟩ := PhysicalProfileLifts.bounded_directions s hs ref
  let dAll := G + U + T
  have hdAll : 0 ≤ dAll := by dsimp [dAll]; positivity
  obtain ⟨E, hE, hrepair⟩ := SeedScales.eventually_repaired_host q hq ref s₀ L W ℓ dAll U z
    hs₀ hL hW.le hℓ hdAll hU.le hz
  obtain ⟨err, herr, hlower⟩ := hcount E (coeff * U) (T + G) hE
    (mul_nonneg hcoeff hU.le) (by positivity)
  refine ⟨err, herr, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ), hin, hgeometry, hrepair, hlower,
    PhysicalHorizonCounts.eventually_dense dAll z hz] with n hn hi hg hp hl hdense
  intro colour m hclasses hmargin hinterior hsize hdegree
  obtain ⟨d, hd, hdn, hwl, hwu, hload⟩ := hi colour (fun t => (m t : ℝ)) hclasses hinterior hmargin
  have hcls (i : C) : q ≤ profile colour univ i := by have := hd i; omega
  obtain ⟨A, X, F, f, hAX, hAF, hXF, hcolour, hsep, hbank, hX, hA, hF, habs, hcover⟩ :=
    hg colour hclasses
  have he : Divisible q (∅ : Finset (Edge n)) := by
    constructor
    · simp
    · intro v
      simp [CoverDown.degree, vertexSets]
  obtain ⟨P₀, hP₀⟩ := habs ∅ (empty_subset X) he
  rw [union_empty] at hP₀
  let PB := basalBlocks hq' j s hs f
  let P := PB ∪ P₀
  have hP : packs P (F ∪ A) := packs_union hq' hbank hP₀ hAF.symm
  let J₀ : Finset (Edge n) := (F ∪ A)ᶜ
  let J := (A ∪ X ∪ F)ᶜ
  have hJ : J₀ ∩ Xᶜ = J := by
    ext e
    simp [J₀, J]
    tauto
  have hP' : packs P J₀ᶜ := by simpa [J₀] using hP
  let scale := (n : ℝ) ^ (1 - z)
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hdeg (v : Fin n) : (∑ e : (Jᶜ : Finset (Edge n)), incidence 2 e v) ≤ dAll * scale := by
    have hdF : Disjoint (A ∪ X) F := disjoint_union_left.mpr ⟨hAF, hXF⟩
    have hcompl : Jᶜ = A ∪ X ∪ F := compl_compl _
    have hs : (∑ e : (Jᶜ : Finset (Edge n)), incidence 2 e v) =
        (∑ e : A, incidence 2 e v) + (∑ e : X, incidence 2 e v) +
        (∑ e : F, incidence 2 e v) := by
      calc
        _ = ∑ e ∈ Jᶜ, incidence 2 e v :=
          sum_coe_sort Jᶜ (fun e : Edge n => incidence 2 e v)
        _ = _ := by
          rw [hcompl, sum_union hdF, sum_union hAX]
          rw [sum_coe_sort A (fun e : Edge n => incidence 2 e v),
            sum_coe_sort X (fun e : Edge n => incidence 2 e v),
            sum_coe_sort F (fun e : Edge n => incidence 2 e v)]
    rw [hs]
    change _ ≤ (G + U + T) * scale
    linarith only [hA v, hX v, hF v]
  have hdeg' (v : Fin n) :
      (∑ e : ((J₀ ∩ Xᶜ)ᶜ : Finset (Edge n)), incidence 2 e v) ≤ dAll * scale := by
    rw [hJ]
    exact hdeg v
  have hhost := hp colour d hd hdn g hgb hgc hgm
    P J₀ X (dAll * scale) (U * scale) (mul_nonneg hdAll hscale) (mul_nonneg hU.le hscale)
    le_rfl le_rfl hP' hdeg' hX _ hwu hwl hload
  dsimp only at hhost
  rw [hJ] at hhost
  obtain ⟨w, hwload, hwbound, hdiff, hmass⟩ := hhost
  have hJdense := hdense J (dAll * scale) le_rfl hdeg
  have hJpos : 0 < J.card := by
    have hh : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    exact_mod_cast (lt_of_lt_of_le (by positivity : (0 : ℝ) < (n : ℝ) ^ 2 / 4) hJdense)
  have hbound (b : HostCorrection.availableBlocks n q J) :
      0 ≤ w b ∧ w b ≤ (W + 1) * HostCorrection.scale n q :=
    ⟨(by unfold HostCorrection.scale; positivity : 0 ≤ ℓ * HostCorrection.scale n q / 4).trans
      (hwbound b).1, (hwbound b).2⟩
  have hseed (b : Clique n q) : ℓ * HostCorrection.scale n q ≤
      ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ)) b ∧
      ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ)) b ≤
        (W + 1) * HostCorrection.scale n q :=
    ⟨hwl b, (abs_le.mp (hwu b)).2.trans
      (mul_le_mul_of_nonneg_right (by linarith) (by unfold HostCorrection.scale; positivity))⟩
  have hbaseCard : (P.card : ℝ) ≤ (T + G) * (n : ℝ) ^ (2 - z) := by
    have hcardP : P.card ≤ (F ∪ A).card := by
      apply BankCapacity.block_card_of_marking P (F ∪ A)
      · intro e
        change PhysicalBank.edgeMultiplicity P e ≤ 1
        rw [hP e]
        split_ifs <;> omega
      · intro b hb
        have hne : (resources n q b).Nonempty := by
          apply card_pos.mp
          rw [resources_card]
          exact Nat.choose_pos hq'
        obtain ⟨e, he⟩ := hne
        exact ⟨e, mem_inter.mpr ⟨he, edge_of_packs hP hb he⟩⟩
    have hPcard : (P.card : ℝ) ≤ (F.card : ℝ) + A.card := by
      exact_mod_cast hcardP.trans (card_union_le F A)
    have hx : (n : ℝ) * scale = (n : ℝ) ^ (2 - z) := by
      have hn₀ : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      calc
        _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 - z) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hn₀]; congr 1; ring
    have hFcard := edge_card_of_degree F (T * scale) hF
    have hAcard := edge_card_of_degree A (G * scale) hA
    calc
      _ ≤ (n : ℝ) * (T * scale) + (n : ℝ) * (G * scale) := by
        linarith only [hPcard, hFcard, hAcard]
      _ = _ := by rw [← hx]; ring
  have hrepairMass (t : TypeProfile C q) :
      |(m t : ℝ) - (integerHistogram colour P t : ℝ) - hostHistogram colour J w t| ≤
        (coeff * U) * (n : ℝ) ^ (2 - z) := by
    have hh := hmass t
    rw [show histogram colour (ProfileWeights.weight (cliqueType colour) (fun t => (m t : ℝ))) t =
        (m t : ℝ) from seed_mass colour hcls _ t] at hh
    exact hh
  have hmargin' (e : Edge n) : pairMargin colour (fun t => (m t : ℝ)) e =
      ∑ g : Edge n, if profile colour (g : Finset (Fin n)) =
        profile colour (e : Finset (Fin n)) then 1 else 0 := by
    rw [hmargin, sum_boole]
    have hf : (univ.filter fun g : Edge n => profile colour g.val = profile colour e.val) =
        ProfileWeights.fibre (cliqueType colour) (cliqueType colour e) := by
      ext g
      simp only [ProfileWeights.fibre, mem_filter, mem_univ, true_and]
      exact (cliqueType_eq colour g (cliqueType colour e)).symm
    rw [hf, fibre_card]
    rfl
  refine hl colour m P J w hcls hJdense hbound hwload hseed hdiff hrepairMass hbaseCard ?_
  intro h hlen hstop hv htype
  have hprefix := BankCapacity.prefix_histogram_bound hq hn J hJpos colour w
    (fun b => (hbound b).1) hwload a z D ha₀ hzle hza h hv hlen
    (by simpa only [hlen] using htype)
  let M := (J.card : ℝ) / (r : ℝ)
  have hM : 0 < M := div_pos (by exact_mod_cast hJpos) hr
  have hMJ : (J.card : ℝ) = (r : ℝ) * M := by dsimp [M]; field_simp
  have hcard : Fintype.card (Edge n) = n.choose 2 := by
    rw [Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]
  have hMu : M ≤ (n : ℝ) ^ 2 := by
    apply (div_le_self (Nat.cast_nonneg J.card) hr₁).trans
    have hh : J.card ≤ Fintype.card (Edge n) := card_le_univ _
    rw [hcard] at hh
    exact_mod_cast hh.trans (Nat.choose_le_pow n 2)
  have hleave := horizon_leave_for_cover hn a ha₀ ha₂ J M hM hMu hMJ h hlen hv hstop
  have hJX : Disjoint J X := disjoint_left.mpr fun e he hx =>
    mem_compl.mp he (mem_union_left _ (mem_union_right _ hx))
  have hcover' := hcover _ hleave (hJX.mono_left (remaining_subset_host J h))
  exact hcomplete hn colour f hcolour hsep (fun i => hq'.trans (hcls i))
    A X F hAX hAF hXF hbank habs (divisible_complete hsize hdegree)
    G U z (coeff * U) (D + 2) hzle (by positivity) le_rfl hA hX m hmargin' P₀ hP₀
    h (hostHistogram colour J w) hv
    (fun t => (abs_sub_comm _ _).le.trans (hprefix t))
    hrepairMass hcover'

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.eventually_lower_of_omni
