module
public import CoverBudgetScales
public import CoverThresholds
public import CoverSelectors
public import CoverPairSelector

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Filter Finset ReserveCuts ReserveRandom

/-- For every sufficiently large host, one reserve covers every
admissible leave disjoint from it by the two-phase construction. -/
theorem eventually_cover (q : ℕ) (hq : 3 ≤ q) (z M : ℝ) (hz : 0 < z) (hM : 0 ≤ M)
    (hgap : (2 * (q : ℝ) + 1) * z < 1) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K ≥ K₀, ∀ᶠ n : ℕ in atTop,
      ∃ (p : unitInterval) (ω : Sym2 (Fin n) → Bool), (p : ℝ) = K * (n : ℝ) ^ (-z) ∧
        RootGood p ω (q - 1) ∧
        ∀ L : Finset (Finset (Fin n)), (∀ e ∈ L, e.card = 2) →
          (L.card : ℝ) ≤ M * (n : ℝ) ^ (2 - (2 * (q : ℝ) - 1) * z) →
          Disjoint L (reserveEdges (adj ω) univ) →
          ∃ P Y : Finset (Finset (Fin n)), Cover q L (reserveEdges (adj ω) univ) P ∅ Y ∧
            Y.card ≤ q.choose 2 * L.card := by
  classical
  let a := (2 * (q : ℝ) - 1) * z
  let β := 1 - 2 * z
  let γ := 1 - a + 2 * z
  let D := 1 + 4 * ((q.choose 2 : ℝ) + (q - 2 : ℕ)) * M
  let Pmax := (2 : ℝ) + ((q - 2 : ℕ) : ℝ) * 3
  let l := q - 2
  let r := q.choose 2 - 1
  let cs : ℝ := (1 / (4 * ((q - 1 : ℕ) : ℝ))) ^ (q - 1) / 2 ^ (q - 1).choose 2
  let cp : ℝ := (1 / (8 * (l : ℝ))) ^ l / 2 ^ l.choose 2
  have hql : 0 < l := by dsimp [l]; omega
  have hqlR : (0 : ℝ) < l := by exact_mod_cast hql
  have hql' : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < q - 1)
  have hcs : 0 < cs := by dsimp [cs]; positivity
  have hcp : 0 < cp := by dsimp [cp]; positivity
  let Mstar := (q.choose 2 : ℝ) * M * 2 ^ (q - 3)
  let Mlink := 2 * Pmax * 2 ^ (q - 3)
  let Msat := (D + 1) * 2 ^ (q - 3)
  let Mused := (q.choose 2 : ℝ) * M * 2 ^ (q - 4)
  obtain ⟨K₀, hK₀, hgap'⟩ :=
    eventually_cover_ratios q hq z hz Mstar Mlink Msat Mused cs (cp / 4) hcs (by positivity)
  refine ⟨K₀, hK₀, fun K hK => ?_⟩
  have hKp : 0 < K := zero_lt_one.trans_le (hK₀.trans hK)
  filter_upwards [eventually_reserve_counts q hq hKp (show (0 : ℝ) < 1 by norm_num) hz hgap,
    eventually_cover_thresholds q hq z 1 M hz (by norm_num) hM hgap, hgap' K hK,
    eventually_ge_atTop (1 : ℕ)] with n hRes hThresh hRatio hn
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨p, ω, hp, hroot, hclique, hpair, _⟩ := hRes
  refine ⟨p, ω, hp, hroot, ?_⟩
  intro L hL hN hdis
  let B := q.choose 2 * L.card
  let dL := ⌈2 * (n : ℝ) ^ β⌉₊
  let dY := ⌈(n : ℝ) ^ β⌉₊
  let cap := dY + (q - 2) * dL
  let m := ⌈(n : ℝ) ^ β⌉₊
  let zmax := ⌈D * (n : ℝ) ^ γ⌉₊
  have thresholds := hThresh L.card hN
  norm_num at thresholds
  obtain ⟨hY, hP, hm, hZstar, hZpair, hzmax, hcap⟩ :
      q - 2 ≤ dY ∧ q - 1 ≤ cap ∧ m + zmax ≤ dL + 1 ∧
        2 * B ≤ zmax * (dY - (q - 2) + 1) ∧
        2 * (B + (q - 2) * L.card) ≤ zmax * (cap - (q - 1) + 1) ∧
        (zmax : ℝ) ≤ (D + 1) * (n : ℝ) ^ γ ∧ (cap : ℝ) ≤ Pmax * (n : ℝ) ^ β := by
    norm_num [Pmax, a, β, γ, D, B, dL, dY, cap, m, zmax] at thresholds ⊢
    exact thresholds
  have hp0 : 0 < (p : ℝ) := by rw [hp]; positivity
  have hB : (B : ℝ) ≤ (q.choose 2 : ℝ) * M * (n : ℝ) ^ (2 - a) := by
    dsimp [B]
    rw [Nat.cast_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hN (by positivity)
  have hcommon (H : Finset (Fin n)) (hH : H.card < q) :
      ((common (adj ω) univ H).card : ℝ) ≤ 2 * (n : ℝ) * (p : ℝ) ^ H.card :=
    by simpa only [Fintype.card_fin] using (hroot H (by omega)).1
  have hR (v : Fin n) : ¬ adj ω v v := fun h => h.1 rfl
  have ⟨hs, hlink, hsat, hused⟩ := hRatio
  rw [← hp] at hs hlink hsat hused
  have hStarRoom (W : Finset (Fin n)) (hW : m ≤ W.card) :
      (B : ℝ) * ((2 * (n : ℝ)) ^ (q - 3) *
        (p : ℝ) ^ (2 * (q - 3) + (q - 3).choose 2)) < (cliquesIn (adj ω) W (q - 1)).card := by
    have hW' : (n : ℝ) ^ β ≤ W.card :=
      (Nat.le_ceil _).trans (by exact_mod_cast hW)
    have hc := hclique W (q - 1) (by omega) (by simp) (by simpa using hW')
    have hc' := star_candidate_scale (q - 1) hn₀.le (by norm_num : (0 : ℝ) ≤ 1)
      hp0.le (by omega : 0 < q - 1) (by simpa only [one_mul] using hW')
    have hle := mul_le_mul_of_nonneg_right hB (show 0 ≤ (2 * (n : ℝ)) ^ (q - 3) *
      (p : ℝ) ^ (2 * (q - 3) + (q - 3).choose 2) by positivity)
    refine hle.trans_lt ?_
    have hEq : ((q.choose 2 : ℝ) * M * (n : ℝ) ^ (2 - a)) *
        ((2 * (n : ℝ)) ^ (q - 3) * (p : ℝ) ^ (2 * (q - 3) + (q - 3).choose 2)) =
        Mstar * (n : ℝ) ^ (((q - 3 : ℕ) : ℝ) + 2 - a) * (p : ℝ) ^ ((q - 1).choose 2 - 1) := by
      rw [star_edge_exponent hq, mul_pow, ← Real.rpow_natCast (n : ℝ) (q - 3),
        show ((q - 3 : ℕ) : ℝ) + 2 - a = ((q - 3 : ℕ) : ℝ) + (2 - a) by ring,
        Real.rpow_add hn₀]
      dsimp [Mstar]
      ring
    rw [hEq]
    rw [mul_comm β ((q - 1 : ℕ) : ℝ)] at hc'
    exact hs.trans_le (hc'.trans hc)

  have hPairRoom (u v : Fin n) (huv : u ≠ v) :
      ((zmax + 2 * cap : ℕ) : ℝ) *
          ((2 * (n : ℝ)) ^ (q - 3) * (p : ℝ) ^ (3 * (q - 3) + (q - 3).choose 2)) +
        (B : ℝ) * (if 4 ≤ q then
          (2 * (n : ℝ)) ^ (q - 4) * (p : ℝ) ^ (4 * (q - 4) + (q - 4).choose 2) else 0) <
        (rootedExtensions (adj ω) univ u v l).card := by
    let Vbound := (2 * (n : ℝ)) ^ (q - 3) * (p : ℝ) ^ (3 * (q - 3) + (q - 3).choose 2)
    let Ebound := if 4 ≤ q then
      (2 * (n : ℝ)) ^ (q - 4) * (p : ℝ) ^ (4 * (q - 4) + (q - 4).choose 2) else 0
    let W := (n : ℝ) ^ l * (p : ℝ) ^ r
    have hW : 0 < W := by dsimp [W]; positivity
    have hv0 : 0 ≤ Vbound := by dsimp [Vbound]; positivity
    have h1 : (2 * (cap : ℝ)) * Vbound < (cp / 4) * W := by
      have hcap' := mul_le_mul_of_nonneg_left hcap (show (0 : ℝ) ≤ 2 by norm_num)
      refine (mul_le_mul_of_nonneg_right hcap' hv0).trans_lt ?_
      have he : (2 * (Pmax * (n : ℝ) ^ β)) * Vbound =
          Mlink * (n : ℝ) ^ (((q - 3 : ℕ) : ℝ) + 1 - 2 * z) * (p : ℝ) ^ (r - 2) := by
        dsimp [Vbound, Mlink, β, r]
        rw [pair_vertex_exponent hq, mul_pow, ← Real.rpow_natCast (n : ℝ) (q - 3),
          show ((q - 3 : ℕ) : ℝ) + 1 - 2 * z = ((q - 3 : ℕ) : ℝ) + (1 - 2 * z) by ring,
          Real.rpow_add hn₀]
        ring
      rw [he]
      simpa only [W, Real.rpow_natCast, mul_assoc] using hlink
    have h2 : (zmax : ℝ) * Vbound < (cp / 4) * W := by
      refine (mul_le_mul_of_nonneg_right hzmax hv0).trans_lt ?_
      have he : ((D + 1) * (n : ℝ) ^ γ) * Vbound =
          Msat * (n : ℝ) ^ (((q - 3 : ℕ) : ℝ) + 1 - a + 2 * z) * (p : ℝ) ^ (r - 2) := by
        dsimp [Vbound, Msat, γ, r]
        rw [pair_vertex_exponent hq, mul_pow, ← Real.rpow_natCast (n : ℝ) (q - 3)]
        have hh : (n : ℝ) ^ (((q - 3 : ℕ) : ℝ) + 1 - a + 2 * z) =
            (n : ℝ) ^ (((q - 3 : ℕ) : ℝ)) * (n : ℝ) ^ (1 - a + 2 * z) := by
          rw [← Real.rpow_add hn₀]
          congr 1
          ring
        rw [hh]
        ring
      rw [he]
      simpa only [W, Real.rpow_natCast, mul_assoc] using hsat
    have h3 : (B : ℝ) * Ebound < (cp / 4) * W := by
      by_cases hq4 : 4 ≤ q
      · have he0 : 0 ≤ Ebound := by dsimp [Ebound]; rw [ite_eq_left hq4]; positivity
        refine (mul_le_mul_of_nonneg_right hB he0).trans_lt ?_
        have he : ((q.choose 2 : ℝ) * M * (n : ℝ) ^ (2 - a)) * Ebound =
            Mused * (n : ℝ) ^ (((q - 4 : ℕ) : ℝ) + 2 - a) * (p : ℝ) ^ (r - 5) := by
          dsimp [Ebound, Mused, r]
          rw [ite_eq_left hq4, pair_edge_exponent hq4, mul_pow,
            ← Real.rpow_natCast (n : ℝ) (q - 4),
            show ((q - 4 : ℕ) : ℝ) + 2 - a = ((q - 4 : ℕ) : ℝ) + (2 - a) by ring,
            Real.rpow_add hn₀]
          ring
        rw [he]
        simpa only [W, Real.rpow_natCast, mul_assoc] using hused hq4
      · have hzero : Ebound = 0 := ite_eq_right hq4
        rw [hzero, mul_zero]
        positivity
    have hTotal : ((zmax + 2 * cap : ℕ) : ℝ) * Vbound + (B : ℝ) * Ebound < cp * W := by
      push_cast
      nlinarith only [h1, h2, h3, mul_pos hcp hW]
    have hLower : cp * W ≤ (rootedExtensions (adj ω) univ u v l).card := by
      have he := pair_candidate_scale hq (n : ℝ) (p : ℝ)
      change cp * (n : ℝ) ^ l * (p : ℝ) ^ r = _ at he
      dsimp [W]
      rw [← mul_assoc, he]
      exact hpair u v huv
    exact hTotal.trans_le hLower

  refine cover_two_phases (adj ω) univ L q dL dY cap hq hdis (by rfl) ?_ ?_
  · intro J Y hJ hsub hYcard _ u hu
    obtain ⟨C, hpw, hnC, hsize, hJY, hc⟩ := select_star (adj ω) hR (p : ℝ) hp0.le
      q dL dY m zmax B hq hY (by simpa only [Fintype.card_fin] using hcommon)
      hZstar hm (by simpa only [Fintype.card_fin] using hStarRoom) J Y
      (fun f hf => hL f (hJ hf))
      (fun f hf => (mem_powersetCard.mp (mem_filter.mp (hsub hf)).1).2)
      (hYcard.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))) u hu
    exact ⟨C, subset_univ _, hpw, hnC, hsize, hJY, hc⟩
  · intro J Y hJ hsub hYcard hpot e he
    exact select_pair (adj ω) hR (p : ℝ) hp0.le q cap zmax B L.card hq hP
      (by simpa only [Fintype.card_fin] using hcommon) hZpair
      (by simpa only [Fintype.card_fin] using hPairRoom) J Y
      (fun f hf => (mem_powersetCard.mp (mem_filter.mp (hsub hf)).1).2)
      (fun f hf => hL f (hJ hf)) (card_le_card hJ)
      (hYcard.trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))) hpot e he

end KqR75.CoverDown

#print axioms KqR75.CoverDown.eventually_cover
