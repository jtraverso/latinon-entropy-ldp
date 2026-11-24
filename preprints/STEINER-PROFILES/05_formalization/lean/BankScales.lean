module
public import PhysicalBank
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section
noncomputable section
namespace KqR75.BankScales

open Filter Finset ColouredCliques SlotProfiles

/-- The rounding of the placement budget and capacity preserves the
degree exponent. The host threshold is independent of the cells and host. -/
theorem eventually_parameters (slots : ℕ) {ρ z B D : ℝ}
    (hρ : 0 < ρ) (hz : 0 < z) (hz₁ : z ≤ 1) (hB : 0 ≤ B) :
    ∃ G : ℝ, 0 < G ∧ ∀ᶠ n : ℕ in atTop,
      ∀ cells degree : ℕ, (cells : ℝ) ≤ B * (n : ℝ) ^ (2 - z) →
        (degree : ℝ) ≤ D * (n : ℝ) ^ (1 - z) →
        ∃ cap budget : ℕ, 0 < cap ∧ cells * slots ≤ budget * cap ∧
          (↑(slots * cap) : ℝ) ≤ G * (n : ℝ) ^ (1 - z) ∧
          (↑(budget + slots * (degree + slots * cap + 1)) : ℝ) < ρ * n := by
  let H : ℝ := 1 + 4 * slots * B / ρ
  let G : ℝ := 1 + slots * (H + 1)
  let L : ℝ := slots * (D + G + 1)
  have hH : 0 < H := by dsimp [H]; positivity
  have hG : 0 < G := by dsimp [G]; positivity
  refine ⟨G, hG, ?_⟩
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ z) atTop atTop :=
    (tendsto_rpow_atTop hz).comp hnat
  have hnlarge : ∀ᶠ n : ℕ in atTop, max 1 (4 / ρ) ≤ (n : ℝ) :=
    (tendsto_atTop.1 hnat) _
  have hplarge : ∀ᶠ n : ℕ in atTop, L / (ρ / 2) < (n : ℝ) ^ z :=
    hpow.eventually_gt_atTop _
  filter_upwards [hnlarge, hplarge] with n hn hb
  intro cells degree hcells hdegree
  have hn₁ : (1 : ℝ) ≤ n := (le_max_left _ _).trans hn
  have hn₀ : 0 < (n : ℝ) := by linarith
  have hnρ : 4 ≤ ρ * (n : ℝ) := by
    have hh := (div_le_iff₀ hρ).mp ((le_max_right _ _).trans hn)
    rwa [mul_comm] at hh
  let P := (n : ℝ) ^ (1 - z)
  have hP : 1 ≤ P := Real.one_le_rpow hn₁ (by linarith)
  have hP₀ : 0 < P := by linarith
  have hNP : (n : ℝ) * P = (n : ℝ) ^ (2 - z) := by
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * P := by rw [Real.rpow_one]
      _ = _ := by dsimp [P]; rw [← Real.rpow_add hn₀]; congr 1; ring
  have hPz : (n : ℝ) ^ z * P = n := by
    dsimp [P]
    rw [← Real.rpow_add hn₀, show z + (1 - z) = 1 by ring, Real.rpow_one]
  let cap := ⌈H * P⌉₊
  let budget := ⌊ρ * (n : ℝ) / 2⌋₊
  have hc₀ : H * P ≤ (cap : ℝ) := Nat.le_ceil _
  have hc : (cap : ℝ) ≤ (H + 1) * P := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ H * P by positivity)
    change (cap : ℝ) < H * P + 1 at hh
    linarith
  have hb₀ : ρ * (n : ℝ) / 4 ≤ (budget : ℝ) := by
    have hh := Nat.lt_floor_add_one (ρ * (n : ℝ) / 2)
    change ρ * (n : ℝ) / 2 < (budget : ℝ) + 1 at hh
    linarith
  have hb₁ : (budget : ℝ) ≤ ρ * (n : ℝ) / 2 := Nat.floor_le (by positivity)
  have hcap : 0 < cap := by
    exact_mod_cast (mul_pos hH hP₀).trans_le hc₀
  have hdegcap : (slots : ℝ) * cap ≤ G * P := by
    calc
      _ ≤ (slots : ℝ) * ((H + 1) * P) := mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ _ := by
        dsimp [G]
        nlinarith only [hP]
  refine ⟨cap, budget, hcap, ?_, ?_, ?_⟩
  · have hh : (slots : ℝ) * B ≤ (ρ / 4) * H := by
      dsimp [H]
      field_simp
      nlinarith only [hρ]
    have hmul : (cells : ℝ) * slots ≤ (budget : ℝ) * cap := by
      calc
        _ ≤ B * ((n : ℝ) * P) * slots := by
          rw [hNP]
          exact mul_le_mul_of_nonneg_right hcells (by positivity)
        _ = ((slots : ℝ) * B) * ((n : ℝ) * P) := by ring
        _ ≤ ((ρ / 4) * H) * ((n : ℝ) * P) := mul_le_mul_of_nonneg_right hh (by positivity)
        _ = (ρ * (n : ℝ) / 4) * (H * P) := by ring
        _ ≤ _ := mul_le_mul hb₀ hc₀ (by positivity) (by positivity)
    exact_mod_cast hmul
  · push_cast
    exact hdegcap
  · have hslack : L * P < ρ * (n : ℝ) / 2 := by
      have h := (div_lt_iff₀ (show 0 < ρ / 2 by positivity)).mp hb
      have hg := mul_lt_mul_of_pos_right h hP₀
      calc
        _ < ((n : ℝ) ^ z * (ρ / 2)) * P := hg
        _ = (ρ / 2) * ((n : ℝ) ^ z * P) := by ring
        _ = _ := by rw [hPz]; ring
    push_cast
    calc
      _ ≤ ρ * (n : ℝ) / 2 + (slots : ℝ) * ((D * P + G * P) + P) :=
        add_le_add hb₁ (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hdegree hdegcap) hP)
          (by positivity))
      _ = ρ * (n : ℝ) / 2 + L * P := by dsimp [L]; ring
      _ < _ := by linarith

/-- For every large host, place all copies of both orientations with
degree on the required scale, uniformly over the colouring and
forbidden pairs. -/
theorem eventually_place_copies {C K : Type*} [Fintype C] [DecidableEq C]
    [Field K] [Fintype K] [DecidableEq K] (q : ℕ) (ref : C) {ρ z B D : ℝ}
    (hρ : 0 < ρ) (hz : 0 < z) (hz₁ : z ≤ 1) (hB : 0 ≤ B) :
    ∃ G : ℝ, 0 < G ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (M degree : ℕ), (M : ℝ) ≤ B * (n : ℝ) ^ (2 - z) →
        (degree : ℝ) ≤ D * (n : ℝ) ^ (1 - z) →
        ∀ (tag : High C q ref → Fin q → C) (colour : Fin n → C)
          (forbidden : Fin n → Finset (Fin n)),
          (∀ c, ρ * (n : ℝ) ≤ (profile colour univ c : ℝ)) →
          (∀ v, (forbidden v).card ≤ degree) →
          (∀ a b, a ∈ forbidden b ↔ b ∈ forbidden a) →
          ∃ f : PhysicalBank.Copy q ref M → (Fin q × K) ↪ Fin n,
            (∀ j i x, colour (f j (i, x)) = if x = 0 then tag j.1 i else ref) ∧
            (∀ j x y, x ≠ y → f j x ∉ forbidden (f j y)) ∧
            (∀ i j, i ≠ j → ((univ.map (f i)) ∩ (univ.map (f j))).card ≤ 1) ∧
            ∀ v, (↑(((univ : Finset (PhysicalBank.Copy q ref M)).biUnion fun j =>
              if v ∈ univ.map (f j) then univ.map (f j) else ∅).card) : ℝ) ≤
                G * (n : ℝ) ^ (1 - z) := by
  classical
  let h := Fintype.card (High C q ref)
  let slots := q * Fintype.card K
  obtain ⟨G, hG, he⟩ := eventually_parameters slots hρ hz hz₁
    (B := (h : ℝ) * 2 * B) (D := D) (by positivity)
  refine ⟨G, hG, ?_⟩
  filter_upwards [he] with n hn
  intro M degree hM hdegree tag colour forbidden hclasses hforbid hsym
  have hcells : (↑(h * (2 * M)) : ℝ) ≤ (h : ℝ) * 2 * B * (n : ℝ) ^ (2 - z) := by
    push_cast
    calc
      _ = ((h : ℝ) * 2) * M := by ring
      _ ≤ ((h : ℝ) * 2) * (B * (n : ℝ) ^ (2 - z)) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by ring
  obtain ⟨cap, budget, hcap, htotal, hcapdegree, hspace⟩ := hn _ degree hcells hdegree
  have hspace' (c : C) : budget + slots * (degree + slots * cap + 1) < profile colour univ c := by
    exact_mod_cast hspace.trans_le (hclasses c)
  obtain ⟨f, hf, havoid, hsep, hbound⟩ := PhysicalBank.place_copies ref tag colour
    forbidden degree cap budget hcap hforbid hsym htotal hspace'
  refine ⟨f, hf, havoid, hsep, fun v => le_trans ?_ hcapdegree⟩
  exact_mod_cast hbound v

end KqR75.BankScales

#print axioms KqR75.BankScales.eventually_parameters
#print axioms KqR75.BankScales.eventually_place_copies
