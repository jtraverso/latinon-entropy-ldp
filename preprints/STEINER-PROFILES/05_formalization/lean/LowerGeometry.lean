module
public import CompletionWithCapacity
public import LowerHostScales
public import BankReserve

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Filter Finset ColouredCliques CompleteJohnson SparseGram CliqueGram SlotProfiles ReserveRandom
open PhysicalBank (Copy basalBlocks)

variable {C K : Type*} [Fintype C] [DecidableEq C] [Field K] [Fintype K] [DecidableEq K]

/-- The exact physical interface used to place an omniabsorber.
Its degree constant is uniform in the subsequently chosen bank. -/
def PhysicalOmniPlacement (q : ℕ) (z : ℝ) : Prop :=
  ∀ U : ℝ, 0 ≤ U →
    ∃ G : ℝ, 0 < G ∧ ∀ T : ℝ, 0 ≤ T → ∀ᶠ n : ℕ in atTop,
      ∀ (F X : Finset (Edge n)), Disjoint X F →
        (∀ v : Fin n, ∑ e : F, incidence 2 e v ≤ T * (n : ℝ) ^ (1 - z)) →
        (∀ v : Fin n, ∑ e : X, incidence 2 e v ≤ U * (n : ℝ) ^ (1 - z)) →
        ∃ A : Finset (Edge n), Disjoint A X ∧ Disjoint A F ∧
          (∀ v : Fin n, ∑ e : A, incidence 2 e v ≤ G * (n : ℝ) ^ (1 - z)) ∧
          ∀ S ⊆ X, Divisible q S → ∃ P : Finset (Clique n q), packs P (A ∪ S)

/-- Choose the reserve scale and absorber degree before fixing the
number of bank copies. The bank can then be placed outside the reserve,
and the absorber outside both. -/
theorem eventually_lower_geometry (q : ℕ) (hq : 3 ≤ q) (ρ : ℝ) (hρ : 0 < ρ)
    (ref : C) (s : Fin q → K) (hs : Function.Injective s)
    (tag : High C q ref → Fin q → C) (j : High C q ref → Fin q) (B : ℤ) (hB : 0 ≤ B)
    (coeff E₂ : ℝ) (hcoeff : 0 ≤ coeff) (hE₂ : 0 ≤ E₂)
    (homni : PhysicalOmniPlacement q (GreedyScales.criticalExponent q)) :
    let r := q.choose 2
    let z := GreedyScales.criticalExponent q
    let a := (2 * (q : ℝ) - 1) * z
    ∃ U G T : ℝ, 0 < U ∧ 0 < G ∧ 0 < T ∧ ∀ᶠ n : ℕ in atTop,
      ∀ colour : Fin n → C, (∀ c, ρ * (n : ℝ) ≤ (profile colour univ c : ℝ)) →
      let ε := ⌈(coeff * U + E₂ + G + U) * (n : ℝ) ^ (2 - z)⌉₊
      let M := B.toNat * ε
      ∃ (A X F : Finset (Edge n)) (f : Copy q ref M → (Fin q × K) ↪ Fin n),
        Disjoint A X ∧ Disjoint A F ∧ Disjoint X F ∧
        (∀ t i x, colour (f t (i, x)) = if x = 0 then tag t.1 i else ref) ∧
        (∀ i j, i ≠ j → ((univ.map (f i)) ∩ (univ.map (f j))).card ≤ 1) ∧
        packs (basalBlocks (by omega : 2 ≤ q) j s hs f) F ∧
        (∀ v : Fin n, ∑ e : X, incidence 2 e v ≤ U * (n : ℝ) ^ (1 - z)) ∧
        (∀ v : Fin n, ∑ e : A, incidence 2 e v ≤ G * (n : ℝ) ^ (1 - z)) ∧
        (∀ v : Fin n, ∑ e : F, incidence 2 e v ≤ T * (n : ℝ) ^ (1 - z)) ∧
        (∀ S ⊆ X, Divisible q S → ∃ P : Finset (Clique n q), packs P (A ∪ S)) ∧
        ∀ L : Finset (Edge n), (L.card : ℝ) ≤ 2 * (r : ℝ) * (n : ℝ) ^ (2 - a) →
          Disjoint L X → ∃ (PC : Finset (Clique n q)) (Y : Finset (Edge n)),
            Y ⊆ X ∧ packs PC (L ∪ Y) ∧
            ∀ b ∈ PC, ((resources n q b) ∩ X).Nonempty := by
  let r := q.choose 2
  let z := GreedyScales.criticalExponent q
  let a := (2 * (q : ℝ) - 1) * z
  have hq' : 2 ≤ q := by omega
  obtain ⟨hz, hz', _, _, _, hgap⟩ := critical_completion_scales q hq
  obtain ⟨K₀, hK₀, hcover⟩ := CoverDown.eventually_cover_physical q hq z
    (2 * (r : ℝ)) hz (by positivity) hgap
  let U := 2 * K₀
  have hU : 0 < U := by dsimp [U]; linarith
  obtain ⟨G, hG, hplace⟩ := homni U hU.le
  let D := coeff * U + E₂ + G + U
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let V := (B : ℝ) * (D + 1)
  have hV : 0 ≤ V := by dsimp [V]; exact mul_nonneg (by exact_mod_cast hB) (by positivity)
  obtain ⟨T, hT, hbank⟩ := eventually_basal_outside_reserve q hq' ref s hs
    (B := V) (D := U) hρ hz (by linarith) hV
  refine ⟨U, G, T, hU, hG, hT, ?_⟩
  filter_upwards [hcover K₀ le_rfl, hbank, hplace T hT.le, eventually_ge_atTop (1 : ℕ)]
    with n hncover hnbank hnabs hn
  intro colour hclasses
  obtain ⟨p, ω, hp, hroot, hcov⟩ := hncover
  let X := PhysicalReserve.edges ω
  let ε := ⌈D * (n : ℝ) ^ (2 - z)⌉₊
  let M := B.toNat * ε
  have hM : (M : ℝ) ≤ V * (n : ℝ) ^ (2 - z) :=
    (BankCapacity.capacity_rounding (B := B) hn hB hD (by linarith)).2.1
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpow : (n : ℝ) * (n : ℝ) ^ (-z) = (n : ℝ) ^ (1 - z) := by
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-z) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn₀]; rfl
  have hdegX (v : Fin n) : ∑ e : X, incidence 2 e v ≤ U * (n : ℝ) ^ (1 - z) := by
    have h := PhysicalReserve.degree_le p ω (by omega : 1 ≤ q - 1) hroot v
    change ∑ e : X, incidence 2 e v ≤ _ at h
    rw [hp] at h
    calc
      _ ≤ _ := h
      _ = U * ((n : ℝ) * (n : ℝ) ^ (-z)) := by dsimp [U]; ring
      _ = _ := by rw [hpow]
  let degree := ⌊U * (n : ℝ) ^ (1 - z)⌋₊
  have hd : (degree : ℝ) ≤ U * (n : ℝ) ^ (1 - z) := Nat.floor_le (by positivity)
  have hneigh (v : Fin n) : (ReserveCuts.common (adj ω) univ {v}).card ≤ degree := by
    apply Nat.le_floor
    rw [← PhysicalReserve.degree_eq_neighbours]
    exact hdegX v
  obtain ⟨f, F, hcolour, hsep, hF, hXF, hdegF⟩ :=
    hnbank M degree hM hd tag j colour ω hclasses hneigh
  obtain ⟨A, hAX, hAF, hdegA, hA⟩ := hnabs F X hXF hdegF hdegX
  refine ⟨A, X, F, f, hAX, hAF, hXF, hcolour, hsep, hF, hdegX, hdegA, hdegF, hA, ?_⟩
  intro L hL hdis
  obtain ⟨PC, Y, hY, _, hPC, hmark⟩ := hcov L hL hdis
  exact ⟨PC, Y, hY, hPC, hmark⟩

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.eventually_lower_geometry
