module
public import ProfileWeights
public import SparseGram
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

@[expose] public section
noncomputable section
namespace KqR75.ColouredCliques

open Finset
variable {V C : Type*} [DecidableEq V] [Fintype C] [DecidableEq C]

def part (colour : V → C) (s : Finset V) (i : C) : Finset V :=
  s.filter fun v => colour v = i

def profile (colour : V → C) (s : Finset V) (i : C) : ℕ := (part colour s i).card

theorem sum_profile (colour : V → C) (s : Finset V) :
    ∑ i, profile colour s i = s.card := by
  simpa [profile, part] using sum_card_fiberwise_eq_card_filter s (univ : Finset C) colour

/-- The actual subsets with the given profile and containing the fixed set e. -/
def extensions (colour : V → C) (s e : Finset V) (t : C → ℕ) : Finset (Finset V) :=
  s.powerset.filter fun b => e ⊆ b ∧ profile colour b = t

def partChoices (colour : V → C) (s e : Finset V) (t : C → ℕ) (i : C) :
    Finset (Finset V) :=
  ((part colour s i).powersetCard (t i)).filter fun b => part colour e i ⊆ b

theorem part_mono (colour : V → C) {a b : Finset V} (h : a ⊆ b) (i : C) :
    part colour a i ⊆ part colour b i := by
  intro v hv
  exact mem_filter.mpr ⟨h (mem_filter.mp hv).1, (mem_filter.mp hv).2⟩

def extensionEquiv (colour : V → C) (s e : Finset V) (t : C → ℕ) :
    ↥(extensions colour s e t) ≃ (∀ i, ↥(partChoices colour s e t i)) where
  toFun b i := ⟨part colour b i, by
    have hb := mem_filter.mp b.property
    apply mem_filter.mpr
    exact ⟨mem_powersetCard.mpr ⟨part_mono colour (mem_powerset.mp hb.1) i,
      congrFun hb.2.2 i⟩, part_mono colour hb.2.1 i⟩⟩
  invFun a := ⟨univ.biUnion (fun i => (a i : Finset V)), by
    have ha (i : C) := mem_filter.mp (a i).property
    have hsub (i : C) := (mem_powersetCard.mp (ha i).1).1
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr ?_, ?_, ?_⟩
    · intro v hv
      obtain ⟨i, _, hv⟩ := mem_biUnion.mp hv
      exact (mem_filter.mp (hsub i hv)).1
    · intro v hv
      exact mem_biUnion.mpr ⟨colour v, mem_univ _, (ha (colour v)).2 (mem_filter.mpr ⟨hv, rfl⟩)⟩
    · funext i
      have he : part colour (univ.biUnion (fun j => (a j : Finset V))) i = a i := by
        ext v
        constructor
        · intro hv
          obtain ⟨j, _, hj⟩ := mem_biUnion.mp (mem_filter.mp hv).1
          have hij := (mem_filter.mp (hsub j hj)).2.symm.trans (mem_filter.mp hv).2
          subst j
          exact hj
        · intro hv
          exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨i, mem_univ _, hv⟩,
            (mem_filter.mp (hsub i hv)).2⟩
      exact (congrArg Finset.card he).trans (mem_powersetCard.mp (ha i).1).2⟩
  left_inv b := by
    apply Subtype.ext
    ext v
    change (v ∈ univ.biUnion (fun i => part colour b i)) ↔ v ∈ (b : Finset V)
    simp only [mem_biUnion, mem_univ, true_and, part, mem_filter]
    exact ⟨fun ⟨_, hv, _⟩ => hv, fun hv => ⟨colour v, hv, rfl⟩⟩
  right_inv a := by
    funext i
    apply Subtype.ext
    change part colour (univ.biUnion (fun j => (a j : Finset V))) i = a i
    have hsub (j : C) := (mem_powersetCard.mp (mem_filter.mp (a j).property).1).1
    ext v
    constructor
    · intro hv
      obtain ⟨j, _, hj⟩ := mem_biUnion.mp (mem_filter.mp hv).1
      have hij := (mem_filter.mp (hsub j hj)).2.symm.trans (mem_filter.mp hv).2
      subst j
      exact hj
    · intro hv
      exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨i, mem_univ _, hv⟩,
        (mem_filter.mp (hsub i hv)).2⟩

theorem card_partChoices (colour : V → C) {s e : Finset V} (he : e ⊆ s)
    (t : C → ℕ) (i : C) :
    (partChoices colour s e t i).card =
      ProfileWeights.completionChoices (profile colour s i) (t i) (profile colour e i) := by
  by_cases h : profile colour e i ≤ t i
  · rw [ProfileWeights.completionChoices, if_pos h]
    exact card_filter_powersetCard_subset _ _ _ (part_mono colour he i) h
  · rw [ProfileWeights.completionChoices, if_neg h]
    apply card_eq_zero.mpr
    apply filter_eq_empty_iff.mpr
    intro b hb hsub
    exact h ((card_le_card hsub).trans_eq (mem_powersetCard.mp hb).2)

theorem card_extensions (colour : V → C) {s e : Finset V} (he : e ⊆ s) (t : C → ℕ) :
    (extensions colour s e t).card =
      ∏ i, ProfileWeights.completionChoices (profile colour s i) (t i) (profile colour e i) := by
  have h := Fintype.card_congr (extensionEquiv colour s e t)
  simpa only [Fintype.card_pi, Fintype.card_coe, card_partChoices colour he t] using h

def cliques (colour : V → C) (s : Finset V) (t : C → ℕ) : ℕ :=
  ∏ i, (profile colour s i).choose (t i)

theorem card_extensions_empty (colour : V → C) (s : Finset V) (t : C → ℕ) :
    (extensions colour s ∅ t).card = cliques colour s t := by
  rw [card_extensions colour (empty_subset s)]
  simp [cliques, ProfileWeights.completionChoices, profile, part]

/-- Multiply the independent within-colour incidence identities. This counts
extensions of a fixed edge and edges of that type in the same equation. -/
theorem incidence_identity (colour : V → C) {s e : Finset V} (he : e ⊆ s) (t : C → ℕ) :
    (extensions colour s e t).card * cliques colour s (profile colour e) =
      (∏ i, (t i).choose (profile colour e i)) * cliques colour s t := by
  rw [card_extensions colour he]
  unfold cliques
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [mul_comm] using
    ProfileWeights.choose_completion (profile colour s i) (t i) (profile colour e i)

abbrev Clique (n q : ℕ) := ↥((univ : Finset (Fin n)).powersetCard q)

abbrev TypeProfile (C : Type*) [Fintype C] (q : ℕ) :=
  {t : C → Fin (q + 1) // (∑ i, (t i : ℕ)) = q}

def cliqueType {n q : ℕ} (colour : Fin n → C) (b : Clique n q) : TypeProfile C q := by
  refine ⟨fun i => ⟨profile colour b i, ?_⟩, ?_⟩
  · have hb := (mem_powersetCard.mp b.property).2
    have hi := card_le_card (filter_subset (fun v => colour v = i) (b : Finset (Fin n)))
    change profile colour b i ≤ (b : Finset (Fin n)).card at hi
    omega
  · exact (sum_profile colour b).trans (mem_powersetCard.mp b.property).2

theorem cliqueType_eq {n q : ℕ} (colour : Fin n → C) (b : Clique n q) (t : TypeProfile C q) :
    cliqueType colour b = t ↔ profile colour b = fun i => (t.val i : ℕ) := by
  constructor
  · intro h
    exact congrArg (fun u : TypeProfile C q => fun i => (u.val i : ℕ)) h
  · intro h
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrFun h i

theorem card_clique_fibre {n q : ℕ} (colour : Fin n → C) (e : Finset (Fin n))
    (t : TypeProfile C q) :
    ((ProfileWeights.fibre (cliqueType colour) t).filter
      fun b : Clique n q => e ⊆ (b : Finset (Fin n))).card =
      (extensions colour univ e (fun i => t.val i)).card := by
  classical
  apply card_bij (fun (b : Clique n q) _ => (b : Finset (Fin n)))
  · intro b hb
    simpa [ProfileWeights.fibre, extensions, and_comm, cliqueType_eq] using hb
  · intro a _ b _ h
    exact Subtype.ext h
  · intro b hb
    obtain ⟨_, he, ht⟩ := mem_filter.mp hb
    have hq : b.card = q := by rw [← sum_profile colour b, ht]; exact t.property
    let a : Clique n q := ⟨b, mem_powersetCard.mpr ⟨subset_univ _, hq⟩⟩
    refine ⟨a, ?_, rfl⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, (cliqueType_eq colour a t).mpr ht⟩, he⟩

theorem fibre_card {n q : ℕ} (colour : Fin n → C) (t : TypeProfile C q) :
    (ProfileWeights.fibre (cliqueType colour) t).card = cliques colour univ (fun i => t.val i) := by
  have h := card_clique_fibre colour ∅ t
  simpa [card_extensions_empty] using h

theorem incidence_card {n q : ℕ} (colour : Fin n → C) (t : TypeProfile C q)
    (e : CompleteJohnson.Edge n) :
    ProfileWeights.incidenceCount (SparseGram.resources n q) (cliqueType colour) e t =
      (extensions colour univ e (fun i => t.val i)).card := by
  classical
  simpa [ProfileWeights.incidenceCount, SparseGram.resources] using card_clique_fibre colour e t

theorem fibre_pos {n q : ℕ} (colour : Fin n → C)
    (hclasses : ∀ i, q ≤ profile colour univ i) (t : TypeProfile C q) :
    0 < (ProfileWeights.fibre (cliqueType colour) t).card := by
  rw [fibre_card]
  exact Finset.prod_pos (fun i _ => Nat.choose_pos ((Nat.le_of_lt_succ (t.val i).isLt).trans (hclasses i)))

/-- Uniform bounds on the size of a fibre. A fixed positive fraction of
vertices in each class lets one take d proportional to n. -/
theorem fibre_bounds {n q : ℕ} (colour : Fin n → C) (d : ℕ)
    (hd : ∀ i, d + q ≤ profile colour univ i) (t : TypeProfile C q) :
    (d : ℝ) ^ q / (q.factorial : ℝ) ^ Fintype.card C ≤
      ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ) ∧
    ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ) ≤ (n : ℝ) ^ q := by
  rw [fibre_card]
  simp only [cliques, Nat.cast_prod]
  constructor
  · calc
      _ = ∏ i, (d : ℝ) ^ (t.val i : ℕ) / (q.factorial : ℝ) := by
        rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, t.property,
          Finset.prod_const, Finset.card_univ]
      _ ≤ _ := by
        apply Finset.prod_le_prod₀ (fun i _ => by positivity)
        intro i _
        let u := (t.val i : ℕ)
        let N := profile colour (univ : Finset (Fin n)) i
        have hu : u ≤ q := Nat.le_of_lt_succ (t.val i).isLt
        have hbase : d ≤ N + 1 - u := by have := hd i; dsimp only [N, u] at *; omega
        have hfac : (u.factorial : ℝ) ≤ (q.factorial : ℝ) := by exact_mod_cast Nat.factorial_le hu
        calc
          (d : ℝ) ^ u / (q.factorial : ℝ) ≤ ((N + 1 - u : ℕ) : ℝ) ^ u / (q.factorial : ℝ) :=
            div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hbase) _)
              (by positivity)
          _ ≤ ((N + 1 - u : ℕ) : ℝ) ^ u / (u.factorial : ℝ) :=
            div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast Nat.factorial_pos u) hfac
          _ ≤ (N.choose u : ℝ) := by
            simpa only [Nat.cast_pow] using (Nat.pow_le_choose (α := ℝ) u N)
  · calc
      _ ≤ ∏ i, (n : ℝ) ^ (t.val i : ℕ) := by
        apply Finset.prod_le_prod₀ (fun i _ => by positivity)
        intro i _
        have hi : profile colour (univ : Finset (Fin n)) i ≤ n := by
          simpa [profile, part] using card_le_card (filter_subset (fun v => colour v = i) univ)
        exact_mod_cast (Nat.choose_le_pow (profile colour univ i) (t.val i : ℕ)).trans
          (Nat.pow_le_pow_left hi _)
      _ = _ := by rw [Finset.prod_pow_eq_pow_sum, t.property]

theorem seed_mass {n q : ℕ} (colour : Fin n → C)
    (hclasses : ∀ i, q ≤ profile colour univ i) (m : TypeProfile C q → ℝ) (t : TypeProfile C q) :
    (∑ b ∈ ProfileWeights.fibre (cliqueType colour) t, ProfileWeights.weight (cliqueType colour) m b) =
      m t :=
  ProfileWeights.fibre_mass (cliqueType colour) m t (fibre_pos colour hclasses t)

/-- A per-type budget of A n² gives an envelope in the same normalisation
as the clique Gram matrix. The estimate also covers signed histograms. -/
theorem seed_weight_abs_le {n q : ℕ} (colour : Fin n → C) (hq : 2 ≤ q) (hn : q ≤ n)
    (d : ℕ) (s A : ℝ) (hs : 0 < s) (hA : 0 ≤ A)
    (hd : ∀ i, d + q ≤ profile colour univ i) (hdn : s * (n : ℝ) ≤ d)
    (m : TypeProfile C q → ℝ) (hm : ∀ t, |m t| ≤ A * (n : ℝ) ^ 2)
    (b : Clique n q) :
    |ProfileWeights.weight (cliqueType colour) m b| ≤
      (A * (q.factorial : ℝ) ^ Fintype.card C / s ^ q) *
        ((n - 2).choose (q - 2) : ℝ)⁻¹ := by
  let t := cliqueType colour b
  let N := ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ)
  let F := (q.factorial : ℝ) ^ Fintype.card C
  let D := ((n - 2).choose (q - 2) : ℝ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hF : 0 < F := by dsimp [F]; positivity
  have hD : 0 < D := by
    dsimp only [D]
    exact_mod_cast Nat.choose_pos (show q - 2 ≤ n - 2 by omega)
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast fibre_pos colour (fun i => (Nat.le_add_left q d).trans (hd i)) t
  have hlow : (s * (n : ℝ)) ^ q ≤ N * F := by
    apply (div_le_iff₀ hF).mp
    exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hdn q) hF.le).trans
      (fibre_bounds colour d hd t).1
  have hDle : D ≤ (n : ℝ) ^ (q - 2) := by
    dsimp only [D]
    exact_mod_cast ((Nat.choose_le_pow (n - 2) (q - 2)).trans
      (Nat.pow_le_pow_left (Nat.sub_le n 2) _))
  have hp : (n : ℝ) ^ (q - 2) * (n : ℝ) ^ 2 = (n : ℝ) ^ q := by
    rw [← pow_add, Nat.sub_add_cancel hq]
  have hmD : |m t| * D ≤ A * (n : ℝ) ^ q := calc
    _ ≤ (A * (n : ℝ) ^ 2) * (n : ℝ) ^ (q - 2) :=
      mul_le_mul (hm t) hDle hD.le (by positivity)
    _ = _ := by rw [mul_assoc, mul_comm ((n : ℝ) ^ 2), hp]
  have hmul := mul_le_mul_of_nonneg_right hmD (pow_nonneg hs.le q)
  have hscaled := mul_le_mul_of_nonneg_left hlow hA
  rw [mul_pow] at hscaled
  have hresult : |m t| * (s ^ q * D) ≤ (A * F) * N := by nlinarith only [hmul, hscaled]
  change |m t / N| ≤ A * F / s ^ q * D⁻¹
  rw [abs_div, abs_of_pos hN, ← div_eq_mul_inv (A * F / s ^ q) D, div_div]
  exact (div_le_div_iff₀ hN (mul_pos (pow_pos hs _) hD)).mpr hresult

/-- A uniform positive budget per type gives a lower diffuse weight. -/
theorem seed_weight_lower {n q : ℕ} (colour : Fin n → C) (hq : 2 ≤ q) (hn : 2 * q ≤ n)
    (hclasses : ∀ i, q ≤ profile colour univ i) (a : ℝ) (ha : 0 ≤ a)
    (m : TypeProfile C q → ℝ) (hm : ∀ t, a * (n : ℝ) ^ 2 ≤ m t) (b : Clique n q) :
    (a / (2 ^ (q - 2) * ((q - 2).factorial : ℝ))) *
        ((n - 2).choose (q - 2) : ℝ)⁻¹ ≤ ProfileWeights.weight (cliqueType colour) m b := by
  let t := cliqueType colour b
  let N := ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ)
  let D := ((n - 2).choose (q - 2) : ℝ)
  let F := (2 : ℝ) ^ (q - 2) * ((q - 2).factorial : ℝ)
  have hF : 0 < F := by dsimp [F]; positivity
  have hD : 0 < D := by
    dsimp only [D]
    exact_mod_cast Nat.choose_pos (show q - 2 ≤ n - 2 by omega)
  have hN : 0 < N := by
    dsimp only [N]
    exact_mod_cast fibre_pos colour hclasses t
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hNle : N ≤ (n : ℝ) ^ q := (fibre_bounds colour 0 (by simpa using hclasses) t).2
  have hbase : (n : ℝ) / 2 ≤ (((n - 2 + 1 - (q - 2) : ℕ)) : ℝ) := by
    have hc : n ≤ 2 * (n - 2 + 1 - (q - 2)) := by omega
    have hc' : (n : ℝ) ≤ 2 * (((n - 2 + 1 - (q - 2) : ℕ)) : ℝ) := by exact_mod_cast hc
    linarith
  have hdlow : (n : ℝ) ^ (q - 2) ≤ D * F := by
    have hfact : (0 : ℝ) < (q - 2).factorial := by positivity
    have hchoose : (n : ℝ) ^ (q - 2) / F ≤ D := calc
      _ = ((n : ℝ) / 2) ^ (q - 2) / ((q - 2).factorial : ℝ) := by
        rw [div_pow, div_div]
      _ ≤ (((n - 2 + 1 - (q - 2) : ℕ)) : ℝ) ^ (q - 2) / ((q - 2).factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase _) hfact.le
      _ ≤ D := by
        simpa only [D, Nat.cast_pow] using (Nat.pow_le_choose (α := ℝ) (q - 2) (n - 2))
    exact (div_le_iff₀ hF).mp hchoose
  have hp : (n : ℝ) ^ (q - 2) * (n : ℝ) ^ 2 = (n : ℝ) ^ q := by
    rw [← pow_add, Nat.sub_add_cancel hq]
  have hp' := mul_le_mul_of_nonneg_right hdlow (sq_nonneg (n : ℝ))
  rw [hp] at hp'
  have hresult : a * N ≤ m t * (F * D) := by
    have hleft := mul_le_mul_of_nonneg_left (hNle.trans hp') ha
    have hright := mul_le_mul_of_nonneg_right (hm t) (mul_nonneg hF.le hD.le)
    nlinarith only [hleft, hright]
  change a / F * D⁻¹ ≤ m t / N
  rw [← div_eq_mul_inv (a / F) D, div_div]
  exact (div_le_div_iff₀ (mul_pos hF hD) hN).mpr hresult

def pairMargin {n q : ℕ} (colour : Fin n → C) (m : TypeProfile C q → ℝ)
    (e : CompleteJohnson.Edge n) : ℝ :=
  ∑ t, ((∏ i, (t.val i : ℕ).choose (profile colour (e : Finset (Fin n)) i) : ℕ) : ℝ) * m t

theorem edge_fibre_pos {n : ℕ} (colour : Fin n → C) (e : CompleteJohnson.Edge n) :
    0 < cliques colour univ (profile colour (e : Finset (Fin n))) := by
  rw [← card_extensions_empty]
  apply card_pos.mpr
  exact ⟨e, mem_filter.mpr ⟨mem_powerset.mpr (subset_univ _), empty_subset _, rfl⟩⟩

/-- The signed and positive profile lifts use the same physical incidence. -/
theorem seed_load_eq_margin {n q : ℕ} (colour : Fin n → C)
    (hclasses : ∀ i, q ≤ profile colour univ i) (m : TypeProfile C q → ℝ)
    (e : CompleteJohnson.Edge n) :
    WeightedEnergy.load (SparseGram.resources n q) (ProfileWeights.weight (cliqueType colour) m) e =
      pairMargin colour m e / (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ) := by
  classical
  unfold pairMargin
  refine ProfileWeights.load_eq_margin (SparseGram.resources n q) (cliqueType colour) m
      (fun t => ((∏ i, (t.val i : ℕ).choose (profile colour (e : Finset (Fin n)) i) : ℕ) : ℝ))
      e (cliques colour univ (profile colour (e : Finset (Fin n)))) ?_ ?_ ?_
  · exact_mod_cast edge_fibre_pos colour e
  · exact fibre_pos colour hclasses
  · intro t
    rw [fibre_card, incidence_card]
    exact_mod_cast incidence_identity colour (subset_univ (e : Finset (Fin n))) (fun i => (t.val i : ℕ))

/-- The prescribed pair margins give unit physical edge loads. -/
theorem seed_load {n q : ℕ} (colour : Fin n → C)
    (hclasses : ∀ i, q ≤ profile colour univ i) (m : TypeProfile C q → ℝ)
    (hmargin : ∀ e : CompleteJohnson.Edge n,
      pairMargin colour m e = (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ))
    (e : CompleteJohnson.Edge n) :
    WeightedEnergy.load (SparseGram.resources n q) (ProfileWeights.weight (cliqueType colour) m) e = 1 := by
  have hpos : (0 : ℝ) < cliques colour univ (profile colour (e : Finset (Fin n))) := by
    exact_mod_cast edge_fibre_pos colour e
  rw [seed_load_eq_margin colour hclasses, hmargin, div_self hpos.ne']

theorem seed_load_zero {n q : ℕ} (colour : Fin n → C)
    (hclasses : ∀ i, q ≤ profile colour univ i) (m : TypeProfile C q → ℝ)
    (hmargin : ∀ e : CompleteJohnson.Edge n, pairMargin colour m e = 0)
    (e : CompleteJohnson.Edge n) :
    WeightedEnergy.load (SparseGram.resources n q) (ProfileWeights.weight (cliqueType colour) m) e = 0 := by
  rw [seed_load_eq_margin colour hclasses, hmargin, zero_div]

end KqR75.ColouredCliques

#print axioms KqR75.ColouredCliques.card_extensions
#print axioms KqR75.ColouredCliques.seed_load
#print axioms KqR75.ColouredCliques.seed_load_zero
#print axioms KqR75.ColouredCliques.seed_mass
#print axioms KqR75.ColouredCliques.fibre_bounds
#print axioms KqR75.ColouredCliques.seed_weight_abs_le
#print axioms KqR75.ColouredCliques.seed_weight_lower
