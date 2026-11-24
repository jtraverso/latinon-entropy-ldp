module
public import R75
public import ProfileTypeLaw
public import ProfileLDPPrinciple
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section
noncomputable section
namespace KqR75.ProfileLDP

open Finset Filter Topology ColouredCliques CompleteJohnson PhysicalCompletion
open SparseGram (resources)

variable {C : Type*} [Fintype C] [DecidableEq C]

def admissible (q n : ℕ) : Prop :=
  q.choose 2 ∣ n.choose 2 ∧ q - 1 ∣ n - 1

def designs (q n : ℕ) : Finset (Finset (Clique n q)) := by
  classical
  exact univ.filter fun D => packs D univ

theorem mem_designs {q n : ℕ} {D : Finset (Clique n q)} :
    D ∈ designs q n ↔ packs D univ := by
  classical
  simp only [designs, mem_filter, mem_univ, true_and]

def normalizedQuota {q : ℕ} (n : ℕ) (m : TypeProfile C q → ℤ) (t : TypeProfile C q) : ℝ :=
  (m t : ℝ) / blockMass n q

def profileOf {n q : ℕ} (colour : Fin n → C) (D : Finset (Clique n q)) :
    TypeProfile C q → ℝ :=
  normalizedQuota n (BankCapacity.integerHistogram colour D)

def profileCount {n q : ℕ} (colour : Fin n → C) (A : Set (TypeProfile C q → ℝ)) : ℝ := by
  classical
  exact (((designs q n).filter fun D => profileOf colour D ∈ A).card : ℝ)

def profiles {n q : ℕ} (colour : Fin n → C) : Finset (TypeProfile C q → ℝ) := by
  classical
  exact (designs q n).image (profileOf colour)

theorem mem_profiles {n q : ℕ} {colour : Fin n → C} {Q : TypeProfile C q → ℝ} :
    Q ∈ profiles colour ↔ ∃ D ∈ designs q n, profileOf colour D = Q := by
  classical
  exact mem_image

theorem profileCount_sum {n q : ℕ} (colour : Fin n → C) (A : Set (TypeProfile C q → ℝ)) :
    profileCount colour A = (by
      classical
      exact Finset.sum ((profiles colour).filter (· ∈ A)) (fun Q => profileCount colour {Q})) := by
  classical
  let S := (designs q n).filter fun D => profileOf colour D ∈ A
  have him : S.image (profileOf colour) = (profiles colour).filter (· ∈ A) := by
    ext Q
    simp only [S, mem_image, mem_filter, mem_profiles]
    constructor
    · rintro ⟨D, ⟨hD, hA⟩, rfl⟩
      exact ⟨⟨D, hD, rfl⟩, hA⟩
    · rintro ⟨⟨D, hD, rfl⟩, hA⟩
      exact ⟨D, ⟨hD, hA⟩, rfl⟩
  have hf (Q : TypeProfile C q → ℝ) (hQ : Q ∈ S.image (profileOf colour)) :
      (S.filter fun D => profileOf colour D = Q) =
        (designs q n).filter (fun D => profileOf colour D ∈ ({Q} : Set _)) := by
    have hQA := (mem_filter.mp (him ▸ hQ)).2
    ext D
    simp only [S, mem_filter, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hD, _⟩, he⟩
      exact ⟨hD, he⟩
    · rintro ⟨hD, he⟩
      exact ⟨⟨hD, he ▸ hQA⟩, he⟩
  calc
    profileCount colour A = ∑ Q ∈ S.image (profileOf colour), profileCount colour {Q} := by
      have hs := sum_fiberwise_of_maps_to (t := S.image (profileOf colour))
        (fun D hD => mem_image_of_mem (profileOf colour) hD) (fun _ => (1 : ℝ))
      simp only [sum_const, nsmul_eq_mul, mul_one] at hs
      refine hs.symm.trans (sum_congr rfl fun Q hQ => ?_)
      rw [hf Q hQ, profileCount]
      apply congrArg (fun s : Finset (Finset (Clique n q)) => (s.card : ℝ))
      ext D
      simp only [mem_filter]
    _ = _ := by rw [him]

theorem profileCount_mono {n q : ℕ} (colour : Fin n → C)
    {A B : Set (TypeProfile C q → ℝ)} (hAB : A ⊆ B) :
    profileCount colour A ≤ profileCount colour B := by
  classical
  unfold profileCount
  apply Nat.cast_le.mpr
  apply card_le_card
  intro D hD
  exact mem_filter.mpr ⟨(mem_filter.mp hD).1, hAB (mem_filter.mp hD).2⟩

theorem profileCount_singleton {n q : ℕ} (colour : Fin n → C) (m : TypeProfile C q → ℤ)
    (hB : blockMass n q ≠ 0) :
    profileCount colour {normalizedQuota n m} = (designFibre colour m).card := by
  classical
  unfold profileCount
  refine congrArg (fun S : Finset (Finset (Clique n q)) => (S.card : ℝ)) ?_
  ext D
  simp only [mem_filter, mem_designs, mem_designFibre]
  apply and_congr_right
  intro _
  simp only [Set.mem_singleton_iff, funext_iff, profileOf, normalizedQuota,
    div_left_inj' hB, Int.cast_inj]

theorem edge_card (n : ℕ) : Fintype.card (Edge n) = n.choose 2 := by
  rw [Fintype.card_coe, card_powersetCard, card_univ, Fintype.card_fin]

theorem blockMass_nonneg (n q : ℕ) : 0 ≤ blockMass n q := by unfold blockMass; positivity

theorem blockMass_pos {n q : ℕ} (hn : 2 ≤ n) (hq : 2 ≤ q) : 0 < blockMass n q := by
  rw [blockMass, edge_card]
  exact div_pos (by exact_mod_cast Nat.choose_pos hn) (by exact_mod_cast Nat.choose_pos hq)

theorem histogram_margin {n q : ℕ} (colour : Fin n → C) {D : Finset (Clique n q)}
    (hD : D ∈ designs q n) (e : Edge n) :
    pairMargin colour (fun t => (BankCapacity.integerHistogram colour D t : ℝ)) e =
      (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ) := by
  classical
  simp_rw [← BankCapacity.histogram_indicator]
  rw [ProfileBalance.margin_histogram]
  have hload (f : Edge n) : WeightedEnergy.load (resources n q)
      (fun b => if b ∈ D then 1 else 0) f = 1 := by
    rw [BankCapacity.load_indicator]
    exact_mod_cast (show PhysicalBank.edgeMultiplicity D f = 1 from
      (mem_designs.mp hD f).trans (ite_eq_left (mem_univ f)))
  simp_rw [hload, one_mul, sum_boole]
  have hf : (univ.filter fun f : Edge n => profile colour (f : Finset (Fin n)) =
      profile colour (e : Finset (Fin n))) = ProfileWeights.fibre (cliqueType colour) (cliqueType colour e) := by
    ext f
    simp only [ProfileWeights.fibre, mem_filter, mem_univ, true_and]
    exact (cliqueType_eq colour f (cliqueType colour e)).symm
  rw [hf, fibre_card]
  rfl

theorem histogram_mass {n q : ℕ} (hq : 2 ≤ q) (colour : Fin n → C)
    {D : Finset (Clique n q)} (hD : D ∈ designs q n) :
    ∑ t : TypeProfile C q, (BankCapacity.integerHistogram colour D t : ℝ) = blockMass n q :=
  profile_mass_of_designFibre hq colour _ D ((mem_designFibre _ _ _).mpr ⟨mem_designs.mp hD, fun _ => rfl⟩)

theorem histogram_nonneg {n q : ℕ} (colour : Fin n → C) (D : Finset (Clique n q))
    (t : TypeProfile C q) : 0 ≤ (BankCapacity.integerHistogram colour D t : ℝ) := by
  unfold BankCapacity.integerHistogram
  positivity

theorem profileOf_sum {n q : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n) (colour : Fin n → C)
    {D : Finset (Clique n q)} (hD : D ∈ designs q n) :
    ∑ t, profileOf colour D t = 1 := by
  simp only [profileOf, normalizedQuota, ← sum_div, histogram_mass hq colour hD,
    div_self (blockMass_pos hn hq).ne']

theorem profileOf_box {n q : ℕ} (hq : 2 ≤ q) (hn : 2 ≤ n) (colour : Fin n → C)
    {D : Finset (Clique n q)} (hD : D ∈ designs q n) :
    profileOf colour D ∈ Set.Icc (0 : TypeProfile C q → ℝ) 1 := by
  have h0 (t : TypeProfile C q) : 0 ≤ profileOf colour D t :=
    div_nonneg (histogram_nonneg colour D t) (blockMass_nonneg n q)
  exact ⟨h0, fun t => (single_le_sum (fun i _ => h0 i) (mem_univ t)).trans_eq
    (profileOf_sum hq hn colour hD)⟩

theorem profiles_card_le {n q : ℕ} (hq : 2 ≤ q) (colour : Fin n → C) :
    (profiles (q := q) colour).card ≤ (n.choose 2 + 1) ^ Fintype.card (TypeProfile C q) := by
  classical
  let encode (k : TypeProfile C q → Fin (n.choose 2 + 1)) : TypeProfile C q → ℝ :=
    fun t => (k t : ℕ) / blockMass n q
  have hsub : profiles (q := q) colour ⊆ univ.image encode := by
    intro Q hQ
    obtain ⟨D, hD, rfl⟩ := mem_profiles.mp hQ
    let k (t : TypeProfile C q) : ℕ := (D.filter fun b => cliqueType colour b = t).card
    have hk (t : TypeProfile C q) : k t ≤ n.choose 2 := by
      have ht : (k t : ℝ) ≤ blockMass n q := by
        change (BankCapacity.integerHistogram colour D t : ℝ) ≤ blockMass n q
        rw [← histogram_mass hq colour hD]
        exact single_le_sum (fun i _ => histogram_nonneg colour D i) (mem_univ t)
      have hr : (1 : ℝ) ≤ q.choose 2 := by exact_mod_cast Nat.choose_pos hq
      have hb : blockMass n q ≤ n.choose 2 := by
        rw [blockMass, edge_card]
        exact div_le_self (Nat.cast_nonneg _) hr
      exact_mod_cast ht.trans hb
    exact mem_image.mpr ⟨fun t => ⟨k t, Nat.lt_succ_of_le (hk t)⟩, mem_univ _, by
      funext t
      simp [encode, k, profileOf, normalizedQuota, BankCapacity.integerHistogram]⟩
  exact (card_le_card hsub).trans (card_image_le.trans (by simp))

def baseline (q n : ℕ) : ℝ :=
  Real.log ((n - 2).choose (q - 2) : ℝ) - ((q.choose 2 - 1 : ℕ) : ℝ)

theorem total_eq_unit_fibre {n q : ℕ} (hn : q ≤ n) (hq : 2 ≤ q) (had : admissible q n) :
    let m : TypeProfile Unit q → ℤ := fun _ => (n.choose 2 / q.choose 2 : ℕ)
    (designs q n = designFibre (fun _ => ()) m) ∧
    ExactPairMargins (fun _ : Fin n => ()) m ∧
    (∀ t, normalizedQuota n m t = 1 ∧ finiteTypeLaw (fun _ : Fin n => ()) t = 1) := by
  classical
  intro m
  let t₀ : TypeProfile Unit q := ⟨fun _ => ⟨q, Nat.lt_succ_self q⟩, by simp⟩
  have he (t : TypeProfile Unit q) : t = t₀ := by
    apply Subtype.ext
    funext u
    apply Fin.ext
    cases u
    simpa [t₀] using t.property
  have hsum (f : TypeProfile Unit q → ℝ) : ∑ t, f t = f t₀ := by
    exact sum_eq_single t₀ (fun t _ ht => (ht (he t)).elim) (fun h => (h (mem_univ _)).elim)
  have hB : ∀ t, (m t : ℝ) = blockMass n q := by
    intro t
    simp only [m, Int.cast_natCast, blockMass, edge_card]
    exact Nat.cast_div had.1 (by exact_mod_cast (Nat.choose_pos hq).ne')
  have hP (t : TypeProfile Unit q) : finiteTypeLaw (fun _ : Fin n => ()) t = 1 := by
    rw [he t, ← hsum (finiteTypeLaw (fun _ : Fin n => ())), sum_finiteTypeLaw hn]
  refine ⟨?_, ?_, fun t => ⟨by rw [normalizedQuota, hB t, div_self (blockMass_pos (hq.trans hn) hq).ne'], hP t⟩⟩
  · ext D
    rw [mem_designs, mem_designFibre]
    refine ⟨fun h => ⟨h, fun t => ?_⟩, And.left⟩
    have hd := histogram_mass hq (fun _ : Fin n => ()) (mem_designs.mpr h)
    rw [hsum] at hd
    rw [he t]
    exact_mod_cast hd.trans (hB t₀).symm
  · apply (exactPairMargins_iff _ _ (fun u => ?_)).mpr
    · intro e
      simpa only [hB, hP, mul_one] using
        (finiteTypeLaw_physical_margin hq hn (fun _ : Fin n => ()) e)
    · cases u
      simpa [profile, part] using hq.trans hn

end KqR75.ProfileLDP
