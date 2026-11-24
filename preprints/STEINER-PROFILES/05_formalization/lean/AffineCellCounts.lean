module
public import TransversalBank
public import Mathlib.Data.Fintype.Prod

@[expose] public section
namespace KqR75.AffineCellCounts

open Finset Transversal

variable {K G C T : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Fintype G] [DecidableEq G] [DecidableEq C] [DecidableEq T]

/-- Pull back a fixed vertex colouring through permutations of the
points in each group of the transversal design. -/
def lineColours (s : G → K) (σ : G → Equiv.Perm K)
    (tag : G → C) (ref : C) (p : K × K) (i : G) : C :=
  if σ i (point (s i) p) = 0 then tag i else ref

def active (tag : G → C) (ref : C) : Finset G :=
  univ.filter fun i => tag i ≠ ref

theorem active_subset (s : G → K) (σ : G → Equiv.Perm K)
    (tag : G → C) (ref : C) (p : K × K) :
    active (lineColours s σ tag ref p) ref ⊆ active tag ref := by
  intro i hi
  have h := (mem_filter.mp hi).2
  change (if σ i (point (s i) p) = 0 then tag i else ref) ≠ ref at h
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  split_ifs at h
  · exact h
  · exact False.elim (h rfl)

theorem eq_tag_of_card_ge (s : G → K) (σ : G → Equiv.Perm K)
    (tag : G → C) (ref : C) (p : K × K)
    (h : (active tag ref).card ≤ (active (lineColours s σ tag ref p) ref).card) :
    lineColours s σ tag ref p = tag := by
  have he := eq_of_subset_of_card_le (active_subset s σ tag ref p) h
  funext i
  unfold lineColours
  split_ifs with hzero
  · rfl
  · by_contra htag
    have hi : i ∈ active tag ref := by simp [active, Ne.symm htag]
    rw [← he] at hi
    simpa [active, lineColours, hzero] using hi

theorem baseline_unique (s : G → K) (tag : G → C) (ref : C)
    {i j : G} (hij : s i ≠ s j) (hi : tag i ≠ ref) (hj : tag j ≠ ref) (p : K × K) :
    lineColours s (fun _ => Equiv.refl K) tag ref p = tag ↔ p = (0, 0) := by
  constructor
  · intro h
    have hp (a : G) (ha : tag a ≠ ref) : point (s a) p = 0 := by
      by_contra hn
      have he := congrFun h a
      simp only [lineColours, Equiv.refl_apply, hn, ite_false] at he
      exact ha he.symm
    apply pair_injective (s i) (s j) hij
    change (point (s i) p, point (s j) p) = (point (s i) (0, 0), point (s j) (0, 0))
    rw [hp i hi, hp j hj]
    simp [point]
  · rintro rfl
    funext a
    simp [lineColours, point]

theorem shifted_excludes_top (s : G → K) (tag : G → C) (ref : C)
    {i j r : G} (hij : s i ≠ s j) (hir : i ≠ r) (hjr : j ≠ r)
    (hi : tag i ≠ ref) (hj : tag j ≠ ref) (hr : tag r ≠ ref)
    (τ : Equiv.Perm K) (hτ : τ 0 ≠ 0) (p : K × K) :
    lineColours s (fun a => if a = r then τ else Equiv.refl K) tag ref p ≠ tag := by
  intro h
  have hp (a : G) (ha : tag a ≠ ref) :
      (if a = r then τ else Equiv.refl K) (point (s a) p) = 0 := by
    by_contra hn
    have he := congrFun h a
    simp only [lineColours, hn, ite_false] at he
    exact ha he.symm
  have hi0 : point (s i) p = 0 := by simpa [hir] using hp i hi
  have hj0 : point (s j) p = 0 := by simpa [hjr] using hp j hj
  have hr0 : τ (point (s r) p) = 0 := by simpa using hp r hr
  have hp0 : p = (0, 0) := by
    apply pair_injective (s i) (s j) hij
    change (point (s i) p, point (s j) p) = (point (s i) (0, 0), point (s j) (0, 0))
    rw [hi0, hj0]
    simp [point]
  subst p
  exact hτ (by simpa [point] using hr0)

def histogram (typeOf : (G → C) → T) (s : G → K) (σ : G → Equiv.Perm K)
    (tag : G → C) (ref : C) (u : T) : ℤ :=
  ∑ p : K × K, if typeOf (lineColours s σ tag ref p) = u then 1 else 0

/-- The two histograms differ by 1 at the top coordinate and by 0 at
every other coordinate of at least the same degree. -/
theorem top_difference (typeOf : (G → C) → T) (degree : T → ℕ)
    (ref : C)
    (hdegree : ∀ f, degree (typeOf f) = (active f ref).card)
    (s : G → K) (tag : G → C)
    {i j r : G} (hij : s i ≠ s j) (hir : i ≠ r) (hjr : j ≠ r)
    (hi : tag i ≠ ref) (hj : tag j ≠ ref) (hr : tag r ≠ ref)
    (τ : Equiv.Perm K) (hτ : τ 0 ≠ 0)
    (u : T) (hu : degree (typeOf tag) ≤ degree u) :
    histogram typeOf s (fun _ => Equiv.refl K) tag ref u -
      histogram typeOf s (fun a => if a = r then τ else Equiv.refl K) tag ref u =
        if typeOf tag = u then 1 else 0 := by
  classical
  have htag (σ : G → Equiv.Perm K) (p : K × K)
      (he : typeOf (lineColours s σ tag ref p) = u) :
      lineColours s σ tag ref p = tag := by
    apply eq_tag_of_card_ge
    rw [← hdegree tag, ← hdegree (lineColours s σ tag ref p), he]
    exact hu
  have hshift (p : K × K) :
      typeOf (lineColours s (fun a => if a = r then τ else Equiv.refl K) tag ref p) ≠ u :=
    fun he => shifted_excludes_top s tag ref hij hir hjr hi hj hr τ hτ p (htag _ _ he)
  have hbase (p : K × K) :
      typeOf (lineColours s (fun _ => Equiv.refl K) tag ref p) = u ↔
        p = (0, 0) ∧ typeOf tag = u := by
    constructor
    · intro he
      have h := htag _ _ he
      exact ⟨(baseline_unique s tag ref hij hi hj p).mp h, (congrArg typeOf h).symm.trans he⟩
    · rintro ⟨hp, he⟩
      rw [(baseline_unique s tag ref hij hi hj p).mpr hp, he]
  simp only [histogram, hshift, ite_false, Finset.sum_const_zero, sub_zero, hbase]
  rw [Finset.sum_eq_single (0, 0)]
  · simp
  · intro p _ hp
    simp [hp]
  · simp

/-- Each function of the two colours on a pair of groups has the same
sum before and after permuting the points inside the groups. -/
theorem pair_colour_sum (s : G → K) (tag : G → C) (ref : C)
    (i j : G) (hij : s i ≠ s j) (σ : G → Equiv.Perm K) (f : C → C → ℤ) :
    (∑ p : K × K, f (lineColours s σ tag ref p i) (lineColours s σ tag ref p j)) =
      ∑ p : K × K, f (lineColours s (fun _ => Equiv.refl K) tag ref p i)
        (lineColours s (fun _ => Equiv.refl K) tag ref p j) := by
  let E : K × K ≃ K × K :=
    Equiv.ofBijective _ (pair_bijective (s i) (s j) hij)
  let e := E.trans ((σ i).prodCongr (σ j))
  let g : K × K → ℤ := fun x =>
    f (if x.1 = 0 then tag i else ref) (if x.2 = 0 then tag j else ref)
  change (∑ p, g (e p)) = ∑ p, g (E p)
  exact (e.sum_comp g).trans (E.sum_comp g).symm

/-- Any type statistic that is a sum of pair contributions has equal
total over the two transversal decompositions. -/
theorem histogram_pair_invariant [Fintype T]
    (typeOf : (G → C) → T) (a : T → ℤ) (P : Finset (G × G))
    (s : G → K) (hP : ∀ ij ∈ P, s ij.1 ≠ s ij.2)
    (f : C → C → ℤ)
    (ha : ∀ labels, a (typeOf labels) = ∑ ij ∈ P, f (labels ij.1) (labels ij.2))
    (tag : G → C) (ref : C) (σ : G → Equiv.Perm K) :
    (∑ u, histogram typeOf s σ tag ref u * a u) =
      ∑ u, histogram typeOf s (fun _ => Equiv.refl K) tag ref u * a u := by
  classical
  have he (π : G → Equiv.Perm K) :
      (∑ u, histogram typeOf s π tag ref u * a u) =
        ∑ ij ∈ P, ∑ p : K × K, f (lineColours s π tag ref p ij.1)
          (lineColours s π tag ref p ij.2) := by
    unfold histogram
    simp_rw [Finset.sum_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_comm]
    have hp (p : K × K) :
        (∑ u, if typeOf (lineColours s π tag ref p) = u then a u else 0) =
          a (typeOf (lineColours s π tag ref p)) := by simp
    simp_rw [hp, ha]
    exact Finset.sum_comm
  rw [he, he]
  exact Finset.sum_congr rfl (fun ij hij =>
    pair_colour_sum s tag ref ij.1 ij.2 (hP ij hij) σ f)

end KqR75.AffineCellCounts

#print axioms KqR75.AffineCellCounts.top_difference
#print axioms KqR75.AffineCellCounts.pair_colour_sum
#print axioms KqR75.AffineCellCounts.histogram_pair_invariant
