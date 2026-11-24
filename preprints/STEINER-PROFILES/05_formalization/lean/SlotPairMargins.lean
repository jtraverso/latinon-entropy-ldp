module
public import SlotProfiles

@[expose] public section
noncomputable section
namespace KqR75.SlotPairMargins

open Finset ColouredCliques SlotProfiles

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Number of ordered, distinct slots whose colours are i and j. The
diagonal is twice the number of unordered monochromatic pairs. -/
def orderedCount {q : ℕ} (t : TypeProfile C q) (i j : C) : ℕ :=
  (t.val i : ℕ) * ((t.val j : ℕ) - if i = j then 1 else 0)

theorem orderedCount_slots {q : ℕ} (tag : Fin q → C) (i j : C) :
    (orderedCount (slotType tag) i j : ℤ) =
      ∑ p ∈ (univ : Finset (Fin q)).offDiag,
        if tag p.1 = i ∧ tag p.2 = j then 1 else 0 := by
  let F (i : C) := (univ : Finset (Fin q)).filter fun x => tag x = i
  have hset : (((univ : Finset (Fin q)).offDiag).filter
      fun p => tag p.1 = i ∧ tag p.2 = j) =
      ((F i ×ˢ F j).filter fun p => p.1 ≠ p.2) := by
    ext ⟨a, b⟩
    simp [F, Finset.mem_offDiag, and_assoc, and_left_comm, and_comm]
  rw [← Finset.sum_filter, hset, Finset.sum_const, nsmul_eq_mul, mul_one]
  have htype (i : C) : ((slotType tag).val i : ℕ) = (F i).card := rfl
  unfold orderedCount
  rw [htype i, htype j]
  congr 1
  by_cases hij : i = j
  · subst j
    have hoff : ((F i ×ˢ F i).filter fun p => p.1 ≠ p.2) = (F i).offDiag := by
      ext ⟨a, b⟩
      simp [Finset.mem_offDiag, and_assoc]
    rw [hoff, offDiag_card, if_pos rfl, Nat.mul_sub_one]
  · rw [if_neg hij, Nat.sub_zero, filter_true_of_mem, card_product]
    rintro ⟨a, b⟩ hp he
    change a = b at he
    subst b
    obtain ⟨ha, hb⟩ := mem_product.mp hp
    exact hij ((mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2)

/-- Each affine swap preserves the actual ordered pair counts of the
profile histogram, including pairs of a single colour. -/
theorem ordered_margin_invariant {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {q : ℕ} (s : Fin q → K) (hs : Function.Injective s)
    (tag : Fin q → C) (ref i j : C) (σ : Fin q → Equiv.Perm K) :
    (∑ u, AffineCellCounts.histogram slotType s σ tag ref u * (orderedCount u i j : ℤ)) =
      ∑ u, AffineCellCounts.histogram slotType s (fun _ => Equiv.refl K) tag ref u *
        (orderedCount u i j : ℤ) := by
  classical
  exact AffineCellCounts.histogram_pair_invariant slotType
    (fun u => (orderedCount u i j : ℤ)) (univ : Finset (Fin q)).offDiag
    s (fun p hp he => (mem_offDiag.mp hp).2.2 (hs he))
    (fun a b => if a = i ∧ b = j then 1 else 0)
    (fun labels => orderedCount_slots labels i j) tag ref σ

def demand (i j c : C) : ℕ := (if i = c then 1 else 0) + (if j = c then 1 else 0)

theorem demand_le_of_pos {q : ℕ} {u : TypeProfile C q} {i j : C}
    (h : 0 < orderedCount u i j) (c : C) : demand i j c ≤ (u.val c : ℕ) := by
  unfold orderedCount at h
  have h₁ : 0 < (u.val i : ℕ) := Nat.pos_of_ne_zero (fun hz => by rw [hz, zero_mul] at h; omega)
  have h₂ : 0 < (u.val j : ℕ) - (if i = j then 1 else 0) :=
    Nat.pos_of_ne_zero (fun hz => by rw [hz, mul_zero] at h; omega)
  by_cases hij : i = j
  · subst j
    change 0 < (u.val i : ℕ) - (if i = i then 1 else 0) at h₂
    by_cases hic : i = c
    · subst c
      simp only [demand, eq_self, ite_true] at h₂ ⊢
      omega
    · simp [demand, hic]
  · change 0 < (u.val j : ℕ) - (if i = j then 1 else 0) at h₂
    simp only [hij, ite_false, Nat.sub_zero] at h₂
    by_cases hic : i = c
    · subst c
      simp [demand, Ne.symm hij] <;> omega
    · by_cases hjc : j = c
      · subst c
        simp [demand, hij] <;> omega
      · simp [demand, hic, hjc]

theorem rest_count {q : ℕ} (u : TypeProfile C q) (ref : C) :
    degree ref u + (u.val ref : ℕ) = q :=
  (Finset.sum_erase_add _ _ (mem_univ ref)).trans u.property

theorem sum_demand (ref i j : C) :
    ∑ c ∈ univ.erase ref, demand i j c =
      (if i = ref then 0 else 1) + (if j = ref then 0 else 1) := by
  simp only [demand, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_erase,
    Finset.mem_univ, and_true]
  by_cases hi : i = ref <;> by_cases hj : j = ref <;> simp [hi, hj]

private theorem agrees_of_saturation {q : ℕ} (ref : C) (u : TypeProfile C q)
    (g : C → ℕ) (h : ∀ c, g c ≤ (u.val c : ℕ))
    (hs : degree ref u ≤ ∑ c ∈ univ.erase ref, g c) :
    ∀ c, c ≠ ref → (u.val c : ℕ) = g c := by
  intro c hc
  by_contra he
  have hlt : g c < (u.val c : ℕ) := lt_of_le_of_ne (h c) (Ne.symm he)
  have ht := Finset.sum_lt_sum (s := univ.erase ref)
    (fun x _ => h x) ⟨c, by simp [hc], hlt⟩
  exact (not_lt_of_ge hs) ht

/-- Any occupied pair with as many non-reference slots as the permitted
degree isolates a unique type among profiles below that degree. -/
theorem eq_of_saturating_pair {q : ℕ} (ref i j : C) (u v : TypeProfile C q)
    (hu : degree ref u ≤ ∑ c ∈ univ.erase ref, demand i j c)
    (hv : degree ref v ≤ ∑ c ∈ univ.erase ref, demand i j c)
    (hp : 0 < orderedCount u i j) (hp' : 0 < orderedCount v i j) : u = v := by
  have he (c : C) (hc : c ≠ ref) : (u.val c : ℕ) = (v.val c : ℕ) :=
    (agrees_of_saturation ref u _ (demand_le_of_pos hp) hu c hc).trans
      (agrees_of_saturation ref v _ (demand_le_of_pos hp') hv c hc).symm
  have hd : degree ref u = degree ref v := by
    apply Finset.sum_congr rfl
    intro c hc
    exact he c (mem_erase.mp hc).1
  apply Subtype.ext
  funext c
  apply Fin.ext
  by_cases hc : c = ref
  · subst c
    have h₁ := rest_count u ref
    have h₂ := rest_count v ref
    omega
  · exact he c hc

private theorem exists_pos_of_sum_pos {s : Finset C} (f : C → ℕ)
    (h : 0 < ∑ i ∈ s, f i) : ∃ i ∈ s, 0 < f i := by
  by_contra hn
  push_neg at hn
  have hs : (∑ i ∈ s, f i) = 0 := Finset.sum_eq_zero (fun i hi => Nat.eq_zero_of_le_zero (hn i hi))
  omega

theorem exists_saturating_pair {q : ℕ} (hq : 2 ≤ q) (ref : C) (u : TypeProfile C q)
    (hu : degree ref u ≤ 2) :
    ∃ i j, 0 < orderedCount u i j ∧ degree ref u = ∑ c ∈ univ.erase ref, demand i j c := by
  have hrest := rest_count u ref
  by_cases hzero : degree ref u = 0
  · refine ⟨ref, ref, ?_, ?_⟩
    · unfold orderedCount
      simp only [eq_self, ite_true]
      exact Nat.mul_pos (by omega) (by omega)
    · simp [sum_demand, hzero]
  have hd : 0 < degree ref u := by omega
  obtain ⟨i, hi, hip⟩ := exists_pos_of_sum_pos (fun i => (u.val i : ℕ)) hd
  have hir : i ≠ ref := (mem_erase.mp hi).1
  by_cases hone : degree ref u = 1
  · refine ⟨i, ref, ?_, ?_⟩
    · simpa [orderedCount, hir] using Nat.mul_pos hip (show 0 < (u.val ref : ℕ) by omega)
    · simp [sum_demand, hone, hir]
  have htwo : degree ref u = 2 := by omega
  by_cases hbig : 2 ≤ (u.val i : ℕ)
  · refine ⟨i, i, ?_, ?_⟩
    · unfold orderedCount
      simp only [eq_self, ite_true]
      exact Nat.mul_pos hip (by omega)
    · simp [sum_demand, htwo, hir]
  have hs : 0 < ∑ j ∈ (univ.erase ref).erase i, (u.val j : ℕ) := by
    have h := Finset.sum_erase_add _ (fun j => (u.val j : ℕ)) hi
    change _ + (u.val i : ℕ) = degree ref u at h
    omega
  obtain ⟨j, hj, hjp⟩ := exists_pos_of_sum_pos _ hs
  have hij : i ≠ j := Ne.symm (mem_erase.mp hj).1
  have hjr : j ≠ ref := (mem_erase.mp (mem_erase.mp hj).2).1
  exact ⟨i, j, by simpa [orderedCount, hij] using Nat.mul_pos hip hjp,
    by simp [sum_demand, htwo, hir, hjr]⟩

/-- Ordered pair margins determine a histogram remaining on the low types.
Descending elimination isolates a single occupied pair at each step. -/
theorem low_eq_zero {q : ℕ} {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (hq : 2 ≤ q) (ref : C) (w : TypeProfile C q → R)
    (hhigh : ∀ u, 2 < degree ref u → w u = 0)
    (hmargin : ∀ i j, ∑ u, w u * (orderedCount u i j : R) = 0) : w = 0 := by
  have step (k : ℕ) (hk : k ≤ 2) (habove : ∀ u, k < degree ref u → w u = 0)
      (u : TypeProfile C q) (hu : degree ref u = k) : w u = 0 := by
    obtain ⟨i, j, hp, hs⟩ := exists_saturating_pair hq ref u (by omega)
    have hm := hmargin i j
    have hoff (v : TypeProfile C q) (_ : v ∈ univ) (hne : v ≠ u) :
        w v * (orderedCount v i j : R) = 0 := by
      by_cases hab : k < degree ref v
      · rw [habove v hab, zero_mul]
      · by_cases hpos : 0 < orderedCount v i j
        · exact False.elim (hne (eq_of_saturating_pair ref i j v u
            (by rw [← hs, hu]; omega) hs.le hpos hp))
        · have h0 : orderedCount v i j = 0 := by omega
          simp [h0]
    rw [Finset.sum_eq_single u hoff (by simp)] at hm
    exact (mul_eq_zero.mp hm).resolve_right (by exact_mod_cast hp.ne')
  have h₂ := step 2 le_rfl hhigh
  have h₁ := step 1 (by omega) (fun u hu => by
    by_cases h : 2 < degree ref u
    · exact hhigh u h
    · exact h₂ u (by omega))
  have h₀ := step 0 (by omega) (fun u hu => by
    by_cases h : 1 < degree ref u
    · by_cases h' : 2 < degree ref u
      · exact hhigh u h'
      · exact h₂ u (by omega)
    · exact h₁ u (by omega))
  funext u
  by_cases h : 2 < degree ref u
  · exact hhigh u h
  · by_cases h' : degree ref u = 2
    · exact h₂ u h'
    · by_cases h'' : degree ref u = 1
      · exact h₁ u h''
      · exact h₀ u (by omega)

def cellDifference {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {q : ℕ} (s : Fin q → K) (ref : C) (tag : Fin q → C) (r : Fin q)
    (v : TypeProfile C q) : ℤ :=
  AffineCellCounts.histogram slotType s (fun _ => Equiv.refl K) tag ref v -
    AffineCellCounts.histogram slotType s
      (fun a => if a = r then Equiv.swap 0 1 else Equiv.refl K) tag ref v

theorem cellDifference_margin_zero {K R : Type*}
    [Field K] [Fintype K] [DecidableEq K] [CommRing R]
    {q : ℕ} (s : Fin q → K) (hs : Function.Injective s)
    (ref : C) (tag : Fin q → C) (r : Fin q) (i j : C) :
    ∑ v, (cellDifference s ref tag r v : R) * (orderedCount v i j : R) = 0 := by
  have hm : (∑ v, cellDifference s ref tag r v * (orderedCount v i j : ℤ)) = 0 := by
    simp only [cellDifference, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (ordered_margin_invariant s hs tag ref i j
      (fun a => if a = r then Equiv.swap 0 1 else Equiv.refl K)).symm
  simpa only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Int.cast_zero] using
    congrArg (fun x : ℤ => (x : R)) hm

/-- Actual affine-cell differences generate the whole ordered pair-margin
kernel. Over the integers the coefficients are integral. -/
theorem affine_spans_kernel {K R : Type*}
    [Field K] [Fintype K] [DecidableEq K] [CommRing R] [IsDomain R] [CharZero R]
    {q : ℕ} (hq : 2 ≤ q) (s : Fin q → K) (hs : Function.Injective s) (ref : C) :
    ∃ (tag : High C q ref → Fin q → C) (r : High C q ref → Fin q),
      (∀ j, slotType (tag j) = j.val) ∧
      ∀ w : TypeProfile C q → R,
        (∀ i j, ∑ v, w v * (orderedCount v i j : R) = 0) →
        ∃ a : High C q ref → R,
          ∀ v, w v = ∑ k, a k * (cellDifference s ref (tag k) (r k) v : R) := by
  classical
  choose tag r htag htop hpair using fun u : High C q ref => cell_column s hs ref u
  refine ⟨tag, r, htag, ?_⟩
  intro w hw
  let col (j i : High C q ref) : R := (cellDifference s ref (tag j) (r j) i.val : R)
  have hdiag (i : High C q ref) : col i i = 1 := by
    have h := htop i i.val le_rfl
    change cellDifference s ref (tag i) (r i) i.val = (if i.val = i.val then (1 : ℤ) else 0) at h
    simpa [col] using congrArg (fun z : ℤ => (z : R)) h
  have htri (i j : High C q ref) (hle : degree ref j.val ≤ degree ref i.val) (hne : j ≠ i) :
      col j i = 0 := by
    have hv : j.val ≠ i.val := fun h => hne (Subtype.ext h)
    have h := htop j i.val hle
    change cellDifference s ref (tag j) (r j) i.val = (if j.val = i.val then (1 : ℤ) else 0) at h
    simpa [col, hv] using congrArg (fun z : ℤ => (z : R)) h
  obtain ⟨a, ha⟩ := GradedColumns.solve_all (fun j : High C q ref => degree ref j.val)
    col hdiag htri (fun j => w j.val)
  let z (v : TypeProfile C q) : R := ∑ k, a k * (cellDifference s ref (tag k) (r k) v : R)
  have hh (v : TypeProfile C q) (hv : 2 < degree ref v) : w v - z v = 0 := by
    have he := congrFun ha ⟨v, hv⟩
    exact sub_eq_zero.mpr he.symm
  have hz (i j : C) : ∑ v, (w v - z v) * (orderedCount v i j : R) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, hw, zero_sub, neg_eq_zero]
    simp only [z, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, cellDifference_margin_zero s hs ref, mul_zero]
    simp
  have h := low_eq_zero hq ref (fun v => w v - z v) hh hz
  exact ⟨a, fun v => sub_eq_zero.mp (congrFun h v)⟩

/-- Count an unordered colour pair by dividing its ordered count by two
only in the monochromatic case. This identity is stated without division. -/
theorem orderedCount_demand {q : ℕ} (v : TypeProfile C q) (i j : C) :
    (if i = j then 2 else 1) * (∏ c, (v.val c : ℕ).choose (demand i j c)) =
      orderedCount v i j := by
  by_cases hij : i = j
  · subst j
    have hprod : (∏ c, (v.val c : ℕ).choose (demand i i c)) = (v.val i : ℕ).choose 2 := by
      rw [Finset.prod_eq_single i]
      · simp [demand]
      · intro c _ hc
        simp [demand, hc.symm]
      · simp
    rw [hprod]
    have h := Nat.choose_mul (n := (v.val i : ℕ)) (k := 2) (s := 1) (by omega)
    norm_num [Nat.choose_one_right] at h
    simpa [orderedCount, mul_comm] using h
  · have hprod : (∏ c, (v.val c : ℕ).choose (demand i j c)) = (v.val i : ℕ) * (v.val j : ℕ) := by
      rw [← Finset.prod_erase_mul univ _ (mem_univ j)]
      rw [Finset.prod_eq_single_of_mem i (by simp [hij])]
      · simp [demand, hij, Ne.symm hij]
      · intro c hc hci
        have hcj := (mem_erase.mp hc).1
        simp [demand, hci.symm, hcj.symm]
    simp [hprod, orderedCount, hij]

theorem edge_profile_demand {n : ℕ} (colour : Fin n → C)
    (e : CompleteJohnson.Edge n) :
    ∃ i j, profile colour (e : Finset (Fin n)) = demand i j := by
  obtain ⟨x, y, hxy, he⟩ := Finset.card_eq_two.mp (mem_powersetCard.mp e.property).2
  refine ⟨colour x, colour y, ?_⟩
  funext c
  simp only [profile, part, he, Finset.card_filter, Finset.sum_pair hxy, demand]

theorem physical_margin_mul {n q : ℕ} (colour : Fin n → C) (w : TypeProfile C q → ℝ)
    (e : CompleteJohnson.Edge n) (i j : C) (he : profile colour (e : Finset (Fin n)) = demand i j) :
    ((if i = j then 2 else 1 : ℕ) : ℝ) * pairMargin colour w e =
      ∑ v, w v * (orderedCount v i j : ℝ) := by
  have hprod (v : TypeProfile C q) :
      ((if i = j then 2 else 1 : ℕ) : ℝ) * ((∏ c, (v.val c : ℕ).choose (demand i j c) : ℕ) : ℝ) =
        (orderedCount v i j : ℝ) := by
    exact_mod_cast orderedCount_demand v i j
  unfold pairMargin
  simp_rw [congrFun he, Finset.mul_sum, ← mul_assoc, hprod, mul_comm _ (w _)]

/-- Vanishing ordered margins imply zero margins on every physical edge
of the complete host, in the normalisation used by the seed lift. -/
theorem physical_margin_zero {n q : ℕ} (colour : Fin n → C) (w : TypeProfile C q → ℝ)
    (hw : ∀ i j, ∑ v, w v * (orderedCount v i j : ℝ) = 0)
    (e : CompleteJohnson.Edge n) : pairMargin colour w e = 0 := by
  obtain ⟨i, j, he⟩ := edge_profile_demand colour e
  have hd : 0 < ((if i = j then 2 else 1 : ℕ) : ℝ) := by split_ifs <;> norm_num
  have hm := (physical_margin_mul colour w e i j he).trans (hw i j)
  exact (mul_eq_zero.mp hm).resolve_left hd.ne'

theorem exists_edge_demand {n : ℕ} (colour : Fin n → C)
    (hclasses : ∀ i, 2 ≤ profile colour univ i) (i j : C) :
    ∃ e : CompleteJohnson.Edge n, profile colour (e : Finset (Fin n)) = demand i j := by
  have hpos : 0 < cliques colour univ (demand i j) := by
    apply Finset.prod_pos
    intro c _
    apply Nat.choose_pos
    exact (show demand i j c ≤ 2 by unfold demand; split_ifs <;> omega).trans (hclasses c)
  rw [← card_extensions_empty] at hpos
  obtain ⟨e, he⟩ := card_pos.mp hpos
  have hprofile := (mem_filter.mp he).2.2
  have hcard : e.card = 2 := by
    rw [← sum_profile colour e, hprofile]
    simp [demand, Finset.sum_add_distrib, Finset.sum_ite_eq]
  exact ⟨⟨e, mem_powersetCard.mpr ⟨subset_univ _, hcard⟩⟩, hprofile⟩

/-- On a host with two vertices of each colour the physical margins and
the ordered margins have precisely the same kernel. -/
theorem ordered_margins_zero_iff {n q : ℕ} (colour : Fin n → C)
    (hclasses : ∀ i, 2 ≤ profile colour univ i) (w : TypeProfile C q → ℝ) :
    (∀ i j, ∑ v, w v * (orderedCount v i j : ℝ) = 0) ↔
      ∀ e : CompleteJohnson.Edge n, pairMargin colour w e = 0 := by
  refine ⟨physical_margin_zero colour w, ?_⟩
  intro hw i j
  obtain ⟨e, he⟩ := exists_edge_demand colour hclasses i j
  rw [← physical_margin_mul colour w e i j he, hw e, mul_zero]

/-- An affine integer combination lifts each high coordinate, with exactly
zero pair margins. Over the reals these are the histogram directions
needed for simultaneous load and histogram repair. -/
theorem affine_coordinate_lifts {K R : Type*}
    [Field K] [Fintype K] [DecidableEq K] [CommRing R]
    {q : ℕ} (s : Fin q → K) (hs : Function.Injective s) (ref : C) :
    ∃ g : High C q ref → TypeProfile C q → R,
      (∀ i j : High C q ref, g j i.val = if i = j then 1 else 0) ∧
      ∀ j i₁ i₂, ∑ v, g j v * (orderedCount v i₁ i₂ : R) = 0 := by
  classical
  obtain ⟨tag, r, L, _, hL⟩ := cell_high_coordinates s hs ref
  let g (j : High C q ref) (v : TypeProfile C q) : R :=
    ∑ k, (L j k : R) * (cellDifference s ref (tag k) (r k) v : R)
  refine ⟨g, ?_, ?_⟩
  · intro i j
    have h := congrArg (fun x : ℤ => (x : R)) (hL i j)
    simpa only [g, cellDifference, Int.cast_sum, Int.cast_mul, Int.cast_sub, apply_ite,
      Int.cast_zero, Int.cast_one] using h
  · intro j i₁ i₂
    simp only [g, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum, cellDifference_margin_zero s hs ref, mul_zero]
    simp

end KqR75.SlotPairMargins

#print axioms KqR75.SlotPairMargins.orderedCount_slots
#print axioms KqR75.SlotPairMargins.ordered_margin_invariant
#print axioms KqR75.SlotPairMargins.low_eq_zero
#print axioms KqR75.SlotPairMargins.affine_spans_kernel
#print axioms KqR75.SlotPairMargins.physical_margin_zero
#print axioms KqR75.SlotPairMargins.affine_coordinate_lifts
#print axioms KqR75.SlotPairMargins.ordered_margins_zero_iff
