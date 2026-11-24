module
public import ReserveScales

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Finset

variable {V : Type*} [DecidableEq V]

/-- The degree in a finite family of pairs. -/
def degree (E : Finset (Finset V)) (v : V) : ℕ :=
  (E.filter (fun e => v ∈ e)).card

/-- Each packing step uses some edges of the leave and some of the reserve.
The next states delete the former and mark the latter as used. -/
def take (L Y B : Finset (Finset V)) : Finset (Finset V) × Finset (Finset V) :=
  (L \ B, Y ∪ (B \ L))

theorem degree_union {X Y : Finset (Finset V)} (h : Disjoint X Y) (v : V) :
    degree (X ∪ Y) v = degree X v + degree Y v := by
  rw [degree, filter_union, card_union_of_disjoint ((h.mono (filter_subset _ _) (filter_subset _ _)))]
  rfl

theorem degree_sdiff_add {X Y : Finset (Finset V)} (h : Y ⊆ X) (v : V) :
    degree (X \ Y) v + degree Y v = degree X v := by
  have he : (X \ Y) ∪ Y = X := by
    rw [sdiff_union_self_eq_union, union_eq_left.mpr h]
  rw [← degree_union sdiff_disjoint v, he]

/-- In a clique, each vertex is incident with precisely one pair for
every other vertex. -/
theorem clique_degree (C : Finset V) (v : V) :
    degree (C.powersetCard 2) v = if v ∈ C then C.card - 1 else 0 := by
  by_cases hv : v ∈ C
  · have hs : ({v} : Finset V) ⊆ C := singleton_subset_iff.mpr hv
    unfold degree
    simp only [ite_eq_left hv]
    simp_rw [← singleton_subset_iff]
    rw [card_filter_powersetCard_subset _ _ _ hs (by simp : ({v} : Finset V).card ≤ 2),
      card_singleton, Nat.succ_sub_succ_eq_sub, Nat.sub_zero, Nat.choose_one_right]
  · rw [ite_eq_right hv, degree, filter_eq_empty_iff.mpr]
    · rfl
    · intro e he hv'
      exact hv ((mem_powersetCard.mp he).1 hv')

/-- A phase-two step changes the reserve/leave potential by zero at the
roots, by q−1 at each auxiliary, and by zero off the chosen clique. -/
theorem pair_step_potential {L Y : Finset (Finset V)} (C e : Finset V)
    (he : e ∈ C.powersetCard 2) (heL : e ∈ L)
    (hother : Disjoint ((C.powersetCard 2).erase e) L)
    (hunused : Disjoint Y ((C.powersetCard 2).erase e)) (v : V) :
    let q := C.card
    let out := take L Y (C.powersetCard 2)
    degree out.2 v + (q - 2) * degree out.1 v =
      degree Y v + (q - 2) * degree L v + if v ∈ C ∧ v ∉ e then q - 1 else 0 := by
  let B := C.powersetCard 2
  have hBL : B \ L = B.erase e := by
    ext f
    simp only [mem_sdiff, mem_erase]
    constructor
    · rintro ⟨hf, hn⟩
      exact ⟨fun hh => hn (hh.symm ▸ heL), hf⟩
    · rintro ⟨hn, hf⟩
      exact ⟨hf, fun hfl => disjoint_left.mp hother (mem_erase.mpr ⟨hn, hf⟩) hfl⟩
  have hLB : L \ B = L \ {e} := by
    ext f
    simp only [mem_sdiff, mem_singleton]
    constructor
    · rintro ⟨hf, hn⟩
      exact ⟨hf, fun hh => hn (hh.symm ▸ he)⟩
    · rintro ⟨hf, hn⟩
      exact ⟨hf, fun hfb => disjoint_left.mp hother (mem_erase.mpr ⟨hn, hfb⟩) hf⟩
  have heB : ({e} : Finset (Finset V)) ⊆ B := singleton_subset_iff.mpr he
  have hY := degree_union hunused v
  have hL := degree_sdiff_add (singleton_subset_iff.mpr heL) v
  have hE := degree_sdiff_add heB v
  rw [sdiff_singleton_eq_erase] at hE
  have heq : degree ({e} : Finset (Finset V)) v = if v ∈ e then 1 else 0 := by
    by_cases h : v ∈ e
    · rw [ite_eq_left h, degree, filter_eq_self.mpr (fun f hf => ?_), card_singleton]
      rwa [mem_singleton.mp hf]
    · rw [ite_eq_right h, degree, filter_eq_empty_iff.mpr (fun f hf => ?_), card_empty]
      rwa [mem_singleton.mp hf]
  have hC := clique_degree C v
  change degree (Y ∪ (B \ L)) v + (C.card - 2) * degree (L \ B) v =
    degree Y v + (C.card - 2) * degree L v + if v ∈ C ∧ v ∉ e then C.card - 1 else 0
  rw [hBL, hLB, hY]
  have hcard : 2 ≤ C.card := (mem_powersetCard.mp he).2 ▸ card_le_card (mem_powersetCard.mp he).1
  change degree B v = _ at hC
  change degree (B.erase e) v + _ = _ at hE
  change degree Y v + degree (B.erase e) v + _ = _
  by_cases hv : v ∈ e
  · have hvC := (mem_powersetCard.mp he).1 hv
    have hOn : degree ({e} : Finset (Finset V)) v = 1 := heq.trans (ite_eq_left hv)
    rw [hOn] at hE hL
    rw [ite_eq_left hvC] at hC
    rw [ite_eq_right (fun h : v ∈ C ∧ v ∉ e => h.2 hv), Nat.add_zero]
    rw [← hL, Nat.mul_add, mul_one]
    omega
  · have hOff : degree ({e} : Finset (Finset V)) v = 0 := heq.trans (ite_eq_right hv)
    rw [hOff, Nat.add_zero] at hE hL
    rw [hL, hE, hC]
    simp [hv, Nat.add_comm, Nat.add_left_comm]

/-- A phase-two step removes exactly one leave edge. -/
theorem pair_step_leave_card {L Y : Finset (Finset V)} (C e : Finset V)
    (he : e ∈ C.powersetCard 2) (heL : e ∈ L)
    (hother : Disjoint ((C.powersetCard 2).erase e) L) :
    ((take L Y (C.powersetCard 2)).1).card + 1 = L.card := by
  have hLB : L \ C.powersetCard 2 = L \ {e} := by
    ext f
    simp only [mem_sdiff, mem_singleton]
    constructor
    · rintro ⟨hf, hn⟩
      exact ⟨hf, fun hh => hn (hh.symm ▸ he)⟩
    · rintro ⟨hf, hn⟩
      exact ⟨hf, fun hfb => disjoint_left.mp hother (mem_erase.mpr ⟨hn, hfb⟩) hf⟩
  change (L \ C.powersetCard 2).card + 1 = L.card
  rw [hLB]
  simpa only [card_singleton] using card_sdiff_add_card_eq_card (singleton_subset_iff.mpr heL)

/-- Fixing some auxiliaries moves them into the root set and leaves an
extension of the corresponding smaller size. This gives an upper bound
for every forbidden-vertex or forbidden-edge fibre used by cover-down. -/
theorem extension_fibre_le (R : V → V → Prop) [DecidableRel R]
    (S H A : Finset V) (k : ℕ) :
    ((ReserveCuts.extensions R S H k).filter (A ⊆ ·)).card ≤
      (ReserveCuts.extensions R S (H ∪ A) (k - A.card)).card := by
  apply card_le_card_of_injOn (fun C : Finset V => C \ A)
  · intro C hC
    obtain ⟨hC, hA⟩ := mem_filter.mp hC
    have hC' : C ⊆ ReserveCuts.common R S H ∧ C.card = k ∧ (C : Set V).Pairwise R := by
      simpa only [ReserveCuts.extensions, ReserveCuts.cliquesIn, mem_filter, mem_powersetCard,
        and_assoc] using hC
    change C \ A ∈ ReserveCuts.extensions R S (H ∪ A) (k - A.card)
    rw [ReserveCuts.extensions, ReserveCuts.cliquesIn, mem_filter, mem_powersetCard]
    refine ⟨⟨?_, by rw [card_sdiff_of_subset hA, hC'.2.1]⟩, ?_⟩
    · intro w hw
      obtain ⟨hW, hnot⟩ := mem_sdiff.mp hw
      obtain ⟨hS, hH⟩ := mem_filter.mp (hC'.1 hW)
      refine mem_filter.mpr ⟨hS, fun u hu => ?_⟩
      rcases mem_union.mp hu with huH | huA
      · exact hH u huH
      · exact hC'.2.2 (hA huA) hW (fun he => hnot (he ▸ huA))
    · exact hC'.2.2.mono (fun _ hw => (mem_sdiff.mp hw).1)
  · intro C hC D hD he
    have hA_C := (mem_filter.mp hC).2
    have hA_D := (mem_filter.mp hD).2
    calc
      C = (C \ A) ∪ A := by rw [sdiff_union_self_eq_union, union_eq_left.mpr hA_C]
      _ = (D \ A) ∪ A := congrArg (· ∪ A) he
      _ = D := by rw [sdiff_union_self_eq_union, union_eq_left.mpr hA_D]

/-- Bounding the fibres of forbidden objects gives a usable clique when
the sum of the obstruction bounds is smaller than the candidate family. -/
theorem exists_avoiding {I : Type*} [DecidableEq I] (E : Finset (Finset V))
    (F : Finset I) (bad : I → Finset V → Prop) [∀ i, DecidablePred (bad i)]
    (b : I → ℕ) (hf : ∀ i ∈ F, (E.filter (bad i)).card ≤ b i)
    (hcount : (∑ i ∈ F, b i) < E.card) :
    ∃ C ∈ E, ∀ i ∈ F, ¬ bad i C := by
  classical
  let U := F.biUnion (fun i => E.filter (bad i))
  have hU : U.card ≤ ∑ i ∈ F, b i :=
    (card_biUnion_le : U.card ≤ ∑ i ∈ F, (E.filter (bad i)).card).trans (sum_le_sum hf)
  have hex : (E \ U).Nonempty := by
    have hCard : 0 < (E \ U).card := by
      have h : E.card ≤ (E \ U).card + U.card := card_le_card_sdiff_add_card
      omega
    exact card_pos.mp hCard
  obtain ⟨C, hC⟩ := hex
  refine ⟨C, (mem_sdiff.mp hC).1, fun i hi hb => (mem_sdiff.mp hC).2 ?_⟩
  exact mem_biUnion.mpr ⟨i, hi, mem_filter.mpr ⟨(mem_sdiff.mp hC).1, hb⟩⟩

/-- Edges of the chosen star, expressed as unordered two-sets. -/
def star (u : V) (S : Finset V) : Finset (Finset V) :=
  S.image (fun w => {u, w})

private theorem star_card (u : V) (S : Finset V) (hu : u ∉ S) : (star u S).card = S.card := by
  apply card_image_of_injOn
  intro w hw v hv he
  change ({u, w} : Finset V) = {u, v} at he
  have hmem : w ∈ ({u, v} : Finset V) := he ▸ (by simp : w ∈ ({u, w} : Finset V))
  exact mem_singleton.mp ((mem_insert.mp hmem).resolve_left (fun h => hu (h ▸ hw)))

theorem star_clique_split (u : V) (S : Finset V) (hu : u ∉ S) :
    (insert u S).powersetCard 2 = S.powersetCard 2 ∪ star u S := by
  rw [show (2 : ℕ) = 1 + 1 by rfl, powersetCard_succ_insert hu, powersetCard_one]
  congr 1
  ext e
  rw [star]
  constructor
  · intro he
    obtain ⟨x, hx, rfl⟩ := mem_image.mp he
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hx
    exact mem_image.mpr ⟨w, hw, rfl⟩
  · intro he
    obtain ⟨w, hw, rfl⟩ := mem_image.mp he
    exact mem_image.mpr ⟨{w}, mem_map.mpr ⟨w, hw, rfl⟩, rfl⟩

/-- A phase-one step removes the full chosen star and charges just the
internal pairs of its auxiliary clique to used reserve degree. -/
theorem star_step {L Y : Finset (Finset V)} (u : V) (S : Finset V) (hu : u ∉ S)
    (hstar : star u S ⊆ L) (hinside : Disjoint (S.powersetCard 2) L)
    (hunused : Disjoint Y (S.powersetCard 2)) :
    let out := take L Y ((insert u S).powersetCard 2)
    out.1.card + S.card = L.card ∧
      degree out.1 u + S.card = degree L u ∧
      ∀ v, degree out.2 v = degree Y v + if v ∈ S then S.card - 1 else 0 := by
  have hleft : L \ (S.powersetCard 2 ∪ star u S) = L \ star u S := by
    ext e
    simp only [mem_sdiff, mem_union, not_or]
    constructor
    · exact fun ⟨he, _, hs⟩ => ⟨he, hs⟩
    · exact fun ⟨he, hs⟩ => ⟨he, fun hc => disjoint_left.mp hinside hc he, hs⟩
  have hright : (S.powersetCard 2 ∪ star u S) \ L = S.powersetCard 2 := by
    ext e
    simp only [mem_sdiff, mem_union]
    exact ⟨fun ⟨he, hn⟩ => he.resolve_right (fun hs => hn (hstar hs)),
      fun he => ⟨Or.inl he, fun hl => disjoint_left.mp hinside he hl⟩⟩
  have hd : degree (star u S) u = S.card := by
    unfold degree
    rw [filter_eq_self.mpr (fun e he => ?_), star_card u S hu]
    obtain ⟨w, _, rfl⟩ := mem_image.mp he
    exact mem_insert_self _ _
  change (L \ _).card + S.card = L.card ∧ degree (L \ _) u + S.card = degree L u ∧
    ∀ v, degree (Y ∪ (_ \ L)) v = degree Y v + if v ∈ S then S.card - 1 else 0
  rw [star_clique_split u S hu, hleft, hright]
  exact ⟨by simpa only [star_card u S hu] using card_sdiff_add_card_eq_card hstar,
    by simpa only [hd] using degree_sdiff_add hstar u,
    fun v => (degree_union hunused v).trans (by rw [clique_degree])⟩

end KqR75.CoverDown

#print axioms KqR75.CoverDown.pair_step_potential
#print axioms KqR75.CoverDown.pair_step_leave_card
#print axioms KqR75.CoverDown.extension_fibre_le
#print axioms KqR75.CoverDown.exists_avoiding
#print axioms KqR75.CoverDown.star_step
