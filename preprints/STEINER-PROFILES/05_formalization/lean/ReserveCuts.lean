module
public import KqCore
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Pairwise
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.List.Forall2

@[expose] public section
noncomputable section
namespace KqR75.ReserveCuts

open Finset

variable {V : Type*} [DecidableEq V]

/-- The neighbours of one vertex in a prescribed candidate class. -/
def neighbours (R : V → V → Prop) [DecidableRel R] (W : Finset V) (u : V) : Finset V :=
  W.filter (fun v => R u v)

def cutLower (R : V → V → Prop) [DecidableRel R] (p : ℝ) (t : ℕ) : Prop :=
  ∀ U W : Finset V, Disjoint U W → t ≤ U.card → t ≤ W.card →
    (p / 2) * (U.card : ℝ) * (W.card : ℝ) ≤ ∑ u ∈ U, ((neighbours R W u).card : ℝ)

omit [DecidableEq V] in
/-- A cut lower bound rules out t vertices that are all deficient
against the same sufficiently large target class. -/
theorem bad_card_lt (R : V → V → Prop) [DecidableRel R] (p : ℝ) {t : ℕ} (ht : 0 < t)
    (hcut : cutLower R p t) (U W : Finset V) (hdis : Disjoint U W) (hW : t ≤ W.card) :
    (U.filter (fun u => ((neighbours R W u).card : ℝ) < (p / 2) * (W.card : ℝ))).card < t := by
  classical
  let Bad := U.filter (fun u => ((neighbours R W u).card : ℝ) < (p / 2) * (W.card : ℝ))
  change Bad.card < t
  by_contra! hb
  have hne : Bad.Nonempty := card_pos.mp (ht.trans_le hb)
  have hs := hcut Bad W (hdis.mono_left (filter_subset _ _)) hb hW
  have hlt : (∑ u ∈ Bad, ((neighbours R W u).card : ℝ)) <
      ∑ _u ∈ Bad, (p / 2) * (W.card : ℝ) :=
    sum_lt_sum_of_nonempty hne (fun u hu => (mem_filter.mp hu).2)
  simp only [sum_const, nsmul_eq_mul] at hlt
  exact (not_lt_of_ge hs) (hlt.trans_eq (by ring))

/-- At a greedy embedding step, excluding the vertices deficient
against any future candidate class costs at most t−1 per class. -/
theorem good_choices (R : V → V → Prop) [DecidableRel R] (p : ℝ) {t : ℕ} (ht : 0 < t)
    (hcut : cutLower R p t) (U : Finset V) (W : Finset (Finset V))
    (hW : ∀ S ∈ W, Disjoint U S ∧ t ≤ S.card) :
    ∃ G : Finset V, G ⊆ U ∧
      U.card ≤ G.card + W.card * (t - 1) ∧
      ∀ u ∈ G, ∀ S ∈ W, (p / 2) * (S.card : ℝ) ≤ ((neighbours R S u).card : ℝ) := by
  classical
  let bad := fun S : Finset V => U.filter
    (fun u => ((neighbours R S u).card : ℝ) < (p / 2) * (S.card : ℝ))
  let excluded := W.biUnion bad
  let G := U \ excluded
  have hex : excluded ⊆ U := by
    intro u hu
    obtain ⟨S, _, hS⟩ := mem_biUnion.mp hu
    exact (mem_filter.mp hS).1
  have hb : excluded.card ≤ W.card * (t - 1) := by
    refine card_biUnion_le_card_mul _ _ _ (fun S hS => ?_)
    have hh := bad_card_lt R p ht hcut U S (hW S hS).1 (hW S hS).2
    change (bad S).card < t at hh
    omega
  refine ⟨G, sdiff_subset, ?_, ?_⟩
  · have he : G.card + excluded.card = U.card := card_sdiff_add_card_eq_card hex
    omega
  · intro u hu S hS
    apply le_of_not_gt
    intro hbad
    exact (mem_sdiff.mp hu).2 (mem_biUnion.mpr ⟨S, hS, mem_filter.mpr ⟨(mem_sdiff.mp hu).1, hbad⟩⟩)

def consEmbedding (u : V) : List V ↪ List V := ⟨List.cons u, fun _ _ h => (List.cons.inj h).2⟩

/-- Ordered choices taking one vertex from each candidate class.
At every step all later classes are restricted to neighbours. -/
def embeddings (R : V → V → Prop) [DecidableRel R] : List (Finset V) → Finset (List V)
  | [] => {[]}
  | U :: W => U.biUnion fun u =>
    (embeddings R (W.map (fun S => neighbours R S u))).map (consEmbedding u)
termination_by W => W.length
decreasing_by simp

/-- Counting ordered cliques across disjoint candidate classes. The
threshold uses the minimum class size after the final restriction. -/
theorem count_embeddings (R : V → V → Prop) [DecidableRel R] (p : ℝ)
    (hp : 0 ≤ p) (hp₂ : p ≤ 2) {t : ℕ} (ht : 0 < t) (hcut : cutLower R p t)
    (W : List (Finset V)) (m : ℝ) (hm : 0 ≤ m)
    (hdis : W.Pairwise Disjoint) (hsize : ∀ S ∈ W, m ≤ (S.card : ℝ))
    (hbudget : (W.length : ℝ) * t ≤ (m / 2) * (p / 2) ^ (W.length - 1)) :
    (∏ j ∈ range W.length, m * (p / 2) ^ j / 2) ≤ ((embeddings R W).card : ℝ) := by
  classical
  have hp₀ : 0 ≤ p / 2 := by positivity
  have hp₁ : p / 2 ≤ 1 := by linarith
  generalize hL : W.length = N
  induction N using Nat.strong_induction_on generalizing W m with
  | h N ih =>
    cases W with
    | nil => subst N; simp [embeddings]
    | cons U W =>
      obtain ⟨hUW, hWW⟩ := List.pairwise_cons.mp hdis
      have hUb := hsize U (List.mem_cons_self)
      have hWb (S : Finset V) (hS : S ∈ W) : m ≤ (S.card : ℝ) :=
        hsize S (List.mem_cons_of_mem _ hS)
      have hpow : (p / 2) ^ W.length ≤ 1 := pow_le_one₀ hp₀ hp₁
      have hbudget' : (W.length : ℝ) * t + t ≤ (m / 2) * (p / 2) ^ W.length := by
        simpa only [List.length_cons, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hbudget
      have htM : (t : ℝ) ≤ m / 2 := by
        have h := hbudget'.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
        linarith only [h, mul_nonneg (show (0 : ℝ) ≤ W.length by positivity) (show (0 : ℝ) ≤ t by positivity)]
      obtain ⟨G, hGsub, hGcard, hG⟩ := good_choices R p ht hcut U W.toFinset
        (fun S hS => ⟨hUW S (List.mem_toFinset.mp hS), by
          have h := hWb S (List.mem_toFinset.mp hS)
          exact_mod_cast (show (t : ℝ) ≤ S.card by linarith)⟩)
      have hGbound : m / 2 ≤ (G.card : ℝ) := by
        have hc : (U.card : ℝ) ≤ G.card + (W.toFinset.card : ℝ) * ((t - 1 : ℕ) : ℝ) := by
          exact_mod_cast hGcard
        have hwt : (W.toFinset.card : ℝ) ≤ W.length := by exact_mod_cast List.toFinset_card_le W
        have htm : (↑(t - 1 : ℕ) : ℝ) ≤ t := by exact_mod_cast Nat.sub_le t 1
        have hmul : (W.toFinset.card : ℝ) * ((t - 1 : ℕ) : ℝ) ≤ (W.length : ℝ) * t :=
          mul_le_mul hwt htm (by positivity) (by positivity)
        have hb := hbudget'.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
        linarith only [hc, hUb, hmul, hb, (show (0 : ℝ) ≤ t by positivity)]
      let tail := fun u : V => W.map (fun S => neighbours R S u)
      have htail (u : V) (hu : u ∈ G) :
          (∏ j ∈ range W.length, (m * (p / 2)) * (p / 2) ^ j / 2) ≤
            ((embeddings R (tail u)).card : ℝ) := by
        have hlen : (tail u).length = W.length := List.length_map _
        have hd : (tail u).Pairwise Disjoint := by
          apply List.pairwise_map.mpr
          exact hWW.imp (fun h => h.mono (filter_subset _ _) (filter_subset _ _))
        have hm' (S : Finset V) (hS : S ∈ tail u) : m * (p / 2) ≤ (S.card : ℝ) := by
          obtain ⟨S', hS', rfl⟩ := List.mem_map.mp hS
          calc
            _ ≤ (S'.card : ℝ) * (p / 2) := mul_le_mul_of_nonneg_right (hWb S' hS') hp₀
            _ = (p / 2) * S'.card := mul_comm _ _
            _ ≤ _ := hG u hu S' (List.mem_toFinset.mpr hS')
        have hbd : ((tail u).length : ℝ) * t ≤ (m * (p / 2) / 2) * (p / 2) ^ ((tail u).length - 1) := by
          rw [hlen]
          cases W with
          | nil => simp; positivity
          | cons S W =>
            rw [List.length_cons, pow_succ] at hbudget'
            rw [List.length_cons, Nat.add_sub_cancel]
            linarith only [hbudget', (show (0 : ℝ) ≤ t by positivity)]
        have hsm : (tail u).length < N := by rw [← hL, hlen]; simp
        simpa only [hlen] using ih (tail u).length hsm (tail u) (m * (p / 2))
          (mul_nonneg hm hp₀) hd hm' hbd rfl
      let choices := fun u : V => (embeddings R (tail u)).map (consEmbedding u)
      have hpair : (G : Set V).PairwiseDisjoint choices := by
        intro x hx y hy hxy
        apply disjoint_left.mpr
        intro l hlx hly
        obtain ⟨l₁, _, he₁⟩ := mem_map.mp hlx
        obtain ⟨l₂, _, he₂⟩ := mem_map.mp hly
        exact hxy (List.cons.inj (he₁.trans he₂.symm)).1
      have hsub : G.biUnion choices ⊆ embeddings R (U :: W) := by
        rw [embeddings]
        intro l hl
        obtain ⟨u, hu, hmem⟩ := mem_biUnion.mp hl
        exact mem_biUnion.mpr ⟨u, hGsub hu, hmem⟩
      let P := ∏ j ∈ range W.length, (m * (p / 2)) * (p / 2) ^ j / 2
      have hP : 0 ≤ P := prod_nonneg (fun j _ => by positivity)
      calc
        _ = P * (m / 2) := by
          rw [← hL, List.length_cons, prod_range_succ']
          simp only [pow_zero, mul_one]
          congr 1
          apply prod_congr rfl
          intro j _
          rw [pow_succ]
          ring
        _ ≤ P * G.card := mul_le_mul_of_nonneg_left hGbound hP
        _ = ∑ _u ∈ G, P := by rw [sum_const, nsmul_eq_mul]; ring
        _ ≤ ∑ u ∈ G, ((choices u).card : ℝ) := sum_le_sum fun u hu => by
          simpa only [choices, card_map] using htail u hu
        _ = ((G.biUnion choices).card : ℝ) := by rw [card_biUnion hpair, Nat.cast_sum]
        _ ≤ _ := by exact_mod_cast card_le_card hsub

omit [DecidableEq V] in
private theorem assigned {W : List (Finset V)} {xs : List V}
    (h : List.Forall₂ (fun (S : Finset V) (x : V) => x ∈ S) W xs)
    {x : V} (hx : x ∈ xs) : ∃ S ∈ W, x ∈ S := by
  induction h with
  | nil => simp at hx
  | @cons S y W ys hy _ ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨S, List.mem_cons_self, hy⟩
    · obtain ⟨U, hU, hm⟩ := ih hx
      exact ⟨U, List.mem_cons_of_mem _ hU, hm⟩

omit [DecidableEq V] in
private theorem forget_neighbours (R : V → V → Prop) [DecidableRel R] (u : V)
    {W : List (Finset V)} {xs : List V}
    (h : List.Forall₂ (fun (S : Finset V) (x : V) => x ∈ S)
      (W.map (fun S => neighbours R S u)) xs) :
    List.Forall₂ (fun (S : Finset V) (x : V) => x ∈ S) W xs := by
  induction W generalizing xs with
  | nil => cases xs with
    | nil => exact .nil
    | cons x xs => cases h
  | cons S W ih =>
    cases xs with
    | nil => cases h
    | cons x xs =>
      obtain ⟨hx, ht⟩ := List.forall₂_cons.mp h
      exact .cons (mem_filter.mp hx).1 (ih ht)

theorem embedding_spec (R : V → V → Prop) [DecidableRel R] (W : List (Finset V))
    (xs : List V) (hx : xs ∈ embeddings R W) :
    List.Forall₂ (fun (S : Finset V) (x : V) => x ∈ S) W xs ∧ xs.Pairwise R := by
  cases W with
  | nil =>
    rw [embeddings, mem_singleton] at hx
    subst xs
    exact ⟨.nil, .nil⟩
  | cons S W =>
    rw [embeddings] at hx
    obtain ⟨u, hu, hm⟩ := mem_biUnion.mp hx
    obtain ⟨ys, hy, rfl⟩ := mem_map.mp hm
    obtain ⟨hmem, hp⟩ := embedding_spec R (W.map (fun U => neighbours R U u)) ys hy
    apply And.intro (.cons hu (forget_neighbours R u hmem))
    apply List.pairwise_cons.mpr
    refine ⟨fun v hv => ?_, hp⟩
    obtain ⟨U, hU, hmem'⟩ := assigned hmem hv
    obtain ⟨A, _, rfl⟩ := List.mem_map.mp hU
    exact (mem_filter.mp hmem').2
termination_by W.length
decreasing_by simp_all

omit [DecidableEq V] in
private theorem not_in_tail {S : Finset V} {W : List (Finset V)} {ys : List V} {x : V}
    (hd : ∀ U ∈ W, Disjoint S U) (hmem : List.Forall₂ (fun (S : Finset V) (x : V) => x ∈ S) W ys)
    (hx : x ∈ S) : x ∉ ys := by
  intro h
  obtain ⟨U, hU, hm⟩ := assigned hmem h
  exact disjoint_left.mp (hd U hU) hx hm

private theorem toFinset_injective_forall₂ {W : List (Finset V)} {xs ys : List V}
    (hdis : W.Pairwise Disjoint)
    (hx : List.Forall₂ (fun (S : Finset V) (x : V) => x ∈ S) W xs)
    (hy : List.Forall₂ (fun (S : Finset V) (x : V) => x ∈ S) W ys)
    (he : xs.toFinset = ys.toFinset) : xs = ys := by
  induction hx generalizing ys with
  | nil => cases hy; rfl
  | @cons S x W xs hx hxs ih =>
    cases hy with
    | @cons _ y _ ys hy hys =>
      obtain ⟨hd, hdd⟩ := List.pairwise_cons.mp hdis
      have hn := not_in_tail hd hys hx
      have hny := not_in_tail hd hxs hx
      have hxy : x = y := by
        have hm : x ∈ (y :: ys).toFinset := by rw [← he]; simp
        exact (List.mem_cons.mp (List.mem_toFinset.mp hm)).resolve_right hn
      subst y
      have he' := congrArg (fun S : Finset V => S.erase x) he
      have hn' : x ∉ ys.toFinset := fun h => hn (List.mem_toFinset.mp h)
      have hny' : x ∉ xs.toFinset := fun h => hny (List.mem_toFinset.mp h)
      have he'': xs.toFinset = ys.toFinset := by
        simpa [List.toFinset_cons, erase_insert, hny', hn'] using he'
      exact congrArg (List.cons x) (ih hdd hys he'')

/-- The count also holds for unordered vertex sets, since the
disjoint classes determine the order uniquely. -/
theorem count_vertex_sets (R : V → V → Prop) [DecidableRel R] (p : ℝ)
    (hp : 0 ≤ p) (hp₂ : p ≤ 2) {t : ℕ} (ht : 0 < t) (hcut : cutLower R p t)
    (W : List (Finset V)) (m : ℝ) (hm : 0 ≤ m)
    (hdis : W.Pairwise Disjoint) (hsize : ∀ S ∈ W, m ≤ (S.card : ℝ))
    (hbudget : (W.length : ℝ) * t ≤ (m / 2) * (p / 2) ^ (W.length - 1)) :
    (∏ j ∈ range W.length, m * (p / 2) ^ j / 2) ≤ ((embeddings R W).image List.toFinset).card := by
  rw [card_image_of_injOn]
  · exact count_embeddings R p hp hp₂ ht hcut W m hm hdis hsize hbudget
  · intro l hl m hm he
    exact toFinset_injective_forall₂ hdis (embedding_spec R W l hl).1 (embedding_spec R W m hm).1 he

theorem disjoint_classes (S : Finset V) (l m : ℕ) (hs : l * m ≤ S.card) :
    ∃ W : List (Finset V), W.length = l ∧ W.Pairwise Disjoint ∧
      ∀ U ∈ W, U ⊆ S ∧ U.card = m := by
  induction l generalizing S with
  | zero => exact ⟨[], rfl, .nil, by simp⟩
  | succ l ih =>
    have hm : m ≤ S.card := by rw [Nat.succ_mul] at hs; omega
    obtain ⟨U, hUS, hU⟩ := exists_subset_card_eq hm
    have hS : l * m ≤ (S \ U).card := by
      have he := card_sdiff_add_card_eq_card hUS
      rw [hU] at he
      rw [Nat.succ_mul] at hs
      omega
    obtain ⟨W, hlen, hdis, hmem⟩ := ih (S \ U) hS
    refine ⟨U :: W, by simp [hlen], List.pairwise_cons.mpr ⟨?_, hdis⟩, ?_⟩
    · intro W' hW'
      exact disjoint_left.mpr (fun x hx hy => (mem_sdiff.mp ((hmem W' hW').1 hy)).2 hx)
    · intro W' hW'
      rcases List.mem_cons.mp hW' with rfl | hh
      · exact ⟨hUS, hU⟩
      · exact ⟨(hmem W' hh).1.trans sdiff_subset, (hmem W' hh).2⟩

omit [DecidableEq V] in
private theorem nodup_of_classes {W : List (Finset V)} {xs : List V}
    (hdis : W.Pairwise Disjoint)
    (hmem : List.Forall₂ (fun (S : Finset V) (x : V) => x ∈ S) W xs) : xs.Nodup := by
  induction hmem with
  | nil => exact List.nodup_nil
  | cons hx ht ih =>
    obtain ⟨hd, hdd⟩ := List.pairwise_cons.mp hdis
    exact List.nodup_cons.mpr ⟨not_in_tail hd ht hx, ih hdd⟩

/-- The unordered cliques of size l contained in S. -/
def cliquesIn (R : V → V → Prop) [DecidableRel R] (S : Finset V) (l : ℕ) : Finset (Finset V) :=
  (S.powersetCard l).filter (fun C => (C : Set V).Pairwise R)

/-- Lower bound for cliques in an arbitrary set admitting l disjoint classes of size m. -/
theorem count_cliques (R : V → V → Prop) [DecidableRel R] [Std.Symm R] (p : ℝ)
    (hp : 0 ≤ p) (hp₂ : p ≤ 2) {t : ℕ} (ht : 0 < t) (hcut : cutLower R p t)
    (S : Finset V) (l m : ℕ) (hs : l * m ≤ S.card)
    (hbudget : (l : ℝ) * t ≤ ((m : ℝ) / 2) * (p / 2) ^ (l - 1)) :
    (∏ j ∈ range l, (m : ℝ) * (p / 2) ^ j / 2) ≤ ((cliquesIn R S l).card : ℝ) := by
  classical
  obtain ⟨W, hlen, hdis, hmem⟩ := disjoint_classes S l m hs
  have hcount := count_vertex_sets R p hp hp₂ ht hcut W (m : ℝ) (by positivity) hdis
    (fun U hU => by rw [(hmem U hU).2]) (by rw [hlen]; exact hbudget)
  rw [hlen] at hcount
  refine hcount.trans ?_
  exact_mod_cast card_le_card (show (embeddings R W).image List.toFinset ⊆ cliquesIn R S l from by
    intro C hC
    obtain ⟨xs, hx, rfl⟩ := mem_image.mp hC
    obtain ⟨hxs, hpw⟩ := embedding_spec R W xs hx
    have hn := nodup_of_classes hdis hxs
    have hcard : xs.toFinset.card = l := by
      rw [List.toFinset_card_of_nodup hn, ← hxs.length_eq, hlen]
    rw [cliquesIn, mem_filter]
    refine ⟨mem_powersetCard.mpr ⟨?_, hcard⟩, (List.pairwise_iff_coe_toFinset_pairwise hn).mpr hpw⟩
    intro v hv
    obtain ⟨U, hU, hvU⟩ := assigned hxs (List.mem_toFinset.mp hv)
    exact (hmem U hU).1 hvU)

/-- The closed form of the greedy product. -/
private theorem clique_product (a b : ℝ) (l : ℕ) :
    (∏ j ∈ range l, a * b ^ j) = a ^ l * b ^ l.choose 2 := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [prod_range_succ, ih, Nat.choose_succ_succ, Nat.choose_one_right, pow_add, pow_succ a]
    ring

/-- Clique count in a large set, with the small-cut budget at exponent l−1. -/
theorem count_cliques_large (R : V → V → Prop) [DecidableRel R] [Std.Symm R] (p : ℝ)
    (hp : 0 ≤ p) (hp₂ : p ≤ 2) {t : ℕ} (ht : 0 < t) (hcut : cutLower R p t)
    (S : Finset V) (l : ℕ) (hl : 0 < l) (hS : 2 * l ≤ S.card)
    (hb : (l : ℝ) * t ≤ ((S.card : ℝ) / (4 * l)) * (p / 2) ^ (l - 1)) :
    ((S.card : ℝ) / (4 * l)) ^ l * (p / 2) ^ l.choose 2 ≤ ((cliquesIn R S l).card : ℝ) := by
  let m := S.card / l
  have hmul : l * m ≤ S.card := Nat.mul_div_le _ _
  have hmod := Nat.mod_lt S.card hl
  have he := Nat.mod_add_div S.card l
  change S.card % l + l * m = S.card at he
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hm : (S.card : ℝ) / (4 * l) ≤ (m : ℝ) / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hsum : (S.card % l : ℕ) + l * m = S.card := he
    have hR : ((S.card % l : ℕ) : ℝ) + (l : ℝ) * m = S.card := by exact_mod_cast hsum
    have hmodR : ((S.card % l : ℕ) : ℝ) < l := by exact_mod_cast hmod
    have hSR : 2 * (l : ℝ) ≤ S.card := by exact_mod_cast hS
    nlinarith only [hR, hmodR, hSR]
  have hcount := count_cliques R p hp hp₂ ht hcut S l m hmul
    (hb.trans (mul_le_mul_of_nonneg_right hm (by positivity)))
  calc
    _ = ∏ j ∈ range l, ((S.card : ℝ) / (4 * l)) * (p / 2) ^ j :=
      (clique_product _ _ _).symm
    _ ≤ ∏ j ∈ range l, (m : ℝ) * (p / 2) ^ j / 2 := by
      apply prod_le_prod₀ (fun j _ => by positivity)
      intro j _
      calc
        _ ≤ ((m : ℝ) / 2) * (p / 2) ^ j := mul_le_mul_of_nonneg_right hm (by positivity)
        _ = _ := by ring
    _ ≤ _ := hcount

/-- Vertices connected to both roots by reserve edges. -/
def commonPair (R : V → V → Prop) [DecidableRel R] (S : Finset V) (u v : V) : Finset V :=
  S.filter (fun w => R u w ∧ R v w)

/-- Clique extensions of a root pair, with its own edge left unconstrained. -/
def rootedExtensions (R : V → V → Prop) [DecidableRel R]
    (S : Finset V) (u v : V) (l : ℕ) : Finset (Finset V) :=
  cliquesIn R (commonPair R S u v) l

theorem mem_rootedExtensions (R : V → V → Prop) [DecidableRel R]
    (S : Finset V) (u v : V) (l : ℕ) (C : Finset V) :
    C ∈ rootedExtensions R S u v l ↔
      C.card = l ∧ (C : Set V).Pairwise R ∧ ∀ w ∈ C, w ∈ S ∧ R u w ∧ R v w := by
  rw [rootedExtensions, cliquesIn, mem_filter, mem_powersetCard]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hpair⟩
    exact ⟨hcard, hpair, fun w hw => mem_filter.mp (hsub hw)⟩
  · rintro ⟨hcard, hpair, hsub⟩
    exact ⟨⟨fun w hw => mem_filter.mpr (hsub w hw), hcard⟩, hpair⟩

theorem count_rooted_extensions (R : V → V → Prop) [DecidableRel R] [Std.Symm R] (p : ℝ)
    (hp : 0 ≤ p) (hp₂ : p ≤ 2) {t : ℕ} (ht : 0 < t) (hcut : cutLower R p t)
    (S : Finset V) (u v : V) (l : ℕ) (hl : 0 < l)
    (hS : 2 * l ≤ (commonPair R S u v).card)
    (hc : (S.card : ℝ) * p ^ 2 / 2 ≤ (commonPair R S u v).card)
    (hb : (l : ℝ) * t ≤ ((S.card : ℝ) * p ^ 2 / (8 * l)) * (p / 2) ^ (l - 1)) :
    ((S.card : ℝ) * p ^ 2 / (8 * l)) ^ l * (p / 2) ^ l.choose 2 ≤
      ((rootedExtensions R S u v l).card : ℝ) := by
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl
  have hc' : (S.card : ℝ) * p ^ 2 / (8 * l) ≤
      ((commonPair R S u v).card : ℝ) / (4 * l) := by
    calc
      _ = ((S.card : ℝ) * p ^ 2 / 2) / (4 * l) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hc (by positivity)
  refine le_trans ?_ (count_cliques_large R p hp hp₂ ht hcut (commonPair R S u v) l hl hS
    (hb.trans (mul_le_mul_of_nonneg_right hc' (by positivity))))
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hc' l) (by positivity)

end KqR75.ReserveCuts

#print axioms KqR75.ReserveCuts.good_choices
#print axioms KqR75.ReserveCuts.count_embeddings
#print axioms KqR75.ReserveCuts.count_vertex_sets
#print axioms KqR75.ReserveCuts.disjoint_classes
#print axioms KqR75.ReserveCuts.count_cliques
#print axioms KqR75.ReserveCuts.count_cliques_large
#print axioms KqR75.ReserveCuts.count_rooted_extensions
