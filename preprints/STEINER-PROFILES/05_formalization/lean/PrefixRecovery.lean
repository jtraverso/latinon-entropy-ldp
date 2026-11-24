module
public import PrefixPacking
public import Mathlib.Data.List.Permutation

@[expose] public section
noncomputable section
namespace KqR75.WeightedGreedy

open Finset
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

theorem mem_picked {h : List (Option B)} {b : B} : b ∈ picked h ↔ some b ∈ h := by
  simp [picked, List.mem_filterMap]

theorem nodup_history (I : B → Finset E) (J : Finset E)
    (hI : ∀ b, (I b).Nonempty) (h : List (Option B)) (hv : valid I J h)
    (hn : none ∉ h) : h.Nodup := by
  induction h with
  | nil => simp
  | cons a h ih =>
    cases a with
    | none => exact (hn (by simp)).elim
    | some b =>
      obtain ⟨hh, hs⟩ := hv
      refine List.nodup_cons.mpr ⟨?_, ih hh (fun hn' => hn (by simp [hn']))⟩
      intro hb
      obtain ⟨e, he⟩ := hI b
      have ht := (picked_partition I J hI h hh).1 e
      have hp : 0 < ((picked h).filter (fun c => e ∈ I c)).card :=
        card_pos.mpr ⟨b, mem_filter.mpr ⟨mem_picked.mpr hb, he⟩⟩
      rw [ite_eq_left (hs he)] at ht
      split_ifs at ht <;> omega

/-- All earlier choices are cliques of the fixed host. -/
theorem picked_fits (I : B → Finset E) (J : Finset E)
    (h : List (Option B)) (hv : valid I J h) :
    ∀ b ∈ picked h, I b ⊆ J := by
  have hrem (h' : List (Option B)) : remaining I J h' ⊆ J := by
    induction h' with
    | nil => exact Subset.rfl
    | cons a h' ih =>
      cases a with
      | none => exact ih
      | some c => exact sdiff_subset.trans ih
  induction h with
  | nil => simp [picked]
  | cons a h ih =>
    intro b hb
    cases a with
    | none =>
      have ht : picked (none :: h) = picked h := by simp [picked]
      exact ih hv b (ht ▸ hb)
    | some c =>
      rcases List.mem_cons.mp (mem_picked.mp hb) with he | hb'
      · have he' := Option.some.inj he
        subst b
        exact hv.2.trans (hrem h)
      · exact ih hv.1 b (mem_picked.mpr hb')

/-- Recover a prefix by restricting a completed block set to the fixed
greedy host. Every additional block has an edge outside that host. -/
theorem recover_picked (I : B → Finset E) (J : Finset E)
    (h : List (Option B)) (hv : valid I J h) (P : Finset B) (hsub : picked h ⊆ P)
    (hadd : ∀ b ∈ P, b ∉ picked h → ¬ I b ⊆ J) :
    P.filter (fun b => I b ⊆ J) = picked h := by
  ext b
  rw [mem_filter]
  exact ⟨fun ⟨hb, he⟩ => by by_contra hp; exact hadd b hb hp he,
    fun hb => ⟨hsub hb, picked_fits I J h hv b hb⟩⟩

/-- The complete fibre over a physical output has at most T! histories
whenever the reserved-block classification recovers their block sets. -/
theorem order_fibre_card (I : B → Finset E) (J : Finset E) (hI : ∀ b, (I b).Nonempty)
    (T : ℕ) (S : Finset B) (F : Finset (List (Option B)))
    (hF : ∀ h ∈ F, h.length = T ∧ valid I J h ∧ none ∉ h ∧ picked h = S) :
    F.card ≤ T.factorial := by
  classical
  by_cases hFne : F.Nonempty
  · obtain ⟨h₀, hh₀⟩ := hFne
    obtain ⟨hT, hv, hn, he⟩ := hF h₀ hh₀
    have hScard : S.card = T := he ▸ ((picked_card I J hI h₀ hv hn).trans hT)
    let roster := S.toList.map (Option.some : B → Option B)
    have hr : roster.length = T := by simp [roster, hScard]
    have hRn : roster.Nodup := (nodup_toList S).map (Option.some_injective B)
    have hsub : F ⊆ roster.permutations.toFinset := by
      intro h hh
      obtain ⟨_, hv', hn', hs⟩ := hF h hh
      apply List.mem_toFinset.mpr
      apply List.mem_permutations.mpr
      apply (List.perm_ext_iff_of_nodup (nodup_history I J hI h hv' hn') hRn).mpr
      intro u
      cases u with
      | none => simp [hn', roster]
      | some b =>
        calc
          some b ∈ h ↔ b ∈ S := by rw [← mem_picked, hs]
          _ ↔ some b ∈ roster := by simp [roster]
    exact (card_le_card hsub).trans ((List.toFinset_card_le _).trans
      (by rw [List.length_permutations, hr]))
  · rw [not_nonempty_iff_eq_empty.mp hFne, card_empty]
    exact Nat.zero_le _

end KqR75.WeightedGreedy

#print axioms KqR75.WeightedGreedy.recover_picked
#print axioms KqR75.WeightedGreedy.order_fibre_card
