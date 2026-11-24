module
public import PhysicalHorizonCounts

@[expose] public section
noncomputable section
namespace KqR75.WeightedGreedy

open Finset
variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]

/-- The unordered packing read from a greedy history. The order is
retained separately in the original history for the factorial bound. -/
def picked (h : List (Option B)) : Finset B := (h.filterMap id).toFinset

/-- A valid greedy history partitions the host into the selected
packing and the remaining edges. Its path counts are exact counts
of the corresponding blocks in the packing. -/
theorem picked_partition (I : B → Finset E) (J : Finset E)
    (hI : ∀ b, (I b).Nonempty) (h : List (Option B)) (hv : valid I J h) :
    (∀ e : E, ((picked h).filter (fun b => e ∈ I b)).card +
      (if e ∈ remaining I J h then 1 else 0) = if e ∈ J then 1 else 0) ∧
    (∀ S : Finset B, ((picked h).filter (· ∈ S)).card = TypeCounts.count S h) := by
  classical
  induction h with
  | nil =>
    simp [picked, remaining, TypeCounts.count]
    exact fun _ => rfl
  | cons a h ih =>
    cases a with
    | none =>
      obtain ⟨he, hs⟩ := ih hv
      simpa [picked, remaining, TypeCounts.count] using ⟨he, hs⟩
    | some b =>
      obtain ⟨hh, hsub⟩ := hv
      obtain ⟨he, hs⟩ := ih hh
      have hnot : b ∉ picked h := by
        intro hb
        obtain ⟨e, he'⟩ := hI b
        have hcard : 0 < ((picked h).filter (fun c => e ∈ I c)).card :=
          card_pos.mpr ⟨b, mem_filter.mpr ⟨hb, he'⟩⟩
        have h := he e
        rw [ite_eq_left (hsub he')] at h
        split_ifs at h <;> omega
      have hinsert : picked (some b :: h) = insert b (picked h) := by
        simp [picked]
      constructor
      · intro e
        rw [hinsert]
        by_cases heb : e ∈ I b
        · rw [filter_insert, ite_eq_left heb, card_insert_of_notMem
            (fun h => hnot (mem_filter.mp h).1)]
          have hh := he e
          rw [ite_eq_left (hsub heb)] at hh
          change ((picked h).filter (fun c => e ∈ I c)).card + 1 +
              (if e ∈ remaining I J h \ I b then 1 else 0) = _
          rw [ite_eq_right (fun h => (mem_sdiff.mp h).2 heb), Nat.add_zero]
          exact hh
        · rw [filter_insert, ite_eq_right heb]
          change _ + (if e ∈ remaining I J h \ I b then 1 else 0) = _
          simpa only [mem_sdiff, heb, not_false_eq_true, and_true] using he e
      · intro S
        rw [hinsert, filter_insert]
        change (if b ∈ S then insert b ((picked h).filter (· ∈ S)) else
          (picked h).filter (· ∈ S)).card = TypeCounts.count S h + (if b ∈ S then 1 else 0)
        by_cases hb : b ∈ S
        · rw [ite_eq_left hb, card_insert_of_notMem (fun h => hnot (mem_filter.mp h).1),
            hs, ite_eq_left hb]
        · rw [ite_eq_right hb, hs, ite_eq_right hb, Nat.add_zero]

private theorem count_univ (h : List (Option B)) :
    TypeCounts.count (univ : Finset B) h = selectedCount h := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    cases a with
    | none => exact ih
    | some b => simp [TypeCounts.count, selectedCount, ih]

theorem picked_card (I : B → Finset E) (J : Finset E)
    (hI : ∀ b, (I b).Nonempty) (h : List (Option B)) (hv : valid I J h)
    (hn : none ∉ h) : (picked h).card = h.length := by
  have hc := (picked_partition I J hI h hv).2 univ
  rw [count_univ, TypeDriftEnvelope.count_eq_length h hn] at hc
  have he : (picked h).filter (· ∈ (univ : Finset B)) = picked h := by ext b; simp
  rwa [he] at hc

end KqR75.WeightedGreedy

#print axioms KqR75.WeightedGreedy.picked_partition
#print axioms KqR75.WeightedGreedy.picked_card
