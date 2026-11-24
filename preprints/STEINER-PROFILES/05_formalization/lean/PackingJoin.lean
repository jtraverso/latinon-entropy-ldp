module
public import BankDesign
public import PrefixRecovery
public import PhysicalCover

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Finset ColouredCliques CompleteJohnson SparseGram WeightedGreedy
open PhysicalBank (edgeMultiplicity)

/-- Exact physical multiplicities on a set of edges. -/
def packs {n q : ℕ} (P : Finset (Clique n q)) (A : Finset (Edge n)) : Prop :=
  ∀ e : Edge n, edgeMultiplicity P e = if e ∈ A then 1 else 0

theorem edge_of_packs {n q : ℕ} {P : Finset (Clique n q)} {A : Finset (Edge n)}
    (hP : packs P A) {b : Clique n q} (hb : b ∈ P) : resources n q b ⊆ A := by
  intro e he
  by_contra hn
  have hs : 0 < edgeMultiplicity P e := card_pos.mpr ⟨b, mem_filter.mpr ⟨hb, he⟩⟩
  have hp := hP e
  rw [ite_eq_right hn] at hp
  omega

theorem packs_disjoint {n q : ℕ} (hq : 2 ≤ q) {P Q : Finset (Clique n q)}
    {A B : Finset (Edge n)} (hP : packs P A) (hQ : packs Q B) (hd : Disjoint A B) :
    Disjoint P Q := by
  apply disjoint_left.mpr
  intro c hp hq'
  have hcard : 0 < (resources n q c).card := by rw [resources_card]; exact Nat.choose_pos hq
  obtain ⟨e, he⟩ := card_pos.mp hcard
  exact disjoint_left.mp hd (edge_of_packs hP hp he) (edge_of_packs hQ hq' he)

theorem packs_union {n q : ℕ} (hq : 2 ≤ q) {P Q : Finset (Clique n q)}
    {A B : Finset (Edge n)} (hP : packs P A) (hQ : packs Q B) (hd : Disjoint A B) :
    packs (P ∪ Q) (A ∪ B) := by
  intro e
  have hh := packs_disjoint hq hP hQ hd
  unfold edgeMultiplicity
  rw [filter_union, card_union_of_disjoint (hh.mono (filter_subset _ _) (filter_subset _ _))]
  change edgeMultiplicity P e + edgeMultiplicity Q e = _
  rw [hP e, hQ e]
  by_cases ha : e ∈ A
  · have hb : e ∉ B := fun hb => disjoint_left.mp hd ha hb
    simp [ha, hb]
  · simp [ha]

/-- The greedy packing covers precisely the edges that are no longer
in the leave. -/
theorem prefix_packs {n q : ℕ} (hq : 2 ≤ q) (J : Finset (Edge n))
    (h : List (Option (Clique n q))) (hv : valid (resources n q) J h) :
    packs (picked h) (J \ remaining (resources n q) J h) := by
  intro e
  have hne (b : Clique n q) : (resources n q b).Nonempty := by
    apply card_pos.mp
    rw [resources_card]
    exact Nat.choose_pos hq
  have hh := (picked_partition (resources n q) J hne h hv).1 e
  change edgeMultiplicity (picked h) e +
    (if e ∈ remaining (resources n q) J h then 1 else 0) = if e ∈ J then 1 else 0 at hh
  by_cases he : e ∈ J <;> by_cases hr : e ∈ remaining (resources n q) J h <;>
    simp [he, hr] at hh ⊢ <;> omega

/-- Cover-down joins the prefix to a packing of the greedy host and the
used part of the reserve. -/
theorem prefix_cover_packs {n q : ℕ} (hq : 2 ≤ q) (J Y : Finset (Edge n))
    (h : List (Option (Clique n q))) (Pcover : Finset (Clique n q))
    (hv : valid (resources n q) J h)
    (hcover : packs Pcover (remaining (resources n q) J h ∪ Y))
    (hJY : Disjoint J Y) : packs (picked h ∪ Pcover) (J ∪ Y) := by
  let L := remaining (resources n q) J h
  have hrem (g : List (Option (Clique n q))) (hg : valid (resources n q) J g) :
      remaining (resources n q) J g ⊆ J := by
    induction g with
    | nil => exact Subset.rfl
    | cons a g ih =>
      cases a with
      | none => exact ih hg
      | some b => exact sdiff_subset.trans (ih hg.1)
  have hd : Disjoint (J \ L) (L ∪ Y) := by
    rw [disjoint_union_right]
    exact ⟨sdiff_disjoint, hJY.mono_left sdiff_subset⟩
  have hpack := packs_union hq (prefix_packs hq J h hv) hcover hd
  have hparts : (J \ L) ∪ (L ∪ Y) = J ∪ Y := by
    rw [← union_assoc, sdiff_union_self_eq_union, union_eq_left.mpr (hrem h hv)]
  rwa [hparts] at hpack

/-- The prefix and its cover and absorber completions form an exact
packing of the complement of the bank. -/
theorem packs_outside_bank {n q : ℕ} (hq : 2 ≤ q) (A X F Y : Finset (Edge n))
    (hAX : Disjoint A X) (hAF : Disjoint A F) (hXF : Disjoint X F) (hY : Y ⊆ X)
    (h : List (Option (Clique n q))) (Pcover Pabs : Finset (Clique n q))
    (hv : valid (resources n q) (A ∪ X ∪ F)ᶜ h)
    (hcover : packs Pcover (remaining (resources n q) (A ∪ X ∪ F)ᶜ h ∪ Y))
    (habs : packs Pabs (A ∪ (X \ Y))) : packs (picked h ∪ Pcover ∪ Pabs) Fᶜ := by
  let J := (A ∪ X ∪ F)ᶜ
  have hJ : Disjoint J (A ∪ X ∪ F) := disjoint_compl_left
  have hJX : Disjoint J X := hJ.mono_right ((subset_union_right : X ⊆ A ∪ X).trans subset_union_left)
  have hJA : Disjoint J A := hJ.mono_right ((subset_union_left : A ⊆ A ∪ X).trans subset_union_left)
  have hp₁ := prefix_cover_packs hq J Y h Pcover hv hcover (hJX.mono_right hY)
  have hd₂ : Disjoint (J ∪ Y) (A ∪ (X \ Y)) := by
    rw [disjoint_union_left, disjoint_union_right, disjoint_union_right]
    exact ⟨⟨hJA, hJX.mono_right sdiff_subset⟩, ⟨hAX.symm.mono_left hY, sdiff_disjoint.symm⟩⟩
  have hp₂ := packs_union hq hp₁ habs hd₂
  have h₂ : (J ∪ Y) ∪ (A ∪ (X \ Y)) = J ∪ A ∪ X := by
    ext e
    simp only [mem_union, mem_sdiff]
    have h := fun he : e ∈ Y => hY he
    tauto
  rw [h₂] at hp₂
  have he : J ∪ A ∪ X = Fᶜ := by
    ext e
    simp only [J, mem_union, mem_compl]
    have ha : e ∈ A → e ∉ F := fun h => disjoint_left.mp hAF h
    have hx : e ∈ X → e ∉ F := fun h => disjoint_left.mp hXF h
    tauto
  rwa [he] at hp₂

/-- Combine the prefix, cover-down, absorber and bank when their edge
parts have been matched. The completed block set recovers its prefix
by restriction to the greedy host. -/
theorem assemble {n q : ℕ} (hq : 2 ≤ q) (A X F Y : Finset (Edge n))
    (hAX : Disjoint A X) (hAF : Disjoint A F) (hXF : Disjoint X F) (hY : Y ⊆ X)
    (h : List (Option (Clique n q))) (Pcover Pabs Pbank : Finset (Clique n q))
    (hv : valid (resources n q) (A ∪ X ∪ F)ᶜ h)
    (hcover : packs Pcover (remaining (resources n q) (A ∪ X ∪ F)ᶜ h ∪ Y))
    (hmark : ∀ b ∈ Pcover, ((resources n q b) ∩ X).Nonempty)
    (habs : packs Pabs (A ∪ (X \ Y))) (hbank : packs Pbank F) :
    let J := (A ∪ X ∪ F)ᶜ
    let P := picked h ∪ Pcover ∪ Pabs ∪ Pbank
    packs P univ ∧ P.filter (fun b => resources n q b ⊆ J) = picked h := by
  classical
  let J := (A ∪ X ∪ F)ᶜ
  have hJ : Disjoint J (A ∪ X ∪ F) := disjoint_compl_left
  have hJX : Disjoint J X := hJ.mono_right ((subset_union_right : X ⊆ A ∪ X).trans subset_union_left)
  have hJA : Disjoint J A := hJ.mono_right ((subset_union_left : A ⊆ A ∪ X).trans subset_union_left)
  have hJF : Disjoint J F := hJ.mono_right subset_union_right
  have hp := packs_outside_bank hq A X F Y hAX hAF hXF hY h Pcover Pabs hv hcover habs
  have hp₃ := packs_union hq hp hbank (disjoint_compl_left : Disjoint Fᶜ F)
  have hfull : Fᶜ ∪ F = (univ : Finset (Edge n)) := by
    ext e
    simp only [mem_union, mem_compl, mem_univ, iff_true]
    tauto
  rw [hfull] at hp₃
  refine ⟨hp₃, recover_picked (resources n q) J h hv _ ?_ ?_⟩
  · exact subset_union_left.trans (subset_union_left.trans subset_union_left)
  · intro b hb hnot hfit
    rcases mem_union.mp hb with hb | hbF
    · rcases mem_union.mp hb with hb | hbA
      · rcases mem_union.mp hb with hb | hbC
        · exact hnot hb
        · obtain ⟨e, he⟩ := hmark b hbC
          exact disjoint_left.mp hJX (hfit (mem_inter.mp he).1) (mem_inter.mp he).2
      · have heC : 0 < (resources n q b).card := by rw [resources_card]; exact Nat.choose_pos hq
        obtain ⟨e, he⟩ := card_pos.mp heC
        have heA := edge_of_packs habs hbA he
        rcases mem_union.mp heA with ha | hx
        · exact disjoint_left.mp hJA (hfit he) ha
        · exact disjoint_left.mp hJX (hfit he) (mem_sdiff.mp hx).1
    · have heC : 0 < (resources n q b).card := by rw [resources_card]; exact Nat.choose_pos hq
      obtain ⟨e, he⟩ := card_pos.mp heC
      exact disjoint_left.mp hJF (hfit he) (edge_of_packs hbank hbF he)

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.assemble
#print axioms KqR75.PhysicalCompletion.packs_outside_bank
