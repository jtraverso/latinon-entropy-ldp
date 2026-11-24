module
public import CoverDown

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Adjacent vertices in a family of unordered pairs. -/
def adjacentVertices (L : Finset (Finset V)) (u : V) : Finset V :=
  (univ.erase u).filter (fun v => {u, v} ∈ L)

theorem star_adjacentVertices (L : Finset (Finset V)) (u : V)
    (hL : ∀ e ∈ L, e.card = 2) :
    star u (adjacentVertices L u) = L.filter (fun e => u ∈ e) := by
  ext e
  constructor
  · intro he
    obtain ⟨v, hv, rfl⟩ := mem_image.mp he
    exact mem_filter.mpr ⟨(mem_filter.mp hv).2, mem_insert_self _ _⟩
  · intro he
    obtain ⟨heL, hu⟩ := mem_filter.mp he
    obtain ⟨x, y, hxy, hpair⟩ := card_eq_two.mp (hL e heL)
    rw [hpair] at hu
    rcases (mem_insert.mp hu).imp_right mem_singleton.mp with hux | huy
    · subst x
      exact mem_image.mpr ⟨y, mem_filter.mpr
        ⟨mem_erase.mpr ⟨hxy.symm, mem_univ _⟩, hpair ▸ heL⟩, hpair.symm⟩
    · subst y
      have hpair' := hpair.trans (pair_comm x u)
      exact mem_image.mpr ⟨x, mem_filter.mpr
        ⟨mem_erase.mpr ⟨hxy, mem_univ _⟩, hpair' ▸ heL⟩, hpair'.symm⟩

theorem adjacentVertices_card (L : Finset (Finset V)) (u : V)
    (hL : ∀ e ∈ L, e.card = 2) : (adjacentVertices L u).card = degree L u := by
  have hnot : u ∉ adjacentVertices L u := fun h => (mem_erase.mp (mem_filter.mp h).1).1 rfl
  have hcard : (star u (adjacentVertices L u)).card = (adjacentVertices L u).card := by
    apply card_image_of_injOn
    intro a ha b hb h
    change ({u, a} : Finset V) = {u, b} at h
    have hm : a ∈ ({u, b} : Finset V) := h ▸ mem_insert_of_mem (mem_singleton_self a)
    exact (mem_insert.mp hm).resolve_left (fun he => hnot (he ▸ ha)) |> mem_singleton.mp
  rw [star_adjacentVertices L u hL] at hcard
  exact hcard.symm

theorem sum_degrees (L : Finset (Finset V)) (hL : ∀ e ∈ L, e.card = 2) :
    (∑ u : V, degree L u) = 2 * L.card := by
  classical
  calc
    _ = ∑ u : V, ∑ e ∈ L, if u ∈ e then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro u _
      rw [degree, sum_boole]
      simp
    _ = ∑ e ∈ L, ∑ u : V, if u ∈ e then (1 : ℕ) else 0 := sum_comm
    _ = ∑ e ∈ L, (2 : ℕ) := by
      apply sum_congr rfl
      intro e he
      rw [sum_boole, filter_mem_eq_of_subset (subset_univ e)]
      simpa using hL e he
    _ = _ := by simp [mul_comm]

/-- A nonnegative integer potential bounds how many vertices
have reached the threshold for exclusion. -/
theorem card_large (f : V → ℕ) (D : ℕ) :
    ((univ.filter (fun v => D ≤ f v)).card) * D ≤ ∑ v : V, f v := by
  let S := univ.filter (fun v => D ≤ f v)
  calc
    _ = ∑ v ∈ S, D := by
      change S.card * D = _
      rw [sum_const, Nat.nsmul_eq_mul]
    _ ≤ ∑ v ∈ S, f v := sum_le_sum (fun v hv => (mem_filter.mp hv).2)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.zero_le _)

end KqR75.CoverDown

#print axioms KqR75.CoverDown.adjacentVertices_card
#print axioms KqR75.CoverDown.sum_degrees
#print axioms KqR75.CoverDown.card_large
