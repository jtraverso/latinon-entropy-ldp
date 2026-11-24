module
public import ReserveScales
public import CompleteJohnson

@[expose] public section
noncomputable section
namespace KqR75.PhysicalReserve

open Finset CompleteJohnson CliqueGram ReserveRandom ReserveCuts

/-- The reserve as a subset of the physical edge universe used by the greedy process. -/
def edges {n : ℕ} (ω : Sym2 (Fin n) → Bool) : Finset (Edge n) :=
  univ.filter (fun e => ((e.val : Finset (Fin n)) : Set (Fin n)).Pairwise (adj ω))

/-- The physical edge carried by a pair of distinct vertices. -/
def pairEdge {n : ℕ} (u v : Fin n) (h : u ≠ v) : Edge n :=
  ⟨{u, v}, mem_powersetCard.mpr ⟨subset_univ _, card_eq_two.mpr ⟨u, v, h, rfl⟩⟩⟩

theorem pairEdge_mem {n : ℕ} (ω : Sym2 (Fin n) → Bool) {u v : Fin n} (h : u ≠ v) :
    pairEdge u v h ∈ edges ω ↔ adj ω u v := by
  rw [edges, mem_filter]
  simp only [mem_univ, true_and]
  constructor
  · intro hP
    exact hP (by simp [pairEdge]) (by simp [pairEdge]) h
  · intro hA x hx y hy hxy
    have hx' : x = u ∨ x = v := by simpa [pairEdge] using hx
    have hy' : y = u ∨ y = v := by simpa [pairEdge] using hy
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · exact (hxy rfl).elim
    · exact hA
    · exact Std.Symm.symm _ _ hA
    · exact (hxy rfl).elim

/-- The degree counted by the incidence matrix equals the common-neighbour
count for a singleton root. -/
theorem degree_eq_neighbours {n : ℕ} (ω : Sym2 (Fin n) → Bool) (v : Fin n) :
    (∑ e : edges ω, incidence 2 e v) =
      ((common (adj ω) univ {v}).card : ℝ) := by
  classical
  rw [sum_coe_sort (edges ω) (fun e : Edge n => incidence (V := Fin n) 2 e v)]
  change (∑ e ∈ edges ω, if v ∈ e.val then (1 : ℝ) else 0) = _
  rw [sum_boole]
  have hc (w : Fin n) : w ∈ common (adj ω) univ {v} ↔ adj ω v w := by
    simp [common]
  have he : ((edges ω).filter (fun e => v ∈ e.val)).card =
      (common (adj ω) univ {v}).card := by
    symm
    apply card_bij (fun w hw => pairEdge v w ((hc w).mp hw).1)
    · intro w hw
      have hvw := (hc w).mp hw
      exact mem_filter.mpr ⟨(pairEdge_mem ω hvw.1).mpr hvw, by simp [pairEdge]⟩
    · intro x hx y hy hxy
      have hne := ((hc x).mp hx).1
      have hh : ({v, x} : Finset (Fin n)) = {v, y} := congrArg Subtype.val hxy
      have hx' : x ∈ ({v, y} : Finset (Fin n)) := hh ▸ (by simp : x ∈ ({v, x} : Finset (Fin n)))
      exact (mem_insert.mp hx').resolve_left hne.symm |> mem_singleton.mp
    · intro e hEdge
      obtain ⟨heX, hv⟩ := mem_filter.mp hEdge
      obtain ⟨u, w, huw, hPair⟩ := card_eq_two.mp (mem_powersetCard.mp e.property).2
      have hu : adj ω u w := by
        have hEq : e = pairEdge u w huw := Subtype.ext hPair
        exact (pairEdge_mem ω huw).mp (hEq ▸ heX)
      rw [hPair] at hv
      rcases (mem_insert.mp hv).imp_right mem_singleton.mp with hvu | hvw
      · subst v
        exact ⟨w, (hc w).mpr hu, Subtype.ext hPair.symm⟩
      · subst v
        exact ⟨u, (hc u).mpr (Std.Symm.symm _ _ hu),
          Subtype.ext ((Finset.pair_comm _ _).trans hPair.symm)⟩
  exact_mod_cast he

theorem degree_le {n : ℕ} (p : unitInterval) (ω : Sym2 (Fin n) → Bool)
    {d : ℕ} (hd : 1 ≤ d) (hroot : RootGood p ω d) (v : Fin n) :
    ∑ e : edges ω, incidence 2 e v ≤ 2 * (n : ℝ) * (p : ℝ) := by
  rw [degree_eq_neighbours]
  simpa using (hroot {v} (by simpa using hd)).1

end KqR75.PhysicalReserve

#print axioms KqR75.PhysicalReserve.degree_eq_neighbours
#print axioms KqR75.PhysicalReserve.degree_le
