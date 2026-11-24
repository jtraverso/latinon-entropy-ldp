module
public import CoverComplete
public import CoverTransfer

@[expose] public section
noncomputable section
namespace KqR75.CoverDown

open Filter Finset CompleteJohnson ColouredCliques ReserveRandom

/-- The universal cover-down in the same edge and clique types as the
greedy process. Its output includes the reserve witness for recovery
of the greedy prefix from the completed design. -/
theorem eventually_cover_physical (q : ℕ) (hq : 3 ≤ q) (z M : ℝ) (hz : 0 < z) (hM : 0 ≤ M)
    (hgap : (2 * (q : ℝ) + 1) * z < 1) :
    ∃ K₀ : ℝ, 1 ≤ K₀ ∧ ∀ K ≥ K₀, ∀ᶠ n : ℕ in atTop,
      ∃ (p : unitInterval) (ω : Sym2 (Fin n) → Bool), (p : ℝ) = K * (n : ℝ) ^ (-z) ∧
        RootGood p ω (q - 1) ∧
        let X := PhysicalReserve.edges ω
        ∀ L : Finset (Edge n), (L.card : ℝ) ≤ M * (n : ℝ) ^ (2 - (2 * (q : ℝ) - 1) * z) →
          Disjoint L X →
          ∃ P : Finset (Clique n q), ∃ Y : Finset (Edge n), Y ⊆ X ∧
            Y.card ≤ q.choose 2 * L.card ∧
            (∀ e : Edge n, (P.filter (fun C => e ∈ SparseGram.resources n q C)).card =
              if e ∈ L ∪ Y then 1 else 0) ∧
            ∀ C ∈ P, ((SparseGram.resources n q C) ∩ X).Nonempty := by
  obtain ⟨K₀, hK₀, h⟩ := eventually_cover q hq z M hz hM hgap
  refine ⟨K₀, hK₀, fun K hK => ?_⟩
  filter_upwards [h K hK] with n hn
  obtain ⟨p, ω, hp, hr, hc⟩ := hn
  let X := PhysicalReserve.edges ω
  refine ⟨p, ω, hp, hr, ?_⟩
  change ∀ (L : Finset (Edge n)), _ → Disjoint L X → _
  intro L hL hdis
  have hraw : Disjoint (vertexSets L) (reserveEdges (adj ω) univ) := by
    rw [← reserve_vertexSets]
    apply disjoint_left.mpr
    intro e he hx
    obtain ⟨f, hf, rfl⟩ := mem_map.mp he
    exact disjoint_left.mp hdis hf ((vertexSets_mem X f).mp hx)
  obtain ⟨P, Y, hcov, hsize⟩ := hc (vertexSets L) (fun e he => vertexSets_card he)
    (by simpa only [vertexSets_size] using hL) hraw
  rw [← reserve_vertexSets] at hcov
  obtain ⟨hYX, hYcard, hmult, hw⟩ := physical_completion hcov
  refine ⟨physicalSets q P, physicalSets 2 Y, hYX, ?_, hmult, hw⟩
  simpa only [hYcard, vertexSets_size] using hsize

end KqR75.CoverDown

#print axioms KqR75.CoverDown.eventually_cover_physical
