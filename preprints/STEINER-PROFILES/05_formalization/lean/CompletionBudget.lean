module
public import BankHorizon
public import PackingJoin

@[expose] public section
noncomputable section
namespace KqR75.PhysicalCompletion

open Finset CliqueGram ColouredCliques CompleteJohnson SparseGram
open PhysicalBank (edgeMultiplicity)
open BankCapacity (edge_card_of_degree block_card_of_marking)

private theorem packing_bound {n q : ℕ} {P : Finset (Clique n q)}
    {A : Finset (Edge n)} (h : packs P A) (e : Edge n) :
    (P.filter (fun b => e ∈ resources n q b)).card ≤ 1 := by
  change edgeMultiplicity P e ≤ 1
  rw [h e]
  split_ifs <;> omega

private theorem card_le_edges {n q : ℕ} (hq : 2 ≤ q)
    {P : Finset (Clique n q)} {A : Finset (Edge n)} (h : packs P A) : P.card ≤ A.card := by
  apply block_card_of_marking P A (packing_bound h)
  intro b hb
  have hpos : 0 < (resources n q b).card := by
    rw [resources_card]
    exact Nat.choose_pos hq
  obtain ⟨e, he⟩ := card_pos.mp hpos
  exact ⟨e, mem_inter.mpr ⟨he, edge_of_packs h hb he⟩⟩

/-- The total number of blocks charged to the correction, counting the
empty absorber decomposition as well, is bounded using just the reserve
and absorber degrees. The degree of the bank does not enter the bound. -/
theorem completion_block_budget {n q : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n)
    {A X Y L : Finset (Edge n)} {P₀ PC PA : Finset (Clique n q)}
    (h₀ : packs P₀ A) (hC : packs PC (L ∪ Y)) (hA : packs PA (A ∪ (X \ Y)))
    (hmark : ∀ b ∈ PC, ((resources n q b) ∩ X).Nonempty)
    (G U z : ℝ)
    (hdegA : ∀ v : Fin n, ∑ e : A, incidence 2 e v ≤ G * (n : ℝ) ^ (1 - z))
    (hdegX : ∀ v : Fin n, ∑ e : X, incidence 2 e v ≤ U * (n : ℝ) ^ (1 - z)) :
    (P₀.card : ℝ) + PC.card + PA.card ≤ (G + U) * (n : ℝ) ^ (2 - z) := by
  have hbase : (P₀.card : ℝ) ≤ A.card := by exact_mod_cast card_le_edges hq h₀
  have hc : (PC.card : ℝ) ≤ X.card := by
    exact_mod_cast block_card_of_marking PC X (packing_bound hC) hmark
  have ha : (PA.card : ℝ) ≤ (A.card : ℝ) + X.card := by
    have hcard := (card_le_edges hq hA).trans <|
      (card_union_le A (X \ Y)).trans (Nat.add_le_add_left (card_le_card sdiff_subset) _)
    exact_mod_cast hcard
  have hn₀ : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hx : (n : ℝ) * (n : ℝ) ^ (1 - z) = (n : ℝ) ^ (2 - z) := by
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 - z) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hn₀]
        congr 1
        ring
  have ha' := edge_card_of_degree A _ hdegA
  have hx' := edge_card_of_degree X _ hdegX
  calc
    _ ≤ 2 * (A.card : ℝ) + 2 * (X.card : ℝ) := by linarith only [hbase, hc, ha]
    _ ≤ (n : ℝ) * (G * (n : ℝ) ^ (1 - z)) +
        (n : ℝ) * (U * (n : ℝ) ^ (1 - z)) := by linarith only [ha', hx']
    _ = _ := by rw [← hx]; ring

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The defect bound uses the reserve-repair and prefix errors and the
completion block budget. The baseline bank histogram cancels exactly. -/
theorem completion_type_budget {n q : ℕ} (colour : Fin n → C)
    (bank basal picked cover absorbed : Finset (Clique n q)) (t : TypeProfile C q)
    {m repaired ε₁ ε₂ E : ℝ}
    (h₁ : |m - (BankCapacity.integerHistogram colour bank t : ℝ) -
      (BankCapacity.integerHistogram colour basal t : ℝ) - repaired| ≤ ε₁)
    (h₂ : |repaired - (BankCapacity.integerHistogram colour picked t : ℝ)| ≤ ε₂)
    (hbudget : (basal.card : ℝ) + cover.card + absorbed.card ≤ E)
    (hd₁ : Disjoint bank picked) (hd₂ : Disjoint (bank ∪ picked) cover)
    (hd₃ : Disjoint (bank ∪ picked ∪ cover) absorbed) :
    |m - (BankCapacity.integerHistogram colour (bank ∪ picked ∪ cover ∪ absorbed) t : ℝ)|
      ≤ ε₁ + ε₂ + E := by
  let H := fun P : Finset (Clique n q) => (BankCapacity.integerHistogram colour P t : ℝ)
  have hsum {P Q : Finset (Clique n q)} (hd : Disjoint P Q) : H (P ∪ Q) = H P + H Q := by
    simp only [H, BankCapacity.integerHistogram, Int.cast_natCast]
    rw [filter_union, card_union_of_disjoint (hd.mono (filter_subset _ _) (filter_subset _ _)),
      Nat.cast_add]
  have hn (P : Finset (Clique n q)) : 0 ≤ H P := by
    simp [H, BankCapacity.integerHistogram]
  have hle (P : Finset (Clique n q)) : H P ≤ (P.card : ℝ) := by
    simp only [H, BankCapacity.integerHistogram, Int.cast_natCast, Nat.cast_le]
    exact card_filter_le _ _
  change |m - H (bank ∪ picked ∪ cover ∪ absorbed)| ≤ _
  rw [hsum hd₃, hsum hd₂, hsum hd₁]
  refine (BankCapacity.completed_defect h₁ h₂ (hn basal) (hn cover) (hn absorbed)).trans ?_
  linarith only [hbudget, hle basal, hle cover, hle absorbed]

end KqR75.PhysicalCompletion

#print axioms KqR75.PhysicalCompletion.completion_block_budget
#print axioms KqR75.PhysicalCompletion.completion_type_budget
