module
public import KqCore
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section
noncomputable section
namespace KqR75.CliqueGram

open Finset
open scoped Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of q-cliques containing both specified sets of vertices. -/
def multiplicity (q : ℕ) (e f : Finset V) : ℕ :=
  (((univ : Finset V).powersetCard q).filter fun b => e ⊆ b ∧ f ⊆ b).card

/-- Vertex incidence of the complete q-uniform system. At q=2 its rows are edges. -/
def incidence (q : ℕ) : Matrix ((univ : Finset V).powersetCard q) V ℝ :=
  fun b v => if v ∈ (b : Finset V) then 1 else 0

/-- Actual resource-block incidence: rows are pairs and columns are q-cliques. -/
def pairIncidence (q : ℕ) :
    Matrix ((univ : Finset V).powersetCard 2) ((univ : Finset V).powersetCard q) ℝ :=
  fun e b => if (e : Finset V) ⊆ (b : Finset V) then 1 else 0

theorem multiplicity_eq_choose (q : ℕ) (e f : Finset V) (h : (e ∪ f).card ≤ q) :
    multiplicity q e f = (Fintype.card V - (e ∪ f).card).choose (q - (e ∪ f).card) := by
  simpa only [multiplicity, ← Finset.union_subset_iff, Finset.card_univ] using
    Finset.card_filter_powersetCard_subset (e ∪ f) univ q (subset_univ _) h

/-- The exceptional small-q case is zero, rather than a truncated binomial ratio. -/
theorem multiplicity_eq_zero (q : ℕ) (e f : Finset V) (h : q < (e ∪ f).card) :
    multiplicity q e f = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro b hb hsub
  have hc := (Finset.mem_powersetCard.mp hb).2
  have hs := Finset.card_le_card (Finset.union_subset_iff.mpr hsub)
  omega

/-- The actual incidence Gram entry equals its finite clique multiplicity. -/
theorem gram_entry (q : ℕ) (e f : Finset V) :
    (∑ b : ((univ : Finset V).powersetCard q),
      (if e ⊆ (b : Finset V) then (1 : ℝ) else 0) *
        (if f ⊆ (b : Finset V) then (1 : ℝ) else 0)) = (multiplicity q e f : ℝ) := by
  rw [Finset.sum_coe_sort ((univ : Finset V).powersetCard q)
    (fun b : Finset V => (if e ⊆ b then (1 : ℝ) else 0) *
      (if f ⊆ b then (1 : ℝ) else 0))]
  simp only [ite_mul, one_mul, zero_mul, ← ite_and]
  simp [multiplicity, Finset.sum_boole]

theorem pair_gram_entry (q : ℕ)
    (e f : ((univ : Finset V).powersetCard 2)) :
    (pairIncidence (V := V) q * (pairIncidence (V := V) q)ᵀ) e f =
      (multiplicity q (e : Finset V) (f : Finset V) : ℝ) := by
  exact gram_entry q (e : Finset V) (f : Finset V)

/-- The adjacent binomial ratio used to normalize clique Gram entries. -/
theorem choose_ratio (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) / ((n + 1).choose (k + 1) : ℝ) =
      ((k + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) := by
  have hd : ((n + 1).choose (k + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.succ_le_succ hk)).ne'
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hh : ((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ) =
      ((n + 1).choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq n k
  apply (div_eq_div_iff hd hn).mpr
  nlinarith only [hh]

theorem incidence_row_sum (q : ℕ) (b : ((univ : Finset V).powersetCard q)) :
    (∑ v, incidence q b v) = (q : ℝ) := by
  have hb : (b : Finset V).card = q := (Finset.mem_powersetCard.mp b.property).2
  simp [incidence, Finset.sum_boole, hb]

theorem edge_gram_entry (e f : ((univ : Finset V).powersetCard 2)) :
    (incidence (V := V) 2 * (incidence (V := V) 2)ᵀ) e f =
      (((e : Finset V) ∩ (f : Finset V)).card : ℝ) := by
  change (∑ v, (if v ∈ (e : Finset V) then (1 : ℝ) else 0) *
    (if v ∈ (f : Finset V) then (1 : ℝ) else 0)) = _
  simp only [ite_mul, one_mul, zero_mul, ← ite_and, ← Finset.mem_inter]
  have hfilter : (univ.filter fun v => v ∈ (e : Finset V) ∩ (f : Finset V)) =
      (e : Finset V) ∩ (f : Finset V) :=
    Finset.filter_mem_eq_of_subset (Finset.subset_univ _)
  simp only [Finset.sum_boole, hfilter]

theorem incidence_column_sum (v : V) :
    (∑ b, incidence 2 b v) = ((Fintype.card V - 1 : ℕ) : ℝ) := by
  have hh := gram_entry 2 ({v} : Finset V) ∅
  simp only [Finset.singleton_subset_iff, Finset.empty_subset, ite_true, mul_one] at hh
  rw [multiplicity_eq_choose 2 ({v} : Finset V) ∅ (by simp)] at hh
  simpa [incidence] using hh

/-- The vertex Gram of the complete graph, proved from actual edge counts. -/
theorem vertex_gram (hn : 2 ≤ Fintype.card V) :
    (incidence (V := V) 2)ᵀ * incidence (V := V) 2 =
      ((Fintype.card V : ℝ) - 2) • (1 : Matrix V V ℝ) +
        Matrix.of (fun (_ : V) (_ : V) => (1 : ℝ)) := by
  ext v w
  have hh := gram_entry 2 ({v} : Finset V) ({w} : Finset V)
  simp only [Finset.singleton_subset_iff] at hh
  change (∑ b : ((univ : Finset V).powersetCard 2),
      (if v ∈ (b : Finset V) then (1 : ℝ) else 0) *
        (if w ∈ (b : Finset V) then (1 : ℝ) else 0)) = _
  rw [hh]
  by_cases hvw : v = w
  · subst w
    rw [multiplicity_eq_choose 2 ({v} : Finset V) {v} (by simp)]
    have hn1 : 1 ≤ Fintype.card V := by omega
    simp [Nat.cast_sub hn1, Matrix.one_apply]
    <;> ring
  · rw [multiplicity_eq_choose 2 ({v} : Finset V) {w} (by simp [hvw])]
    simp [hvw, Matrix.one_apply]

theorem adjacent_ratio (n q : ℕ) (hq : 3 ≤ q) (hn : q + 2 ≤ n) :
    ((n - 3).choose (q - 3) : ℝ) / ((n - 2).choose (q - 2) : ℝ) =
      ((q : ℝ) - 2) / ((n : ℝ) - 2) := by
  have hh := choose_ratio (n - 3) (q - 3) (by omega)
  have hn' : n - 3 + 1 = n - 2 := by omega
  have hq' : q - 3 + 1 = q - 2 := by omega
  rw [hn', hq'] at hh
  simpa only [Nat.cast_sub (by omega : 2 ≤ q), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_ofNat] using hh

theorem disjoint_ratio (n q : ℕ) (hq : 4 ≤ q) (hn : q + 2 ≤ n) :
    ((n - 4).choose (q - 4) : ℝ) / ((n - 2).choose (q - 2) : ℝ) =
      (((q : ℝ) - 2) * ((q : ℝ) - 3)) / (((n : ℝ) - 2) * ((n : ℝ) - 3)) := by
  have hh := choose_ratio (n - 4) (q - 4) (by omega)
  have hn' : n - 4 + 1 = n - 3 := by omega
  have hq' : q - 4 + 1 = q - 3 := by omega
  rw [hn', hq'] at hh
  have hh' : ((n - 4).choose (q - 4) : ℝ) / ((n - 3).choose (q - 3) : ℝ) =
      ((q : ℝ) - 3) / ((n : ℝ) - 3) := by
    simpa only [Nat.cast_sub (by omega : 3 ≤ q), Nat.cast_sub (by omega : 3 ≤ n),
      Nat.cast_ofNat] using hh
  have hB : ((n - 3).choose (q - 3) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : q - 3 ≤ n - 3)).ne'
  have hD : ((n - 2).choose (q - 2) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : q - 2 ≤ n - 2)).ne'
  calc
    _ = (((n - 4).choose (q - 4) : ℝ) / ((n - 3).choose (q - 3) : ℝ)) *
        (((n - 3).choose (q - 3) : ℝ) / ((n - 2).choose (q - 2) : ℝ)) := by
      field_simp [hB, hD]
    _ = (((q : ℝ) - 3) / ((n : ℝ) - 3)) * (((q : ℝ) - 2) / ((n : ℝ) - 2)) := by
      rw [hh', adjacent_ratio n q (by omega) hn]
    _ = _ := by rw [div_mul_div_comm]; congr 1 <;> ring

end KqR75.CliqueGram

#print axioms KqR75.CliqueGram.multiplicity_eq_choose
#print axioms KqR75.CliqueGram.multiplicity_eq_zero
#print axioms KqR75.CliqueGram.gram_entry
#print axioms KqR75.CliqueGram.vertex_gram
