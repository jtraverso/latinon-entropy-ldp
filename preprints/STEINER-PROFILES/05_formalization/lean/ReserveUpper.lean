module
public import ReserveCuts
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section
noncomputable section
namespace KqR75.ReserveCuts

open Finset

variable {V : Type*} [DecidableEq V]

/-- Vertices of S joined to every prescribed root. -/
def common (R : V → V → Prop) [DecidableRel R] (S H : Finset V) : Finset V :=
  S.filter (fun w => ∀ u ∈ H, R u w)

/-- Auxiliary vertices extending a fixed root set, with no conditions on the
edges internal to the roots. -/
def extensions (R : V → V → Prop) [DecidableRel R] (S H : Finset V)
    (k : ℕ) : Finset (Finset V) := cliquesIn R (common R S H) k

private theorem mem_extensions (R : V → V → Prop) [DecidableRel R]
    (S H : Finset V) (k : ℕ) (C : Finset V) :
    C ∈ extensions R S H k ↔
      C ⊆ common R S H ∧ C.card = k ∧ (C : Set V).Pairwise R := by
  rw [extensions, cliquesIn, mem_filter, mem_powersetCard, and_assoc]

/-- A nonempty extension is obtained by adjoining one vertex to a smaller
extension whose root set includes that vertex. -/
private theorem extensions_succ_subset (R : V → V → Prop) [DecidableRel R]
    (S H : Finset V) (k : ℕ) :
    extensions R S H (k + 1) ⊆ (common R S H).biUnion (fun w =>
      (extensions R S (insert w H) k).image (insert w)) := by
  intro C hC
  obtain ⟨hsub, hcard, hpair⟩ := (mem_extensions R S H (k + 1) C).mp hC
  obtain ⟨w, hw⟩ := card_pos.mp (by omega : 0 < C.card)
  refine mem_biUnion.mpr ⟨w, hsub hw, mem_image.mpr ⟨C.erase w, ?_, insert_erase hw⟩⟩
  refine (mem_extensions R S (insert w H) k (C.erase w)).mpr ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨hxw, hxC⟩ := mem_erase.mp hx
    obtain ⟨hxS, hxH⟩ := mem_filter.mp (hsub hxC)
    refine mem_filter.mpr ⟨hxS, fun u hu => ?_⟩
    rcases mem_insert.mp hu with rfl | hu
    · exact hpair hw hxC (Ne.symm hxw)
    · exact hxH u hu
  · rw [card_erase_of_mem hw, hcard, Nat.add_sub_cancel]
  · exact hpair.mono (fun _ hx => (mem_erase.mp hx).2)

/-- Uniform common-neighbour bounds control all extensions, even when the
roots are not themselves a clique. -/
theorem extensions_card_le (R : V → V → Prop) [DecidableRel R] (hirr : ∀ v, ¬ R v v)
    (S : Finset V) (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (d : ℕ)
    (hcommon : ∀ H ⊆ S, H.card < d → ((common R S H).card : ℝ) ≤ b H.card)
    (H : Finset V) (hH : H ⊆ S) (k : ℕ) (hlim : H.card + k ≤ d) :
    ((extensions R S H k).card : ℝ) ≤ ∏ j ∈ range k, b (H.card + j) := by
  induction k generalizing H with
  | zero =>
    simp only [range_zero, prod_empty]
    have hs : extensions R S H 0 ⊆ {∅} := by
      intro C hC
      simpa only [mem_singleton, ← card_eq_zero] using (mem_extensions R S H 0 C).mp hC |>.2.1
    exact_mod_cast (card_le_card hs).trans (by simp)
  | succ k ih =>
    let P := ∏ j ∈ range k, b (H.card + 1 + j)
    have hP : 0 ≤ P := prod_nonneg (fun j _ => hb _)
    have hsmall : H.card < d := by omega
    have hstep (w : V) (hw : w ∈ common R S H) :
        (((extensions R S (insert w H) k).image (insert w)).card : ℝ) ≤ P := by
      obtain ⟨hwS, hwH⟩ := mem_filter.mp hw
      have hnot : w ∉ H := fun h => hirr w (hwH w h)
      have hc : (insert w H).card = H.card + 1 := card_insert_of_notMem hnot
      have hbound := ih (insert w H) (insert_subset hwS hH) (by rw [hc]; omega)
      rw [hc] at hbound
      refine le_trans ?_ hbound
      exact_mod_cast card_image_le
    calc
      _ ≤ (((common R S H).biUnion fun w =>
          (extensions R S (insert w H) k).image (insert w)).card : ℝ) := by
        exact_mod_cast card_le_card (extensions_succ_subset R S H k)
      _ ≤ ∑ w ∈ common R S H, (((extensions R S (insert w H) k).image (insert w)).card : ℝ) := by
        rw [← Nat.cast_sum]
        exact_mod_cast card_biUnion_le
      _ ≤ ∑ _w ∈ common R S H, P := sum_le_sum (fun w hw => hstep w hw)
      _ = ((common R S H).card : ℝ) * P := by rw [sum_const, nsmul_eq_mul]
      _ ≤ b H.card * P := mul_le_mul_of_nonneg_right (hcommon H hH hsmall) hP
      _ = _ := by
        rw [prod_range_succ', Nat.add_zero, mul_comm]
        congr 1
        apply prod_congr rfl
        intro j _
        congr 1
        omega

/-- The polynomial upper bound from common-neighbour estimates at density p. -/
theorem extensions_card_le_density (R : V → V → Prop) [DecidableRel R]
    (hirr : ∀ v, ¬ R v v) (S : Finset V) (p : ℝ) (hp : 0 ≤ p) (d : ℕ)
    (hcommon : ∀ H ⊆ S, H.card < d →
      ((common R S H).card : ℝ) ≤ 2 * (S.card : ℝ) * p ^ H.card)
    (H : Finset V) (hH : H ⊆ S) (k : ℕ) (hlim : H.card + k ≤ d) :
    ((extensions R S H k).card : ℝ) ≤
      (2 * (S.card : ℝ)) ^ k * p ^ (H.card * k + k.choose 2) := by
  refine (extensions_card_le R hirr S (fun j => 2 * (S.card : ℝ) * p ^ j)
    (fun j => by positivity) d hcommon H hH k hlim).trans_eq ?_
  rw [prod_mul_distrib, prod_const, card_range, prod_pow_eq_pow_sum]
  congr 2
  rw [sum_add_distrib, sum_const, card_range, Nat.nsmul_eq_mul, sum_range_id,
    Nat.choose_two_right, Nat.mul_comm k H.card]

theorem common_pair_eq (R : V → V → Prop) [DecidableRel R] (S : Finset V) (u v : V) :
    common R S {u, v} = commonPair R S u v := by
  ext w
  simp [common, commonPair]

end KqR75.ReserveCuts

#print axioms KqR75.ReserveCuts.extensions_card_le
#print axioms KqR75.ReserveCuts.extensions_card_le_density
