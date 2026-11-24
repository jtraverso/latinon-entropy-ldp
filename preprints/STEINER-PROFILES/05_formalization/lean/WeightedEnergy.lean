module
public import SignedBlock

@[expose] public section
noncomputable section
namespace KqR75.WeightedEnergy

open Finset

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

def load (I : B → Finset E) (w : B → ℝ) (e : E) : ℝ :=
  ∑ b, if e ∈ I b then w b else 0

theorem incidence_sum (I : B → Finset E) (w : B → ℝ) (f : E → ℝ) :
    (∑ b, w b * ∑ e ∈ I b, f e) = ∑ e, load I w e * f e := by
  have hi (b : B) : w b * ∑ e ∈ I b, f e =
      ∑ e, (if e ∈ I b then w b else 0) * f e := by
    rw [Finset.mul_sum]
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter]
    simp
  simp_rw [hi]
  rw [Finset.sum_comm]
  simp only [load, Finset.sum_mul]

/-- The universal block inequality after summing actual positive block weights.
Zero-load resources are retained on the right, so no division by zero is required. -/
theorem signed_quadratic (I : B → Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b)
    (r : ℕ) (hr : 1 ≤ r) (hcard : ∀ b, (I b).card = r)
    (k : ℝ) (hk : 0 < k) (x : E → ℝ)
    (hx : ∀ e, 0 < load I w e → x e = load I w e - k) :
    (∑ e, load I w e * (x e) ^ 2) -
        2 * (∑ b, w b * (∑ e ∈ I b, x e) ^ 2) ≤
      (2 * (r : ℝ) - 1) * k * ∑ e, (x e) ^ 2 := by
  classical
  have hload (e : E) : 0 ≤ load I w e := by
    apply Finset.sum_nonneg
    intro b _
    split_ifs
    · exact hw b
    · exact le_rfl
  have hb (b : B) :
      w b * ((∑ e ∈ I b, (x e) ^ 2) - 2 * (∑ e ∈ I b, x e) ^ 2) ≤
        w b * ((2 * (r : ℝ) - 1) * k * ∑ e ∈ I b, (x e) ^ 2 / load I w e) := by
    by_cases hzero : w b = 0
    · simp [hzero]
    have hwb : 0 < w b := lt_of_le_of_ne (hw b) (Ne.symm hzero)
    have hpos (e : I b) : 0 < load I w e := by
      have hh : w b ≤ load I w e := by
        have hh := Finset.single_le_sum
          (f := fun c : B => if (e : E) ∈ I c then w c else 0)
          (fun c (_ : c ∈ (univ : Finset B)) => by
            split_ifs
            · exact hw c
            · exact le_rfl)
          (mem_univ b)
        simpa only [load, e.property, ite_true] using hh
      exact hwb.trans_le hh
    have he (e : I b) : load I w e - k = x e := (hx e (hpos e)).symm
    have hsize : 1 ≤ Fintype.card (I b) := by simpa [hcard b] using hr
    have hh := KqR75.SignedBlock.universal (fun e : I b => load I w e) hpos k hk hsize
    simp_rw [he] at hh
    have hsq : (∑ e : I b, (x (e : E)) ^ 2) = ∑ e ∈ I b, (x e) ^ 2 :=
      Finset.sum_coe_sort (I b) (fun e : E => (x e) ^ 2)
    have hlin : (∑ e : I b, x (e : E)) = ∑ e ∈ I b, x e :=
      Finset.sum_coe_sort (I b) x
    have hquot : (∑ e : I b, (x (e : E)) ^ 2 / load I w e) =
        ∑ e ∈ I b, (x e) ^ 2 / load I w e :=
      Finset.sum_coe_sort (I b) (fun e : E => (x e) ^ 2 / load I w e)
    rw [hsq, hlin, hquot, Fintype.card_coe, hcard] at hh
    have hh' : (∑ e ∈ I b, (x e) ^ 2) - 2 * (∑ e ∈ I b, x e) ^ 2 ≤
        (2 * (r : ℝ) - 1) * k * ∑ e ∈ I b, (x e) ^ 2 / load I w e := by
      exact hh
    exact mul_le_mul_of_nonneg_left hh' (hw b)
  have hs := Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset B)) => hb b)
  have hleft : (∑ b, w b * ((∑ e ∈ I b, (x e) ^ 2) -
      2 * (∑ e ∈ I b, x e) ^ 2)) =
      (∑ e, load I w e * (x e) ^ 2) - 2 * ∑ b, w b * (∑ e ∈ I b, x e) ^ 2 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    rw [incidence_sum]
    congr 1
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hright : (∑ b, w b * ((2 * (r : ℝ) - 1) * k *
      ∑ e ∈ I b, (x e) ^ 2 / load I w e)) =
      (2 * (r : ℝ) - 1) * k * ∑ e, load I w e * ((x e) ^ 2 / load I w e) := by
    calc
      _ = ∑ b, ((2 * (r : ℝ) - 1) * k) *
          (w b * ∑ e ∈ I b, (x e) ^ 2 / load I w e) := by
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = ((2 * (r : ℝ) - 1) * k) *
          ∑ b, w b * ∑ e ∈ I b, (x e) ^ 2 / load I w e :=
        (Finset.mul_sum _ _ _).symm
      _ = _ := by rw [incidence_sum]
  rw [hleft, hright] at hs
  have he (e : E) : load I w e * ((x e) ^ 2 / load I w e) ≤ (x e) ^ 2 := by
    by_cases hz : load I w e = 0
    · simp [hz, sq_nonneg]
    · have hh : load I w e * ((x e) ^ 2 / load I w e) = (x e) ^ 2 := by
        field_simp [hz]
      exact hh.le
  have hrR : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  exact hs.trans (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun e (_ : e ∈ (univ : Finset E)) => he e))
    (mul_nonneg (by linarith) hk.le))

end KqR75.WeightedEnergy

#print axioms KqR75.WeightedEnergy.incidence_sum
#print axioms KqR75.WeightedEnergy.signed_quadratic
