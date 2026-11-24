module
public import HostCorrection
public import WeightedEnergy

@[expose] public section
noncomputable section
namespace KqR75.PrunedWeights

open Finset CliqueGram CompleteJohnson SparseGram
open scoped Matrix

variable {E B : Type*} [Fintype E] [DecidableEq E] [Fintype B]

/-- A removed block has a deleted resource. Sum a nonnegative weight
over such blocks by charging it to all its deleted resources. -/
theorem deleted_sum_le (I : B → Finset E) (J : Finset E) (w : B → ℝ) (hw : ∀ b, 0 ≤ w b) :
    (∑ b, if I b ⊆ J then 0 else w b) ≤
      ∑ f : (Jᶜ : Finset E), ∑ b, if (f : E) ∈ I b then w b else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b _
  have hn (f : (Jᶜ : Finset E)) : 0 ≤ (if (f : E) ∈ I b then w b else 0) := by
    split_ifs <;> first | exact hw b | exact le_rfl
  by_cases hb : I b ⊆ J
  · simp only [hb, ite_true]
    exact Finset.sum_nonneg (fun f _ => hn f)
  · obtain ⟨f, hf, hfJ⟩ := Finset.not_subset.mp hb
    let g : (Jᶜ : Finset E) := ⟨f, Finset.mem_compl.mpr hfJ⟩
    have hg := Finset.single_le_sum (s := (univ : Finset (Jᶜ : Finset E)))
      (f := fun f : (Jᶜ : Finset E) => if (f : E) ∈ I b then w b else 0)
      (fun f _ => hn f) (mem_univ g)
    simpa only [hb, ite_false, g, hf, ite_true] using hg

theorem deleted_row_le (I : B → Finset E) (J : Finset E) (w : B → ℝ)
    (hw : ∀ b, 0 ≤ w b) (e : E) :
    (∑ b, if I b ⊆ J then 0 else if e ∈ I b then w b else 0) ≤
      ∑ f : (Jᶜ : Finset E), DeletedGram.gram I w e f := by
  have hs := deleted_sum_le I J (fun b => if e ∈ I b then w b else 0)
    (fun b => by split_ifs <;> first | exact hw b | exact le_rfl)
  refine hs.trans_eq ?_
  apply Finset.sum_congr rfl
  intro f _
  unfold DeletedGram.gram
  apply Finset.sum_congr rfl
  intro b _
  by_cases he : e ∈ I b <;> by_cases hf : (f : E) ∈ I b <;> simp [he, hf]

variable {n q : ℕ}

theorem scaled_incidence_sum (hq : 3 ≤ q) (hn : q + 2 ≤ n) (e : Edge n) :
    (∑ b : HostCorrection.Block n q,
      if e ∈ resources n q b then HostCorrection.scale n q else 0) = 1 := by
  have h := congrFun (congrFun (weightedGram_eq n q) e) e
  simpa [DeletedGram.gram, HostCorrection.scale, HostCorrection.normalizedGram_diag n q hq hn] using h

/-- The total absolute weight removed from any type is bounded by the
number of deleted edges times the original per-edge envelope. -/
theorem deleted_weight_le (hq : 3 ≤ q) (hn : q + 2 ≤ n)
    (J : Finset (Edge n)) (C : ℝ) (hC : 0 ≤ C)
    (w : HostCorrection.Block n q → ℝ) (hw : ∀ b, |w b| ≤ C * HostCorrection.scale n q) :
    (∑ b, if resources n q b ⊆ J then 0 else |w b|) ≤
      C * ((Jᶜ : Finset (Edge n)).card : ℝ) := by
  have hα : 0 ≤ HostCorrection.scale n q := by unfold HostCorrection.scale; positivity
  calc
    _ ≤ ∑ b : HostCorrection.Block n q,
        if resources n q b ⊆ J then 0 else C * HostCorrection.scale n q := by
      apply Finset.sum_le_sum
      intro b _
      split_ifs <;> first | exact le_rfl | exact hw b
    _ ≤ ∑ f : (Jᶜ : Finset (Edge n)), ∑ b : HostCorrection.Block n q,
        if (f : Edge n) ∈ resources n q b then C * HostCorrection.scale n q else 0 :=
      deleted_sum_le (resources n q) J _ (fun _ => mul_nonneg hC hα)
    _ = _ := by
      have he (f : Edge n) :
          (∑ b : HostCorrection.Block n q,
            if f ∈ resources n q b then C * HostCorrection.scale n q else 0) = C := by
        conv_rhs => rw [← mul_one C, ← scaled_incidence_sum hq hn f, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        split_ifs <;> simp
      simp only [he, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_coe]
      ring

theorem type_mass_defect (hq : 3 ≤ q) (hn : q + 2 ≤ n)
    (J : Finset (Edge n)) (C : ℝ) (hC : 0 ≤ C)
    (w : HostCorrection.Block n q → ℝ) (hw : ∀ b, |w b| ≤ C * HostCorrection.scale n q)
    (S : Finset (HostCorrection.Block n q)) :
    |(∑ b ∈ S, w b) -
      (∑ b : HostCorrection.availableBlocks n q J, if (b : HostCorrection.Block n q) ∈ S then w b else 0)|
      ≤ C * ((Jᶜ : Finset (Edge n)).card : ℝ) := by
  classical
  let v : HostCorrection.Block n q → ℝ := fun b => if b ∈ S then w b else 0
  have hα : 0 ≤ HostCorrection.scale n q := by unfold HostCorrection.scale; positivity
  have hv (b : HostCorrection.Block n q) : |v b| ≤ C * HostCorrection.scale n q := by
    dsimp only [v]
    split_ifs
    · exact hw b
    · simp only [abs_zero]
      exact mul_nonneg hC hα
  change |(∑ b ∈ S, w b) - (∑ b : HostCorrection.availableBlocks n q J, v b)| ≤ _
  rw [Finset.sum_coe_sort _ v]
  have hS : (∑ b ∈ S, w b) = ∑ b, v b := by
    have hF : univ.filter (fun b => b ∈ S) = S := filter_mem_eq_of_subset (subset_univ _)
    rw [← hF, Finset.sum_filter] <;> rfl
  rw [hS]
  simp only [HostCorrection.availableBlocks, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ b, |v b - if resources n q b ⊆ J then v b else 0| := abs_sum_le_sum_abs _ _
    _ = ∑ b, if resources n q b ⊆ J then 0 else |v b| := by
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp
    _ ≤ _ := deleted_weight_le hq hn J C hC v hv

/-- Restricting even a signed lift changes an edge load by at most the
normalised outside Gram mass times the pointwise weight bound. -/
theorem host_load_defect (hq : 3 ≤ q) (hn : q + 2 ≤ n)
    (J : Finset (Edge n)) (t C : ℝ) (hC : 0 ≤ C)
    (hdeg : ∀ v : Fin n, ∑ f : (Jᶜ : Finset (Edge n)), incidence 2 f v ≤ t)
    (w : HostCorrection.Block n q → ℝ) (hw : ∀ b, |w b| ≤ C * HostCorrection.scale n q)
    (e : J) :
    |WeightedEnergy.load (resources n q) w e -
      (HostCorrection.hostIncidence n q J *ᵥ
        (fun b : HostCorrection.availableBlocks n q J => w b)) e| ≤ C * outsideBound n q t := by
  let I := resources n q
  let α := HostCorrection.scale n q
  have hα : 0 ≤ α := by dsimp [α, HostCorrection.scale]; positivity
  have hsum :
      WeightedEnergy.load I w e -
        (HostCorrection.hostIncidence n q J *ᵥ (fun b : HostCorrection.availableBlocks n q J => w b)) e =
      ∑ b, if I b ⊆ J then 0 else if (e : Edge n) ∈ I b then w b else 0 := by
    simp only [Matrix.mulVec, dotProduct, HostCorrection.hostIncidence, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_coe_sort _ (fun b : HostCorrection.Block n q => if (e : Edge n) ∈ I b then w b else 0)]
    simp only [HostCorrection.availableBlocks, Finset.sum_filter, WeightedEnergy.load]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    change (if (e : Edge n) ∈ I b then w b else 0) -
      (if I b ⊆ J then (if (e : Edge n) ∈ I b then w b else 0) else 0) = _
    by_cases hb : I b ⊆ J <;> simp [hb]
  rw [hsum]
  calc
    _ ≤ ∑ b, |if I b ⊆ J then 0 else if (e : Edge n) ∈ I b then w b else 0| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ b, if I b ⊆ J then 0 else if (e : Edge n) ∈ I b then C * α else 0 := by
      apply Finset.sum_le_sum
      intro b _
      split_ifs <;> first | exact hw b | simp only [abs_zero, le_refl]
    _ ≤ ∑ f : (Jᶜ : Finset (Edge n)), DeletedGram.gram I (fun _ => C * α) e f :=
      deleted_row_le I J _ (fun _ => mul_nonneg hC hα) e
    _ = C * ∑ f : (Jᶜ : Finset (Edge n)), normalizedGram n q e f := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      have hG := congrFun (congrFun (weightedGram_eq n q) (e : Edge n)) (f : Edge n)
      change DeletedGram.gram I (fun _ => α) e f = _ at hG
      rw [← hG]
      simp only [DeletedGram.gram, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      split_ifs <;> simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (outside_mass_le n q hq hn _ t hdeg e (by simpa using e.property)) hC

/-- A signed lift of zero full-host load can be repaired on the surviving
cliques. Each type mass changes by at most the deleted mass plus the
total absolute load correction. -/
theorem repair_signed_column (hq : 3 ≤ q) (hn : 2 * q ^ 2 ≤ n)
    (J : Finset (Edge n)) (t C : ℝ) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hdeg : ∀ v : Fin n, ∑ f : (Jᶜ : Finset (Edge n)), incidence 2 f v ≤ t)
    (hsmall : 4 * (1 + (q.choose 2 : ℝ)) * outsideBound n q t ≤ 1 / 2)
    (w : HostCorrection.Block n q → ℝ) (hw : ∀ b, |w b| ≤ C * HostCorrection.scale n q)
    (hzero : ∀ e, WeightedEnergy.load (resources n q) w e = 0) :
    let u := C * (4 * (q : ℝ) ^ 2 * t / n)
    ∃ z : HostCorrection.availableBlocks n q J → ℝ,
      HostCorrection.hostIncidence n q J *ᵥ z = 0 ∧
      (∀ b, |z b - w b| ≤ 8 * (q.choose 2 : ℝ) * HostCorrection.scale n q * u) ∧
      ∀ S : Finset (HostCorrection.Block n q),
        |(∑ b ∈ S, w b) -
          (∑ b : HostCorrection.availableBlocks n q J, if (b : HostCorrection.Block n q) ∈ S then z b else 0)|
          ≤ C * ((Jᶜ : Finset (Edge n)).card : ℝ) + 8 * (J.card : ℝ) * u := by
  classical
  let u := C * (4 * (q : ℝ) ^ 2 * t / n)
  let W : HostCorrection.availableBlocks n q J → ℝ := fun b => w b
  let A := HostCorrection.hostIncidence n q J
  let h := A *ᵥ W
  have hnq : q + 2 ≤ n := by nlinarith
  have hn6 : 6 ≤ n := by nlinarith
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hhu (e : J) : |h e| ≤ u := by
    have hd := host_load_defect hq hnq J t C hC hdeg w hw e
    rw [hzero, zero_sub, abs_neg] at hd
    exact hd.trans (mul_le_mul_of_nonneg_left (outsideBound_le n q hq hn6 t ht) hC)
  obtain ⟨v, hv, hl1, hpoint⟩ := HostCorrection.solve_defect n q hq hn J t u hu hdeg hsmall h hhu
  refine ⟨W - v, ?_, ?_, ?_⟩
  · change A *ᵥ (W - v) = 0
    rw [Matrix.mulVec_sub, hv, sub_self]
  · intro b
    change |w b - v b - w b| ≤ _
    have he : w b - v b - w b = -v b := by ring
    rw [he, abs_neg]
    exact hpoint b
  · intro S
    let m₀ := ∑ b ∈ S, w b
    let m₁ := ∑ b : HostCorrection.availableBlocks n q J,
      if (b : HostCorrection.Block n q) ∈ S then W b else 0
    let m₂ := ∑ b : HostCorrection.availableBlocks n q J,
      if (b : HostCorrection.Block n q) ∈ S then (W - v) b else 0
    have h₁ : |m₀ - m₁| ≤ C * ((Jᶜ : Finset (Edge n)).card : ℝ) :=
      type_mass_defect hq hnq J C hC w hw S
    have h₂ : |m₁ - m₂| ≤ ∑ b, |v b| := by
      dsimp only [m₁, m₂]
      rw [← Finset.sum_sub_distrib]
      refine (abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro b _
      by_cases hb : (b : HostCorrection.Block n q) ∈ S
      · simp [hb]
      · simp [hb]
    have hJ : (∑ e : J, |h e|) ≤ (J.card : ℝ) * u := by
      calc
        _ ≤ ∑ _e : J, u := Finset.sum_le_sum (fun e _ => hhu e)
        _ = _ := by simp [nsmul_eq_mul]
    have he : m₀ - m₂ = (m₀ - m₁) + (m₁ - m₂) := by ring
    change |m₀ - m₂| ≤ _
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add h₁
      (h₂.trans (hl1.trans (by linarith [mul_le_mul_of_nonneg_left hJ (by norm_num : (0 : ℝ) ≤ 8)]))))

/-- Assemble the repaired columns, with the same type selector used in the
complete host. The entry bound directly gives the row norm required for
the simultaneous load and histogram correction. -/
theorem assemble_lifts {D : Type*} [Fintype D] [DecidableEq D]
    (hq : 3 ≤ q) (hn : 2 * q ^ 2 ≤ n)
    (J : Finset (Edge n)) (t C : ℝ) (ht : 0 ≤ t) (hC : 0 ≤ C)
    (hdeg : ∀ v : Fin n, ∑ f : (Jᶜ : Finset (Edge n)), incidence 2 f v ≤ t)
    (hsmall : 4 * (1 + (q.choose 2 : ℝ)) * outsideBound n q t ≤ 1 / 2)
    (w : D → HostCorrection.Block n q → ℝ)
    (hw : ∀ j b, |w j b| ≤ C * HostCorrection.scale n q)
    (hzero : ∀ j e, WeightedEnergy.load (resources n q) (w j) e = 0)
    (S : D → Finset (HostCorrection.Block n q))
    (hfull : ∀ i j, (∑ b ∈ S i, w j b) = (1 : Matrix D D ℝ) i j) :
    let u := C * (4 * (q : ℝ) ^ 2 * t / n)
    let H : Matrix D (HostCorrection.availableBlocks n q J) ℝ :=
      fun i b => if (b : HostCorrection.Block n q) ∈ S i then 1 else 0
    ∃ L : Matrix (HostCorrection.availableBlocks n q J) D ℝ,
      HostCorrection.hostIncidence n q J * L = 0 ∧
      (∀ i, ∑ j, |((1 : Matrix D D ℝ) - H * L) i j| ≤
        (Fintype.card D : ℝ) * (C * ((Jᶜ : Finset (Edge n)).card : ℝ) + 8 * (J.card : ℝ) * u)) ∧
      (∀ b j, |L b j - w j b| ≤ 8 * (q.choose 2 : ℝ) * HostCorrection.scale n q * u) := by
  classical
  let u := C * (4 * (q : ℝ) ^ 2 * t / n)
  let H : Matrix D (HostCorrection.availableBlocks n q J) ℝ :=
    fun i b => if (b : HostCorrection.Block n q) ∈ S i then 1 else 0
  choose z hz hpoint hmass using fun j =>
    repair_signed_column hq hn J t C ht hC hdeg hsmall (w j) (hw j) (hzero j)
  let L : Matrix (HostCorrection.availableBlocks n q J) D ℝ := fun b j => z j b
  refine ⟨L, ?_, ?_, fun b j => hpoint j b⟩
  · ext e j
    exact congrFun (hz j) e
  · intro i
    change (∑ j, |((1 : Matrix D D ℝ) - H * L) i j|) ≤
      (Fintype.card D : ℝ) * (C * ((Jᶜ : Finset (Edge n)).card : ℝ) + 8 * (J.card : ℝ) * u)
    have he (j : D) : (H * L) i j =
        ∑ b : HostCorrection.availableBlocks n q J, if (b : HostCorrection.Block n q) ∈ S i then z j b else 0 := by
      change (∑ b, H i b * L b j) = _
      simp only [H, L, ite_mul, one_mul, zero_mul]
    calc
      _ ≤ ∑ _j : D, (C * ((Jᶜ : Finset (Edge n)).card : ℝ) + 8 * (J.card : ℝ) * u) := by
        apply Finset.sum_le_sum
        intro j _
        have hm := hmass j (S i)
        rw [hfull i j] at hm
        simpa only [Matrix.sub_apply, he j] using hm
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end KqR75.PrunedWeights

#print axioms KqR75.PrunedWeights.deleted_sum_le
#print axioms KqR75.PrunedWeights.host_load_defect
#print axioms KqR75.PrunedWeights.type_mass_defect
#print axioms KqR75.PrunedWeights.repair_signed_column
#print axioms KqR75.PrunedWeights.assemble_lifts
