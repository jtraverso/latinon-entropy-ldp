module
public import PrunedWeights
public import SlotPairMargins

@[expose] public section
noncomputable section
namespace KqR75.PhysicalProfileLifts

open Finset ColouredCliques SlotProfiles SlotPairMargins CompleteJohnson SparseGram CliqueGram
open scoped Matrix

variable {C K : Type*} [Fintype C] [DecidableEq C]
  [Field K] [Fintype K] [DecidableEq K]

/-- One finite bound for the coordinate directions, fixed before
the size or colouring of the physical host is chosen. -/
theorem bounded_directions {q : ℕ} (s : Fin q → K) (hs : Function.Injective s) (ref : C) :
    ∃ G : ℝ, 0 ≤ G ∧ ∃ g : High C q ref → TypeProfile C q → ℝ,
      (∀ j v, |g j v| ≤ G) ∧
      (∀ i j : High C q ref, g j i.val = if i = j then 1 else 0) ∧
      ∀ j i₁ i₂, ∑ v, g j v * (orderedCount v i₁ i₂ : ℝ) = 0 := by
  obtain ⟨g, hg, hz⟩ := affine_coordinate_lifts (R := ℝ) s hs ref
  let G := ∑ j, ∑ v, |g j v|
  refine ⟨G, Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun v _ => abs_nonneg _)),
    g, ?_, hg, hz⟩
  intro j v
  calc
    _ ≤ ∑ v', |g j v'| := Finset.single_le_sum (fun v' _ => abs_nonneg (g j v')) (mem_univ v)
    _ ≤ G := Finset.single_le_sum (fun j' _ => Finset.sum_nonneg (fun v' _ => abs_nonneg (g j' v')))
      (mem_univ j)

/-- Build the physical zero-load matrix for the histogram correction.
The bound on its perturbation uses only the explicit deleted-degree and
deleted-edge estimates, and a coefficient bound on the fixed directions. -/
theorem host_columns {n q : ℕ} (hq : 3 ≤ q) (hn : 2 * q ^ 2 ≤ n)
    (colour : Fin n → C) (ref : C) (d : ℕ) (s G : ℝ)
    (hs : 0 < s) (hG : 0 ≤ G) (hclasses : ∀ i, d + q ≤ profile colour univ i)
    (hdn : s * (n : ℝ) ≤ d)
    (g : High C q ref → TypeProfile C q → ℝ) (hg : ∀ j v, |g j v| ≤ G)
    (hcoord : ∀ i j : High C q ref, g j i.val = if i = j then 1 else 0)
    (hmargin : ∀ j i₁ i₂, ∑ v, g j v * (orderedCount v i₁ i₂ : ℝ) = 0)
    (J : Finset (Edge n)) (t : ℝ) (ht : 0 ≤ t)
    (hdeg : ∀ v : Fin n, ∑ f : (Jᶜ : Finset (Edge n)), incidence 2 f v ≤ t)
    (hsmall : 4 * (1 + (q.choose 2 : ℝ)) * outsideBound n q t ≤ 1 / 2) :
    let B := G * (q.factorial : ℝ) ^ Fintype.card C / s ^ q
    let Q := B / (n : ℝ) ^ 2
    let u := Q * (4 * (q : ℝ) ^ 2 * t / n)
    let H : Matrix (High C q ref) (HostCorrection.availableBlocks n q J) ℝ :=
      fun i b => if cliqueType colour (b : HostCorrection.Block n q) = i.val then 1 else 0
    ∃ L : Matrix (HostCorrection.availableBlocks n q J) (High C q ref) ℝ,
      HostCorrection.hostIncidence n q J * L = 0 ∧
      (∀ i, ∑ j, |((1 : Matrix (High C q ref) (High C q ref) ℝ) - H * L) i j| ≤
        (Fintype.card (High C q ref) : ℝ) * (Q * ((Jᶜ : Finset (Edge n)).card : ℝ) + 8 * (J.card : ℝ) * u)) ∧
      ∀ b j, |L b j - ProfileWeights.weight (cliqueType colour) (g j) b| ≤
        8 * (q.choose 2 : ℝ) * HostCorrection.scale n q * u := by
  classical
  let A := G / (n : ℝ) ^ 2
  let Q := (G * (q.factorial : ℝ) ^ Fintype.card C / s ^ q) / (n : ℝ) ^ 2
  let w := fun j => ProfileWeights.weight (cliqueType colour) (g j)
  have hnq : q ≤ n := by nlinarith
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hq' : 2 ≤ q := by omega
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hcls i : q ≤ profile colour univ i := (Nat.le_add_left q d).trans (hclasses i)
  have hcoef : A * (q.factorial : ℝ) ^ Fintype.card C / s ^ q = Q := by
    dsimp only [A, Q]
    ring
  have hw (j : High C q ref) (b : HostCorrection.Block n q) :
      |w j b| ≤ Q * HostCorrection.scale n q := by
    have hm (v : TypeProfile C q) : |g j v| ≤ A * (n : ℝ) ^ 2 := by
      have he : A * (n : ℝ) ^ 2 = G := by
        dsimp only [A]
        field_simp [hn0.ne']
      rw [he]
      exact hg j v
    have he := seed_weight_abs_le colour hq' hnq d s A hs hA hclasses hdn (g j) hm b
    rw [hcoef] at he
    exact he
  have hz (j : High C q ref) (e : Edge n) :
      WeightedEnergy.load (resources n q) (w j) e = 0 :=
    seed_load_zero colour hcls (g j) (physical_margin_zero colour (g j) (hmargin j)) e
  have hhist (i j : High C q ref) :
      (∑ b ∈ ProfileWeights.fibre (cliqueType colour) i.val, w j b) =
        (1 : Matrix (High C q ref) (High C q ref) ℝ) i j := by
    change (∑ b ∈ ProfileWeights.fibre (cliqueType colour) i.val,
      ProfileWeights.weight (cliqueType colour) (g j) b) = _
    rw [seed_mass colour hcls (g j), hcoord, Matrix.one_apply]
  obtain ⟨L, hl, hrow, hb⟩ := PrunedWeights.assemble_lifts hq hn J t Q ht hQ hdeg hsmall
    w hw hz (fun i => ProfileWeights.fibre (cliqueType colour) i.val) hhist
  have hH (i : High C q ref) (b : HostCorrection.availableBlocks n q J) :
      ((b : HostCorrection.Block n q) ∈ ProfileWeights.fibre (cliqueType colour) i.val) ↔
        cliqueType colour (b : HostCorrection.Block n q) = i.val := by simp [ProfileWeights.fibre]
  refine ⟨L, hl, ?_, hb⟩
  simpa only [hH] using hrow

end KqR75.PhysicalProfileLifts

#print axioms KqR75.PhysicalProfileLifts.host_columns
