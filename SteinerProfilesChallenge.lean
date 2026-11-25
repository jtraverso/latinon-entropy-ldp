module
public import Mathlib

/-! # Steiner designs with prescribed color profiles
Statements of the uniform exact-profile count, its upper bound including empty fibers, and profile large deviations. Definitions follow the preprint 1.0 Lean sources. -/

@[expose] public section
noncomputable section

namespace KqR75.CompleteJohnson
open Finset

/-- An unordered pair of distinct vertices. -/
abbrev Edge (n : ℕ) := ((univ : Finset (Fin n)).powersetCard 2)
end KqR75.CompleteJohnson

namespace KqR75.ColouredCliques
open Finset
variable {V C : Type*} [DecidableEq V] [Fintype C] [DecidableEq C]

/-- Points of a finite set having the chosen color. -/
def part (colour : V → C) (s : Finset V) (i : C) : Finset V :=
  s.filter fun v => colour v = i

/-- Number of points of a given color in a finite set. -/
def profile (colour : V → C) (s : Finset V) (i : C) : ℕ := (part colour s i).card

/-- Summing the color counts recovers the size of the set. -/
theorem sum_profile (colour : V → C) (s : Finset V) :
    ∑ i, profile colour s i = s.card := by
  simpa [profile, part] using sum_card_fiberwise_eq_card_filter s (univ : Finset C) colour

/-- Number of subsets with a prescribed color histogram. -/
def cliques (colour : V → C) (s : Finset V) (t : C → ℕ) : ℕ :=
  ∏ i, (profile colour s i).choose (t i)

/-- A block of q vertices among n labeled points. -/
abbrev Clique (n q : ℕ) := ↥((univ : Finset (Fin n)).powersetCard q)

/-- Color multiplicities of a block of size q. -/
abbrev TypeProfile (C : Type*) [Fintype C] (q : ℕ) :=
  {t : C → Fin (q + 1) // (∑ i, (t i : ℕ)) = q}

/-- The color multiplicities of a block. -/
def cliqueType {n q : ℕ} (colour : Fin n → C) (b : Clique n q) : TypeProfile C q := by
  refine ⟨fun i => ⟨profile colour b i, ?_⟩, ?_⟩
  · have hb := (mem_powersetCard.mp b.property).2
    have hi := card_le_card (filter_subset (fun v => colour v = i) (b : Finset (Fin n)))
    change profile colour b i ≤ (b : Finset (Fin n)).card at hi
    omega
  · exact (sum_profile colour b).trans (mem_powersetCard.mp b.property).2

/-- Weighted pair margin for an edge. -/
def pairMargin {n q : ℕ} (colour : Fin n → C) (m : TypeProfile C q → ℝ)
    (e : CompleteJohnson.Edge n) : ℝ :=
  ∑ t, ((∏ i, (t.val i : ℕ).choose (profile colour (e : Finset (Fin n)) i) : ℕ) : ℝ) * m t
end KqR75.ColouredCliques

namespace KqR75.ProfileWeights
open Finset
variable {E B T : Type*} [Fintype E] [DecidableEq E] [Fintype B] [DecidableEq B]
  [Fintype T] [DecidableEq T]

/-- All blocks of a given type. -/
def fibre (typeOf : B → T) (t : T) : Finset B := univ.filter fun b => typeOf b = t
end KqR75.ProfileWeights

namespace KqR75.SparseGram
open Finset CompleteJohnson
variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]

/-- Pairs covered by a block. -/
def resources (n q : ℕ) (b : ((univ : Finset (Fin n)).powersetCard q)) : Finset (Edge n) :=
  univ.filter fun e => (e : Finset (Fin n)) ⊆ (b : Finset (Fin n))
end KqR75.SparseGram

namespace KqR75.PhysicalBank
open Finset ColouredCliques CompleteJohnson SparseGram
variable {C K : Type*} [Fintype C] [DecidableEq C]
  [Field K] [Fintype K] [DecidableEq K]

/-- Edge multiplicity in a family of physical cliques. -/
def edgeMultiplicity {n q : ℕ} (P : Finset (Clique n q)) (e : Edge n) : ℕ :=
  (P.filter (fun b => e ∈ resources n q b)).card
end KqR75.PhysicalBank

namespace KqR75.BankCapacity
open Finset ColouredCliques
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The exact type histogram of a finite family of physical cliques. -/
def integerHistogram {n q : ℕ} (colour : Fin n → C) (P : Finset (Clique n q))
    (t : TypeProfile C q) : ℤ :=
  ((P.filter (fun b => cliqueType colour b = t)).card : ℤ)
end KqR75.BankCapacity

namespace KqR75.PhysicalCompletion
open Finset ColouredCliques CompleteJohnson PhysicalBank

/-- Exact physical multiplicities on a set of edges. -/
def packs {n q : ℕ} (P : Finset (Clique n q)) (A : Finset (Edge n)) : Prop :=
  ∀ e : Edge n, edgeMultiplicity P e = if e ∈ A then 1 else 0
end KqR75.PhysicalCompletion

namespace KqR75.PhysicalCompletion
open Finset CompleteJohnson ColouredCliques
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Labelled clique decompositions with the specified integer counts
of each block type, in the same edge universe as the greedy process. -/
noncomputable def designFibre {n q : ℕ} (colour : Fin n → C) (m : TypeProfile C q → ℤ) :
    Finset (Finset (Clique n q)) := by
  classical
  exact univ.filter fun P => packs P univ ∧
    ∀ t, BankCapacity.integerHistogram colour P t = m t
end KqR75.PhysicalCompletion

namespace KqR75.SlotPairMargins
open Finset ColouredCliques
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Color multiplicity of a point color in the pair of prescribed colors. -/
def demand (i j c : C) : ℕ := (if i = c then 1 else 0) + (if j = c then 1 else 0)

/-- Number of ordered, distinct slots whose colours are i and j. The
diagonal is twice the number of unordered monochromatic pairs. -/
def orderedCount {q : ℕ} (t : TypeProfile C q) (i j : C) : ℕ :=
  (t.val i : ℕ) * ((t.val j : ℕ) - if i = j then 1 else 0)
end KqR75.SlotPairMargins

namespace KqR75.PhysicalCompletion
open Finset ColouredCliques SlotPairMargins
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The matrix equation on two-colour multisets. The component indexed by
`i, j` counts pairs of that type in the requested block histogram. -/
def ExactPairMargins {n q : ℕ} (colour : Fin n → C) (m : TypeProfile C q → ℤ) : Prop :=
  ∀ i j : C, (∑ t : TypeProfile C q,
    ((∏ c, (t.val c : ℕ).choose (demand i j c) : ℕ) : ℤ) * m t) =
    (cliques colour univ (demand i j) : ℤ)
end KqR75.PhysicalCompletion

namespace KqR75.GreedyScales
open Finset

/-- Exponent in the uniform lower counting error. -/
def criticalExponent (q : ℕ) : ℝ := 1 / ((4 * (q.choose 2 : ℝ) - 1) * (2 * (q : ℝ) - 1) + 2)
end KqR75.GreedyScales

namespace KqR75.ProfileLDP
open Finset Filter Topology

/-- Relative entropy `D(Q‖P) = Σ Q log(Q/P)`, with `0 log(0/P) = 0`. -/
noncomputable def KL {ι : Type*} [Fintype ι] (Q P : ι → ℝ) : ℝ :=
  ∑ i, Q i * Real.log (Q i / P i)
end KqR75.ProfileLDP

namespace KqR75.ProfileLDP
open Finset Filter Topology ColouredCliques CompleteJohnson
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The number of blocks in a decomposition when the order is admissible. -/
def blockMass (n q : ℕ) : ℝ :=
  (Fintype.card (Edge n) : ℝ) / (q.choose 2 : ℝ)

/-- The type law of q independent colours. -/
def multinomialTypeLaw {q : ℕ} (p : C → ℝ) (t : TypeProfile C q) : ℝ :=
  (q.factorial : ℝ) * ∏ c, p c ^ (t.val c : ℕ) / ((t.val c : ℕ).factorial : ℝ)
end KqR75.ProfileLDP

namespace KqR75.ProfileLDP
open Finset Filter Topology ColouredCliques CompleteJohnson PhysicalCompletion
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Pair-count and vertex-degree divisibility conditions for Steiner designs. -/
def admissible (q n : ℕ) : Prop :=
  q.choose 2 ∣ n.choose 2 ∧ q - 1 ∣ n - 1

/-- All designs covering each pair exactly once. -/
def designs (q n : ℕ) : Finset (Finset (Clique n q)) := by
  classical
  exact univ.filter fun D => packs D univ

/-- A type quota divided by the block count. -/
def normalizedQuota {q : ℕ} (n : ℕ) (m : TypeProfile C q → ℤ) (t : TypeProfile C q) : ℝ :=
  (m t : ℝ) / blockMass n q

/-- Empirical type distribution of a design. -/
def profileOf {n q : ℕ} (colour : Fin n → C) (D : Finset (Clique n q)) :
    TypeProfile C q → ℝ :=
  normalizedQuota n (BankCapacity.integerHistogram colour D)

/-- Number of designs whose empirical profile belongs to the given event. -/
def profileCount {n q : ℕ} (colour : Fin n → C) (A : Set (TypeProfile C q → ℝ)) : ℝ := by
  classical
  exact (((designs q n).filter fun D => profileOf colour D ∈ A).card : ℝ)
end KqR75.ProfileLDP

namespace KqR75.ProfileLDP
open Finset Filter Topology ColouredCliques PhysicalCompletion
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Filter of sufficiently large admissible orders. -/
abbrev admissibleOrders (q : ℕ) : Filter ℕ := atTop ⊓ 𝓟 {n | admissible q n}
end KqR75.ProfileLDP

namespace KqR75.ProfileLDP
open Finset Filter Topology ColouredCliques CompleteJohnson PhysicalCompletion SlotPairMargins
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- The pair-margin matrix with ordered pairs, including twice the same-colour margin. -/
def orderedMargins (q : ℕ) : (TypeProfile C q → ℝ) →ₗ[ℝ] (C → C → ℝ) where
  toFun Q i j := ∑ t, Q t * (orderedCount t i j : ℝ)
  map_add' X Y := by
    funext i j
    simp [add_mul, sum_add_distrib]
  map_smul' a X := by
    funext i j
    simp [mul_assoc, Finset.mul_sum]

/-- Probability profiles with the same pair margins as the limiting reference law. -/
def feasible {q : ℕ} (P : TypeProfile C q → ℝ) : Set (TypeProfile C q → ℝ) :=
  {Q | Q ∈ Set.Icc 0 1 ∧ (∑ t, Q t) = 1 ∧ orderedMargins q Q = orderedMargins q P}

/-- Corollary 10.1. Upper and lower probability bounds and compact rate sublevels. -/
theorem designProfileLDP_probability {q : ℕ} (hq : 3 ≤ q) [Nonempty C]
    (colour : (n : ℕ) → Fin n → C) (p : C → ℝ) (hp : ∀ c, 0 < p c)
    (hcolour : ∀ c, Tendsto (fun n => (profile (colour n) univ c : ℝ) / n)
      (admissibleOrders q) (𝓝 (p c))) :
    let P : TypeProfile C q → ℝ := multinomialTypeLaw p
    (∀ F : Set (TypeProfile C q → ℝ), IsClosed F → ∀ r : ℝ,
      (∀ Q ∈ F, Q ∈ feasible P → r < KL Q P) →
      ∀ᶠ n in admissibleOrders q, profileCount (colour n) F / (designs q n).card ≤
        Real.exp (-(blockMass n q * r))) ∧
    (∀ G : Set (TypeProfile C q → ℝ), IsOpen G → ∀ Q ∈ G, Q ∈ feasible P → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in admissibleOrders q, Real.exp (-(blockMass n q * (KL Q P + ε))) ≤
        profileCount (colour n) G / (designs q n).card) ∧
    ∀ a : ℝ, IsCompact {Q | Q ∈ feasible P ∧ KL Q P ≤ a} := by sorry
end KqR75.ProfileLDP

namespace KqR75.UpperCounting
open Filter Finset ColouredCliques CompleteJohnson PhysicalCompletion
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Theorem 1.1, upper bound. The multiplicative estimate also covers empty fibers. -/
theorem eventually_card_designFibre_upper_entropy (q : ℕ) (hq : 3 ≤ q)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ err : ℝ, 0 ≤ err ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (colour : Fin n → C) (m : TypeProfile C q → ℤ),
      (∀ c, ρ * (n : ℝ) ≤ (profile colour univ c : ℝ)) →
      (∀ e : Edge n, pairMargin colour (fun t => (m t : ℝ)) e =
        (cliques colour univ (profile colour (e : Finset (Fin n))) : ℝ)) →
      let r := q.choose 2
      let s : ℝ := (r - 1 : ℕ)
      let B := (Fintype.card (Edge n) : ℝ) / (r : ℝ)
      let N := fun t : TypeProfile C q => ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ)
      let K := ∑ t, ((m t : ℝ) / B) * Real.log (((m t : ℝ) / B) / (N t / (n.choose q : ℝ)))
      ((designFibre colour m).card : ℝ) ≤ Real.exp (
        B * (Real.log ((n - 2).choose (q - 2)) - s - K) +
        err * (n : ℝ) ^ (2 - 1 / s)) := by sorry
end KqR75.UpperCounting

namespace KqR75.PhysicalCompletion
open Filter Finset ColouredCliques CompleteJohnson
variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Theorem 1.1. Uniform bilateral enumeration for fixed positive interior quotas. -/
theorem eventually_designFibre_bilateral (q : ℕ) (hq : 3 ≤ q) (ρ κ : ℝ)
    (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ err : ℝ, 0 ≤ err ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (colour : Fin n → C) (m : TypeProfile C q → ℤ),
      (∀ c, ρ * (n : ℝ) ≤ (profile colour univ c : ℝ)) →
      ExactPairMargins colour m →
      (∀ t, κ * ((Fintype.card (Edge n) : ℝ) / (q.choose 2 : ℝ)) ≤ (m t : ℝ)) →
      q.choose 2 ∣ n.choose 2 → q - 1 ∣ n - 1 →
      let r := q.choose 2
      let z := GreedyScales.criticalExponent q
      let s : ℝ := (r - 1 : ℕ)
      let B := (Fintype.card (Edge n) : ℝ) / (r : ℝ)
      let N := fun t : TypeProfile C q => ((ProfileWeights.fibre (cliqueType colour) t).card : ℝ)
      let K := ∑ t, ((m t : ℝ) / B) * Real.log (((m t : ℝ) / B) / (N t / (n.choose q : ℝ)))
      let main := B * (Real.log ((n - 2).choose (q - 2)) - s - K)
      0 < (designFibre colour m).card ∧
        main - err * ((n : ℝ) ^ (2 - z) * Real.log n) ≤
          Real.log ((designFibre colour m).card : ℝ) ∧
        Real.log ((designFibre colour m).card : ℝ) ≤
          main + err * (n : ℝ) ^ (2 - 1 / s) := by sorry
end KqR75.PhysicalCompletion

