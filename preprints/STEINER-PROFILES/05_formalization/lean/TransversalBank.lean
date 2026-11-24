module
public import KqCore

@[expose] public section
namespace KqR75.Transversal

variable {K : Type*} [Field K]

/-- The point in the group indexed by slope s on the line with parameters (x,y). -/
def point (s : K) (p : K × K) : K := p.1 + s * p.2

theorem pair_injective (s t : K) (hst : s ≠ t) :
    Function.Injective (fun p : K × K => (point s p, point t p)) := by
  intro a b hab
  have h1 : a.1 + s * a.2 = b.1 + s * b.2 := congrArg Prod.fst hab
  have h2 : a.1 + t * a.2 = b.1 + t * b.2 := congrArg Prod.snd hab
  have hz : (t - s) * (a.2 - b.2) = 0 := by linear_combination h2 - h1
  have hy : a.2 = b.2 := sub_eq_zero.mp
    ((mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hst.symm))
  have hx : a.1 = b.1 := by rw [hy] at h1; exact add_right_cancel h1
  exact Prod.ext hx hy

theorem pair_surjective (s t : K) (hst : s ≠ t) :
    Function.Surjective (fun p : K × K => (point s p, point t p)) := by
  rintro ⟨u, v⟩
  let y := (v - u) / (t - s)
  refine ⟨(u - s * y, y), ?_⟩
  apply Prod.ext
  · dsimp [point]; ring
  · dsimp [point, y]
    field_simp [sub_ne_zero.mpr hst.symm]
    <;> ring

/-- Every pair of vertices from distinct slope groups lies in exactly one block. -/
theorem pair_bijective (s t : K) (hst : s ≠ t) :
    Function.Bijective (fun p : K × K => (point s p, point t p)) :=
  ⟨pair_injective s t hst, pair_surjective s t hst⟩

/-- Two unshifted active points force the zero line, excluding a shifted third. -/
theorem shifted_active_impossible (s t r : K) (hst : s ≠ t)
    (p : K × K) (hs : point s p = 0) (ht : point t p = 0)
    (a : K) (ha : a ≠ 0) : point r p ≠ a := by
  have hp : p = (0, 0) := pair_injective s t hst (by
    change (point s p, point t p) = (point s (0, 0), point t (0, 0))
    calc
      (point s p, point t p) = (0, 0) := Prod.ext hs ht
      _ = (point s (0, 0), point t (0, 0)) := by simp [point])
  subst p
  simpa [point] using ha.symm

end KqR75.Transversal

#print axioms KqR75.Transversal.pair_bijective
#print axioms KqR75.Transversal.shifted_active_impossible
