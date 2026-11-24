module
public import KqCore

@[expose] public section
noncomputable section
namespace KqR75.ScalarDrift

/-- A variance form of Young's inequality, with an explicit error constant. -/
theorem young_variance (a b c t : ℝ) (ha : 0 < a) (hvar : t ^ 2 ≤ a * b) :
    c * |t| ≤ b / 4 + a * c ^ 2 := by
  have hs := sq_nonneg (|t| - 2 * a * c)
  have hh : 0 ≤ a * (b / 4 + a * c ^ 2 - c * |t|) := by
    nlinarith only [hs, hvar, sq_abs t]
  by_contra hn
  have hneg : b / 4 + a * c ^ 2 - c * |t| < 0 := by linarith only [hn]
  have hp := mul_neg_of_pos_of_neg ha hneg
  linarith only [hh, hp]

/-- The multiple-intersection error consumes only 3/16 of the energy slack. -/
theorem overlap_bound (r m k Z γ X L : ℝ) (hr : 0 < r) (hm : 0 < m) (hk : 0 < k)
    (hZ : m * k / 2 ≤ Z) (hγ : 0 ≤ γ) (hsmall : 64 * γ ≤ k)
    (hX : 0 ≤ X) (hL : 0 ≤ L) (hvar : L ^ 2 ≤ r * m * X) :
    2 * γ * (X + k * L) / Z ≤ 3 * X / (16 * m) + 32 * r * γ ^ 2 := by
  have hden : 0 < m * k / 2 := by positivity
  have hnum : 0 ≤ 2 * γ * (X + k * L) := by positivity
  have hratio : 4 * γ / k ≤ 1 / 16 := (div_le_iff₀ hk).mpr (by linarith only [hsmall])
  have hfirst : (4 * γ / k) * (X / m) ≤ X / (16 * m) := by
    have h := mul_le_mul_of_nonneg_right hratio (div_nonneg hX hm.le)
    convert h using 1 <;> field_simp [hm.ne', hk.ne'] <;> ring
  have hy := young_variance (r * m) X (8 * γ) L (mul_pos hr hm) hvar
  rw [abs_of_nonneg hL] at hy
  have hsecond : 4 * γ * L / m ≤ X / (8 * m) + 32 * r * γ ^ 2 := by
    apply (div_le_iff₀ hm).mpr
    have he : (X / (8 * m) + 32 * r * γ ^ 2) * m = X / 8 + 32 * r * m * γ ^ 2 := by
      field_simp [hm.ne']
      <;> ring
    rw [he]
    nlinarith only [hy]
  calc
    _ ≤ 2 * γ * (X + k * L) / (m * k / 2) := div_le_div_of_nonneg_left hnum hden hZ
    _ = (4 * γ / k) * (X / m) + 4 * γ * L / m := by
      field_simp [hm.ne', hk.ne']
      <;> ring
    _ ≤ X / (16 * m) + (X / (8 * m) + 32 * r * γ ^ 2) := add_le_add hfirst hsecond
    _ = _ := by field_simp [hm.ne'] <;> ring

/-- The leading signed-block term leaves at least one half unit of slack. -/
theorem leading_bound (r m k Z X : ℝ) (hm : 0 < m) (hZ : 0 < Z) (hX : 0 ≤ X)
    (hnear : (2 * r - 1) * k * m ≤ (2 * r - 1 / 2) * Z) :
    (2 * r - 1) * k * X / Z ≤ (2 * r - 1 / 2) * X / m := by
  have hh : (2 * r - 1) * k / Z ≤ (2 * r - 1 / 2) / m :=
    (div_le_div_iff₀ hZ hm).mpr hnear
  have hs := mul_le_mul_of_nonneg_right hh hX
  convert hs using 1 <;> ring

/-- The uncancelled profile shift costs at most one quarter unit of slack. -/
theorem temporal_bound (r m k Z X s C δ η : ℝ) (hr : 1 ≤ r) (hm : 0 < m)
    (hk : 0 < k) (hk1 : k ≤ 1) (hZ : m * k / 2 ≤ Z) (hC : 0 ≤ C)
    (hδ : δ ≤ C * k / m ^ 2) (hη0 : 0 ≤ η) (hη : η ≤ (r - 1) * k / m)
    (hvar : s ^ 2 ≤ r * m * X) :
    2 * |s| * δ + 2 * η * k * |s| / Z ≤
      X / (4 * m) + r * (2 * C + 4 * (r - 1)) ^ 2 / m ^ 2 := by
  have hr0 : 0 < r := by linarith
  have hden : 0 < m * k / 2 := by positivity
  have hsecond : 2 * η * k * |s| / Z ≤ 4 * (r - 1) * k * |s| / m ^ 2 := by
    calc
      _ ≤ 2 * η * k * |s| / (m * k / 2) :=
        div_le_div_of_nonneg_left (by positivity) hden hZ
      _ = 4 * η * |s| / m := by field_simp [hm.ne', hk.ne'] <;> ring
      _ ≤ 4 * ((r - 1) * k / m) * |s| / m := by
        apply div_le_div_of_nonneg_right _ hm.le
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hη (by norm_num)) (abs_nonneg s)
      _ = _ := by field_simp [hm.ne'] <;> ring
  have hc : 0 ≤ 2 * C + 4 * (r - 1) := by linarith
  have hprod : (2 * C + 4 * (r - 1)) * k * |s| ≤ (2 * C + 4 * (r - 1)) * |s| := by
    have hh := mul_le_mul_of_nonneg_right hk1 (mul_nonneg hc (abs_nonneg s))
    nlinarith only [hh]
  have hy := young_variance r (m * X) (2 * C + 4 * (r - 1)) s hr0 (by simpa only [mul_assoc] using hvar)
  calc
    _ ≤ 2 * |s| * (C * k / m ^ 2) + 4 * (r - 1) * k * |s| / m ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hδ (by positivity)) hsecond
    _ = (2 * C + 4 * (r - 1)) * k * |s| / m ^ 2 := by ring
    _ ≤ (2 * C + 4 * (r - 1)) * |s| / m ^ 2 :=
      div_le_div_of_nonneg_right hprod (sq_nonneg m)
    _ ≤ (m * X / 4 + r * (2 * C + 4 * (r - 1)) ^ 2) / m ^ 2 :=
      div_le_div_of_nonneg_right hy (sq_nonneg m)
    _ = _ := by field_simp [hm.ne'] <;> ring

theorem eta_square_bound (r m k η : ℝ) (hr : 1 ≤ r) (hm : 1 ≤ m) (hk1 : k ≤ 1)
    (hη0 : 0 ≤ η) (hη : η ≤ (r - 1) * k / m) :
    r * η ^ 2 * (m - 1) ≤ r * (r - 1) ^ 2 / m := by
  have hm0 : 0 < m := by linarith
  have hr0 : 0 ≤ r := by linarith
  have hr1 : 0 ≤ r - 1 := by linarith
  have htop : η ≤ (r - 1) / m := hη.trans
    (div_le_div_of_nonneg_right (by nlinarith only [mul_nonneg hr1 (sub_nonneg.mpr hk1)]) hm0.le)
  have hright : 0 ≤ (r - 1) / m := div_nonneg hr1 hm0.le
  have hsq : η ^ 2 ≤ ((r - 1) / m) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr htop) (add_nonneg hη0 hright)]
  calc
    _ ≤ r * η ^ 2 * m := mul_le_mul_of_nonneg_left (show m - 1 ≤ m by linarith) (by positivity)
    _ ≤ r * ((r - 1) / m) ^ 2 * m := by
      have hh := mul_le_mul_of_nonneg_left hsq (mul_nonneg hr0 hm0.le)
      nlinarith only [hh]
    _ = _ := by field_simp [hm0.ne'] <;> ring

theorem temporal_identity (r m k Z X s η : ℝ) (hr : 0 < r) (hm : 0 < m) (hZ : 0 < Z)
    (hmass : s = r * (Z - m * k)) :
    -2 * (r - 1) * k * (X + k * s) / Z + 2 * η * (s - (X + k * s) / Z) =
      2 * s * (η - (r - 1) * k / m) +
        2 * (r - 1) * k * (s ^ 2 / (r * m) - X) / Z - 2 * η * (X + k * s) / Z := by
  let T := -2 * (r - 1) * k * (X + k * s) / Z + 2 * η * (s - (X + k * s) / Z)
  let U := 2 * s * (η - (r - 1) * k / m) +
    2 * (r - 1) * k * (s ^ 2 / (r * m) - X) / Z - 2 * η * (X + k * s) / Z
  have hn : (T - U) * (r * m * Z) = 2 * k * s * (r - 1) * (-k * m * r + r * Z - s) := by
    dsimp only [T, U]
    field_simp [hr.ne', hm.ne', hZ.ne']
    <;> ring
  have he : -k * m * r + r * Z - s = 0 := by nlinarith only [hmass]
  rw [he, mul_zero] at hn
  have hp : r * m * Z ≠ 0 := by positivity
  exact sub_eq_zero.mp ((mul_eq_zero.mp hn).resolve_right hp)

/-- Small total energy gives both denominator guards used by the drift bound. -/
theorem regularity (r m k Z X s : ℝ) (hr : 1 ≤ r) (hm : 0 < m) (hk : 0 < k)
    (hmass : s = r * (Z - m * k)) (hvar : s ^ 2 ≤ r * m * X)
    (hsmall : 16 * r * X ≤ m * k ^ 2) :
    m * k / 2 ≤ Z ∧ (2 * r - 1) * k * m ≤ (2 * r - 1 / 2) * Z := by
  have hr0 : 0 < r := by linarith
  have hmk : 0 < m * k := mul_pos hm hk
  have hsq : 16 * s ^ 2 ≤ m ^ 2 * k ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hsmall hm.le
    nlinarith only [hh, hvar]
  have habs : 4 * |s| ≤ m * k := by
    by_contra hn
    have hdiff : 0 < 4 * |s| - m * k := by linarith only [hn]
    have hsum : 0 < 4 * |s| + m * k := by positivity
    have hp := mul_pos hdiff hsum
    nlinarith only [hsq, hp, sq_abs s]
  have hlower : m * k * (r - 1 / 4) ≤ r * Z := by
    nlinarith only [hmass, habs, neg_le_abs s]
  constructor
  · have hh : m * k / 4 ≤ r * (Z - m * k / 2) := by
      have hp := mul_nonneg (show 0 ≤ r - 1 by linarith) hmk.le
      nlinarith only [hlower, hp]
    by_contra hn
    have hneg : Z - m * k / 2 < 0 := by linarith only [hn]
    have hp := mul_neg_of_pos_of_neg hr0 hneg
    linarith only [hh, hp, hmk]
  · have hh := mul_nonneg (show 0 ≤ 2 * r - 1 / 2 by linarith)
      (sub_nonneg.mpr hlower)
    have hg : m * k / 8 ≤ r * ((2 * r - 1 / 2) * Z - (2 * r - 1) * k * m) := by
      nlinarith only [hh]
    by_contra hn
    have hneg : (2 * r - 1 / 2) * Z - (2 * r - 1) * k * m < 0 := by linarith only [hn]
    have hp := mul_neg_of_pos_of_neg hr0 hneg
    linarith only [hg, hp, hmk]

theorem temporal_upper (r m k Z X s η : ℝ) (hr : 1 ≤ r) (hm : 0 < m)
    (hk : 0 < k) (hZ : 0 < Z) (hX : 0 ≤ X) (hη : 0 ≤ η)
    (hδ : 0 ≤ (r - 1) * k / m - η) (hmass : s = r * (Z - m * k))
    (hvar : s ^ 2 ≤ r * m * X) :
    -2 * (r - 1) * k * (X + k * s) / Z + 2 * η * (s - (X + k * s) / Z) ≤
      2 * |s| * ((r - 1) * k / m - η) + 2 * η * k * |s| / Z := by
  have hr0 : 0 < r := by linarith
  rw [temporal_identity r m k Z X s η hr0 hm hZ hmass]
  have hr1 : 0 ≤ r - 1 := by linarith
  have hv : s ^ 2 / (r * m) ≤ X :=
    (div_le_iff₀ (mul_pos hr0 hm)).mpr (by nlinarith only [hvar])
  have hmiddle : 2 * (r - 1) * k * (s ^ 2 / (r * m) - X) / Z ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hZ.le
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hv)
  have hfirst : 2 * s * (η - (r - 1) * k / m) ≤ 2 * |s| * ((r - 1) * k / m - η) := by
    have hh := mul_le_mul_of_nonneg_right (neg_le_abs s) (show 0 ≤ 2 * ((r - 1) * k / m - η) by linarith)
    nlinarith only [hh]
  have hlast : -(2 * η * (X + k * s) / Z) ≤ 2 * η * k * |s| / Z := by
    rw [← neg_div]
    apply div_le_div_of_nonneg_right _ hZ.le
    have hh := mul_le_mul_of_nonneg_left (neg_le_abs s)
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hη) hk.le)
    nlinarith only [hh, mul_nonneg hη hX]
  linarith only [hfirst, hmiddle, hlast]

/-- Closing the explicit slack budget. This is a scalar lemma: the physical
mean identity and its geometric error bounds supply its hypotheses. -/
theorem close_budget (r m k Z γ X L s C δ η W D : ℝ)
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hk : 0 < k) (hk1 : k ≤ 1)
    (hZ : m * k / 2 ≤ Z) (hnear : (2 * r - 1) * k * m ≤ (2 * r - 1 / 2) * Z)
    (hγ : 0 ≤ γ) (hsmall : 64 * γ ≤ k) (hX : 0 ≤ X) (hL : 0 ≤ L)
    (hvarL : L ^ 2 ≤ r * m * X) (hvarS : s ^ 2 ≤ r * m * X)
    (hC : 0 ≤ C) (hδ : δ ≤ C * k / m ^ 2)
    (hη0 : 0 ≤ η) (hη : η ≤ (r - 1) * k / m)
    (hraw : D ≤ (2 * r - 1) * k * X / Z + 2 * γ * (X + k * L) / Z +
      (2 * |s| * δ + 2 * η * k * |s| / Z) + W + r * η ^ 2 * (m - 1)) :
    D ≤ 2 * r * X / m + 32 * r * γ ^ 2 + r * (2 * C + 4 * (r - 1)) ^ 2 / m ^ 2 +
      r * (r - 1) ^ 2 / m + W := by
  have hr0 : 0 < r := by linarith
  have hm0 : 0 < m := by linarith
  have hZ0 : 0 < Z := lt_of_lt_of_le (by positivity : 0 < m * k / 2) hZ
  have h1 := leading_bound r m k Z X hm0 hZ0 hX hnear
  have h2 := overlap_bound r m k Z γ X L hr0 hm0 hk hZ hγ hsmall hX hL hvarL
  have h3 := temporal_bound r m k Z X s C δ η hr hm0 hk hk1 hZ hC hδ hη0 hη hvarS
  have h4 := eta_square_bound r m k η hr hm hk1 hη0 hη
  have hs := hraw.trans (add_le_add
    (add_le_add (add_le_add (add_le_add h1 h2) h3) le_rfl) h4)
  have he : (2 * r - 1 / 2) * X / m + (3 * X / (16 * m) + 32 * r * γ ^ 2) +
      (X / (4 * m) + r * (2 * C + 4 * (r - 1)) ^ 2 / m ^ 2) + W +
      r * (r - 1) ^ 2 / m =
      2 * r * X / m + 32 * r * γ ^ 2 + r * (2 * C + 4 * (r - 1)) ^ 2 / m ^ 2 +
        r * (r - 1) ^ 2 / m + W - X / (16 * m) := by
    field_simp [hm0.ne']
    <;> ring
  rw [he] at hs
  have hn : 0 ≤ X / (16 * m) := div_nonneg hX (by positivity)
  linarith only [hs, hn]

theorem noise_rate (r C b β m n : ℝ) (hr : 0 ≤ r) (hb : 0 ≤ b) (hβ0 : 0 ≤ β)
    (hn : 1 ≤ n) (hm : n ≤ m) (hβ : β ≤ b / n) :
    32 * r * (r ^ 2 * β) ^ 2 + r * C ^ 2 / m ^ 2 + r * (r - 1) ^ 2 / m + r ^ 3 * β ≤
      (32 * r ^ 5 * b ^ 2 + r * C ^ 2 + r * (r - 1) ^ 2 + r ^ 3 * b) / n := by
  have hn0 : 0 < n := by linarith
  have hm1 : 1 ≤ m := hn.trans hm
  have hm0 : 0 < m := by linarith
  have hn2 : n ≤ n ^ 2 := by nlinarith only [hn]
  have hm2 : n ≤ m ^ 2 := by nlinarith only [hm, hm1]
  have hinvN : 1 / n ^ 2 ≤ 1 / n := div_le_div_of_nonneg_left (by norm_num) hn0 hn2
  have hinvM : 1 / m ≤ 1 / n := div_le_div_of_nonneg_left (by norm_num) hn0 hm
  have hinvM2 : 1 / m ^ 2 ≤ 1 / n := div_le_div_of_nonneg_left (by norm_num) hn0 hm2
  have hbsq : β ^ 2 ≤ (b / n) ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hβ) (add_nonneg (div_nonneg hb hn0.le) hβ0)
    nlinarith only [hh]
  have hβsq : β ^ 2 ≤ b ^ 2 / n := by
    calc
      _ ≤ (b / n) ^ 2 := hbsq
      _ = b ^ 2 * (1 / n ^ 2) := by field_simp [hn0.ne'] <;> ring
      _ ≤ b ^ 2 * (1 / n) := mul_le_mul_of_nonneg_left hinvN (sq_nonneg b)
      _ = _ := by ring
  have h1 := mul_le_mul_of_nonneg_left hβsq (show 0 ≤ 32 * r ^ 5 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hinvM2 (show 0 ≤ r * C ^ 2 by positivity)
  have h3 := mul_le_mul_of_nonneg_left hinvM (show 0 ≤ r * (r - 1) ^ 2 by positivity)
  have h4 := mul_le_mul_of_nonneg_left hβ (show 0 ≤ r ^ 3 by positivity)
  have hs := add_le_add (add_le_add (add_le_add h1 h2) h3) h4
  convert hs using 1 <;> ring

end KqR75.ScalarDrift

#print axioms KqR75.ScalarDrift.young_variance
#print axioms KqR75.ScalarDrift.overlap_bound
#print axioms KqR75.ScalarDrift.temporal_bound
#print axioms KqR75.ScalarDrift.close_budget
#print axioms KqR75.ScalarDrift.noise_rate
