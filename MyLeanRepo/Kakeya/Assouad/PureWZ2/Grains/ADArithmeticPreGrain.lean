import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Basic

/-!
# PreGrain-scale AD arithmetic

Adapted arithmetic for the preGrain AD constant `C = L^(-alpha)` where
`alpha = 3 * loss_src / outputLoss`.

With `loss_src = outputLoss / 2` and `stickyLoss = outputLoss / 3`:
`alpha = 3/2`, so `C = L^(-3/2)`.

## Threshold analysis

### Trivial bound
`1/√ρ + 2 ≤ L^(-alpha)` requires `ρ ≥ 4 * L^(2*alpha)`.
- alpha = 3: ρ ≥ 4L⁶ (original)
- alpha = 3/2: ρ ≥ 4L³ (new, larger threshold)

### Córdoba bound
With the one-cell ratio `V_total/V_min ≤ 1/(2L²)`, the product is
`~L^(-3)` for ρ ≥ 80L². This works for alpha ≥ 3 but **not** for alpha < 3.

For alpha < 3 (e.g., alpha = 3/2), a tighter `V_total` bound is required,
such as the extremal volume bound `V_total ≤ L^(sigma - loss_src)/stickyLoss`.
The general lemma below takes the ratio bound as a parameter.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Real

/-- Helper: 1/L^alpha = L^(-alpha) for L > 0, alpha real. -/
lemma one_div_Lalpha_eq_rpow (L alpha : ℝ) (hL_pos : 0 < L) :
    (1 : ℝ) / L^alpha = L^(-alpha) := by
  have h : L^(-alpha) = 1 / L^alpha := by
    rw [Real.rpow_neg (by linarith)]
    <;> simp
  exact h.symm

/-- Trivial diameter bound at preGrain scale: for L small and ρ ≥ 4L^(2*alpha),
`1/√ρ + 2 ≤ L^(-alpha)`.

Requires `L^(-alpha) ≥ 4`, i.e., `L ≤ 4^(-1/alpha)`.
-/
lemma trivial_covering_arithmetic_alpha
    (L rho alpha : ℝ)
    (hL_pos : 0 < L)
    (hL_half : L ≤ 1 / 2)
    (halpha_pos : 0 < alpha)
    (hL_small : L^(-alpha) ≥ 4)
    (_hrho_pos : 0 < rho)
    (hrho_bound : 4 * L^(2 * alpha) ≤ rho) :
    1 / Real.sqrt rho + 2 ≤ L^(-alpha) := by
  have h1 : 0 ≤ 4 * L^(2 * alpha) := by positivity
  have h2 : Real.sqrt (4 * L^(2 * alpha)) = 2 * L^alpha := by
    have h3 : 0 < L^alpha := Real.rpow_pos_of_pos hL_pos alpha
    have h4 : (2 * L^alpha)^2 = 4 * L^(2 * alpha) := by
      have h5 : L^(2 * alpha) = L^alpha * L^alpha := by
        have h6 : (2 * alpha : ℝ) = alpha + alpha := by ring
        rw [h6]
        exact Real.rpow_add hL_pos alpha alpha
      rw [h5] <;> ring
    rw [← h4, Real.sqrt_sq_eq_abs]
    have h6 : 0 ≤ 2 * L^alpha := by positivity
    rw [abs_of_nonneg h6]
  have h3 : 2 * L^alpha ≤ Real.sqrt rho := by
    have h4 : Real.sqrt (4 * L^(2 * alpha)) ≤ Real.sqrt rho := Real.sqrt_le_sqrt hrho_bound
    rw [h2] at h4
    exact h4
  have h4 : 0 < 2 * L^alpha := by positivity
  have h5 : 1 / Real.sqrt rho ≤ 1 / (2 * L^alpha) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact h3
  have h6 : (2 : ℝ) ≤ 1 / (2 * L^alpha) := by
    have h7 : L^(-alpha) ≥ 4 := hL_small
    have h9 : 0 < L^alpha := Real.rpow_pos_of_pos hL_pos alpha
    have h10 : 1 / (2 * L^alpha) = (1 / 2 : ℝ) * L^(-alpha) := by
      have h11 : L^(-alpha) = 1 / L^alpha := by
        rw [Real.rpow_neg (by linarith)] <;> simp
      rw [h11]
      <;> field_simp [h9.ne'] <;> ring
    rw [h10]
    have h11 : (1 / 2 : ℝ) * L^(-alpha) ≥ (1 / 2 : ℝ) * (4 : ℝ) := by gcongr
    linarith
  have h13 : 1 / Real.sqrt rho + 2 ≤ 1 / (2 * L^alpha) + 1 / (2 * L^alpha) := by
    linarith
  have h14 : 1 / (2 * L^alpha) + 1 / (2 * L^alpha) = 1 / L^alpha := by
    have h15 : 0 < L^alpha := Real.rpow_pos_of_pos hL_pos alpha
    field_simp [h15.ne'] <;> ring
  have h15 : 1 / Real.sqrt rho + 2 ≤ 1 / L^alpha := by
    rw [h14] at h13
    exact h13
  have h16 : (1 : ℝ) / L^alpha = L^(-alpha) := one_div_Lalpha_eq_rpow L alpha hL_pos
  rw [h16] at h15
  exact h15

/-- General Córdoba covering arithmetic at preGrain scale.

Given a ratio bound `V_total/V_min ≤ R`, slab width `W ≤ 40L`, and
`rho ≥ 80L²`, the product is `≤ R * (1/L + 2)`.

For the one-cell bound `R = 1/(2L²)`, this gives `≤ L^(-3)`.
For preGrain alpha < 3, a tighter `R` is needed.
-/
lemma cordoba_covering_arithmetic_general
    (L rho W V_total V_min R : ℝ)
    (hL_pos : 0 < L)
    (hL_half : L ≤ 1 / 2)
    (hrho_pos : 0 < rho)
    (hrho_bound : 80 * L^2 ≤ rho)
    (hW_pos : 0 < W)
    (hW_bound : W ≤ 40 * L)
    (hVmin_pos : 0 < V_min)
    (hV_total_nonneg : 0 ≤ V_total)
    (hR_nonneg : 0 ≤ R)
    (hV_bound : V_total / V_min ≤ R) :
    (V_total / V_min) * (2 * W / rho + 2) ≤ R * (1 / L + 2) := by
  have hL2_pos : 0 < L^2 := by positivity
  have hV_nonneg : 0 ≤ V_total / V_min := by positivity
  have h1 : 2 * W / rho ≤ 1 / L := by
    have h1a : 2 * W ≤ 80 * L := by linarith
    calc
      2 * W / rho ≤ (80 * L) / rho := by gcongr
      _ ≤ (80 * L) / (80 * L^2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hrho_bound
      _ = 1 / L := by field_simp [hL_pos.ne', hL2_pos.ne']
  have h2 : 2 * W / rho + 2 ≤ 1 / L + 2 := by linarith
  have h2' : 0 ≤ 2 * W / rho + 2 := by positivity
  have h3a : (V_total / V_min) * (2 * W / rho + 2) ≤ R * (2 * W / rho + 2) :=
    mul_le_mul_of_nonneg_right hV_bound h2'
  have h3b : R * (2 * W / rho + 2) ≤ R * (1 / L + 2) :=
    mul_le_mul_of_nonneg_left h2 hR_nonneg
  exact le_trans h3a h3b

/-- Córdoba arithmetic for alpha ≥ 3 with the one-cell ratio bound.

When `alpha ≥ 3` and `L ≤ 1/2`, `R * (1/L + 2) ≤ L^(-alpha)` for
`R = 1/(2L²)`. This recovers the original `cordoba_covering_arithmetic`.
-/
lemma cordoba_covering_arithmetic_alpha_ge_3
    (L rho W V_total V_min alpha : ℝ)
    (hL_pos : 0 < L)
    (hL_half : L ≤ 1 / 2)
    (halpha_ge_3 : 3 ≤ alpha)
    (hrho_pos : 0 < rho)
    (hrho_bound : 80 * L^2 ≤ rho)
    (hW_pos : 0 < W)
    (hW_bound : W ≤ 40 * L)
    (hVmin_pos : 0 < V_min)
    (hV_total_nonneg : 0 ≤ V_total)
    (hV_bound : V_total / V_min ≤ 1 / (2 * L^2)) :
    (V_total / V_min) * (2 * W / rho + 2) ≤ L^(-alpha) := by
  have hL2_pos : 0 < L^2 := by positivity
  have hV_nonneg : 0 ≤ V_total / V_min := by positivity
  have h1 : 2 * W / rho ≤ 1 / L := by
    have h1a : 2 * W ≤ 80 * L := by linarith
    calc
      2 * W / rho ≤ (80 * L) / rho := by gcongr
      _ ≤ (80 * L) / (80 * L^2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hrho_bound
      _ = 1 / L := by field_simp [hL_pos.ne', hL2_pos.ne']
  have h2 : 2 * W / rho + 2 ≤ 1 / L + 2 := by linarith
  have h2' : 0 ≤ 2 * W / rho + 2 := by positivity
  have h_bound_pos : 0 < 1 / (2 * L^2) := by positivity
  have h3a : (V_total / V_min) * (2 * W / rho + 2) ≤
      (1 / (2 * L^2)) * (2 * W / rho + 2) :=
    mul_le_mul_of_nonneg_right hV_bound h2'
  have h3b : (1 / (2 * L^2)) * (2 * W / rho + 2) ≤
      (1 / (2 * L^2)) * (1 / L + 2) :=
    mul_le_mul_of_nonneg_left h2 h_bound_pos.le
  have h3 : (V_total / V_min) * (2 * W / rho + 2) ≤
      (1 / (2 * L^2)) * (1 / L + 2) := le_trans h3a h3b
  have h4 : (1 / (2 * L^2)) * (1 / L + 2) = 1 / (2 * L^3) + 1 / L^2 := by
    field_simp [hL_pos.ne']
  have h5 : 1 / L^2 ≤ 1 / (2 * L^3) := by
    have h6 : 0 < L^3 := by positivity
    have h7 : 1 / L^2 = L / L^3 := by field_simp [hL_pos.ne']
    rw [h7]
    have h8 : L / L^3 ≤ (1 / 2 : ℝ) / L^3 :=
      div_le_div_of_nonneg_right hL_half (by positivity)
    have h9 : (1 / 2 : ℝ) / L^3 = 1 / (2 * L^3) := by field_simp [hL_pos.ne']
    rw [h9] at h8
    exact h8
  have h10 : 1 / (2 * L^3) + 1 / L^2 ≤ 1 / (2 * L^3) + 1 / (2 * L^3) :=
    add_le_add_right h5 (1 / (2 * L^3))
  have h11 : 1 / (2 * L^3) + 1 / L^2 ≤ 1 / L^3 := by
    have h12 : 1 / (2 * L^3) + 1 / (2 * L^3) = 1 / L^3 := by
      have h13 : 0 < L^3 := by positivity
      field_simp [h13.ne'] <;> ring
    rw [h12] at h10
    exact h10
  have h_main : (V_total / V_min) * (2 * W / rho + 2) ≤ 1 / L^3 := by
    calc
      (V_total / V_min) * (2 * W / rho + 2)
        ≤ (1 / (2 * L^2)) * (1 / L + 2) := h3
      _ = 1 / (2 * L^3) + 1 / L^2 := h4
      _ ≤ 1 / L^3 := h11
  have hL_le_one : L ≤ 1 := by linarith
  have h_ge : (-alpha : ℝ) ≤ (-3 : ℝ) := by linarith
  have h3 : L^(-3 : ℝ) ≤ L^(-alpha) :=
    Real.rpow_le_rpow_of_exponent_ge hL_pos hL_le_one h_ge
  have h4 : (1 : ℝ) / L^3 = L^(-3 : ℝ) := by
    have h5 : L^(-3 : ℝ) = 1 / L^3 := by
      rw [Real.rpow_neg (by linarith)] <;> simp
    exact h5.symm
  have h6 : (1 : ℝ) / L^3 ≤ L^(-alpha) := by
    calc (1 : ℝ) / L^3
      = L^(-3 : ℝ) := h4
    _ ≤ L^(-alpha) := h3
  exact le_trans h_main h6

/-- Gap analysis for preGrain alpha: trivial and Córdoba regimes overlap when
`4 * L^(2*alpha) ≤ 80 * L^2`, i.e., `L^(2*alpha - 2) ≤ 20`.

For alpha ≥ 1 and L ≤ 1/2, this holds since `2*alpha - 2 ≥ 0` and
`L^(2*alpha - 2) ≤ 1 ≤ 20`.

For alpha = 3/2: `L^1 ≤ 20`, holds for L ≤ 1/2.
For alpha = 3: `L^4 ≤ 20`, holds for L ≤ 1/2.
-/
lemma gap_regimes_overlap_alpha
    (L alpha : ℝ)
    (hL_pos : 0 < L)
    (hL_half : L ≤ 1 / 2)
    (halpha_ge_1 : 1 ≤ alpha) :
    4 * L^(2 * alpha) ≤ 80 * L^2 := by
  have h1 : 2 * alpha - 2 ≥ 0 := by linarith
  have hL_le_one : L ≤ 1 := by linarith
  have h21 : (2 : ℝ) ≤ (2 * alpha : ℝ) := by linarith
  have h2' : L^(2 * alpha) ≤ L^(2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hL_pos hL_le_one h21
  have h_cast : L^(2 : ℝ) = L^2 := by norm_cast
  have h2 : L^(2 * alpha) ≤ L^2 := by
    rw [h_cast] at h2'
    exact h2'
  have h3 : 4 * L^(2 * alpha) ≤ 4 * L^2 := by
    gcongr
  have h4 : 4 * L^2 ≤ 80 * L^2 := by
    have h5 : 0 ≤ L^2 := by positivity
    have h6 : (4 : ℝ) ≤ 80 := by norm_num
    nlinarith
  exact le_trans h3 h4

/-- delta₀_arith for alpha=3 with constant 600000.

Given ε₁ < 1/20 and L ≤ (1/600000)^(4/3), proves:
  600000 * L^(-2-5ε₁) ≤ L^(-3)

This ensures the one-scale Córdoba product bound is absorbed by L^(-alpha)
when alpha ≥ 3.
-/
lemma delta0_arith_alpha3
    (L epsilon₁ : ℝ)
    (hL_pos : 0 < L)
    (hL_lt_one : L < 1)
    (hepsilon₁_lt : epsilon₁ < 1 / 20)
    (hL_bound : L ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ)) :
    (600000 : ℝ) * L ^ (-2 - 5 * epsilon₁) ≤ L ^ (-3 : ℝ) := by
  set C : ℝ := 600000 with hC_def
  have hC_pos : 0 < C := by norm_num [hC_def]
  have hC_nonneg : 0 ≤ C := by linarith
  set d : ℝ := 1 - 5 * epsilon₁ with hd_def
  have hd_gt34 : d > 3 / 4 := by
    rw [hd_def] <;> linarith
  have hd_pos : 0 < d := by linarith
  have h6 : -4 / 3 ≤ -1 / d := by
    have h61 : 1 / d < 4 / 3 := by
      have h62 : 1 / d < 1 / (3 / 4 : ℝ) :=
        one_div_lt_one_div_of_lt (by norm_num) hd_gt34
      have h63 : 1 / (3 / 4 : ℝ) = 4 / 3 := by norm_num
      rw [h63] at h62
      exact h62
    have h64 : 1 / d - 4 / 3 < 0 := by linarith
    have h65 : (-4 / 3 : ℝ) - (-1 / d) = 1 / d - 4 / 3 := by ring
    have h66 : (-4 / 3 : ℝ) - (-1 / d) < 0 := by
      rw [h65]
      exact h64
    have h67 : (-4 / 3 : ℝ) ≤ -1 / d := by linarith
    exact h67
  have hC_ge_one : 1 ≤ C := by norm_num [hC_def]
  have h7 : C ^ (-4 / 3 : ℝ) ≤ C ^ (-1 / d) :=
    Real.rpow_le_rpow_of_exponent_le hC_ge_one h6
  have h8 : (1 / 600000 : ℝ) ^ (4 / 3 : ℝ) = C ^ (-4 / 3 : ℝ) := by
    have h_eq1 : (1 / 600000 : ℝ) = C ^ (-1 : ℝ) := by
      simp [hC_def, Real.rpow_neg hC_nonneg] <;> norm_num
    have h1 : (1 / 600000 : ℝ) ^ (4 / 3 : ℝ) = (C ^ (-1 : ℝ)) ^ (4 / 3 : ℝ) := by
      rw [h_eq1]
    have h2 : (C ^ (-1 : ℝ)) ^ (4 / 3 : ℝ) = C ^ ((-1 : ℝ) * (4 / 3 : ℝ)) :=
      (Real.rpow_mul hC_nonneg (-1 : ℝ) (4 / 3 : ℝ)).symm
    have h3 : (-1 : ℝ) * (4 / 3 : ℝ) = -4 / 3 := by norm_num
    rw [h1, h2, h3]
  have h12 : L ≤ C ^ (-1 / d) := by
    have h9 : L ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ) := hL_bound
    have h10 : L ≤ C ^ (-4 / 3 : ℝ) := by
      calc L
        ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ) := h9
      _ = C ^ (-4 / 3 : ℝ) := h8
    exact h10.trans h7
  have h13 : L ^ d ≤ 1 / C := by
    have h14 : L ^ d ≤ (C ^ (-1 / d)) ^ d := by gcongr
    have h15 : (C ^ (-1 / d)) ^ d = C ^ ((-1 / d) * d) :=
      (Real.rpow_mul hC_nonneg (-1 / d) d).symm
    rw [h15] at h14
    have h16 : (-1 / d) * d = -1 := by
      field_simp [hd_pos.ne'] <;> ring
    rw [h16] at h14
    have h17 : C ^ (-1 : ℝ) = 1 / C := by
      rw [Real.rpow_neg hC_nonneg] <;> simp
    rw [h17] at h14
    exact h14
  have h18 : C * L ^ d ≤ 1 := by
    calc C * L ^ d
      ≤ C * (1 / C) := by gcongr
    _ = 1 := by
      field_simp [hC_pos.ne'] <;> ring
  have h19 : C ≤ L ^ (-d) := by
    have h20 : L ^ (-d) = (L ^ d)⁻¹ := by
      rw [Real.rpow_neg hL_pos.le] <;> simp
    rw [h20]
    have h21 : 0 < L ^ d := Real.rpow_pos_of_pos hL_pos _
    have h22 : C * L ^ d ≤ 1 := h18
    have h23 : C ≤ (L ^ d)⁻¹ := by
      calc C
        = (C * L ^ d) / (L ^ d) := by field_simp [h21.ne'] <;> ring
      _ ≤ 1 / (L ^ d) := by exact div_le_div_of_nonneg_right h22 h21.le
      _ = (L ^ d)⁻¹ := by simp
    exact h23
  have h24 : L ^ (-3 : ℝ) = L ^ (-2 - 5 * epsilon₁) * L ^ (-d) := by
    have h25 : -2 - 5 * epsilon₁ + (-d) = -3 := by
      simp [hd_def] <;> ring
    rw [← Real.rpow_add hL_pos, h25]
  rw [h24]
  have h26 : 0 < L ^ (-2 - 5 * epsilon₁) := Real.rpow_pos_of_pos hL_pos _
  have h27 : C * L ^ (-2 - 5 * epsilon₁) ≤ L ^ (-d) * L ^ (-2 - 5 * epsilon₁) :=
    mul_le_mul_of_nonneg_right h19 h26.le
  have h28 : L ^ (-d) * L ^ (-2 - 5 * epsilon₁) = L ^ (-2 - 5 * epsilon₁) * L ^ (-d) := by ring
  rw [h28] at h27
  exact h27

/-- Slab-to-AD product bound (tightened constants).

Given V_total ≤ 256·π·√3·L³ (ball of radius 4√3·L: volume = (4/3)π(4√3·L)³ = 256π√3·L³),
V_min = (3/200)·L^(3+7ε₁+ε₃), W ≤ 80L, rho ≥ 48L², L ≤ 1/2:
  (V_total/V_min)·(2W/rho+2) ≤ 600000·L^(-2-5ε₁)

Numerical check: constant = (819200/9)·π·√3 ≈ 495000 < 600000.

The W ≤ 80L bound accommodates the extended slab width W = 2·W0
where W0 = 40L in `cordoba_high_to_ad`.
-/
lemma slab_to_ad_product_bound
    (L epsilon₁ epsilon₃ rho W V_total V_min : ℝ)
    (hL_pos : 0 < L)
    (hL_half : L ≤ 1 / 2)
    (heps₃_def : epsilon₃ = 1 - 2 * epsilon₁)
    (hrho_ge : 48 * L^2 ≤ rho)
    (hW_nonneg : 0 ≤ W)
    (hW_le : W ≤ 80 * L)
    (hV_total_nonneg : 0 ≤ V_total)
    (hV_total : V_total ≤ 256 * Real.pi * Real.sqrt 3 * L^3)
    (hV_min : V_min = (3 / 200 : ℝ) * L^(3 + 7 * epsilon₁ + epsilon₃)) :
    (V_total / V_min) * (2 * W / rho + 2) ≤ 600000 * L^(-2 - 5 * epsilon₁) := by
  have h_exp : 3 + 7 * epsilon₁ + epsilon₃ = 4 + 5 * epsilon₁ := by
    rw [heps₃_def] <;> ring
  have hVmin_pos : 0 < V_min := by
    rw [hV_min, h_exp] <;> positivity
  have hL3 : (L ^ 3 : ℝ) = L ^ (3 : ℝ) := by norm_cast
  have h_pos4 : 0 < L^(4 + 5 * epsilon₁) := Real.rpow_pos_of_pos hL_pos _
  have h_add : L^(-1 - 5 * epsilon₁) * L^(4 + 5 * epsilon₁) = L^(3 : ℝ) := by
    rw [← Real.rpow_add hL_pos] <;> norm_num <;> ring
  have h_div2 : L^(3 : ℝ) / L^(4 + 5 * epsilon₁) = L^(-1 - 5 * epsilon₁) := by
    rw [← h_add]
    field_simp [h_pos4.ne'] <;> ring
  set K : ℝ := 256 * Real.pi * Real.sqrt 3 with hK_def
  have hK_pos : 0 < K := by positivity
  have h_div : (K * L^3) / ((3 / 200 : ℝ) * L^(4 + 5 * epsilon₁)) =
      (K * (200 / 3 : ℝ)) * L^(-1 - 5 * epsilon₁) := by
    rw [show K * L^3 = K * L^(3 : ℝ) by rw [←hL3]]
    have h : (K * L^(3 : ℝ)) / ((3 / 200 : ℝ) * L^(4 + 5 * epsilon₁)) =
        (K * (200 / 3 : ℝ)) * (L^(3 : ℝ) / L^(4 + 5 * epsilon₁)) := by
      field_simp [h_pos4.ne'] <;> ring
    rw [h, h_div2] <;> ring
  have h_ratio : V_total / V_min ≤ (K * (200 / 3 : ℝ)) * L^(-1 - 5 * epsilon₁) := by
    rw [hV_min, h_exp]
    have hV_total' : V_total ≤ K * L^3 := by
      simpa [hK_def] using hV_total
    calc V_total / ((3 / 200 : ℝ) * L^(4 + 5 * epsilon₁))
      ≤ (K * L^3) / ((3 / 200 : ℝ) * L^(4 + 5 * epsilon₁)) := by gcongr
    _ = (K * (200 / 3 : ℝ)) * L^(-1 - 5 * epsilon₁) := h_div
  have hL_le_one : L ≤ 1 := by linarith
  have hrho_pos : 0 < rho := by
    have h : 0 < 48 * L^2 := by positivity
    linarith [hrho_ge]
  have hW_term1 : 2 * W / rho ≤ 10 / (3 * L) := by
    have h2 : 2 * W ≤ 160 * L := by linarith
    have h4 : 0 < 48 * L^2 := by positivity
    have h5 : 0 < 3 * L := by positivity
    calc 2 * W / rho
      ≤ (160 * L) / rho := by gcongr
    _ ≤ (160 * L) / (48 * L^2) := by gcongr <;> linarith
    _ = 10 / (3 * L) := by field_simp [hL_pos.ne'] <;> ring
  have h2_le : (2 : ℝ) ≤ 2 / L := by
    have h7 : L ≤ 1 := hL_le_one
    have h8 : 0 < L := hL_pos
    calc (2 : ℝ)
      = 2 * L / L := by field_simp [h8.ne'] <;> ring
    _ ≤ 2 * (1 : ℝ) / L := by gcongr
    _ = 2 / L := by ring
  have hW_term : 2 * W / rho + 2 ≤ 16 / (3 * L) := by
    have h : 2 * W / rho + 2 ≤ 10 / (3 * L) + 2 / L := by linarith
    have h9 : 10 / (3 * L) + 2 / L = 16 / (3 * L) := by
      field_simp [hL_pos.ne'] <;> ring
    rw [h9] at h
    exact h
  have h_ratio_nonneg : 0 ≤ V_total / V_min := by
    apply div_nonneg hV_total_nonneg
    have h : 0 ≤ V_min := by rw [hV_min, h_exp] <;> positivity
    exact h
  have hW_nonneg2 : 0 ≤ 2 * W / rho + 2 := by
    have h1 : 0 ≤ 2 * W := by linarith
    have h2 : 0 ≤ 2 * W / rho := by apply div_nonneg h1; linarith
    linarith
  have h_main : (V_total / V_min) * (2 * W / rho + 2) ≤
      ((K * (200 / 3 : ℝ)) * L^(-1 - 5 * epsilon₁)) * (16 / (3 * L)) := by
    exact mul_le_mul h_ratio hW_term hW_nonneg2 (by positivity)
  have h_final : ((K * (200 / 3 : ℝ)) * L^(-1 - 5 * epsilon₁)) * (16 / (3 * L)) =
      (K * (200 / 3 : ℝ) * (16 / 3 : ℝ)) * L^(-2 - 5 * epsilon₁) := by
    have h1 : (16 / (3 * L) : ℝ) = (16 / 3 : ℝ) * L^(-1 : ℝ) := by
      have h2 : L^(-1 : ℝ) = 1 / L := by
        rw [Real.rpow_neg hL_pos.le] <;> simp
      rw [h2] <;> field_simp [hL_pos.ne'] <;> ring
    have h3 : L^(-1 - 5 * epsilon₁) * L^(-1 : ℝ) = L^(-2 - 5 * epsilon₁) := by
      have h4 : (-1 - 5 * epsilon₁) + (-1 : ℝ) = -2 - 5 * epsilon₁ := by ring
      have h5 : L^(-1 - 5 * epsilon₁) * L^(-1 : ℝ) = L^((-1 - 5 * epsilon₁) + (-1 : ℝ)) := by
        rw [← Real.rpow_add hL_pos]
      rw [h5, h4]
    calc ((K * (200 / 3 : ℝ)) * L^(-1 - 5 * epsilon₁)) * (16 / (3 * L))
      = ((K * (200 / 3 : ℝ)) * L^(-1 - 5 * epsilon₁)) * ((16 / 3 : ℝ) * L^(-1 : ℝ)) := by rw [h1]
    _ = (K * (200 / 3 : ℝ) * (16 / 3 : ℝ)) * (L^(-1 - 5 * epsilon₁) * L^(-1 : ℝ)) := by ring
    _ = (K * (200 / 3 : ℝ) * (16 / 3 : ℝ)) * L^(-2 - 5 * epsilon₁) := by rw [h3]
  rw [h_final] at h_main
  have h_const : K * (200 / 3 : ℝ) * (16 / 3 : ℝ) ≤ (600000 : ℝ) := by
    simp only [hK_def]
    have h_pi_lt : Real.pi < (3.1416 : ℝ) := Real.pi_lt_d4
    have h_pi_bound : Real.pi ≤ (31416 / 10000 : ℝ) := by
      have h_eq : (3.1416 : ℝ) = (31416 / 10000 : ℝ) := by norm_num
      rw [h_eq] at h_pi_lt
      exact h_pi_lt.le
    have h_sqrt3_bound : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)] <;> norm_num
    have h : 256 * Real.pi * Real.sqrt 3 * (200 / 3 : ℝ) * (16 / 3 : ℝ) ≤
        256 * (31416 / 10000 : ℝ) * 2 * (200 / 3 : ℝ) * (16 / 3 : ℝ) := by
      gcongr <;> linarith
    have h2 : 256 * (31416 / 10000 : ℝ) * 2 * (200 / 3 : ℝ) * (16 / 3 : ℝ) ≤ (600000 : ℝ) := by norm_num
    exact h.trans h2
  have h7 : 0 ≤ L^(-2 - 5 * epsilon₁) := by positivity
  exact le_trans h_main (mul_le_mul_of_nonneg_right h_const h7)

/-- Rho gap lemma: ensures `48 * L² ≥ 100 * delta'^outputLoss`, so the trivial AD
threshold `100 * delta'^outputLoss` is below the Córdoba containment threshold `48 * L²`.

Given `L = delta'^stickyLoss`, `stickyLoss ≤ outputLoss/3`, and
`delta' ≤ (1/600000)^(4/(3*stickyLoss))`, we have:
`delta'^(outputLoss - 2*stickyLoss) ≤ (1/600000)^(4/3) < 48/100`.
-/
lemma rho_gap_for_trivial_ad
    (delta' L stickyLoss outputLoss : ℝ)
    (hdelta'_pos : 0 < delta')
    (hdelta'_lt_one : delta' < 1)
    (hstickyLoss_pos : 0 < stickyLoss)
    (h_sticky_le_third : stickyLoss ≤ outputLoss / 3)
    (hL_eq : L = delta' ^ stickyLoss)
    (hdelta'_le_arith : delta' ≤ (1 / 600000 : ℝ) ^ (4 / (3 * stickyLoss))) :
    (100 : ℝ) * delta' ^ outputLoss ≤ 48 * L ^ 2 := by
  set e : ℝ := outputLoss - 2 * stickyLoss with he_def
  have h_e_pos : 0 < e := by
    have h : e ≥ stickyLoss := by dsimp only [e] <;> linarith
    linarith [hstickyLoss_pos]
  have h_e_ge_sticky : e ≥ stickyLoss := by dsimp only [e] <;> linarith
  set a : ℝ := (4 / (3 * stickyLoss)) * e with ha_def
  have h_a_ge : a ≥ 4 / 3 := by
    dsimp only [a]
    have h4 : e ≥ stickyLoss := h_e_ge_sticky
    have h5 : (4 / (3 * stickyLoss)) * e ≥ (4 / (3 * stickyLoss)) * stickyLoss := by gcongr
    have h6 : (4 / (3 * stickyLoss)) * stickyLoss = 4 / 3 := by
      field_simp [hstickyLoss_pos.ne'] <;> ring
    linarith
  have h_base_pos : 0 < (1 / 600000 : ℝ) := by norm_num
  have h_base_le_one : (1 / 600000 : ℝ) ≤ 1 := by norm_num
  have h1 : delta' ^ e ≤ ((1 / 600000 : ℝ) ^ (4 / (3 * stickyLoss))) ^ e :=
    Real.rpow_le_rpow hdelta'_pos.le hdelta'_le_arith h_e_pos.le
  have h2 : ((1 / 600000 : ℝ) ^ (4 / (3 * stickyLoss))) ^ e = (1 / 600000 : ℝ) ^ a := by
    have h21 : ((1 / 600000 : ℝ) ^ (4 / (3 * stickyLoss))) ^ e =
        (1 / 600000 : ℝ) ^ ((4 / (3 * stickyLoss)) * e) :=
      (Real.rpow_mul h_base_pos.le (4 / (3 * stickyLoss)) e).symm
    rw [h21]
    <;> rfl
  have h3 : (1 / 600000 : ℝ) ^ a ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge h_base_pos h_base_le_one h_a_ge
  have h4 : (1 / 600000 : ℝ) ^ (4 / 3 : ℝ) ≤ (1 / 600000 : ℝ) := by
    have h41 : (1 : ℝ) ≤ (4 / 3 : ℝ) := by norm_num
    have h42 : (1 / 600000 : ℝ) ^ (4 / 3 : ℝ) ≤ (1 / 600000 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge h_base_pos h_base_le_one h41
    have h43 : (1 / 600000 : ℝ) ^ (1 : ℝ) = (1 / 600000 : ℝ) := Real.rpow_one _
    rw [h43] at h42
    exact h42
  have h5 : (1 / 600000 : ℝ) ≤ (48 / 100 : ℝ) := by norm_num
  have h6 : delta' ^ e ≤ (48 / 100 : ℝ) := by
    calc delta' ^ e
      ≤ ((1 / 600000 : ℝ) ^ (4 / (3 * stickyLoss))) ^ e := h1
    _ = (1 / 600000 : ℝ) ^ a := h2
    _ ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ) := h3
    _ ≤ (1 / 600000 : ℝ) := h4
    _ ≤ (48 / 100 : ℝ) := h5
  have h7 : L ^ 2 = (delta' ^ stickyLoss) ^ 2 := by rw [hL_eq]
  have h8 : (delta' ^ stickyLoss) ^ 2 = delta' ^ (2 * stickyLoss) := by
    have h81 : (delta' ^ stickyLoss) ^ 2 = (delta' ^ stickyLoss) * (delta' ^ stickyLoss) := by ring
    rw [h81]
    have h82 : (delta' ^ stickyLoss) * (delta' ^ stickyLoss) = delta' ^ (stickyLoss + stickyLoss) :=
      (Real.rpow_add hdelta'_pos stickyLoss stickyLoss).symm
    rw [h82]
    have h83 : stickyLoss + stickyLoss = 2 * stickyLoss := by ring
    rw [h83]
  have h9 : delta' ^ outputLoss = delta' ^ e * delta' ^ (2 * stickyLoss) := by
    have h91 : e + 2 * stickyLoss = outputLoss := by
      dsimp only [e] <;> ring
    have h92 : delta' ^ (e + 2 * stickyLoss) = delta' ^ e * delta' ^ (2 * stickyLoss) :=
      Real.rpow_add hdelta'_pos e (2 * stickyLoss)
    have h93 : delta' ^ outputLoss = delta' ^ (e + 2 * stickyLoss) := by rw [h91]
    rw [h93, h92]
  have h10 : 0 < delta' ^ (2 * stickyLoss) := Real.rpow_pos_of_pos hdelta'_pos _
  have h11 : delta' ^ outputLoss ≤ (48 / 100 : ℝ) * delta' ^ (2 * stickyLoss) := by
    rw [h9]
    have h12 : delta' ^ e ≤ (48 / 100 : ℝ) := h6
    exact mul_le_mul_of_nonneg_right h12 h10.le
  have h13 : (100 : ℝ) * delta' ^ outputLoss ≤ 48 * delta' ^ (2 * stickyLoss) := by
    linarith
  rw [h7, h8]
  exact h13

/-- Full arithmetic chain for slab-to-AD in the HIGH case.

Given the product bound ≤ 600000 * L^(-2-5ε₁), delta₀ arithmetic, and
`3 * stickyLoss ≤ outputLoss`, proves the product ≤ `delta'^(-outputLoss)`.

Chain:
`product ≤ 600000 * L^(-2-5ε₁) ≤ L^(-3) = delta'^(-3*stickyLoss) ≤ delta'^(-outputLoss)`
-/
lemma slab_to_ad_arithmetic_chain
    (delta' L epsilon₁ stickyLoss outputLoss V_total V_min W rho : ℝ)
    (hdelta'_pos : 0 < delta')
    (hdelta'_lt_one : delta' < 1)
    (hL_pos : 0 < L)
    (hL_lt_one : L < 1)
    (hL_eq : L = delta' ^ stickyLoss)
    (hepsilon₁_lt : epsilon₁ < 1 / 20)
    (hL_bound : L ≤ (1 / 600000 : ℝ) ^ (4 / 3 : ℝ))
    (h_sticky_le_third : stickyLoss ≤ outputLoss / 3)
    (h_product : (V_total / V_min) * (2 * W / rho + 2) ≤ (600000 : ℝ) * L ^ (-2 - 5 * epsilon₁))
    (hVmin_pos : 0 < V_min) (hV_total_nonneg : 0 ≤ V_total)
    (hW_nonneg : 0 ≤ W) (hrho_pos : 0 < rho) :
    ENNReal.ofReal ((V_total / V_min) * (2 * W / rho + 2)) ≤
      ENNReal.ofReal (delta' ^ (-outputLoss)) := by
  have h1 : (600000 : ℝ) * L ^ (-2 - 5 * epsilon₁) ≤ L ^ (-3 : ℝ) :=
    delta0_arith_alpha3 L epsilon₁ hL_pos hL_lt_one hepsilon₁_lt hL_bound
  have h2 : L ^ (-3 : ℝ) = delta' ^ (-3 * stickyLoss) := by
    rw [hL_eq]
    have h31 : (delta' ^ stickyLoss) ^ (-3 : ℝ) = delta' ^ (stickyLoss * (-3 : ℝ)) :=
      (Real.rpow_mul hdelta'_pos.le stickyLoss (-3 : ℝ)).symm
    have h32 : stickyLoss * (-3 : ℝ) = -3 * stickyLoss := by ring
    rw [h31, h32]
  have h4 : -3 * stickyLoss ≥ -outputLoss := by linarith
  have hdelta'_le_one : delta' ≤ 1 := by linarith
  have h5 : delta' ^ (-3 * stickyLoss) ≤ delta' ^ (-outputLoss) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta'_pos hdelta'_le_one h4
  have h6 : (V_total / V_min) * (2 * W / rho + 2) ≤ delta' ^ (-outputLoss) :=
    calc (V_total / V_min) * (2 * W / rho + 2)
      ≤ (600000 : ℝ) * L ^ (-2 - 5 * epsilon₁) := h_product
    _ ≤ L ^ (-3 : ℝ) := h1
    _ = delta' ^ (-3 * stickyLoss) := h2
    _ ≤ delta' ^ (-outputLoss) := h5
  have h7 : 0 ≤ (V_total / V_min) * (2 * W / rho + 2) := by positivity
  have h8 : 0 ≤ delta' ^ (-outputLoss) := Real.rpow_nonneg hdelta'_pos.le _
  exact ENNReal.ofReal_le_ofReal h6

/-- Incidence arithmetic: `delta'/L ≤ L` iff `stickyLoss ≤ 1/2`.

Since `L = delta'^stickyLoss`, `delta'/L = delta'^(1-stickyLoss)`.
`delta'/L ≤ L` iff `delta'^(1-stickyLoss) ≤ delta'^stickyLoss`
iff `1-stickyLoss ≥ stickyLoss` (since delta'<1) iff `stickyLoss ≤ 1/2`.
-/
lemma incidence_arithmetic_stickyLoss
    (delta' stickyLoss : ℝ)
    (hdelta_pos : 0 < delta')
    (hdelta_lt_one : delta' < 1)
    (hsticky_pos : 0 < stickyLoss) :
    (delta' / (delta' ^ stickyLoss) ≤ delta' ^ stickyLoss) ↔ (stickyLoss ≤ 1 / 2) := by
  set L : ℝ := delta' ^ stickyLoss with hL_def
  have hL_pos : 0 < L := Real.rpow_pos_of_pos hdelta_pos _
  have h1 : (delta' / L ≤ L) ↔ (L ≥ Real.sqrt delta') := by
    constructor
    · intro h
      have h3 : delta' ≤ L ^ 2 := by
        have h4 : (delta' / L) * L ≤ L * L := mul_le_mul_of_nonneg_right h hL_pos.le
        have h5 : (delta' / L) * L = delta' := by
          field_simp [hL_pos.ne'] <;> ring
        rw [h5] at h4
        nlinarith
      nlinarith [Real.sqrt_nonneg delta', Real.sq_sqrt (show 0 ≤ delta' by linarith)]
    · intro h
      have h3 : L ^ 2 ≥ delta' := by
        nlinarith [Real.sqrt_nonneg delta', Real.sq_sqrt (show 0 ≤ delta' by linarith)]
      have h4 : delta' / L ≤ L := by
        have h5 : (delta' / L) * L ≤ L * L := by
          have h6 : (delta' / L) * L = delta' := by
            field_simp [hL_pos.ne'] <;> ring
          rw [h6]
          nlinarith
        have h7 : (delta' / L) ≤ L := by nlinarith [hL_pos]
        exact h7
      exact h4
  rw [h1]
  have h7 : (L ≥ Real.sqrt delta') ↔ (stickyLoss ≤ 1 / 2) := by
    have h8 : Real.sqrt delta' = delta' ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow] <;> linarith
    rw [h8]
    constructor
    · intro h
      by_contra h9
      have h10 : stickyLoss > 1 / 2 := by linarith
      have h11 : L < delta' ^ (1 / 2 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_gt hdelta_pos hdelta_lt_one (by linarith)
      linarith
    · intro h
      have h10 : stickyLoss ≤ (1 / 2 : ℝ) := by linarith
      exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_lt_one.le h10
  exact h7

/-- Multiplicity growth bound: `(L/delta')^sigma ≤ delta'^(-sigma)` since L < 1. -/
lemma multiplicity_growth_bound
    (L delta' sigma : ℝ)
    (hL_pos : 0 < L)
    (hL_lt_one : L < 1)
    (hdelta_pos : 0 < delta')
    (hsigma_pos : 0 < sigma) :
    (L / delta') ^ sigma ≤ delta' ^ (-sigma) := by
  have h1 : (L / delta') ^ sigma = L ^ sigma / delta' ^ sigma := by
    rw [div_rpow] <;> linarith
  rw [h1]
  have h2 : L ^ sigma < 1 := Real.rpow_lt_one (by linarith) hL_lt_one hsigma_pos
  have h3 : L ^ sigma ≤ 1 := by linarith
  have h4 : 0 < delta' ^ sigma := Real.rpow_pos_of_pos hdelta_pos _
  have h5 : L ^ sigma / delta' ^ sigma ≤ 1 / delta' ^ sigma := by gcongr
  have h6 : (1 : ℝ) / delta' ^ sigma = delta' ^ (-sigma) := by
    rw [Real.rpow_neg (by linarith)] <;> simp
  rw [h6] at h5
  exact h5

end Kakeya.Assouad.PureWZ2
