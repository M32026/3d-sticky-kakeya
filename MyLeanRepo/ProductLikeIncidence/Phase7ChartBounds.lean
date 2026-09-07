module

/-
# Phase7 Cross-Ratio Chart Bounds (Core)

Whiteprint node: phase7_chart_bounds
-/

public import MyLeanRepo.FourSectorSelection
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set

namespace ProductLikeIncidence.ProductReduction

def crossRatioMap (θ1 θ2 θ3 : ℝ) (y : ℝ) : ℝ :=
  ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y))

lemma crossRatio_abs_diff {θ1 θ2 θ3 y z : ℝ}
    (h13 : θ1 < θ3) (h23 : θ3 < θ2)
    (hy : y ≠ θ2) (hz : z ≠ θ2) :
    |crossRatioMap θ1 θ2 θ3 y - crossRatioMap θ1 θ2 θ3 z| =
      ((θ2 - θ3) / (θ3 - θ1)) * (θ2 - θ1) * |y - z| / (|θ2 - y| * |θ2 - z|) := by
  have ha : θ3 - θ1 ≠ 0 := by linarith
  have hb : θ2 - y ≠ 0 := by intro h; exact hy (by linarith)
  have hc : θ2 - z ≠ 0 := by intro h; exact hz (by linarith)
  have hA_pos : 0 < (θ2 - θ3) / (θ3 - θ1) := by
    have h1 : 0 < θ2 - θ3 := by linarith
    have h2 : 0 < θ3 - θ1 := by linarith
    exact div_pos h1 h2
  have h21_pos : 0 < θ2 - θ1 := by linarith
  have h_eq : crossRatioMap θ1 θ2 θ3 y - crossRatioMap θ1 θ2 θ3 z =
      ((θ2 - θ3) / (θ3 - θ1)) * (θ2 - θ1) * (y - z) / ((θ2 - y) * (θ2 - z)) := by
    simp only [crossRatioMap]
    field_simp [ha, hb, hc] <;> ring
  rw [h_eq]
  have h5 : |((θ2 - θ3) / (θ3 - θ1)) * (θ2 - θ1)| =
      (θ2 - θ3) / (θ3 - θ1) * (θ2 - θ1) := by
    rw [abs_mul, abs_of_pos hA_pos, abs_of_pos h21_pos]
  have h6 : |(y - z) / ((θ2 - y) * (θ2 - z))| =
      |y - z| / (|θ2 - y| * |θ2 - z|) := by
    rw [abs_div, abs_mul] <;> ring
  have h7 : (((θ2 - θ3) / (θ3 - θ1)) * (θ2 - θ1)) * ((y - z) / ((θ2 - y) * (θ2 - z))) =
      ((θ2 - θ3) / (θ3 - θ1)) * (θ2 - θ1) * (y - z) / ((θ2 - y) * (θ2 - z)) := by ring
  have h8 : |(((θ2 - θ3) / (θ3 - θ1)) * (θ2 - θ1)) * ((y - z) / ((θ2 - y) * (θ2 - z)))| =
      |((θ2 - θ3) / (θ3 - θ1)) * (θ2 - θ1)| * |(y - z) / ((θ2 - y) * (θ2 - z))| := by
    rw [abs_mul]
  rw [← h7, h8, h5, h6] <;> ring

lemma crossRatio_lipschitz {δ rho_sep θ1 θ2 θ3 r y z : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h13 : θ1 < θ3) (h23 : θ3 < θ2)
    (hθ1_nonneg : 0 ≤ θ1) (hθ2_le_one : θ2 ≤ 1)
    (h_sep : θ3 - θ1 ≥ δ^rho_sep) (hrho_nonneg : 0 ≤ rho_sep)
    (hr_pos : 0 < r)
    (hyp : r ≤ |θ2 - y|) (hzp : r ≤ |θ2 - z|) :
    |crossRatioMap θ1 θ2 θ3 y - crossRatioMap θ1 θ2 θ3 z| ≤
      (δ^(-rho_sep) / r^2) * |y - z| := by
  have hy_ne : y ≠ θ2 := by
    intro h; rw [h] at hyp; simp [abs_zero] at hyp; linarith
  have hz_ne : z ≠ θ2 := by
    intro h; rw [h] at hzp; simp [abs_zero] at hzp; linarith
  rw [crossRatio_abs_diff h13 h23 hy_ne hz_ne]
  set A : ℝ := (θ2 - θ3) / (θ3 - θ1) with hA_def
  set B : ℝ := θ2 - θ1 with hB_def
  set D : ℝ := |θ2 - y| * |θ2 - z| with hD_def
  have h13_pos : 0 < θ3 - θ1 := by linarith
  have h_drp_pos : 0 < δ^rho_sep := Real.rpow_pos_of_pos hδ_pos rho_sep
  have hA_nonneg : 0 ≤ A := by positivity
  have hB_nonneg : 0 ≤ B := by linarith
  have h_drp_neg_nonneg : 0 ≤ δ^(-rho_sep) := by positivity
  have hA_le : A ≤ δ^(-rho_sep) := by
    have h1 : θ2 - θ3 ≤ 1 := by linarith
    have h2 : 0 < θ3 - θ1 := h13_pos
    have h3 : 0 ≤ 1 / (θ3 - θ1) := by positivity
    have h4 : A ≤ 1 / (θ3 - θ1) := by
      simp only [hA_def]
      exact div_le_div_of_nonneg_right h1 (by linarith)
    have h5 : 1 / (θ3 - θ1) ≤ 1 / δ^rho_sep := one_div_le_one_div_of_le h_drp_pos h_sep
    have h6 : δ^(-rho_sep) = (δ^rho_sep)⁻¹ := by
      rw [← Real.rpow_neg hδ_pos.le] <;> ring
    have h5' : 1 / (θ3 - θ1) ≤ (δ^rho_sep)⁻¹ := by
      simpa [one_div] using h5
    rw [h6]
    exact le_trans h4 h5'
  have hB_le : B ≤ 1 := by linarith
  have hAB_le : A * B ≤ δ^(-rho_sep) := by
    have h5 : A * B ≤ A := by nlinarith
    exact le_trans h5 hA_le
  have hD_ge : r^2 ≤ D := by
    simp only [hD_def]
    have h1 : 0 ≤ r := by linarith
    nlinarith [abs_nonneg (θ2 - y), abs_nonneg (θ2 - z)]
  have hD_pos : 0 < D := by
    simp only [hD_def]
    have h4 : θ2 - y ≠ 0 := by intro h; exact hy_ne (by linarith)
    have h5 : θ2 - z ≠ 0 := by intro h; exact hz_ne (by linarith)
    exact mul_pos (abs_pos.mpr h4) (abs_pos.mpr h5)
  have hr2_pos : 0 < r^2 := by positivity
  by_cases h_yz : |y - z| = 0
  · rw [h_yz]; simp
  · have h1 : A * B * r^2 ≤ δ^(-rho_sep) * D := by nlinarith
    have h_denom_pos : 0 < D * r^2 := mul_pos hD_pos hr2_pos
    have h_num_nonpos : A * B * r^2 - δ^(-rho_sep) * D ≤ 0 := by linarith
    have h6 : A * B / D - δ^(-rho_sep) / r^2 =
        (A * B * r^2 - δ^(-rho_sep) * D) / (D * r^2) := by
      field_simp [hD_pos.ne', hr2_pos.ne'] <;> ring
    have h7 : A * B / D ≤ δ^(-rho_sep) / r^2 := by
      rw [← sub_nonpos]
      rw [h6]
      exact div_nonpos_of_nonpos_of_nonneg h_num_nonpos (by positivity)
    have h8 : A * B * |y - z| / D = (A * B / D) * |y - z| := by ring
    rw [h8]
    have h9 : 0 ≤ |y - z| := by positivity
    nlinarith

lemma crossRatio_colipschitz {δ rho_sep θ1 θ2 θ3 y z : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h13 : θ1 < θ3) (h23 : θ3 < θ2)
    (hθ1_nonneg : 0 ≤ θ1) (hθ2_le_one : θ2 ≤ 1)
    (h_sep13 : θ3 - θ1 ≥ δ^rho_sep) (h_sep32 : θ2 - θ3 ≥ δ^rho_sep)
    (hrho_nonneg : 0 ≤ rho_sep)
    (hy_ne : y ≠ θ2) (hz_ne : z ≠ θ2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |y - z| ≤ δ^(-2*rho_sep) * |crossRatioMap θ1 θ2 θ3 y - crossRatioMap θ1 θ2 θ3 z| := by
  set A : ℝ := (θ2 - θ3) / (θ3 - θ1) with hA_def
  set B : ℝ := θ2 - θ1 with hB_def
  set D : ℝ := |θ2 - y| * |θ2 - z| with hD_def
  have h13_pos : 0 < θ3 - θ1 := by linarith
  have hA_nonneg : 0 ≤ A := by positivity
  have hB_nonneg : 0 ≤ B := by linarith
  have h_drp_nonneg : 0 ≤ δ^rho_sep := by positivity
  have hA_ge : A ≥ δ^rho_sep := by
    simp only [hA_def]
    have h1 : θ3 - θ1 ≤ 1 := by linarith
    have h2 : 0 < θ3 - θ1 := h13_pos
    have h3 : 1 / (θ3 - θ1) ≥ 1 := by
      have h4 : 1 / (θ3 - θ1) ≥ 1 / (1 : ℝ) := one_div_le_one_div_of_le (by positivity) h1
      have h5 : 1 / (1 : ℝ) = (1 : ℝ) := by norm_num
      rw [h5] at h4; exact h4
    have h6 : δ^rho_sep / (θ3 - θ1) ≥ δ^rho_sep := by
      have h7 : δ^rho_sep / (θ3 - θ1) = δ^rho_sep * (1 / (θ3 - θ1)) := by ring
      rw [h7]
      nlinarith
    have h10 : δ^rho_sep / (θ3 - θ1) ≤ A := by
      simp only [hA_def]
      have h11 : δ^rho_sep ≤ θ2 - θ3 := h_sep32
      exact div_le_div_of_nonneg_right h11 (by linarith)
    exact le_trans h6 h10
  have hB_ge : B ≥ δ^rho_sep := by
    simp only [hB_def]
    have h1 : θ2 - θ1 = (θ2 - θ3) + (θ3 - θ1) := by ring
    rw [h1]
    linarith
  have hAB_ge : A * B ≥ δ^(2*rho_sep) := by
    have h_exp : δ^(2*rho_sep) = (δ^rho_sep) * (δ^rho_sep) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    rw [h_exp]
    nlinarith
  have hD_pos : 0 < D := by
    simp only [hD_def]
    have h4 : θ2 - y ≠ 0 := by intro h; exact hy_ne (by linarith)
    have h5 : θ2 - z ≠ 0 := by intro h; exact hz_ne (by linarith)
    exact mul_pos (abs_pos.mpr h4) (abs_pos.mpr h5)
  have hD_le_one : D ≤ 1 := by
    simp only [hD_def]
    have hθ2_nonneg : 0 ≤ θ2 := by linarith
    have h_yb1 : -1 ≤ θ2 - y := by linarith
    have h_yb2 : θ2 - y ≤ 1 := by linarith
    have h_yb : |θ2 - y| ≤ 1 := by
      rw [abs_le] <;> exact ⟨h_yb1, h_yb2⟩
    have h_zb1 : -1 ≤ θ2 - z := by linarith
    have h_zb2 : θ2 - z ≤ 1 := by linarith
    have h_zb : |θ2 - z| ≤ 1 := by
      rw [abs_le] <;> exact ⟨h_zb1, h_zb2⟩
    have h : |θ2 - y| * |θ2 - z| ≤ 1 * 1 := by
      exact mul_le_mul h_yb h_zb (by positivity) (by positivity)
    linarith
  have h_abs_diff_eq := crossRatio_abs_diff h13 h23 hy_ne hz_ne
  rw [h_abs_diff_eq]
  by_cases h_yz : |y - z| = 0
  · rw [h_yz]; simp
  · have h1 : δ^(2*rho_sep) * D ≤ A * B := by
      have h2 : δ^(2*rho_sep) * D ≤ δ^(2*rho_sep) := by
        have h3 : 0 ≤ δ^(2*rho_sep) := by positivity
        nlinarith [hD_le_one]
      nlinarith [hAB_ge]
    have h3 : δ^(2*rho_sep) ≤ A * B / D := by
      have h4 : 0 < D := hD_pos
      have h5 : δ^(2*rho_sep) = (δ^(2*rho_sep) * D) / D := by
        field_simp [h4.ne'] <;> ring
      rw [h5]
      exact div_le_div_of_nonneg_right h1 (by positivity)
    have h7 : δ^(2*rho_sep) * |y - z| ≤ (A * B / D) * |y - z| := by
      have h8 : 0 ≤ |y - z| := by positivity
      nlinarith
    have h8 : (A * B / D) * |y - z| = A * B * |y - z| / D := by ring
    rw [h8] at h7
    have h9 : δ^(-2*rho_sep) * δ^(2*rho_sep) = 1 := by
      have h91 : δ^(-2*rho_sep) * δ^(2*rho_sep) = δ^((-2*rho_sep) + (2*rho_sep)) := by
        rw [← Real.rpow_add hδ_pos]
      rw [h91]
      have h92 : (-2*rho_sep) + (2*rho_sep) = 0 := by ring
      rw [h92]
      simp
    have h10 : δ^(-2*rho_sep) * (δ^(2*rho_sep) * |y - z|) = |y - z| := by
      rw [← mul_assoc, h9, one_mul]
    have h11 : δ^(-2*rho_sep) * (δ^(2*rho_sep) * |y - z|) ≤
        δ^(-2*rho_sep) * (A * B * |y - z| / D) := by
      have h12 : 0 ≤ δ^(-2*rho_sep) := by positivity
      nlinarith
    rw [h10] at h11
    exact h11

/-- Bound on |crossRatioMap y| when y is at least r away from θ2. -/
lemma crossRatio_abs_bound {δ rho_sep θ1 θ2 θ3 r y : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h13 : θ1 < θ3) (h23 : θ3 < θ2)
    (hθ1_nonneg : 0 ≤ θ1) (hθ2_le_one : θ2 ≤ 1)
    (h_sep13 : θ3 - θ1 ≥ δ^rho_sep) (hrho_nonneg : 0 ≤ rho_sep)
    (hr_pos : 0 < r) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (hyp : r ≤ |θ2 - y|) :
    |crossRatioMap θ1 θ2 θ3 y| ≤ 1 / (δ^rho_sep * r) := by
  have h13_pos : 0 < θ3 - θ1 := by linarith
  have h_drp_pos : 0 < δ^rho_sep := Real.rpow_pos_of_pos hδ_pos rho_sep
  have hy_ne : y ≠ θ2 := by
    intro h; rw [h] at hyp; simp [abs_zero] at hyp; linarith
  have h_denom_pos : 0 < |(θ3 - θ1) * (θ2 - y)| := by
    have h1 : 0 < θ3 - θ1 := h13_pos
    have h2 : θ2 - y ≠ 0 := by intro h; exact hy_ne (by linarith)
    have h3 : 0 < |θ2 - y| := abs_pos.mpr h2
    have h4 : |(θ3 - θ1) * (θ2 - y)| = |θ3 - θ1| * |θ2 - y| := by rw [abs_mul]
    rw [h4]
    exact mul_pos (abs_pos.mpr h1.ne') h3
  have h_num_bound : |(θ2 - θ3) * (y - θ1)| ≤ 1 := by
    have h1 : |θ2 - θ3| ≤ 1 := by
      rw [abs_of_pos (by linarith)] <;> linarith
    have h2 : |y - θ1| ≤ 1 := by
      have h21 : -1 ≤ y - θ1 := by linarith
      have h22 : y - θ1 ≤ 1 := by linarith
      rw [abs_le] <;> exact ⟨h21, h22⟩
    calc |(θ2 - θ3) * (y - θ1)| = |θ2 - θ3| * |y - θ1| := by rw [abs_mul]
      _ ≤ 1 * 1 := by gcongr <;> linarith
      _ = 1 := by ring
  have h_denom_lower : |(θ3 - θ1) * (θ2 - y)| ≥ δ^rho_sep * r := by
    calc |(θ3 - θ1) * (θ2 - y)| = |θ3 - θ1| * |θ2 - y| := by rw [abs_mul]
      _ = (θ3 - θ1) * |θ2 - y| := by rw [abs_of_pos h13_pos]
      _ ≥ δ^rho_sep * |θ2 - y| := by gcongr
      _ ≥ δ^rho_sep * r := by gcongr
  have h_main : |crossRatioMap θ1 θ2 θ3 y| ≤ 1 / (δ^rho_sep * r) := by
    simp only [crossRatioMap]
    rw [abs_div]
    have h3 : |(θ2 - θ3) * (y - θ1)| / |(θ3 - θ1) * (θ2 - y)| ≤
        1 / (δ^rho_sep * r) := by
      have h4 : |(θ2 - θ3) * (y - θ1)| / |(θ3 - θ1) * (θ2 - y)| ≤
          1 / |(θ3 - θ1) * (θ2 - y)| := by
        have hden_nonneg : 0 ≤ |(θ3 - θ1) * (θ2 - y)| := by positivity
        exact div_le_div_of_nonneg_right h_num_bound hden_nonneg
      have h5 : 1 / |(θ3 - θ1) * (θ2 - y)| ≤ 1 / (δ^rho_sep * r) := by
        apply one_div_le_one_div_of_le (by positivity) h_denom_lower
      exact le_trans h4 h5
    exact h3
  exact h_main

/-- Reciprocal difference identity. -/
lemma reciprocal_diff {θ1 θ2 θ3 y z : ℝ}
    (h13 : θ1 < θ3) (h23 : θ3 < θ2)
    (hy_ne : y ≠ θ2) (hz_ne : z ≠ θ2)
    (hy_ne_θ1 : y ≠ θ1) (hz_ne_θ1 : z ≠ θ1) :
    |1 / crossRatioMap θ1 θ2 θ3 y - 1 / crossRatioMap θ1 θ2 θ3 z| =
      ((θ3 - θ1) * (θ2 - θ1) / (θ2 - θ3)) * |y - z| / (|y - θ1| * |z - θ1|) := by
  set x : ℝ → ℝ := crossRatioMap θ1 θ2 θ3 with hx_def
  have h13' : θ3 - θ1 ≠ 0 := by linarith
  have h23' : θ2 - θ3 ≠ 0 := by linarith
  have hy2 : θ2 - y ≠ 0 := by intro h; exact hy_ne (by linarith)
  have hz2 : θ2 - z ≠ 0 := by intro h; exact hz_ne (by linarith)
  have hy1 : y - θ1 ≠ 0 := by intro h; exact hy_ne_θ1 (by linarith)
  have hz1 : z - θ1 ≠ 0 := by intro h; exact hz_ne_θ1 (by linarith)
  have hxy_def : x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)) := by
    simp [hx_def, crossRatioMap]
  have hxz_def : x z = ((θ2 - θ3) * (z - θ1)) / ((θ3 - θ1) * (θ2 - z)) := by
    simp [hx_def, crossRatioMap]
  have h_eq : 1 / x y - 1 / x z =
      -((θ3 - θ1) * (θ2 - θ1) / (θ2 - θ3)) * (y - z) / ((y - θ1) * (z - θ1)) := by
    rw [hxy_def, hxz_def]
    field_simp [h13', h23', hy2, hz2, hy1, hz1] <;> ring
  rw [h_eq]
  have h_pos : 0 < (θ3 - θ1) * (θ2 - θ1) / (θ2 - θ3) := by
    have h1 : 0 < θ3 - θ1 := by linarith
    have h2 : 0 < θ2 - θ1 := by linarith
    have h3 : 0 < θ2 - θ3 := by linarith
    exact div_pos (mul_pos h1 h2) h3
  have h_abs : |(-((θ3 - θ1) * (θ2 - θ1) / (θ2 - θ3))) * (y - z) / ((y - θ1) * (z - θ1))| =
      ((θ3 - θ1) * (θ2 - θ1) / (θ2 - θ3)) * |y - z| / (|y - θ1| * |z - θ1|) := by
    have h1 : |(-((θ3 - θ1) * (θ2 - θ1) / (θ2 - θ3))) * (y - z) / ((y - θ1) * (z - θ1))| =
        |(-((θ3 - θ1) * (θ2 - θ1) / (θ2 - θ3)))| * |y - z| / (|y - θ1| * |z - θ1|) := by
      rw [abs_div, abs_mul] <;> rw [abs_mul] <;> ring
    rw [h1]
    have h2 : |(-((θ3 - θ1) * (θ2 - θ1) / (θ2 - θ3)))| =
        (θ3 - θ1) * (θ2 - θ1) / (θ2 - θ3) := by
      rw [abs_neg, abs_of_pos h_pos]
    rw [h2] <;> ring
  exact h_abs

/-- Reciprocal co-Lipschitz. -/
lemma reciprocal_colipschitz {δ rho_sep θ1 θ2 θ3 y z : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h13 : θ1 < θ3) (h23 : θ3 < θ2)
    (hθ1_nonneg : 0 ≤ θ1) (hθ2_le_one : θ2 ≤ 1)
    (h_sep13 : θ3 - θ1 ≥ δ^rho_sep) (h_sep32 : θ2 - θ3 ≥ δ^rho_sep)
    (hrho_nonneg : 0 ≤ rho_sep)
    (hy_ne : y ≠ θ2) (hz_ne : z ≠ θ2)
    (hy_ne_θ1 : y ≠ θ1) (hz_ne_θ1 : z ≠ θ1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    |y - z| ≤ δ^(-2*rho_sep) *
      |1 / crossRatioMap θ1 θ2 θ3 y - 1 / crossRatioMap θ1 θ2 θ3 z| := by
  set C : ℝ := (θ3 - θ1) * (θ2 - θ1) / (θ2 - θ3) with hC_def
  set D : ℝ := |y - θ1| * |z - θ1| with hD_def
  have hD_pos : 0 < D := by
    simp only [hD_def]
    have h1 : y - θ1 ≠ 0 := by intro h; exact hy_ne_θ1 (by linarith)
    have h2 : z - θ1 ≠ 0 := by intro h; exact hz_ne_θ1 (by linarith)
    exact mul_pos (abs_pos.mpr h1) (abs_pos.mpr h2)
  have hD_le_one : D ≤ 1 := by
    simp only [hD_def]
    have hyb : |y - θ1| ≤ 1 := by rw [abs_le] <;> constructor <;> linarith
    have hzb : |z - θ1| ≤ 1 := by rw [abs_le] <;> constructor <;> linarith
    calc |y - θ1| * |z - θ1| ≤ 1 * 1 := mul_le_mul hyb hzb (by positivity) (by positivity)
      _ = 1 := by norm_num
  have hC_nonneg : 0 ≤ C := by
    rw [hC_def]
    have h1a : 0 < θ3 - θ1 := by linarith
    have h1b : 0 < θ2 - θ1 := by linarith
    have h1 : 0 ≤ (θ3 - θ1) * (θ2 - θ1) := mul_nonneg h1a.le h1b.le
    have h2 : 0 ≤ θ2 - θ3 := by linarith
    exact div_nonneg h1 h2
  have h_pos23 : 0 < θ2 - θ3 := by linarith
  have hC_ge : C ≥ δ^(2*rho_sep) := by
    rw [hC_def]
    have h_exp : δ^(2*rho_sep) = (δ^rho_sep) * (δ^rho_sep) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    rw [h_exp]
    have h1 : (θ3 - θ1) * (θ2 - θ1) ≥ (δ^rho_sep) * (δ^rho_sep) := by
      have h1a : δ^rho_sep ≤ θ3 - θ1 := h_sep13
      have h1b : δ^rho_sep ≤ θ2 - θ1 := by linarith
      have h1c : 0 ≤ δ^rho_sep := by positivity
      nlinarith
    have h2 : (δ^rho_sep) * (δ^rho_sep) * (θ2 - θ3) ≤ (θ3 - θ1) * (θ2 - θ1) := by
      have h2a : (δ^rho_sep) * (δ^rho_sep) * (θ2 - θ3) ≤ (δ^rho_sep) * (δ^rho_sep) := by
        have h2b : θ2 - θ3 ≤ 1 := by linarith
        have h2c : 0 ≤ (δ^rho_sep) * (δ^rho_sep) := by positivity
        nlinarith
      linarith
    have h3 : (θ3 - θ1) * (θ2 - θ1) / (θ2 - θ3) ≥ (δ^rho_sep) * (δ^rho_sep) := by
      calc (θ3 - θ1) * (θ2 - θ1) / (θ2 - θ3)
        ≥ ((δ^rho_sep) * (δ^rho_sep) * (θ2 - θ3)) / (θ2 - θ3) := by gcongr
      _ = (δ^rho_sep) * (δ^rho_sep) := by
        field_simp [h_pos23.ne'] <;> ring
    exact h3
  have hCD_ge : C / D ≥ C := by
    have h5 : 1 / D ≥ 1 := by
      calc 1 / D ≥ 1 / (1 : ℝ) := one_div_le_one_div_of_le (by positivity) hD_le_one
           _ = 1 := by norm_num
    have h6 : C / D = C * (1 / D) := by ring
    rw [h6]
    have h7 : C * (1 / D) ≥ C := by
      have h8 : 0 ≤ C := hC_nonneg
      nlinarith
    exact h7
  have h8 : C / D ≥ δ^(2*rho_sep) := le_trans hC_ge hCD_ge
  have h_abs_eq := reciprocal_diff h13 h23 hy_ne hz_ne hy_ne_θ1 hz_ne_θ1
  rw [h_abs_eq]
  by_cases h_yz : |y - z| = 0
  · rw [h_yz]; simp
  · have h9 : δ^(2*rho_sep) * |y - z| ≤ (C / D) * |y - z| := by
      exact mul_le_mul_of_nonneg_right h8 (by positivity)
    have h10 : (C / D) * |y - z| = C * |y - z| / D := by ring
    rw [h10] at h9
    have h11 : δ^(-2*rho_sep) * (C * |y - z| / D) ≥ |y - z| := by
      have h12 : δ^(-2*rho_sep) * δ^(2*rho_sep) = 1 := by
        have h13 : δ^(-2*rho_sep) * δ^(2*rho_sep) = δ^((-2*rho_sep) + (2*rho_sep)) := by
          rw [← Real.rpow_add hδ_pos]
        rw [h13]
        have h14 : (-2*rho_sep) + (2*rho_sep) = 0 := by ring
        rw [h14] <;> simp
      have h15 : δ^(-2*rho_sep) * (δ^(2*rho_sep) * |y - z|) = |y - z| := by
        rw [← mul_assoc, h12, one_mul]
      have h16 : δ^(-2*rho_sep) * (δ^(2*rho_sep) * |y - z|) ≤ δ^(-2*rho_sep) * (C * |y - z| / D) := by
        have h17 : 0 ≤ δ^(-2*rho_sep) := by positivity
        nlinarith
      rw [h15] at h16
      exact h16
    exact h11

/-- Co-Lipschitz of sectorTMap i ∘ crossRatioMap, restricted to sectorPredicate i. -/
lemma sector_colipschitz {δ rho_sep θ1 θ2 θ3 y z : ℝ} {i : Fin 4}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (h13 : θ1 < θ3) (h23 : θ3 < θ2)
    (hθ1_nonneg : 0 ≤ θ1) (hθ2_le_one : θ2 ≤ 1)
    (h_sep13 : θ3 - θ1 ≥ δ^rho_sep) (h_sep32 : θ2 - θ3 ≥ δ^rho_sep)
    (hrho_nonneg : 0 ≤ rho_sep)
    (hy_ne : y ≠ θ2) (hz_ne : z ≠ θ2)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hz0 : 0 ≤ z) (hz1 : z ≤ 1)
    (h_sector_y : sectorPredicate i (crossRatioMap θ1 θ2 θ3) y)
    (h_sector_z : sectorPredicate i (crossRatioMap θ1 θ2 θ3) z) :
    |y - z| ≤ δ^(-2*rho_sep) *
      |sectorTMap i (crossRatioMap θ1 θ2 θ3 y) - sectorTMap i (crossRatioMap θ1 θ2 θ3 z)| := by
  set x : ℝ → ℝ := crossRatioMap θ1 θ2 θ3 with hx_def
  fin_cases i
  · -- i = 0
    simp only [sectorTMap]
    exact crossRatio_colipschitz hδ_pos hδ_le_one h13 h23 hθ1_nonneg hθ2_le_one
      h_sep13 h_sep32 hrho_nonneg hy_ne hz_ne hy0 hy1 hz0 hz1
  · -- i = 1
    have hxy_pos : 0 < x y := by
      have h1 : 1 < x y := by simpa [sectorPredicate] using h_sector_y
      linarith
    have hxz_pos : 0 < x z := by
      have h1 : 1 < x z := by simpa [sectorPredicate] using h_sector_z
      linarith
    have hy_ne_θ1 : y ≠ θ1 := by
      intro h; rw [h] at hxy_pos; simp [hx_def, crossRatioMap] at hxy_pos <;> linarith
    have hz_ne_θ1 : z ≠ θ1 := by
      intro h; rw [h] at hxz_pos; simp [hx_def, crossRatioMap] at hxz_pos <;> linarith
    simp only [sectorTMap]
    exact reciprocal_colipschitz hδ_pos hδ_le_one h13 h23 hθ1_nonneg hθ2_le_one
      h_sep13 h_sep32 hrho_nonneg hy_ne hz_ne hy_ne_θ1 hz_ne_θ1 hy0 hy1 hz0 hz1
  · -- i = 2
    simp only [sectorTMap]
    have h_abs : |-(x y) - (-(x z))| = |x y - x z| := by
      have h' : -(x y) - (-(x z)) = -(x y - x z) := by ring
      rw [h', abs_neg]
    rw [h_abs]
    exact crossRatio_colipschitz hδ_pos hδ_le_one h13 h23 hθ1_nonneg hθ2_le_one
      h_sep13 h_sep32 hrho_nonneg hy_ne hz_ne hy0 hy1 hz0 hz1
  · -- i = 3
    have hxy_neg : x y < -1 := by simpa [sectorPredicate] using h_sector_y
    have hxz_neg : x z < -1 := by simpa [sectorPredicate] using h_sector_z
    have hy_ne_θ1 : y ≠ θ1 := by
      intro h; rw [h] at hxy_neg; simp [hx_def, crossRatioMap] at hxy_neg <;> linarith
    have hz_ne_θ1 : z ≠ θ1 := by
      intro h; rw [h] at hxz_neg; simp [hx_def, crossRatioMap] at hxz_neg <;> linarith
    simp only [sectorTMap]
    have h_abs : |(-1 / x y) - (-1 / x z)| = |1 / x y - 1 / x z| := by
      have h' : (-1 / x y) - (-1 / x z) = -(1 / x y - 1 / x z) := by ring
      rw [h', abs_neg]
    rw [h_abs]
    exact reciprocal_colipschitz hδ_pos hδ_le_one h13 h23 hθ1_nonneg hθ2_le_one
      h_sep13 h_sep32 hrho_nonneg hy_ne hz_ne hy_ne_θ1 hz_ne_θ1 hy0 hy1 hz0 hz1

end ProductLikeIncidence.ProductReduction
