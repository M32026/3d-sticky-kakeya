import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.ScaleInterpolation

/-!
# Frostman scale interpolation

Volume ratio estimates for interpolating density control between grid scales.

## Key results

`density_ratio_upper_bound`: If `ρ_k ≤ ρ`, then for any measurable set `K`,
`|K| / |T_ρ| ≤ |K| / |T_{ρ_k}|`.

`density_ratio_lower_bound`: If `ρ_k ≤ ρ ≤ ρ_{k-1}` and `ρ_{k-1} ≤ A * ρ_k`,
then `|K| / |T_{ρ_k}| ≤ C_vol(A) * |K| / |T_ρ|`.
-/

noncomputable section

open Kakeya.Streamlined MeasureTheory

namespace Kakeya.Streamlined.RandomTranslation

/-- If `ρ_k ≤ ρ`, then `|T_ρ| ≥ |T_{ρ_k}|`, so for any `K`:
`|K| / |T_ρ| ≤ |K| / |T_{ρ_k}|`. -/
lemma density_ratio_upper_bound
    {ρ ρ_k : ℝ} (_hρk_pos : 0 < ρ_k) (h_order : ρ_k ≤ ρ)
    (K : Set Point3) :
    MeasureTheory.volume K / Kakeya.deltaTubeVolume ρ ≤
      MeasureTheory.volume K / Kakeya.deltaTubeVolume ρ_k := by
  have h1 : Kakeya.deltaTubeVolume ρ_k ≤ Kakeya.deltaTubeVolume ρ :=
    deltaTubeVolume_mono h_order
  gcongr

/-- Helper: `deltaTubeVolume r` is nonzero for `r > 0`. -/
private lemma deltaTubeVolume_ne_zero {r : ℝ} (hr : 0 < r) :
    Kakeya.deltaTubeVolume r ≠ 0 := by
  have h_lower : ENNReal.ofReal (2 * r ^ 2) ≤ Kakeya.deltaTubeVolume r :=
    deltaTubeVolume_lower_bound hr
  have h_pos : (0 : ENNReal) < ENNReal.ofReal (2 * r ^ 2) := by
    have h2 : 0 < 2 * r ^ 2 := by positivity
    exact ENNReal.ofReal_pos.mpr h2
  have h3 : (0 : ENNReal) < Kakeya.deltaTubeVolume r :=
    lt_of_lt_of_le h_pos h_lower
  exact ne_of_gt h3

/-- Helper: `deltaTubeVolume r` is finite for `0 < r ≤ 1`. -/
private lemma deltaTubeVolume_ne_top {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    Kakeya.deltaTubeVolume r ≠ ⊤ := by
  have h_upper : Kakeya.deltaTubeVolume r ≤
      ENNReal.ofReal ((Real.pi + 8 / 3 * Real.pi) * r ^ 2) :=
    deltaTubeVolume_upper_bound hr hr1
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_upper

/-- If `ρ_k ≤ ρ ≤ ρ_{k-1} ≤ A * ρ_k` with `0 < ρ_k` and `ρ_{k-1} ≤ 1`, then
`|K| / |T_{ρ_k}| ≤ C_vol(A) * |K| / |T_ρ|`. -/
lemma density_ratio_lower_bound
    {ρ ρ_k ρ_km1 A : ℝ}
    (hρk_pos : 0 < ρ_k) (hρ_pos : 0 < ρ)
    (h_order1 : ρ_k ≤ ρ) (h_order2 : ρ ≤ ρ_km1)
    (h_ratio : ρ_km1 ≤ A * ρ_k) (hA_pos : 0 < A)
    (hρkm1_le_one : ρ_km1 ≤ 1)
    (K : Set Point3) :
    MeasureTheory.volume K / Kakeya.deltaTubeVolume ρ_k ≤
      ENNReal.ofReal (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2) *
      (MeasureTheory.volume K / Kakeya.deltaTubeVolume ρ) := by
  set C_vol : ENNReal :=
    ENNReal.ofReal (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2) with hC_vol
  have hρ_le_one : ρ ≤ 1 := le_trans h_order2 hρkm1_le_one
  have h_order12 : ρ_k ≤ ρ_km1 := le_trans h_order1 h_order2
  have h_vol_km1_le : Kakeya.deltaTubeVolume ρ_km1 ≤
      C_vol * Kakeya.deltaTubeVolume ρ_k :=
    deltaTubeVolume_ratio_bound hρk_pos (by linarith) h_order12 h_ratio hA_pos hρkm1_le_one
  have h_vol_ρ_le : Kakeya.deltaTubeVolume ρ ≤ C_vol * Kakeya.deltaTubeVolume ρ_k :=
    le_trans (deltaTubeVolume_mono h_order2) h_vol_km1_le
  have hρk_vol_ne_zero : Kakeya.deltaTubeVolume ρ_k ≠ 0 :=
    deltaTubeVolume_ne_zero hρk_pos
  have hρk_vol_ne_top : Kakeya.deltaTubeVolume ρ_k ≠ ⊤ :=
    deltaTubeVolume_ne_top hρk_pos (le_trans h_order1 hρ_le_one)
  have hρ_vol_ne_zero : Kakeya.deltaTubeVolume ρ ≠ 0 :=
    deltaTubeVolume_ne_zero hρ_pos
  have hρ_vol_ne_top : Kakeya.deltaTubeVolume ρ ≠ ⊤ :=
    deltaTubeVolume_ne_top hρ_pos hρ_le_one
  have hC_vol_pos : 0 < C_vol := by
    simp [hC_vol]
    positivity
  have hC_vol_ne_zero : C_vol ≠ 0 := hC_vol_pos.ne'
  have hC_vol_ne_top : C_vol ≠ ⊤ := by
    have h : C_vol = ENNReal.ofReal (((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2) := hC_vol
    rw [h]
    exact ENNReal.ofReal_ne_top
  set v : ENNReal := MeasureTheory.volume K with hv
  set a : ENNReal := Kakeya.deltaTubeVolume ρ with ha
  set b : ENNReal := Kakeya.deltaTubeVolume ρ_k with hb
  have h_a_le : a ≤ C_vol * b := h_vol_ρ_le
  have ha0 : a ≠ 0 := hρ_vol_ne_zero
  have ha1 : a ≠ ⊤ := hρ_vol_ne_top
  have hb0 : b ≠ 0 := hρk_vol_ne_zero
  have hb1 : b ≠ ⊤ := hρk_vol_ne_top
  have hc0 : C_vol ≠ 0 := hC_vol_ne_zero
  have hc1 : C_vol ≠ ⊤ := hC_vol_ne_top
  -- a ≤ C * b  →  a⁻¹ ≥ (C*b)⁻¹ = C⁻¹ * b⁻¹
  have h_inv1 : a⁻¹ ≥ (C_vol * b)⁻¹ := by
    exact ENNReal.inv_le_inv.mpr h_a_le
  have h_inv2 : (C_vol * b)⁻¹ = C_vol⁻¹ * b⁻¹ := by
    rw [ENNReal.mul_inv] <;> simp [hc0, hb0]
  have h_inv3 : a⁻¹ ≥ C_vol⁻¹ * b⁻¹ := by
    rw [h_inv2] at h_inv1; exact h_inv1
  -- v * a⁻¹ ≥ v * (C⁻¹ * b⁻¹)
  have h4 : v * a⁻¹ ≥ v * (C_vol⁻¹ * b⁻¹) := by
    gcongr
  -- C * (v * a⁻¹) ≥ C * (v * (C⁻¹ * b⁻¹)) = v * b⁻¹
  have h5 : C_vol * (v * a⁻¹) ≥ C_vol * (v * (C_vol⁻¹ * b⁻¹)) := by
    gcongr
  have h6 : C_vol * (v * (C_vol⁻¹ * b⁻¹)) = v * b⁻¹ := by
    have h7 : C_vol * C_vol⁻¹ = 1 := by
      rw [ENNReal.mul_inv_cancel hc0 hc1]
    calc
      C_vol * (v * (C_vol⁻¹ * b⁻¹))
        = C_vol * C_vol⁻¹ * (v * b⁻¹) := by ring
      _ = 1 * (v * b⁻¹) := by rw [h7]
      _ = v * b⁻¹ := by ring
  have h8 : C_vol * (v * a⁻¹) ≥ v * b⁻¹ := by
    calc
      C_vol * (v * a⁻¹) ≥ C_vol * (v * (C_vol⁻¹ * b⁻¹)) := h5
      _ = v * b⁻¹ := h6
  -- Rewrite divisions as v * a⁻¹ and v * b⁻¹
  have h9 : v / a = v * a⁻¹ := by
    exact div_eq_mul_inv v a
  have h10 : v / b = v * b⁻¹ := by
    exact div_eq_mul_inv v b
  rw [h10, h9]
  exact h8

end Kakeya.Streamlined.RandomTranslation

end
