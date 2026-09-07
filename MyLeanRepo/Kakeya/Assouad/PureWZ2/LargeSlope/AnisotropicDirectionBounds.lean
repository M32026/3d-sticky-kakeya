import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2Statements
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredRescalingGeometry
import Mathlib.Tactic

/-!
# Direction ratio bounds for anisotropic rescaling

Given a source direction `d` with `‖d‖ = 1` and `|d 2| ≥ 1/2`,
and anisotropic parameters `g_mid`, `K`, `S` with:
- `|g_mid| ≤ 1`
- `|K| ≤ 1/50`
- `S ≥ 50`

The rescaled direction `d' = normalize(DPhi(d))` satisfies:
- `|d' 0 / d' 2| ≤ 2/25`
- `|d' 1 / d' 2| ≤ 1/1250`

where `DPhi(v) = (v 0 + g_mid * v 1, K * v 1, S * v 2)`.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Direction ratio bounds for anisotropic rescaling. -/
lemma anisotropic_direction_ratio_bounds
    {g_mid K S : ℝ}
    (hg : |g_mid| ≤ 1)
    (hK : |K| ≤ 1 / 50)
    (hS : 50 ≤ S)
    {d : Point3}
    (hd_unit : ‖d‖ = 1)
    (hd_z : 1 / 2 ≤ |d 2|) :
    let DPhi : Point3 → Point3 := fun v =>
      point3 (v 0 + g_mid * v 1) (K * v 1) (S * v 2)
    let d' : Point3 := (‖DPhi d‖⁻¹ : ℝ) • DPhi d
    |d' 0 / d' 2| ≤ 2 / 25 ∧ |d' 1 / d' 2| ≤ 1 / 1250 := by
  let DPhi : Point3 → Point3 := fun v =>
    point3 (v 0 + g_mid * v 1) (K * v 1) (S * v 2)
  let Ad : Point3 := DPhi d

  have h_d0 : |d 0| ≤ 1 := by
    have hsq : ‖d‖ ^ 2 = (d 0)^2 + (d 1)^2 + (d 2)^2 := point3_coord_norm_sq d
    have h4 : (d 0)^2 ≤ ‖d‖ ^ 2 := by rw [hsq] <;> nlinarith
    have h5 : |d 0| ^ 2 = (d 0)^2 := by simp [sq_abs]
    have h6 : |d 0| ^ 2 ≤ ‖d‖ ^ 2 := by rw [h5]; exact h4
    have h7 : 0 ≤ |d 0| := abs_nonneg _
    have h8 : 0 ≤ ‖d‖ := by positivity
    have h9 : |d 0| ≤ ‖d‖ := by nlinarith
    rw [hd_unit] at h9
    exact h9
  have h_d1 : |d 1| ≤ 1 := by
    have hsq : ‖d‖ ^ 2 = (d 0)^2 + (d 1)^2 + (d 2)^2 := point3_coord_norm_sq d
    have h4 : (d 1)^2 ≤ ‖d‖ ^ 2 := by rw [hsq] <;> nlinarith
    have h5 : |d 1| ^ 2 = (d 1)^2 := by simp [sq_abs]
    have h6 : |d 1| ^ 2 ≤ ‖d‖ ^ 2 := by rw [h5]; exact h4
    have h7 : 0 ≤ |d 1| := abs_nonneg _
    have h8 : 0 ≤ ‖d‖ := by positivity
    have h9 : |d 1| ≤ ‖d‖ := by nlinarith
    rw [hd_unit] at h9
    exact h9

  have hAd_x : |Ad 0| ≤ 2 := by
    have h1 : Ad 0 = d 0 + g_mid * d 1 := by simp [Ad, DPhi, point3] <;> ring
    rw [h1]
    calc |d 0 + g_mid * d 1|
      ≤ |d 0| + |g_mid * d 1| := abs_add_le _ _
    _ = |d 0| + |g_mid| * |d 1| := by rw [abs_mul] <;> ring
    _ ≤ 1 + 1 * 1 := by gcongr <;> linarith
    _ = 2 := by norm_num

  have hAd_y : |Ad 1| ≤ 1 / 50 := by
    have h1 : Ad 1 = K * d 1 := by simp [Ad, DPhi, point3] <;> ring
    rw [h1]
    have h2 : |K * d 1| = |K| * |d 1| := by rw [abs_mul]
    rw [h2]
    have h3 : |K| * |d 1| ≤ (1 / 50 : ℝ) := by
      calc |K| * |d 1| ≤ (1 / 50 : ℝ) * 1 := by gcongr <;> linarith
        _ = 1 / 50 := by norm_num
    exact h3

  have hAd_z : |Ad 2| ≥ 25 := by
    have h1 : Ad 2 = S * d 2 := by simp [Ad, DPhi, point3] <;> ring
    rw [h1]
    have h2 : |S * d 2| = |S| * |d 2| := by rw [abs_mul]
    rw [h2]
    have h3 : |S| = S := by rw [abs_of_nonneg] <;> linarith
    rw [h3]
    have h4 : S * |d 2| ≥ 50 * (1 / 2 : ℝ) := by
      gcongr
      <;> linarith
    have h5 : 50 * (1 / 2 : ℝ) = 25 := by norm_num
    linarith

  have hAd_z_ne : Ad 2 ≠ 0 := by
    intro h
    have h9 : |Ad 2| = 0 := by rw [h] <;> simp
    rw [h9] at hAd_z
    norm_num at hAd_z

  have h_norm_pos : 0 < ‖Ad‖ := by
    have h : Ad ≠ 0 := by
      intro h0
      have h9 : Ad 2 = 0 := by rw [h0] <;> simp
      exact hAd_z_ne h9
    exact norm_pos_iff.mpr h

  let d' : Point3 := (‖Ad‖⁻¹ : ℝ) • Ad

  have h_ratio_x : |d' 0 / d' 2| = |Ad 0 / Ad 2| := by
    have h1 : d' 0 = (‖Ad‖⁻¹ : ℝ) * Ad 0 := by simp [d'] <;> ring
    have h2 : d' 2 = (‖Ad‖⁻¹ : ℝ) * Ad 2 := by simp [d'] <;> ring
    rw [h1, h2]
    have h3 : ((‖Ad‖⁻¹ : ℝ) * Ad 0) / ((‖Ad‖⁻¹ : ℝ) * Ad 2) = Ad 0 / Ad 2 := by
      field_simp [hAd_z_ne, h_norm_pos.ne'] <;> ring
    rw [h3]

  have h_ratio_y : |d' 1 / d' 2| = |Ad 1 / Ad 2| := by
    have h1 : d' 1 = (‖Ad‖⁻¹ : ℝ) * Ad 1 := by simp [d'] <;> ring
    have h2 : d' 2 = (‖Ad‖⁻¹ : ℝ) * Ad 2 := by simp [d'] <;> ring
    rw [h1, h2]
    have h3 : ((‖Ad‖⁻¹ : ℝ) * Ad 1) / ((‖Ad‖⁻¹ : ℝ) * Ad 2) = Ad 1 / Ad 2 := by
      field_simp [hAd_z_ne, h_norm_pos.ne'] <;> ring
    rw [h3]

  have h_bound_x : |Ad 0 / Ad 2| ≤ 2 / 25 := by
    have h4 : |Ad 0 / Ad 2| = |Ad 0| / |Ad 2| := by rw [abs_div]
    rw [h4]
    have h5 : 0 < |Ad 2| := by linarith [hAd_z]
    have h6 : |Ad 0| / |Ad 2| ≤ 2 / |Ad 2| := by gcongr
    have h7 : 2 / |Ad 2| ≤ 2 / 25 := by
      gcongr
      <;> linarith [hAd_z]
    exact h6.trans h7

  have h_bound_y : |Ad 1 / Ad 2| ≤ 1 / 1250 := by
    have h4 : |Ad 1 / Ad 2| = |Ad 1| / |Ad 2| := by rw [abs_div]
    rw [h4]
    have h5 : 0 < |Ad 2| := by linarith [hAd_z]
    have h6 : |Ad 1| / |Ad 2| ≤ (1 / 50 : ℝ) / |Ad 2| := by gcongr
    have h7 : (1 / 50 : ℝ) / |Ad 2| ≤ (1 / 50 : ℝ) / 25 := by
      gcongr
      <;> linarith [hAd_z]
    have h8 : (1 / 50 : ℝ) / 25 = 1 / 1250 := by norm_num
    rw [h8] at h7
    exact h6.trans h7

  have h_main : |d' 0 / d' 2| ≤ 2 / 25 ∧ |d' 1 / d' 2| ≤ 1 / 1250 := by
    constructor
    · rw [h_ratio_x]; exact h_bound_x
    · rw [h_ratio_y]; exact h_bound_y
  exact h_main

end Kakeya.Assouad

end
