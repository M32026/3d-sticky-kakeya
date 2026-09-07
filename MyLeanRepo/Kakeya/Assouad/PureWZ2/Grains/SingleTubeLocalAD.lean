import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalSliceGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SmallDiameterAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADBridge
import Mathlib.Tactic

/-!
# Single-tube local AD

Constructs local AD for a single-tube configuration using a constant
perpendicular plane map.

## Key insight

For a single tube with direction `d` and a unit vector `v` perpendicular to `d`,
the scalar projection of the paper tube carrier onto `v` has diameter at most
`14δ`. This is because the projection of the axis line is a single point, and
the `6δ`-thickening contributes at most `7δ` on each side.

With diameter `14δ`, the covering number at any scale `rho ≥ δ` is at most
`14δ/rho + 2 ≤ 16`, so any constant `C ≥ 16` suffices for the AD bound — no
`loss_src > σ/2` condition is needed.
-/

noncomputable section

namespace Kakeya.Assouad

open Classical Metric Set

attribute [local instance] Classical.propDecidable

/-- The projection of a paper tube onto a perpendicular direction has diameter
at most `14δ`. -/
lemma tube_projection_perpendicular_diameter
    {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ)
    (v : Point3)
    (hv_unit : ‖v‖ = 1)
    (hv_perp : inner ℝ T.direction v = 0) :
    ∀ (x y : ℝ), x ∈ scalarProjection v (wz1PaperTubeCarrier T) →
      y ∈ scalarProjection v (wz1PaperTubeCarrier T) → |x - y| ≤ 14 * δ := by
  intro x y hx hy
  rcases hx with ⟨p, hp, rfl⟩
  rcases hy with ⟨q, hq, rfl⟩
  have hp_inf : Metric.infEDist p (tubeAxisLine T) ≤ ENNReal.ofReal (6 * δ) := by
    have h : p ∈ Metric.cthickening (6 * δ) (tubeAxisLine T) := hp.1
    rw [Metric.cthickening_eq_preimage_infEDist] at h
    exact h
  have hq_inf : Metric.infEDist q (tubeAxisLine T) ≤ ENNReal.ofReal (6 * δ) := by
    have h : q ∈ Metric.cthickening (6 * δ) (tubeAxisLine T) := hq.1
    rw [Metric.cthickening_eq_preimage_infEDist] at h
    exact h
  have h_pos7 : 0 < (7 * δ : ℝ) := by linarith
  have h67 : ENNReal.ofReal (6 * δ) < ENNReal.ofReal (7 * δ) :=
    ENNReal.ofReal_lt_ofReal_iff h_pos7 |>.mpr (by linarith)
  have hp_lt : Metric.infEDist p (tubeAxisLine T) < ENNReal.ofReal (7 * δ) :=
    hp_inf.trans_lt h67
  have hq_lt : Metric.infEDist q (tubeAxisLine T) < ENNReal.ofReal (7 * δ) :=
    hq_inf.trans_lt h67
  rcases tube_axis_exists_point T p h_pos7 hp_lt with ⟨p_axis, hp_line, hp_dist⟩
  rcases tube_axis_exists_point T q h_pos7 hq_lt with ⟨q_axis, hq_line, hq_dist⟩
  rcases hp_line with ⟨tp, hp_eq⟩
  rcases hq_line with ⟨tq, hq_eq⟩
  let p_axis' := T.base + tp • T.direction
  let q_axis' := T.base + tq • T.direction
  have hp_axis_eq : p_axis = p_axis' := by simpa [p_axis'] using hp_eq
  have hq_axis_eq : q_axis = q_axis' := by simpa [q_axis'] using hq_eq
  have h_inner_axis : inner ℝ p_axis' v = inner ℝ q_axis' v := by
    have h2 : p_axis' - q_axis' = (tp - tq) • T.direction := by
      ext i
      simp [p_axis', q_axis', Pi.add_apply, Pi.smul_apply] <;> ring
    have h : inner ℝ (p_axis' - q_axis') v = 0 := by
      rw [h2, inner_smul_left, hv_perp] <;> ring
    have h3 : inner ℝ p_axis' v - inner ℝ q_axis' v = inner ℝ (p_axis' - q_axis') v := by
      rw [inner_sub_left]
    linarith
  have h1 : |inner ℝ p v - inner ℝ p_axis' v| ≤ 7 * δ := by
    have h4 : |inner ℝ p v - inner ℝ p_axis' v| ≤ ‖p - p_axis'‖ * ‖v‖ := by
      have h5 : inner ℝ p v - inner ℝ p_axis' v = inner ℝ (p - p_axis') v := by
        rw [inner_sub_left]
      rw [h5]
      exact abs_real_inner_le_norm _ _
    rw [hv_unit] at h4
    have h6 : ‖p - p_axis'‖ < 7 * δ := by
      rw [hp_axis_eq] at hp_dist
      simpa [dist_eq_norm] using hp_dist
    linarith
  have h2 : |inner ℝ q v - inner ℝ q_axis' v| ≤ 7 * δ := by
    have h4 : |inner ℝ q v - inner ℝ q_axis' v| ≤ ‖q - q_axis'‖ * ‖v‖ := by
      have h5 : inner ℝ q v - inner ℝ q_axis' v = inner ℝ (q - q_axis') v := by
        rw [inner_sub_left]
      rw [h5]
      exact abs_real_inner_le_norm _ _
    rw [hv_unit] at h4
    have h6 : ‖q - q_axis'‖ < 7 * δ := by
      rw [hq_axis_eq] at hq_dist
      simpa [dist_eq_norm] using hq_dist
    linarith
  have h3 : inner ℝ p v - inner ℝ q v =
      (inner ℝ p v - inner ℝ p_axis' v) + (inner ℝ p_axis' v - inner ℝ q_axis' v) +
      (inner ℝ q_axis' v - inner ℝ q v) := by ring
  rw [h3]
  have h_mid : inner ℝ p_axis' v - inner ℝ q_axis' v = 0 := by
    rw [h_inner_axis] <;> ring
  have h_simp : (inner ℝ p v - inner ℝ p_axis' v) + (inner ℝ p_axis' v - inner ℝ q_axis' v) +
      (inner ℝ q_axis' v - inner ℝ q v) =
      (inner ℝ p v - inner ℝ p_axis' v) + (inner ℝ q_axis' v - inner ℝ q v) := by
    rw [h_mid] <;> ring
  rw [h_simp]
  have h_tri : |(inner ℝ p v - inner ℝ p_axis' v) + (inner ℝ q_axis' v - inner ℝ q v)| ≤
      |inner ℝ p v - inner ℝ p_axis' v| + |inner ℝ q_axis' v - inner ℝ q v| := by
    exact abs_add_le _ _
  have h_abs : |inner ℝ q_axis' v - inner ℝ q v| = |inner ℝ q v - inner ℝ q_axis' v| := by
    rw [abs_sub_comm]
  rw [h_abs] at h_tri
  linarith [h1, h2, h_tri]

/-- A set of diameter at most `K * δ'` satisfies the paper AD condition at any
scale `rho0 ≥ δ'` with any constant `C ≥ K + 2`. -/
lemma bounded_diameter_ad_simple
    {E : Set ℝ} {delta' rho0 alpha : ℝ} {C : ENNReal}
    (K : ℝ) (hK_pos : 0 < K)
    (hdelta'_pos : 0 < delta')
    (hrho0_pos : 0 < rho0)
    (hrho0_ge_delta' : delta' ≤ rho0)
    (halpha_pos : 0 < alpha)
    (halpha_le_one : alpha ≤ 1)
    (hC_ge : ENNReal.ofReal (K + 2) ≤ C)
    (hC_top : C ≠ ⊤)
    (hE_diam : ∀ (x y : ℝ), x ∈ E → y ∈ E → |x - y| ≤ K * delta') :
    PureWZ2PaperADSet1 E rho0 alpha C := by
  have h1 : 0 < rho0 := hrho0_pos
  have h2 : 0 < alpha := halpha_pos
  have h3 : alpha ≤ 1 := halpha_le_one
  have hK2_pos : 0 < K + 2 := by linarith
  have h4 : (1 : ENNReal) ≤ C := by
    have h : (1 : ℝ) ≤ K + 2 := by linarith
    have h41 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (K + 2) := ENNReal.ofReal_le_ofReal h
    have h42 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by norm_cast
    rw [h42]
    exact h41.trans hC_ge
  have h5 : C ≠ ⊤ := hC_top
  refine' ⟨h1, h2, h3, h4, h5, _⟩
  intro rho hrho hrho_ge left length hlength
  set T : Set ℝ := E ∩ Set.Icc left (left + length) with hT_def
  have hrho_pos : 0 < rho := by linarith
  have hT_diam : ∀ (x y : ℝ), x ∈ T → y ∈ T → |x - y| ≤ K * delta' := by
    intro x y hx hy
    exact hE_diam x y hx.1 hy.1
  set D : ℝ := K * delta' with hD_def
  have hD_nonneg : 0 ≤ D := by positivity
  rcases set_of_diam_subset_interval hD_nonneg hT_diam with ⟨a, hT_sub⟩
  have hcov : (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩ T) : ENNReal) ≤
      ENNReal.ofReal (D / rho) + (2 : ENNReal) := by
    have h := externalCoveringNumber_subset_interval hrho_pos hD_nonneg hT_sub
    simpa using h
  have hD_div : D / rho ≤ K := by
    have h11 : delta' ≤ rho := by linarith
    have h12 : 0 < rho := by linarith
    have h13 : D / rho = (K * delta') / rho := by rfl
    rw [h13]
    have h14 : (K * delta') / rho ≤ (K * rho) / rho := by gcongr
    have h15 : (K * rho) / rho = K := by
      field_simp [h12.ne'] <;> ring
    rw [h15] at h14
    exact h14
  have h6 : ENNReal.ofReal (D / rho) ≤ ENNReal.ofReal K :=
    ENNReal.ofReal_le_ofReal hD_div
  have h7 : ENNReal.ofReal (D / rho) + (2 : ENNReal) ≤ ENNReal.ofReal K + (2 : ENNReal) := by
    gcongr
  have h9 : ENNReal.ofReal K + (2 : ENNReal) = ENNReal.ofReal (K + 2) := by
    have h10 : ENNReal.ofReal K + (2 : ENNReal) = ENNReal.ofReal (K + 2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)] <;> norm_cast
    simpa using h10
  rw [h9] at h7
  have h10 : (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩ T) : ENNReal) ≤ ENNReal.ofReal (K + 2) :=
    hcov.trans h7
  have h11 : 1 ≤ length / rho := by
    have h12 : 0 < rho := by linarith
    calc 1 = rho / rho := by field_simp [h12.ne'] <;> ring
      _ ≤ length / rho := by gcongr
  have h12 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / rho) alpha := by
    have h13 : 0 ≤ alpha := by linarith
    have h14 : (1 : ℝ) ≤ (length / rho) ^ alpha := Real.one_le_rpow h11 h13
    simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal h14
  have h15 : ENNReal.ofReal (K + 2) ≤ C * (1 : ENNReal) := by
    simpa using hC_ge
  have h16 : C * (1 : ENNReal) ≤ C * Kakeya.realRpowENN (length / rho) alpha := by
    gcongr <;> exact h12
  exact h10.trans (h15.trans h16)

end Kakeya.Assouad

end
