import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledTube
import MyLeanRepo.Kakeya.Assouad.WZ1.DirectionInnerProductBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ContainmentNoLineClass
import Mathlib.Tactic

/-!
# Centered literal WZ rescaling for unit-ball containment

The standard `wz2PaperLiteralUnitRescalingMap` translates by
`wz1TubeAxisZeroPoint` (the z=0 plane intersection), which can be far from
the anchor segment.  This module defines a centered variant that translates
by the anchor midpoint instead, ensuring the rescaled target tube lies in
the unit ball when `δ/ρ` is sufficiently small.

The linear part is identical, so direction bounds and carrier-subset proofs
transfer directly.

## Main results

- `wz2PaperCenteredLiteralRescalingMap`: centered affine map
- `wz2PaperCenteredLiteralOrdinaryRescaledTube`: target tube centered at the
  image of the source midpoint under the centered map
- `centered_midpoint_image_norm_le`: ‖centeredMap(sourceMidpoint)‖ ≤ 1/80
- `centered_target_unit_ball`: target carrier ⊆ unit ball when δ/ρ ≤ 39/80
- `centered_image_carrier_subset`: literal image ⊆ centered target carrier
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set InnerProductGeometry

attribute [local instance] Classical.propDecidable

/-- Norm squared decomposition for the literal rescaling linear map.

For arbitrary `v`, decompose `v = vpar + vperp` relative to `e'`.
Then `‖linear(v)‖^2 = (1/100)^2 * (inner(v,e')^2 + ‖vperp‖^2 / ρ^2)`. -/
lemma centered_linear_norm_sq
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho) (v : Point3) :
    ‖wz2PaperLiteralUnitRescalingLinear anchor v‖ ^ 2 =
      (1 / 100 : ℝ) ^ 2 *
        ((inner ℝ v (wz1PaperDirection anchor)) ^ 2 +
          ‖v - inner ℝ v (wz1PaperDirection anchor) • (wz1PaperDirection anchor)‖ ^ 2 / rho ^ 2) := by
  set e' : Point3 := wz1PaperDirection anchor with he'_def
  have he'_unit : ‖e'‖ = 1 := wz1PaperDirection_norm anchor
  set qv : ℝ := inner ℝ v e' with hqv_def
  set vpar : Point3 := qv • e' with hvpar_def
  set vperp : Point3 := v - vpar with hvperp_def
  have hperp : inner ℝ vperp e' = 0 := by
    simp [hvperp_def, hvpar_def, inner_sub_left, inner_smul_left, he'_unit]
    <;> ring
  let L := unitRescalingLinear e' he'_unit rho
  have h_L_e' : L e' = e3 := by
    have h1 : L e' = transverseScaleLin rho (householderToE3 e' he'_unit e') := by rfl
    rw [h1, householderToE3_sends_d_to_e3 e' he'_unit]
    ext i; fin_cases i <;> simp [transverseScaleLin_coord0, transverseScaleLin_coord1,
      transverseScaleLin_coord2, e3] <;> norm_num
  set wpar : Point3 := L vpar with hwpar_def
  set wperp : Point3 := L vperp with hwperp_def
  have h_wpar : wpar = qv • e3 := by
    rw [hwpar_def, hvpar_def, map_smul, h_L_e'] <;> rfl
  have h_wperp_coord2 : wperp 2 = 0 := by
    have h : (L vperp) 2 = inner ℝ vperp e' := unitRescalingLinear_coord2 e' he'_unit rho vperp
    rw [h, hperp] <;> rfl
  have h_wperp_norm : ‖wperp‖ = ‖vperp‖ / rho :=
    unitRescalingLinear_perp_norm e' he'_unit rho hrho vperp hperp
  have h_orth : inner ℝ wpar wperp = 0 := by
    rw [h_wpar]
    have h2 : inner ℝ e3 wperp = wperp 2 := by
      have h3 : inner ℝ wperp e3 = wperp 2 := by
        have h4 := EuclideanSpace.inner_single_right (2 : Fin 3) (1 : ℝ) wperp
        simpa [e3] using h4
      have h5 : inner ℝ e3 wperp = inner ℝ wperp e3 := real_inner_comm wperp e3
      rw [h5, h3]
    have h4 : inner ℝ (qv • e3) wperp = qv * inner ℝ e3 wperp := by
      simp [inner_smul_left] <;> ring
    rw [h4, h2, h_wperp_coord2] <;> ring
  have h_add : wz2PaperLiteralUnitRescalingLinear anchor v = (1 / 100 : ℝ) • (wpar + wperp) := by
    have h : v = vpar + vperp := by simp [hvperp_def] <;> abel
    simp [wz2PaperLiteralUnitRescalingLinear, h, map_add, hwpar_def, hwperp_def] <;> rfl
  have h_main : ‖wpar + wperp‖ ^ 2 = ‖wpar‖ ^ 2 + ‖wperp‖ ^ 2 := by
    rw [norm_add_sq_real wpar wperp, h_orth] <;> ring
  have h6 : ‖wpar‖ ^ 2 = qv ^ 2 := by
    rw [h_wpar, norm_smul, e3_norm]
    have h7 : ‖qv‖ = |qv| := Real.norm_eq_abs qv
    rw [h7]
    have h8 : (|qv| * 1) ^ 2 = |qv| ^ 2 := by ring
    rw [h8]
    have h9 : |qv| ^ 2 = qv ^ 2 := by rw [sq_abs]
    exact h9
  have h11 : ‖(1 / 100 : ℝ) • (wpar + wperp)‖ = (1 / 100 : ℝ) * ‖wpar + wperp‖ := by
    rw [norm_smul]
    have h12 : ‖(1 / 100 : ℝ)‖ = 1 / 100 := by norm_num
    rw [h12] <;> ring
  rw [h_add, h11]
  have h13 : ‖wpar + wperp‖ ^ 2 = qv ^ 2 + ‖vperp‖ ^ 2 / rho ^ 2 := by
    rw [h_main, h6, h_wperp_norm] <;> ring
  nlinarith

/-- Centered literal WZ rescaling map: translate by anchor midpoint instead
of axis zero point. -/
def wz2PaperCenteredLiteralRescalingMap
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho) (point : Point3) : Point3 :=
  wz2PaperLiteralUnitRescalingLinear anchor (point - wz2PaperTubeMidpoint anchor)

/-- The centered map is affine with the same linear part. -/
lemma centered_map_sub
    {rho : ℝ} (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho) (p1 p2 : Point3) :
    wz2PaperCenteredLiteralRescalingMap anchor hrho p1 -
      wz2PaperCenteredLiteralRescalingMap anchor hrho p2 =
    wz2PaperLiteralUnitRescalingLinear anchor (p1 - p2) := by
  simp [wz2PaperCenteredLiteralRescalingMap, map_sub]
  <;> abel

/-- Centered public ordinary target tube. -/
def wz2PaperCenteredLiteralOrdinaryRescaledTube
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    Kakeya.DeltaTube (delta / rho) where
  base :=
    wz2PaperCenteredLiteralRescalingMap anchor hrho (wz2PaperTubeMidpoint source) -
      (1 / 2 : ℝ) • NormedSpace.normalize (wz2PaperLiteralSourceImageDirection source anchor)
  direction :=
    NormedSpace.normalize (wz2PaperLiteralSourceImageDirection source anchor)
  direction_unit :=
    NormedSpace.norm_normalize (wz2PaperLiteralSourceImageDirection_ne_zero source anchor hrho)

/-- Helper: Pythagorean decomposition - perpendicular component has smaller norm. -/
private lemma pythag_perp_le {u w : Point3} (hu : ‖u‖ = 1) :
    ‖w - inner ℝ w u • u‖ ≤ ‖w‖ := by
  set c : ℝ := inner ℝ w u with hc_def
  set wpar : Point3 := c • u with hwpar_def
  set wperp : Point3 := w - wpar with hwperp_def
  have hinner_uu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu] <;> norm_num
  have hcomm : inner ℝ u w = c := by
    have h : inner ℝ u w = inner ℝ w u := (real_inner_comm u w).symm
    rw [h, hc_def]
  have horth : inner ℝ wpar wperp = 0 := by
    have h1 : inner ℝ wpar wperp = c * (inner ℝ u w - c) := by
      calc
        inner ℝ wpar wperp
          = inner ℝ (c • u) (w - c • u) := by rfl
        _ = c * inner ℝ u (w - c • u) := by
            have hsmul : inner ℝ (c • u) (w - c • u) = c * inner ℝ u (w - c • u) := by
              simpa [inner_smul_left] using rfl
            exact hsmul
        _ = c * (inner ℝ u w - inner ℝ u (c • u)) := by
            rw [inner_sub_right]
        _ = c * (inner ℝ u w - c * inner ℝ u u) := by
            rw [inner_smul_right]
        _ = c * (inner ℝ u w - c) := by
            rw [hinner_uu] <;> ring
    rw [h1, hcomm] <;> ring
  have hsum : ‖w‖ ^ 2 = ‖wpar‖ ^ 2 + ‖wperp‖ ^ 2 := by
    have h : w = wpar + wperp := by simp [hwperp_def] <;> abel
    rw [h, norm_add_sq_real wpar wperp, horth] <;> ring
  have h' : ‖wperp‖ ≤ ‖w‖ := by
    nlinarith [norm_nonneg wperp, norm_nonneg w]
  exact h'

/-- Helper: projection of a vector parallel to u onto u' (where u' = ±u) recovers the vector. -/
private lemma projection_parallel {w u u' : Point3} (hu : ‖u‖ = 1) (hu' : ‖u'‖ = 1)
    (hparallel : u' = u ∨ u' = -u) (hw : ∃ c : ℝ, w = c • u) :
    inner ℝ w u' • u' = w := by
  rcases hw with ⟨c, hc⟩
  rcases hparallel with (h | h)
  · -- u' = u
    have h_goal : inner ℝ w u' • u' = w := by
      rw [h, hc]
      have h1 : inner ℝ (c • u) u = c := by
        simp [inner_smul_left, real_inner_self_eq_norm_sq, hu] <;> norm_num
      rw [h1] <;> exact hc.symm
    exact h_goal
  · -- u' = -u
    have h_goal : inner ℝ w u' • u' = w := by
      rw [h, hc]
      have h1 : inner ℝ (c • u) (-u) = -c := by
        simp [inner_smul_left, inner_neg_right, real_inner_self_eq_norm_sq, hu] <;> norm_num
      rw [h1]
      <;> simp [hc, smul_neg] <;> abel
    exact h_goal

/-- Bound on the centered image of the source midpoint.

Given `source.carrier ⊆ anchor.carrier` with `0 < δ ≤ ρ ≤ 1/4`,
the centered image of `sourceMidpoint` has norm at most `1/80`. -/
theorem centered_midpoint_image_norm_le
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hdelta_le_rho : delta ≤ rho)
    (hrhoSmall : rho ≤ 1 / 4)
    (hcontainment : source.carrier ⊆ anchor.carrier) :
    ‖wz2PaperCenteredLiteralRescalingMap anchor hrho (wz2PaperTubeMidpoint source)‖ ≤ 1 / 80 := by
  set sourceMidpoint := wz2PaperTubeMidpoint source with hsm_def
  set anchorMidpoint := wz2PaperTubeMidpoint anchor with ham_def
  set e' := wz1PaperDirection anchor with he'_def
  have he'_unit : ‖e'‖ = 1 := wz1PaperDirection_norm anchor
  have he'_eq : e' = anchor.direction ∨ e' = -anchor.direction := by
    have h : e' = if 0 ≤ anchor.direction (2 : Fin 3) then anchor.direction else -anchor.direction := by
      simp [he'_def, wz1PaperDirection] <;> rfl
    rw [h]
    split_ifs <;> tauto

  -- sourceMidpoint ∈ source.carrier
  have h_eq1 : sourceMidpoint = source.base + (1 / 2 : ℝ) • source.direction := by
    simp [hsm_def, wz2PaperTubeMidpoint] <;> abel
  have hys : sourceMidpoint ∈ Kakeya.unitSegment source.base source.direction :=
    ⟨1 / 2, by norm_num, h_eq1.symm⟩
  have hsm_in_source : sourceMidpoint ∈ source.carrier :=
    Metric.mem_cthickening_of_dist_le sourceMidpoint sourceMidpoint delta
      (Kakeya.unitSegment source.base source.direction) hys
      (by simp [dist_self, hdelta.le])

  have hsm_in_anchor : sourceMidpoint ∈ anchor.carrier := hcontainment hsm_in_source

  -- Find y on anchor segment with ‖sourceMidpoint - y‖ ≤ rho
  have hsegmentCompact : IsCompact (Kakeya.unitSegment anchor.base anchor.direction) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  have hdecomposition :
      anchor.carrier = ⋃ y ∈ Kakeya.unitSegment anchor.base anchor.direction, Metric.closedBall y rho :=
    hsegmentCompact.cthickening_eq_biUnion_closedBall (by linarith)
  rw [hdecomposition] at hsm_in_anchor
  rcases Set.mem_iUnion₂.mp hsm_in_anchor with ⟨y, hy, hdistance⟩
  rcases hy with ⟨t, ht, h_y_eq⟩
  have h_y_eq' : y = anchor.base + t • anchor.direction := h_y_eq.symm
  have hdist : ‖sourceMidpoint - y‖ ≤ rho := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hdistance

  have h_anchor_mid : anchorMidpoint = anchor.base + (1 / 2 : ℝ) • anchor.direction := by
    simp [ham_def, wz2PaperTubeMidpoint] <;> abel

  -- y - anchorMidpoint = (t - 1/2) • anchor.direction
  have h_y_diff : y - anchorMidpoint = (t - 1 / 2 : ℝ) • anchor.direction := by
    have h : y - anchorMidpoint =
        (anchor.base + t • anchor.direction) - (anchor.base + (1 / 2 : ℝ) • anchor.direction) := by
      exact congr_arg₂ Sub.sub h_y_eq' h_anchor_mid
    rw [h]
    <;> simp [sub_smul, add_smul] <;> abel

  set v := sourceMidpoint - anchorMidpoint with hv_def
  set w := sourceMidpoint - y with hw_def

  -- v = w + (y - anchorMidpoint)
  have hv_decomp : v = w + (y - anchorMidpoint) := by
    simp [hv_def, hw_def] <;> abel

  -- Projection of (y - anchorMidpoint) onto e' equals itself
  have h_y_parallel : ∃ c : ℝ, y - anchorMidpoint = c • anchor.direction :=
    ⟨t - 1 / 2, h_y_diff⟩
  have hproj_y : inner ℝ (y - anchorMidpoint) e' • e' = y - anchorMidpoint :=
    projection_parallel anchor.direction_unit he'_unit he'_eq h_y_parallel

  -- Transverse component of v equals transverse component of w
  set vperp := v - inner ℝ v e' • e' with hvperp_def
  have hvperp_eq : vperp = w - inner ℝ w e' • e' := by
    have hinner : inner ℝ v e' = inner ℝ w e' + inner ℝ (y - anchorMidpoint) e' := by
      have h : inner ℝ v e' = inner ℝ (w + (y - anchorMidpoint)) e' := by
        apply congr_arg (fun x => inner ℝ x e')
        exact hv_decomp
      rw [h, inner_add_left]
    have h : vperp = v - inner ℝ v e' • e' := by rfl
    rw [h]
    have hgoal : v - inner ℝ v e' • e' = w - inner ℝ w e' • e' := by
      have h_v : v = w + (y - anchorMidpoint) := hv_decomp
      have h_inner : inner ℝ v e' = inner ℝ w e' + inner ℝ (y - anchorMidpoint) e' := hinner
      have h3 : v - inner ℝ v e' • e' =
          (w + (y - anchorMidpoint)) - (inner ℝ w e' + inner ℝ (y - anchorMidpoint) e') • e' := by
        exact congr_arg₂ Sub.sub h_v (congr_arg (fun x : ℝ => x • e') h_inner)
      rw [h3, add_smul, hproj_y]
      <;> abel
    exact hgoal

  -- Transverse bound
  have hperp_bound : ‖vperp‖ ≤ rho := by
    rw [hvperp_eq]
    have h : ‖w - inner ℝ w e' • e'‖ ≤ ‖w‖ := pythag_perp_le he'_unit
    exact h.trans hdist

  -- Longitudinal bound: |inner(v, e')| ≤ rho + 1/2
  have hinner_v : inner ℝ v e' = inner ℝ w e' + inner ℝ (y - anchorMidpoint) e' := by
    rw [hv_decomp, inner_add_left]
  have h1 : |inner ℝ w e'| ≤ ‖w‖ := by
    calc
      |inner ℝ w e'| ≤ ‖w‖ * ‖e'‖ := abs_real_inner_le_norm w e'
      _ = ‖w‖ := by rw [he'_unit] <;> ring
  have h2 : |inner ℝ (y - anchorMidpoint) e'| ≤ 1 / 2 := by
    have h31 : inner ℝ (y - anchorMidpoint) e' =
        (t - 1 / 2 : ℝ) * inner ℝ anchor.direction e' := by
      rw [h_y_diff]
      simpa [inner_smul_left] using rfl
    have h4 : |inner ℝ anchor.direction e'| = 1 := by
      rcases he'_eq with (h | h)
      · rw [h]
        simp [anchor.direction_unit, real_inner_self_eq_norm_sq] <;> norm_num
      · rw [h]
        simp [inner_neg_right, anchor.direction_unit, real_inner_self_eq_norm_sq] <;> norm_num
    calc
      |inner ℝ (y - anchorMidpoint) e'|
        = |(t - 1 / 2 : ℝ) * inner ℝ anchor.direction e'| := by rw [h31]
      _ = |t - 1 / 2| * |inner ℝ anchor.direction e'| := by rw [abs_mul]
      _ = |t - 1 / 2| := by rw [h4] <;> ring
      _ ≤ 1 / 2 := by
        have ht' : 0 ≤ t ∧ t ≤ 1 := by simpa [Set.mem_Icc] using ht
        rw [abs_le] <;> constructor <;> linarith
  have hinner_abs : |inner ℝ v e'| ≤ rho + 1 / 2 := by
    rw [hinner_v]
    set a := inner ℝ w e' with ha_def
    set b := inner ℝ (y - anchorMidpoint) e' with hb_def
    have h_abs : |a + b| ≤ |a| + |b| := by
      have h1 : -|a| - |b| ≤ a + b := by
        have h1a : -|a| ≤ a := neg_abs_le a
        have h1b : -|b| ≤ b := neg_abs_le b
        linarith
      have h2 : a + b ≤ |a| + |b| := by
        have h2a : a ≤ |a| := le_abs_self a
        have h2b : b ≤ |b| := le_abs_self b
        linarith
      rw [abs_le] <;> constructor <;> linarith
    calc
      |a + b| ≤ |a| + |b| := h_abs
      _ ≤ ‖w‖ + 1 / 2 := by gcongr
      _ ≤ rho + 1 / 2 := by gcongr

  -- Apply norm squared formula
  have hnorm_sq := centered_linear_norm_sq anchor hrho v
  have hlong_sq : (inner ℝ v e') ^ 2 ≤ (rho + 1 / 2) ^ 2 := by
    have h : |inner ℝ v e'| ≤ rho + 1 / 2 := hinner_abs
    have hpos : 0 ≤ rho + 1 / 2 := by linarith
    have hsq : |inner ℝ v e'| ^ 2 ≤ (rho + 1 / 2) ^ 2 := by gcongr
    have habs : (inner ℝ v e') ^ 2 = |inner ℝ v e'| ^ 2 := by
      rw [sq_abs]
    rw [habs]
    exact hsq
  have htrans_sq : ‖vperp‖ ^ 2 / rho ^ 2 ≤ 1 := by
    have h3 : ‖vperp‖ ^ 2 ≤ rho ^ 2 := by
      have h4 : ‖vperp‖ ≤ rho := hperp_bound
      gcongr
    have h5 : 0 < rho ^ 2 := by positivity
    exact (div_le_one h5).mpr h3
  have h_main : ‖wz2PaperLiteralUnitRescalingLinear anchor v‖ ^ 2 ≤ (1 / 80 : ℝ) ^ 2 := by
    rw [hnorm_sq]
    have h6 : (1 / 100 : ℝ) ^ 2 * ((inner ℝ v e') ^ 2 + ‖vperp‖ ^ 2 / rho ^ 2) ≤
        (1 / 100 : ℝ) ^ 2 * ((rho + 1 / 2) ^ 2 + 1) := by
      gcongr
    have h7 : (1 / 100 : ℝ) ^ 2 * ((rho + 1 / 2) ^ 2 + 1) ≤ (1 / 80 : ℝ) ^ 2 := by
      nlinarith [hrhoSmall]
    exact h6.trans h7
  have hnorm_nonneg : 0 ≤ ‖wz2PaperLiteralUnitRescalingLinear anchor v‖ := norm_nonneg _
  have h_final : ‖wz2PaperLiteralUnitRescalingLinear anchor v‖ ≤ 1 / 80 := by
    nlinarith
  exact h_final

/-- The centered target tube carrier is contained in the unit ball when
`δ/ρ ≤ 39/80`. -/
theorem centered_target_unit_ball
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hdelta_le_rho : delta ≤ rho)
    (hrhoSmall : rho ≤ 1 / 4)
    (hcontainment : source.carrier ⊆ anchor.carrier)
    (hscale_small : delta / rho ≤ 39 / 80) :
    (wz2PaperCenteredLiteralOrdinaryRescaledTube source anchor hrho).carrier ⊆
      Metric.closedBall (0 : Point3) 1 := by
  set targetTube := wz2PaperCenteredLiteralOrdinaryRescaledTube source anchor hrho with htarget_def
  set centerPoint := wz2PaperCenteredLiteralRescalingMap anchor hrho (wz2PaperTubeMidpoint source)
    with hcenter_def
  set imageDirection := wz2PaperLiteralSourceImageDirection source anchor with himg_def
  have himageNe : imageDirection ≠ 0 :=
    wz2PaperLiteralSourceImageDirection_ne_zero source anchor hrho
  have hnormUpper : ‖imageDirection‖ ≤ 1 / 20 :=
    containment_image_direction_norm_le_no_line_class
      source anchor hdelta hrho hdelta_le_rho hrhoSmall hcontainment
  have hcenter_norm : ‖centerPoint‖ ≤ 1 / 80 :=
    centered_midpoint_image_norm_le source anchor hdelta hrho hdelta_le_rho hrhoSmall hcontainment

  intro x hx
  have hdecomp : x ∈ Metric.cthickening (delta / rho)
      (Kakeya.unitSegment targetTube.base targetTube.direction) := hx
  have hsegmentCompact : IsCompact (Kakeya.unitSegment targetTube.base targetTube.direction) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  have hdelta'Nonneg : 0 ≤ delta / rho := by positivity
  have hdecomp2 : Metric.cthickening (delta / rho)
      (Kakeya.unitSegment targetTube.base targetTube.direction) =
      ⋃ y ∈ Kakeya.unitSegment targetTube.base targetTube.direction, Metric.closedBall y (delta / rho) :=
    hsegmentCompact.cthickening_eq_biUnion_closedBall hdelta'Nonneg
  rw [hdecomp2] at hdecomp
  rcases Set.mem_iUnion₂.mp hdecomp with ⟨segPoint, hsegPoint, hdistance⟩
  rcases hsegPoint with ⟨s, hs, rfl⟩
  set segPoint := targetTube.base + s • targetTube.direction with hseg_def

  -- segPoint = centerPoint + (s - 1/2) • normalize(imageDirection)
  have hbase : targetTube.base = centerPoint - (1 / 2 : ℝ) • targetTube.direction := by
    simp [htarget_def, wz2PaperCenteredLiteralOrdinaryRescaledTube, hcenter_def]
    <;> rfl
  have hseg_eq : segPoint = centerPoint + (s - 1 / 2 : ℝ) • targetTube.direction := by
    rw [hseg_def, hbase]
    <;> simp [sub_smul, add_smul] <;> abel

  have hseg_norm : ‖segPoint‖ ≤ ‖centerPoint‖ + |s - 1 / 2| * ‖targetTube.direction‖ := by
    rw [hseg_eq]
    calc
      ‖centerPoint + (s - 1 / 2 : ℝ) • targetTube.direction‖
        ≤ ‖centerPoint‖ + ‖(s - 1 / 2 : ℝ) • targetTube.direction‖ := norm_add_le _ _
      _ = ‖centerPoint‖ + |s - 1 / 2| * ‖targetTube.direction‖ := by
        rw [norm_smul, Real.norm_eq_abs] <;> ring
  have hdir_unit : ‖targetTube.direction‖ = 1 := targetTube.direction_unit
  have hs' : 0 ≤ s ∧ s ≤ 1 := by simpa [Set.mem_Icc] using hs
  have h_s_half : |s - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le] <;> constructor <;> linarith [hs'.1, hs'.2]
  have hseg_bound : ‖segPoint‖ ≤ 1 / 80 + 1 / 2 := by
    rw [hdir_unit] at hseg_norm
    linarith [hcenter_norm, h_s_half]

  have hdist : ‖x - segPoint‖ ≤ delta / rho := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hdistance
  have h_final : ‖x‖ ≤ 1 := by
    calc
      ‖x‖ = ‖segPoint + (x - segPoint)‖ := by
        have h_eq : x = segPoint + (x - segPoint) := by simp
        exact congr_arg norm h_eq
      _ ≤ ‖segPoint‖ + ‖x - segPoint‖ := norm_add_le _ _
      _ ≤ (1 / 80 + 1 / 2) + delta / rho := by
        have h21 : ‖segPoint‖ ≤ 1 / 80 + 1 / 2 := hseg_bound
        have h22 : ‖x - segPoint‖ ≤ delta / rho := hdist
        linarith
      _ ≤ 1 := by linarith [hscale_small]
  simpa [Metric.mem_closedBall, dist_eq_norm] using h_final

/-- The image of the source unit segment under the centered map lies in the
centered target unit segment. -/
theorem centered_image_unitSegment_subset
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hrhoSmall : rho ≤ 1 / 4)
    (hdelta_le_rho : delta ≤ rho)
    (hcontainment : source.carrier ⊆ anchor.carrier) :
    wz2PaperCenteredLiteralRescalingMap anchor hrho ''
        Kakeya.unitSegment source.base source.direction ⊆
      Kakeya.unitSegment
        (wz2PaperCenteredLiteralOrdinaryRescaledTube source anchor hrho).base
        (wz2PaperCenteredLiteralOrdinaryRescaledTube source anchor hrho).direction := by
  rintro point ⟨sourcePoint, ⟨parameter, hparameter, rfl⟩, rfl⟩
  let imageDirection := wz2PaperLiteralSourceImageDirection source anchor
  have himageNe : imageDirection ≠ 0 :=
    wz2PaperLiteralSourceImageDirection_ne_zero source anchor hrho
  have hnormUpper : ‖imageDirection‖ ≤ 1 / 20 :=
    containment_image_direction_norm_le_no_line_class
      source anchor hdelta hrho hdelta_le_rho hrhoSmall hcontainment
  have hnormNonneg : 0 ≤ ‖imageDirection‖ := norm_nonneg _
  have hcanonicalSegment :
      source.base + parameter • source.direction ∈
        Kakeya.unitSegment (wz2PaperCanonicalSourceBase source) (wz1PaperDirection source) := by
    rw [wz2PaperCanonicalSourceSegment_eq]
    exact ⟨parameter, hparameter, rfl⟩
  rcases hcanonicalSegment with ⟨canonicalParameter, hcanonicalParameter, hcanonicalPoint⟩
  refine ⟨1 / 2 + (canonicalParameter - 1 / 2) * ‖imageDirection‖, ?_, ?_⟩
  · constructor
    · nlinarith [hcanonicalParameter.1, hcanonicalParameter.2, hnormUpper, hnormNonneg]
    · nlinarith [hcanonicalParameter.1, hcanonicalParameter.2, hnormUpper, hnormNonneg]
  · set targetTube := wz2PaperCenteredLiteralOrdinaryRescaledTube source anchor hrho with htarget_def
    set centerPoint := wz2PaperCenteredLiteralRescalingMap anchor hrho (wz2PaperTubeMidpoint source)
      with hcenter_def
    have hcanonicalPoint' :
        source.base + parameter • source.direction =
          wz2PaperCanonicalSourceBase source + canonicalParameter • wz1PaperDirection source :=
      hcanonicalPoint.symm
    have hnorm_smul : ‖imageDirection‖ • NormedSpace.normalize imageDirection = imageDirection :=
      NormedSpace.norm_smul_normalize imageDirection
    have hbase : targetTube.base = centerPoint - (1 / 2 : ℝ) • targetTube.direction := by
      simp [htarget_def, wz2PaperCenteredLiteralOrdinaryRescaledTube, hcenter_def] <;> rfl
    have hlhs : targetTube.base +
          (1 / 2 + (canonicalParameter - 1 / 2) * ‖imageDirection‖) • targetTube.direction =
        centerPoint + (canonicalParameter - 1 / 2 : ℝ) • imageDirection := by
      rw [hbase]
      have hneg : -((1 / 2 : ℝ) • targetTube.direction) = (-(1 / 2 : ℝ)) • targetTube.direction := by
        rw [neg_smul] <;> rfl
      have h1 : centerPoint - (1 / 2 : ℝ) • targetTube.direction =
          centerPoint + (-(1 / 2 : ℝ)) • targetTube.direction := by
        rw [sub_eq_add_neg, hneg]
      have hsub : (centerPoint - (1 / 2 : ℝ) • targetTube.direction) +
            (1 / 2 + (canonicalParameter - 1 / 2) * ‖imageDirection‖) • targetTube.direction =
          centerPoint + ((-(1 / 2 : ℝ)) • targetTube.direction +
            (1 / 2 + (canonicalParameter - 1 / 2) * ‖imageDirection‖) • targetTube.direction) := by
        rw [h1, add_assoc]
      rw [hsub]
      have h : (-(1 / 2 : ℝ)) + (1 / 2 + (canonicalParameter - 1 / 2) * ‖imageDirection‖) =
          (canonicalParameter - 1 / 2) * ‖imageDirection‖ := by ring
      have h2 : (-(1 / 2 : ℝ)) • targetTube.direction +
            (1 / 2 + (canonicalParameter - 1 / 2) * ‖imageDirection‖) • targetTube.direction =
          ((canonicalParameter - 1 / 2) * ‖imageDirection‖) • targetTube.direction := by
        rw [← add_smul, h]
      rw [h2]
      have h3 : ((canonicalParameter - 1 / 2) * ‖imageDirection‖) • targetTube.direction =
          (canonicalParameter - 1 / 2 : ℝ) • (‖imageDirection‖ • targetTube.direction) := by
        rw [smul_smul] <;> ring
      rw [h3]
      have h4 : ‖imageDirection‖ • targetTube.direction = imageDirection := by
        have hdir : targetTube.direction = NormedSpace.normalize imageDirection := by
          simp [htarget_def, wz2PaperCenteredLiteralOrdinaryRescaledTube] <;> rfl
        rw [hdir]
        exact hnorm_smul
      rw [h4] <;> abel
    have hcanonical : wz2PaperCanonicalSourceBase source =
        wz2PaperTubeMidpoint source - (1 / 2 : ℝ) • wz1PaperDirection source := by rfl
    have himg : imageDirection = wz2PaperLiteralUnitRescalingLinear anchor (wz1PaperDirection source) := by rfl
    have hbase_eq : wz2PaperCenteredLiteralRescalingMap anchor hrho (wz2PaperCanonicalSourceBase source) =
        centerPoint + (-(1 / 2 : ℝ)) • imageDirection := by
      rw [hcanonical, himg]
      simp [wz2PaperCenteredLiteralRescalingMap, map_sub, map_smul, hcenter_def]
      <;> abel
    have hrhs : wz2PaperCenteredLiteralRescalingMap anchor hrho (source.base + parameter • source.direction) =
        centerPoint + (canonicalParameter - 1 / 2 : ℝ) • imageDirection := by
      rw [hcanonicalPoint']
      have hmap_add : wz2PaperCenteredLiteralRescalingMap anchor hrho
            (wz2PaperCanonicalSourceBase source + canonicalParameter • wz1PaperDirection source) =
          wz2PaperCenteredLiteralRescalingMap anchor hrho (wz2PaperCanonicalSourceBase source) +
            canonicalParameter • imageDirection := by
        simp [wz2PaperCenteredLiteralRescalingMap, map_add, map_smul, himg] <;> abel
      rw [hmap_add, hbase_eq]
      <;> simp [add_smul, sub_smul] <;> abel
    exact hlhs.trans hrhs.symm

/-- The complete literal affine image under the centered map lies in the
centered ordinary target carrier. -/
theorem centered_image_carrier_subset
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hrhoSmall : rho ≤ 1 / 4)
    (hdelta_le_rho : delta ≤ rho)
    (hcontainment : source.carrier ⊆ anchor.carrier) :
    wz2PaperCenteredLiteralRescalingMap anchor hrho '' source.carrier ⊆
      (wz2PaperCenteredLiteralOrdinaryRescaledTube source anchor hrho).carrier := by
  intro imagePoint himagePoint
  rcases himagePoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  have hsegmentCompact : IsCompact (Kakeya.unitSegment source.base source.direction) :=
    isCompact_Icc.image (continuous_const.add (continuous_id.smul continuous_const))
  have hdeltaNonneg : 0 ≤ delta := hdelta.le
  have hsourcePoint' : sourcePoint ∈ Metric.cthickening delta
      (Kakeya.unitSegment source.base source.direction) := hsourcePoint
  have hdecomposition : Metric.cthickening delta
      (Kakeya.unitSegment source.base source.direction) =
      ⋃ segmentPoint ∈ Kakeya.unitSegment source.base source.direction, Metric.closedBall segmentPoint delta :=
    hsegmentCompact.cthickening_eq_biUnion_closedBall hdeltaNonneg
  rw [hdecomposition] at hsourcePoint'
  rcases Set.mem_iUnion₂.mp hsourcePoint' with ⟨segmentPoint, hsegmentPoint, hdistance⟩
  have himageSegment :
      wz2PaperCenteredLiteralRescalingMap anchor hrho segmentPoint ∈
        Kakeya.unitSegment
          (wz2PaperCenteredLiteralOrdinaryRescaledTube source anchor hrho).base
          (wz2PaperCenteredLiteralOrdinaryRescaledTube source anchor hrho).direction :=
    centered_image_unitSegment_subset source anchor hdelta hrho hrhoOne hrhoSmall hdelta_le_rho
      hcontainment ⟨segmentPoint, hsegmentPoint, rfl⟩
  have hdistanceSource : dist sourcePoint segmentPoint ≤ delta := by
    simpa [Metric.mem_closedBall] using hdistance
  have hdistanceImage :
      dist (wz2PaperCenteredLiteralRescalingMap anchor hrho sourcePoint)
           (wz2PaperCenteredLiteralRescalingMap anchor hrho segmentPoint) ≤ delta / rho := by
    rw [dist_eq_norm, centered_map_sub]
    calc
      ‖wz2PaperLiteralUnitRescalingLinear anchor (sourcePoint - segmentPoint)‖
        ≤ ‖sourcePoint - segmentPoint‖ / (100 * rho) :=
          wz2PaperLiteralUnitRescalingLinear_norm_le anchor hrho hrhoOne _
      _ ≤ delta / (100 * rho) := by
        gcongr
        simpa [dist_eq_norm] using hdistanceSource
      _ ≤ delta / rho := by
        exact (div_le_div_iff₀ (mul_pos (by norm_num) hrho) hrho).2
          (by nlinarith [hdelta, hrho])
  exact Metric.mem_cthickening_of_dist_le
    (wz2PaperCenteredLiteralRescalingMap anchor hrho sourcePoint)
    (wz2PaperCenteredLiteralRescalingMap anchor hrho segmentPoint)
    (delta / rho)
    (Kakeya.unitSegment
      (wz2PaperCenteredLiteralOrdinaryRescaledTube source anchor hrho).base
      (wz2PaperCenteredLiteralOrdinaryRescaledTube source anchor hrho).direction)
    himageSegment hdistanceImage

end Kakeya.Assouad

end
