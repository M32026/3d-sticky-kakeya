import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledTube
import MyLeanRepo.Kakeya.Assouad.WZ1.DirectionInnerProductBound
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import Mathlib.Tactic

/-!
# Containment-based rescaling without WZ1 line class

Replaces the line-class hypothesis with pure carrier containment.

Provides three main results from carrier containment alone:

1. `containment_image_direction_norm_le_no_line_class`: the literal WZ image
   direction has norm at most `1/20`.
2. `wz2PaperLiteral_image_unitSegment_subset_no_line_class`: the image of the
   source unit segment lies in the target unit segment.
3. `wz2PaperLiteral_image_carrier_subset_no_line_class`: the full literal affine
   image of the source carrier lies in the ordinary target carrier.

All three require only `source.carrier ⊆ anchor.carrier` with
`0 < delta ≤ rho ≤ 1/4`; no `WZ1PaperTubeInLineClass` or `WZ1PaperTubeCovers`
is needed.

## Whiteprint

Node: `wz2_node01_refinement_containment_no_line_class`
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set InnerProductGeometry

attribute [local instance] Classical.propDecidable

/--
Image direction norm bound from carrier containment alone.

Given `source.carrier ⊆ anchor.carrier` with `0 < delta ≤ rho ≤ 1/4`, the
literal WZ image direction has norm at most `1/20`.
-/
theorem containment_image_direction_norm_le_no_line_class
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hdelta_le_rho : delta ≤ rho)
    (hrhoSmall : rho ≤ 1 / 4)
    (hcontainment : source.carrier ⊆ anchor.carrier) :
    ‖wz2PaperLiteralSourceImageDirection source anchor‖ ≤ 1 / 20 := by
  set d : Point3 := source.direction with hd_def
  set e : Point3 := anchor.direction with he_def
  have hd_unit : ‖d‖ = 1 := source.direction_unit
  have he_unit : ‖e‖ = 1 := anchor.direction_unit

  set d' : Point3 := wz1PaperDirection source with hd'_def
  set e' : Point3 := wz1PaperDirection anchor with he'_def

  have hd'_eq : d' = d ∨ d' = -d := by
    have h : d' = if 0 ≤ d (2 : Fin 3) then d else -d := by
      simp [hd'_def, wz1PaperDirection, hd_def] <;> rfl
    rw [h]
    split_ifs <;> tauto
  have he'_eq : e' = e ∨ e' = -e := by
    have h : e' = if 0 ≤ e (2 : Fin 3) then e else -e := by
      simp [he'_def, wz1PaperDirection, he_def] <;> rfl
    rw [h]
    split_ifs <;> tauto

  -- Transverse bound from carrier containment
  have htrans : ‖d - inner ℝ d e • e‖ ≤ 2 * (rho - delta) :=
    direction_transverse_bound_of_containment
      hdelta.le hrho.le hdelta_le_rho source anchor hcontainment

  -- Inner product bound
  have hinner : ∃ (sign : ℝ), (sign = 1 ∨ sign = -1) ∧
      inner ℝ d (sign • e) ≥ Real.sqrt (1 - 4 * rho^2) :=
    direction_inner_product_bound hdelta.le source anchor hcontainment hrho.le hrhoSmall

  -- |inner d e| ≥ sqrt(1 - 4*rho^2)
  have hinner_abs : |inner ℝ d e| ≥ Real.sqrt (1 - 4 * rho^2) := by
    rcases hinner with ⟨sign, hsign, hinner_sign⟩
    rcases hsign with (rfl | rfl)
    · have h' : inner ℝ d e ≥ Real.sqrt (1 - 4 * rho^2) := by
        have h9 : (1 : ℝ) • e = e := by simp
        rw [h9] at hinner_sign
        exact hinner_sign
      have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - 4 * rho^2) := Real.sqrt_nonneg _
      have hnonneg : 0 ≤ inner ℝ d e := by linarith
      rw [abs_of_nonneg hnonneg]; exact h'
    · have h2 : inner ℝ d (-e) ≥ Real.sqrt (1 - 4 * rho^2) := by
        have h9 : (-1 : ℝ) • e = -e := by simp
        rw [h9] at hinner_sign
        exact hinner_sign
      have h3 : inner ℝ d (-e) = -inner ℝ d e := by simp
      rw [h3] at h2
      have hneg : inner ℝ d e ≤ 0 := by
        have hsqrt_nonneg : 0 ≤ Real.sqrt (1 - 4 * rho^2) := Real.sqrt_nonneg _
        linarith
      rw [abs_of_nonpos hneg]; linarith

  -- |inner d' e'| = |inner d e|
  have hinner'_abs : |inner ℝ d' e'| = |inner ℝ d e| := by
    rcases hd'_eq with (hd' | hd')
    · rcases he'_eq with (he' | he')
      · rw [hd', he']
      · rw [hd', he']
        have h : inner ℝ d (-e) = -inner ℝ d e := by simp [inner_neg_right]
        rw [h, abs_neg]
    · rcases he'_eq with (he' | he')
      · rw [hd', he']
        have h : inner ℝ (-d) e = -inner ℝ d e := by simp [inner_neg_left]
        rw [h, abs_neg]
      · rw [hd', he']
        have h : inner ℝ (-d) (-e) = inner ℝ d e := by simp [inner_neg_left, inner_neg_right]
        rw [h]

  -- Transverse norm for d', e' equals that for d, e
  have htrans'_eq : ‖d' - inner ℝ d' e' • e'‖ = ‖d - inner ℝ d e • e‖ := by
    rcases hd'_eq with (hd' | hd') <;> rcases he'_eq with (he' | he')
    · rw [hd', he']
    · rw [hd', he']
      have h : d - inner ℝ d (-e) • (-e) = d - inner ℝ d e • e := by
        have h2 : inner ℝ d (-e) = -inner ℝ d e := by simp [inner_neg_right]
        rw [h2] <;> simp [smul_neg] <;> abel
      rw [h]
    · rw [hd', he']
      have h : (-d) - inner ℝ (-d) e • e = -(d - inner ℝ d e • e) := by
        have h2 : inner ℝ (-d) e = -inner ℝ d e := by simp [inner_neg_left]
        rw [h2] <;> simp [smul_neg] <;> abel
      rw [h, norm_neg]
    · rw [hd', he']
      have h : (-d) - inner ℝ (-d) (-e) • (-e) = -(d - inner ℝ d e • e) := by
        have h2 : inner ℝ (-d) (-e) = inner ℝ d e := by simp [inner_neg_left, inner_neg_right]
        rw [h2] <;> simp [smul_neg] <;> abel
      rw [h, norm_neg]
  have htrans' : ‖d' - inner ℝ d' e' • e'‖ ≤ 2 * (rho - delta) := by
    rw [htrans'_eq]; exact htrans

  let rotation := householderToE3 e' (wz1PaperDirection_norm anchor)
  let u := unitRescalingLinear e' (wz1PaperDirection_norm anchor) rho d'

  have h_rot_e' : rotation e' = e3 :=
    householderToE3_sends_d_to_e3 e' (wz1PaperDirection_norm anchor)
  have h_u_def : u = transverseScaleLin rho (rotation d') := rfl

  set v : Point3 := rotation d' - inner ℝ d' e' • e3 with hv_def
  have h_decomp : rotation d' = inner ℝ d' e' • e3 + v := by
    simp [hv_def] <;> abel

  have h_ts_add : transverseScaleLin rho (inner ℝ d' e' • e3 + v) =
      transverseScaleLin rho (inner ℝ d' e' • e3) + transverseScaleLin rho v := by
    exact (transverseScaleLin rho).map_add (inner ℝ d' e' • e3) v
  have h_ts_smul : transverseScaleLin rho (inner ℝ d' e' • e3) = inner ℝ d' e' • e3 := by
    have h : transverseScaleLin rho (inner ℝ d' e' • e3) = inner ℝ d' e' • transverseScaleLin rho e3 :=
      (transverseScaleLin rho).map_smul (inner ℝ d' e') e3
    rw [h]
    have h_e3 : transverseScaleLin rho e3 = e3 := by
      ext i; fin_cases i <;> simp [transverseScaleLin_coord0, transverseScaleLin_coord1,
        transverseScaleLin_coord2, e3]
    rw [h_e3]

  have h_u : u = inner ℝ d' e' • e3 + transverseScaleLin rho v := by
    rw [h_u_def, h_decomp, h_ts_add, h_ts_smul]

  have h_rot_v : ‖v‖ = ‖d' - inner ℝ d' e' • e'‖ := by
    have h3 : rotation (d' - inner ℝ d' e' • e') = v := by
      simp [hv_def, map_sub, map_smul, h_rot_e'] <;> abel
    rw [←h3]
    exact householderToE3_norm e' (wz1PaperDirection_norm anchor) (d' - inner ℝ d' e' • e')

  have hscale : ‖transverseScaleLin rho v‖ ≤ (1 / rho) * ‖v‖ :=
    transverseScaleLin_norm_bound rho hrho (by linarith) v

  have htrans_v : ‖transverseScaleLin rho v‖ ≤ 2 := by
    calc
      _ ≤ (1 / rho) * ‖v‖ := hscale
      _ = (1 / rho) * ‖d' - inner ℝ d' e' • e'‖ := by rw [h_rot_v]
      _ ≤ (1 / rho) * (2 * (rho - delta)) := by gcongr <;> exact htrans'
      _ ≤ (1 / rho) * (2 * rho) := by gcongr <;> linarith
      _ = 2 := by field_simp [hrho.ne'] <;> ring

  have hlong : ‖inner ℝ d' e' • e3‖ ≤ 1 := by
    have h1 : ‖inner ℝ d' e' • e3‖ = |inner ℝ d' e'| := by
      rw [norm_smul, e3_norm] <;> simp
    rw [h1]
    have h2 : |inner ℝ d' e'| ≤ ‖d'‖ * ‖e'‖ := abs_real_inner_le_norm d' e'
    have h3 : ‖d'‖ = 1 := wz1PaperDirection_norm source
    have h4 : ‖e'‖ = 1 := wz1PaperDirection_norm anchor
    rw [h3, h4] at h2
    linarith

  have hnorm : ‖u‖ ≤ 3 := by
    rw [h_u]
    have h : ‖inner ℝ d' e' • e3 + transverseScaleLin rho v‖ ≤
        ‖inner ℝ d' e' • e3‖ + ‖transverseScaleLin rho v‖ := norm_add_le _ _
    linarith

  have h_main : ‖wz2PaperLiteralSourceImageDirection source anchor‖ = (1 / 100 : ℝ) * ‖u‖ := by
    have h_def : wz2PaperLiteralSourceImageDirection source anchor = (1 / 100 : ℝ) • u := by rfl
    rw [h_def, norm_smul]
    have h_pos : (0 : ℝ) < 1 / 100 := by norm_num
    rw [Real.norm_eq_abs, abs_of_pos h_pos] <;> ring
  rw [h_main]
  have h6 : (1 / 100 : ℝ) * ‖u‖ ≤ (1 / 100 : ℝ) * (3 : ℝ) := by gcongr
  have h7 : (1 / 100 : ℝ) * (3 : ℝ) ≤ 1 / 20 := by norm_num
  exact h6.trans h7

/-- The image unit segment is contained in the ordinary target unit segment,
using only carrier containment. -/
theorem wz2PaperLiteral_image_unitSegment_subset_no_line_class
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hrhoSmall : rho ≤ 1 / 4)
    (hdelta_le_rho : delta ≤ rho)
    (hcontainment : source.carrier ⊆ anchor.carrier) :
    wz2PaperLiteralUnitRescalingMap anchor hrho ''
        Kakeya.unitSegment source.base source.direction ⊆
      Kakeya.unitSegment
        (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho).base
        (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho).direction := by
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
        Kakeya.unitSegment
          (wz2PaperCanonicalSourceBase source)
          (wz1PaperDirection source) := by
    rw [wz2PaperCanonicalSourceSegment_eq]
    exact ⟨parameter, hparameter, rfl⟩
  rcases hcanonicalSegment with
    ⟨canonicalParameter, hcanonicalParameter, hcanonicalPoint⟩
  refine
    ⟨1 / 2 + (canonicalParameter - 1 / 2) * ‖imageDirection‖, ?_, ?_⟩
  · constructor
    · nlinarith [hcanonicalParameter.1, hcanonicalParameter.2, hnormUpper, hnormNonneg]
    · nlinarith [hcanonicalParameter.1, hcanonicalParameter.2, hnormUpper, hnormNonneg]
  · have hcanonicalPoint' :
        source.base + parameter • source.direction =
          wz2PaperCanonicalSourceBase source +
            canonicalParameter • wz1PaperDirection source :=
      hcanonicalPoint.symm
    change
      (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho).base +
          (1 / 2 + (canonicalParameter - 1 / 2) * ‖imageDirection‖) •
            (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho).direction =
        wz2PaperLiteralUnitRescalingMap anchor hrho
          (source.base + parameter • source.direction)
    rw [hcanonicalPoint']
    rw [wz2PaperLiteralUnitRescalingMap_add, map_smul]
    change
      (wz2PaperLiteralUnitRescalingMap anchor hrho
            (wz2PaperTubeMidpoint source) -
          (1 / 2 : ℝ) • NormedSpace.normalize imageDirection) +
          (1 / 2 + (canonicalParameter - 1 / 2) * ‖imageDirection‖) •
            NormedSpace.normalize imageDirection =
        wz2PaperLiteralUnitRescalingMap anchor hrho
          (wz2PaperCanonicalSourceBase source) +
          canonicalParameter • wz2PaperLiteralUnitRescalingLinear anchor
            (wz1PaperDirection source)
    have hnormalize :
        NormedSpace.normalize imageDirection = ‖imageDirection‖⁻¹ • imageDirection := rfl
    rw [hnormalize, smul_smul]
    have hnormNe : ‖imageDirection‖ ≠ 0 := norm_ne_zero_iff.mpr himageNe
    have hcoefficient :
        (1 / 2 + (canonicalParameter - 1 / 2) * ‖imageDirection‖) * ‖imageDirection‖⁻¹ =
          (1 / 2 : ℝ) * ‖imageDirection‖⁻¹ + (canonicalParameter - 1 / 2) := by
      rw [add_mul, mul_assoc, mul_inv_cancel₀ hnormNe, mul_one]
    simp only [smul_smul]
    rw [hcoefficient]
    unfold wz2PaperCanonicalSourceBase
    rw [show
      wz2PaperTubeMidpoint source - (1 / 2 : ℝ) • wz1PaperDirection source =
        wz2PaperTubeMidpoint source + (-(1 / 2 : ℝ) • wz1PaperDirection source) by module]
    rw [wz2PaperLiteralUnitRescalingMap_add, map_smul]
    change
      _ =
        (wz2PaperLiteralUnitRescalingMap anchor hrho
              (wz2PaperTubeMidpoint source) +
            (-(1 / 2 : ℝ)) • imageDirection) +
          canonicalParameter • imageDirection
    module

/-- The complete literal affine image lies in the ordinary target carrier,
using only carrier containment. -/
theorem wz2PaperLiteral_image_carrier_subset_no_line_class
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hrhoSmall : rho ≤ 1 / 4)
    (hdelta_le_rho : delta ≤ rho)
    (hcontainment : source.carrier ⊆ anchor.carrier) :
    wz2PaperLiteralUnitRescalingMap anchor hrho '' source.carrier ⊆
      (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho).carrier := by
  intro imagePoint himagePoint
  rcases himagePoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  have hsegmentCompact :
      IsCompact (Kakeya.unitSegment source.base source.direction) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  have hdeltaNonneg : 0 ≤ delta := hdelta.le
  have hsourcePoint' :
      sourcePoint ∈ Metric.cthickening delta
        (Kakeya.unitSegment source.base source.direction) := hsourcePoint
  have hdecomposition :
      Metric.cthickening delta
          (Kakeya.unitSegment source.base source.direction) =
        ⋃ segmentPoint ∈ Kakeya.unitSegment source.base source.direction,
          Metric.closedBall segmentPoint delta :=
    hsegmentCompact.cthickening_eq_biUnion_closedBall hdeltaNonneg
  rw [hdecomposition] at hsourcePoint'
  rcases Set.mem_iUnion₂.mp hsourcePoint' with
    ⟨segmentPoint, hsegmentPoint, hdistance⟩
  have himageSegment :
      wz2PaperLiteralUnitRescalingMap anchor hrho segmentPoint ∈
        Kakeya.unitSegment
          (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho).base
          (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho).direction :=
    wz2PaperLiteral_image_unitSegment_subset_no_line_class
      source anchor hdelta hrho hrhoOne hrhoSmall hdelta_le_rho hcontainment
      ⟨segmentPoint, hsegmentPoint, rfl⟩
  have hdistanceSource : dist sourcePoint segmentPoint ≤ delta := by
    simpa [Metric.mem_closedBall] using hdistance
  have hdistanceImage :
      dist
          (wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint)
          (wz2PaperLiteralUnitRescalingMap anchor hrho segmentPoint) ≤
        delta / rho := by
    rw [dist_eq_norm, wz2PaperLiteralUnitRescalingMap_sub]
    calc
      ‖wz2PaperLiteralUnitRescalingLinear anchor (sourcePoint - segmentPoint)‖ ≤
          ‖sourcePoint - segmentPoint‖ / (100 * rho) :=
        wz2PaperLiteralUnitRescalingLinear_norm_le anchor hrho hrhoOne _
      _ ≤ delta / (100 * rho) := by
        gcongr
        simpa [dist_eq_norm] using hdistanceSource
      _ ≤ delta / rho := by
        exact (div_le_div_iff₀ (mul_pos (by norm_num) hrho) hrho).2
          (by nlinarith [hdelta, hrho])
  exact
    Metric.mem_cthickening_of_dist_le
      (wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint)
      (wz2PaperLiteralUnitRescalingMap anchor hrho segmentPoint)
      (delta / rho)
      (Kakeya.unitSegment
        (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho).base
        (wz2PaperLiteralOrdinaryRescaledTube source anchor hrho).direction)
      himageSegment hdistanceImage

end Kakeya.Assouad

end
