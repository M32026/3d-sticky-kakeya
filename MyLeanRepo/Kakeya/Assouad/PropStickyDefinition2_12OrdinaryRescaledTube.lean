import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingJacobian
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeReversal

/-!
# Reversal-invariant ordinary target containing one literal affine image

The WZ target tube records only the transformed coaxial line and is used with
the cropped full-line carrier.  It need not contain the exact affine image in
its ordinary unit-segment carrier.

For the public Definition 2.12 family we center the ordinary target at the
image of the source midpoint and orient it by the paper-positive source
direction.  This construction depends only on the unoriented source segment:
reversing the stored base and direction does not change the target carrier.
The transformed source unit segment has length at most `3 / 200`, while the
transformed transverse radius is at most `delta / (100 rho)`.  Hence the
complete literal affine image lies in this ordinary `(delta / rho)`-tube.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

/-- Literal image direction of the paper-positive source orientation. -/
def wz2PaperLiteralSourceImageDirection
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho) : Point3 :=
  wz2PaperLiteralUnitRescalingLinear anchor (wz1PaperDirection source)

theorem wz2PaperLiteralSourceImageDirection_ne_zero
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    wz2PaperLiteralSourceImageDirection source anchor ≠ 0 := by
  intro hzero
  have hmap :
      wz2PaperLiteralUnitRescalingLinear anchor
          (wz1PaperDirection source) =
        wz2PaperLiteralUnitRescalingLinear anchor 0 := by
    simpa [wz2PaperLiteralSourceImageDirection] using hzero
  have hdirection :
      wz1PaperDirection source = 0 :=
    wz2PaperLiteralUnitRescalingLinear_injective anchor hrho hmap
  have hnorm := wz1PaperDirection_norm source
  rw [hdirection, norm_zero] at hnorm
  norm_num at hnorm

/-- Canonically centered base of the source segment in paper-positive
orientation. -/
def wz2PaperCanonicalSourceBase
    {delta : ℝ} (source : Kakeya.DeltaTube delta) : Point3 :=
  wz2PaperTubeMidpoint source -
    (1 / 2 : ℝ) • wz1PaperDirection source

/-- The canonical centered, paper-oriented segment is the original unoriented
source segment. -/
theorem wz2PaperCanonicalSourceSegment_eq
    {delta : ℝ} (source : Kakeya.DeltaTube delta) :
    Kakeya.unitSegment
        (wz2PaperCanonicalSourceBase source)
        (wz1PaperDirection source) =
      Kakeya.unitSegment source.base source.direction := by
  unfold wz2PaperCanonicalSourceBase wz2PaperTubeMidpoint
  unfold wz1PaperDirection
  split_ifs with hdirection
  · have hbase :
        source.base + (1 / 2 : ℝ) • source.direction -
            (1 / 2 : ℝ) • source.direction =
          source.base := by module
    rw [hbase]
  · ext point
    simp only [Kakeya.unitSegment, Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨parameter, hparameter, rfl⟩
      refine ⟨1 - parameter, ⟨by linarith, by linarith⟩, ?_⟩
      module
    · rintro ⟨parameter, hparameter, rfl⟩
      refine ⟨1 - parameter, ⟨by linarith, by linarith⟩, ?_⟩
      module

/-- Reversing the stored orientation leaves the canonical source midpoint
unchanged. -/
theorem wz2PaperTubeMidpoint_reverse
    {delta : ℝ} (source : Kakeya.DeltaTube delta) :
    wz2PaperTubeMidpoint (reverseTube source) =
      wz2PaperTubeMidpoint source := by
  unfold wz2PaperTubeMidpoint reverseTube
  module

/-- The paper-positive direction is insensitive to reversing a tube whose
axis lies in the fixed positive vertical chart. -/
theorem wz1PaperDirection_reverse_of_lineClass
    {delta : ℝ} {source : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass source) :
    wz1PaperDirection (reverseTube source) =
      wz1PaperDirection source := by
  have hpositive :
      0 < (wz1PaperDirection source) (2 : Fin 3) := by
    linarith [hline.1]
  by_cases hsource : 0 ≤ source.direction (2 : Fin 3)
  · have hsourceStrict : 0 < source.direction (2 : Fin 3) := by
      unfold wz1PaperDirection at hpositive
      rw [if_pos hsource] at hpositive
      exact hpositive
    unfold wz1PaperDirection reverseTube
    rw [if_pos hsource]
    have hreversed :
        ¬ 0 ≤ (-source.direction) (2 : Fin 3) := by
      simp only [PiLp.neg_apply]
      linarith
    rw [if_neg hreversed]
    simp
  · have hsourceStrict : source.direction (2 : Fin 3) < 0 :=
      lt_of_not_ge hsource
    unfold wz1PaperDirection reverseTube
    rw [if_neg hsource]
    have hreversed :
        0 ≤ (-source.direction) (2 : Fin 3) := by
      simp only [PiLp.neg_apply]
      linarith
    rw [if_pos hreversed]

/-- Public ordinary target centered at the transformed source midpoint. -/
def wz2PaperLiteralOrdinaryRescaledTube
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    Kakeya.DeltaTube (delta / rho) where
  base :=
    wz2PaperLiteralUnitRescalingMap anchor hrho
        (wz2PaperTubeMidpoint source) -
      (1 / 2 : ℝ) •
        NormedSpace.normalize
          (wz2PaperLiteralSourceImageDirection source anchor)
  direction :=
    NormedSpace.normalize
      (wz2PaperLiteralSourceImageDirection source anchor)
  direction_unit :=
    NormedSpace.norm_normalize
      (wz2PaperLiteralSourceImageDirection_ne_zero
        source anchor hrho)

/-- The repaired public target is invariant under source-tube reversal. -/
theorem wz2PaperLiteralOrdinaryRescaledTube_reverse
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (hline : WZ1PaperTubeInLineClass source) :
    wz2PaperLiteralOrdinaryRescaledTube
        (reverseTube source) anchor hrho =
      wz2PaperLiteralOrdinaryRescaledTube source anchor hrho := by
  rw [Kakeya.DeltaTube.mk.injEq]
  constructor
  · simp only [wz2PaperLiteralOrdinaryRescaledTube,
      wz2PaperLiteralSourceImageDirection]
    rw [wz2PaperTubeMidpoint_reverse,
      wz1PaperDirection_reverse_of_lineClass hline]
  · simp only [wz2PaperLiteralOrdinaryRescaledTube,
      wz2PaperLiteralSourceImageDirection]
    rw [wz1PaperDirection_reverse_of_lineClass hline]

theorem wz2PaperLiteralOrdinaryRescaledTube_axis
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) :
    tubeAxisLine
        (wz2PaperLiteralOrdinaryRescaledTube
          source anchor hrho) =
      wz2PaperLiteralUnitRescalingMap anchor hrho ''
        tubeAxisLine source := by
  let imageDirection :=
    wz2PaperLiteralSourceImageDirection source anchor
  have himageNe : imageDirection ≠ 0 :=
    wz2PaperLiteralSourceImageDirection_ne_zero
      source anchor hrho
  have hsourceAxis :
      tubeAxisLine source =
        Set.range
          (fun parameter : ℝ =>
            wz2PaperTubeMidpoint source +
              parameter • wz1PaperDirection source) := by
    ext point
    unfold tubeAxisLine wz2PaperTubeMidpoint wz1PaperDirection
    split_ifs with hdirection
    · constructor
      · rintro ⟨parameter, rfl⟩
        exact ⟨parameter - 1 / 2, by module⟩
      · rintro ⟨parameter, rfl⟩
        exact ⟨parameter + 1 / 2, by module⟩
    · constructor
      · rintro ⟨parameter, rfl⟩
        exact ⟨1 / 2 - parameter, by module⟩
      · rintro ⟨parameter, rfl⟩
        exact ⟨1 / 2 - parameter, by module⟩
  rw [hsourceAxis,
    wz2PaperLiteralUnitRescalingMap_image_range]
  change
    {point |
      ∃ parameter : ℝ,
        point =
          (wz2PaperLiteralUnitRescalingMap anchor hrho
              (wz2PaperTubeMidpoint source) -
            (1 / 2 : ℝ) • NormedSpace.normalize imageDirection) +
            parameter • NormedSpace.normalize imageDirection} =
      Set.range
        (fun parameter : ℝ =>
          wz2PaperLiteralUnitRescalingMap anchor hrho
              (wz2PaperTubeMidpoint source) +
            parameter • imageDirection)
  ext point
  simp only [Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨parameter, rfl⟩
    refine
      ⟨(parameter - 1 / 2) * ‖imageDirection‖⁻¹, ?_⟩
    have hnorm :
        NormedSpace.normalize imageDirection =
          ‖imageDirection‖⁻¹ • imageDirection := rfl
    rw [hnorm, smul_smul]
    module
  · rintro ⟨parameter, rfl⟩
    refine ⟨1 / 2 + parameter * ‖imageDirection‖, ?_⟩
    have hnorm :
        NormedSpace.normalize imageDirection =
          ‖imageDirection‖⁻¹ • imageDirection := rfl
    have hnormNe : ‖imageDirection‖ ≠ 0 :=
      norm_ne_zero_iff.mpr himageNe
    rw [hnorm, smul_smul]
    have hcancel : ‖imageDirection‖ * ‖imageDirection‖⁻¹ = 1 :=
      mul_inv_cancel₀ hnormNe
    have hcoefficient :
        (1 / 2 + parameter * ‖imageDirection‖) *
            ‖imageDirection‖⁻¹ =
          (1 / 2) * ‖imageDirection‖⁻¹ + parameter := by
      rw [add_mul, mul_assoc, hcancel, mul_one]
    simp only [smul_smul]
    rw [hcoefficient]
    module

/-- The transformed source unit segment lies in the public target segment. -/
theorem wz2PaperLiteral_image_unitSegment_subset
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source anchor) :
    wz2PaperLiteralUnitRescalingMap anchor hrho ''
        Kakeya.unitSegment source.base source.direction ⊆
      Kakeya.unitSegment
        (wz2PaperLiteralOrdinaryRescaledTube
          source anchor hrho).base
        (wz2PaperLiteralOrdinaryRescaledTube
          source anchor hrho).direction := by
  rintro point ⟨sourcePoint, ⟨parameter, hparameter, rfl⟩, rfl⟩
  let imageDirection :=
    wz2PaperLiteralSourceImageDirection source anchor
  have himageNe : imageDirection ≠ 0 :=
    wz2PaperLiteralSourceImageDirection_ne_zero
      source anchor hrho
  have hnormUpper :
      ‖imageDirection‖ ≤ 3 / 200 :=
    by
      have hstored :=
        wz2PaperLiteralUnitRescalingLinear_sourceDirection_norm_le
          hrho hrhoOne hcover
      unfold imageDirection wz2PaperLiteralSourceImageDirection
      unfold wz1PaperDirection
      split_ifs
      · exact hstored
      · simpa using hstored
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
    ⟨1 / 2 +
        (canonicalParameter - 1 / 2) * ‖imageDirection‖,
      ?_, ?_⟩
  · constructor
    · nlinarith [hcanonicalParameter.1, hcanonicalParameter.2,
        hnormUpper, hnormNonneg]
    · nlinarith [hcanonicalParameter.1, hcanonicalParameter.2,
        hnormUpper, hnormNonneg]
  · have hcanonicalPoint' :
        source.base + parameter • source.direction =
          wz2PaperCanonicalSourceBase source +
            canonicalParameter • wz1PaperDirection source :=
      hcanonicalPoint.symm
    change
      (wz2PaperLiteralOrdinaryRescaledTube
          source anchor hrho).base +
          (1 / 2 +
              (canonicalParameter - 1 / 2) *
                ‖imageDirection‖) •
            (wz2PaperLiteralOrdinaryRescaledTube
              source anchor hrho).direction =
        wz2PaperLiteralUnitRescalingMap anchor hrho
          (source.base + parameter • source.direction)
    rw [hcanonicalPoint']
    rw [wz2PaperLiteralUnitRescalingMap_add, map_smul]
    change
      (wz2PaperLiteralUnitRescalingMap anchor hrho
            (wz2PaperTubeMidpoint source) -
          (1 / 2 : ℝ) •
            NormedSpace.normalize imageDirection) +
          (1 / 2 +
              (canonicalParameter - 1 / 2) *
                ‖imageDirection‖) •
            NormedSpace.normalize imageDirection =
        wz2PaperLiteralUnitRescalingMap anchor hrho
            (wz2PaperCanonicalSourceBase source) +
          canonicalParameter •
            wz2PaperLiteralUnitRescalingLinear anchor
              (wz1PaperDirection source)
    have hnormalize :
        NormedSpace.normalize imageDirection =
          ‖imageDirection‖⁻¹ • imageDirection := rfl
    rw [hnormalize, smul_smul]
    have hnormNe : ‖imageDirection‖ ≠ 0 :=
      norm_ne_zero_iff.mpr himageNe
    have hcoefficient :
        (1 / 2 +
            (canonicalParameter - 1 / 2) *
              ‖imageDirection‖) *
            ‖imageDirection‖⁻¹ =
          (1 / 2) * ‖imageDirection‖⁻¹ +
            (canonicalParameter - 1 / 2) := by
      rw [add_mul, mul_assoc, mul_inv_cancel₀ hnormNe, mul_one]
    simp only [smul_smul]
    rw [hcoefficient]
    unfold wz2PaperCanonicalSourceBase
    rw [show
      wz2PaperTubeMidpoint source -
          (1 / 2 : ℝ) • wz1PaperDirection source =
        wz2PaperTubeMidpoint source +
          (-(1 / 2 : ℝ) • wz1PaperDirection source) by module]
    rw [wz2PaperLiteralUnitRescalingMap_add, map_smul]
    change
      _ =
        (wz2PaperLiteralUnitRescalingMap anchor hrho
            (wz2PaperTubeMidpoint source) +
          (-(1 / 2 : ℝ)) • imageDirection) +
          canonicalParameter • imageDirection
    module

/-- The complete literal affine image lies in the ordinary public target. -/
theorem wz2PaperLiteral_image_carrier_subset_ordinary
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hcover : WZ1PaperTubeCovers source anchor) :
    wz2PaperLiteralUnitRescalingMap anchor hrho ''
        source.carrier ⊆
      (wz2PaperLiteralOrdinaryRescaledTube
        source anchor hrho).carrier := by
  intro imagePoint himagePoint
  rcases himagePoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  have hsegmentCompact :
      IsCompact (Kakeya.unitSegment source.base source.direction) :=
    isCompact_Icc.image
      (continuous_const.add
        (continuous_id.smul continuous_const))
  have hdeltaNonneg : 0 ≤ delta := hdelta.le
  have hsourcePoint' :
      sourcePoint ∈ Metric.cthickening delta
        (Kakeya.unitSegment source.base source.direction) :=
    hsourcePoint
  have hdecomposition :
      Metric.cthickening delta
          (Kakeya.unitSegment source.base source.direction) =
        ⋃ segmentPoint ∈
          Kakeya.unitSegment source.base source.direction,
            Metric.closedBall segmentPoint delta :=
    hsegmentCompact.cthickening_eq_biUnion_closedBall hdeltaNonneg
  rw [hdecomposition] at hsourcePoint'
  rcases Set.mem_iUnion₂.mp hsourcePoint' with
    ⟨segmentPoint, hsegmentPoint, hdistance⟩
  have himageSegment :
      wz2PaperLiteralUnitRescalingMap anchor hrho segmentPoint ∈
        Kakeya.unitSegment
          (wz2PaperLiteralOrdinaryRescaledTube
            source anchor hrho).base
          (wz2PaperLiteralOrdinaryRescaledTube
            source anchor hrho).direction :=
    wz2PaperLiteral_image_unitSegment_subset
      source anchor hrho hrhoOne hcover
      ⟨segmentPoint, hsegmentPoint, rfl⟩
  have hdistanceSource :
      dist sourcePoint segmentPoint ≤ delta := by
    simpa [Metric.mem_closedBall] using hdistance
  have hdistanceImage :
      dist
          (wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint)
          (wz2PaperLiteralUnitRescalingMap anchor hrho segmentPoint) ≤
        delta / rho := by
    rw [dist_eq_norm, wz2PaperLiteralUnitRescalingMap_sub]
    calc
      ‖wz2PaperLiteralUnitRescalingLinear anchor
          (sourcePoint - segmentPoint)‖ ≤
          ‖sourcePoint - segmentPoint‖ / (100 * rho) :=
        wz2PaperLiteralUnitRescalingLinear_norm_le
          anchor hrho hrhoOne _
      _ ≤ delta / (100 * rho) := by
        gcongr
        simpa [dist_eq_norm] using hdistanceSource
      _ ≤ delta / rho := by
        exact
          (div_le_div_iff₀
            (mul_pos (by norm_num) hrho) hrho).2
            (by nlinarith [hdelta, hrho])
  exact
    Metric.mem_cthickening_of_dist_le
      (wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint)
      (wz2PaperLiteralUnitRescalingMap anchor hrho segmentPoint)
      (delta / rho)
      (Kakeya.unitSegment
        (wz2PaperLiteralOrdinaryRescaledTube
          source anchor hrho).base
        (wz2PaperLiteralOrdinaryRescaledTube
          source anchor hrho).direction)
      himageSegment hdistanceImage

/-- The public ordinary target and any canonical literal WZ target have the
same full coaxial line. -/
theorem wz2PaperLiteralOrdinaryRescaledTube_same_axis
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (literalTarget : Kakeya.DeltaTube (delta / rho))
    (hliteralAxis :
      tubeAxisLine literalTarget =
        wz2PaperLiteralUnitRescalingMap anchor hrho ''
          tubeAxisLine source) :
    tubeAxisLine
        (wz2PaperLiteralOrdinaryRescaledTube
          source anchor hrho) =
      tubeAxisLine literalTarget := by
  rw [wz2PaperLiteralOrdinaryRescaledTube_axis,
    ← hliteralAxis]

end Kakeya.Assouad

end
