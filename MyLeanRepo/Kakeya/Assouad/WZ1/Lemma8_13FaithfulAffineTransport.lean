import MyLeanRepo.Kakeya.Assouad.WZ1.ActiveProjectionFrostmanTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.FrostmanAffineHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulSanity

/-!
# Affine transport for the faithful PDF Lemma 8.13 first stage

This module closes the common lower-Lipschitz, separation, and active-`F`
Frostman transport used in both normalization-width regimes.
-/

namespace Kakeya.Assouad

open scoped ENNReal

noncomputable section

/-- Application formula for the half-scaled transpose map. -/
lemma wz1Lemma8_13FaithfulFMap_apply
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input)
    (point : Point2) :
    wz1Lemma8_13FaithfulFMap input hwidth point =
      (1 / 2 : ℝ) •
        wideCoarsePhiF
          input.direction
          (wz1Lemma8_13FaithfulNormalizationWidth input)
          hwidth input.direction_unit point := by
  rfl

/-- The half-scaled endpoint map divides perpendicular difference
coordinates by twice the normalization width. -/
lemma wz1Lemma8_13FaithfulGMap_sub_inner_perp
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input)
    (first second : Point2) :
    inner ℝ
        (wz1Lemma8_13FaithfulGMap input hwidth first -
          wz1Lemma8_13FaithfulGMap input hwidth second)
        (wz1Perp2 input.direction) =
      inner ℝ (first - second) (wz1Perp2 input.direction) /
        (2 * wz1Lemma8_13FaithfulNormalizationWidth input) := by
  change
    inner ℝ
        ((1 / 2 : ℝ) •
            wideCoarsePhiG input.direction
              (wz1Lemma8_13FaithfulNormalizationWidth input)
              hwidth input.base 0 input.direction_unit first -
          (1 / 2 : ℝ) •
            wideCoarsePhiG input.direction
              (wz1Lemma8_13FaithfulNormalizationWidth input)
              hwidth input.base 0 input.direction_unit second)
        (wz1Perp2 input.direction) =
      inner ℝ (first - second) (wz1Perp2 input.direction) /
        (2 * wz1Lemma8_13FaithfulNormalizationWidth input)
  rw [← smul_sub, real_inner_smul_left,
    wideCoarsePhiG_sub_inner_perp]
  ring

/-- The faithful endpoint map has the same uniform lower Lipschitz factor as
the faithful first-coordinate map. -/
lemma wz1Lemma8_13FaithfulGMap_lower_lipschitz
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input) :
    ∀ first second : Point2,
      (1 / (2 * wz1Lemma8_13FaithfulAspect input)) *
          dist first second ≤
        dist
          (wz1Lemma8_13FaithfulGMap input hwidth first)
          (wz1Lemma8_13FaithfulGMap input hwidth second) := by
  intro first second
  exact
    wideCoarsePhiG_half_lower_lipschitz
      hwidth input.base 0 input.direction_unit first second

/-- A source separated at the frozen pre-normalization scale remains
separated at the frozen public source scale after faithful endpoint
normalization. -/
lemma wz1Lemma8_13_source_image_separated
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input)
    {source : DiscreteSet 2}
    (hsource :
      source.IsDeltaSeparated
        (wz1Lemma8_13FaithfulSelectionScale input)) :
    let mapped : DiscreteSet 2 :=
      source.image
        (wz1Lemma8_13FaithfulGMap input hwidth)
    mapped.IsDeltaSeparated
        (wz1Lemma8_13FaithfulSourceScale input) := by
  dsimp only
  have haspect :
      0 < wz1Lemma8_13FaithfulAspect input :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hm :
      0 <
        1 / (2 * wz1Lemma8_13FaithfulAspect input) := by
    positivity
  have hmapped :=
    DiscreteSet.isDeltaSeparated_map_expansive
      hsource hm
      (wz1Lemma8_13FaithfulGMap_lower_lipschitz
        input hwidth)
  have hscale :
      (1 / (2 * wz1Lemma8_13FaithfulAspect input)) *
          wz1Lemma8_13FaithfulSelectionScale input =
        wz1Lemma8_13FaithfulSourceScale input := by
    dsimp only [wz1Lemma8_13FaithfulSelectionScale,
      wz1Lemma8_13FaithfulSourceScale]
    field_simp [haspect.ne']
    ring
  rw [hscale] at hmapped
  exact hmapped

/-- Standard `G₁`--`G₂` separation and the faithful endpoint lower
Lipschitz bound give the frozen normalized endpoint-distance window. -/
lemma wz1Lemma8_13FaithfulGMap_endpoint_distance_lower
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input)
    (viewpoint :
      WZ1Lemma49ActiveViewpointData
        input.F input.G₁ input.G₂ input.H
        (Kakeya.realRpowENN delta eta)
        input.base input.direction input.width
        (wz1Lemma8_13FaithfulActiveWidth input))
    {point : Point2} (hpoint : point ∈ viewpoint.source) :
    1 / (4 * wz1Lemma8_13FaithfulAspect input) ≤
      dist
        (wz1Lemma8_13FaithfulGMap input hwidth point)
        (wz1Lemma8_13FaithfulGMap
          input hwidth viewpoint.viewpoint) := by
  have haspect :
      0 < wz1Lemma8_13FaithfulAspect input :=
    zero_lt_one.trans_le (le_max_left _ _)
  have hseparation :
      1 / 2 ≤ dist point viewpoint.viewpoint :=
    input.standardSeparation.2.2.2.1
      point (viewpoint.source_subset hpoint)
      viewpoint.viewpoint viewpoint.viewpoint_mem
  calc
    1 / (4 * wz1Lemma8_13FaithfulAspect input) =
        (1 / (2 * wz1Lemma8_13FaithfulAspect input)) *
          (1 / 2) := by ring
    _ ≤
        (1 / (2 * wz1Lemma8_13FaithfulAspect input)) *
          dist point viewpoint.viewpoint := by
            gcongr
    _ ≤
      dist
        (wz1Lemma8_13FaithfulGMap input hwidth point)
        (wz1Lemma8_13FaithfulGMap
          input hwidth viewpoint.viewpoint) :=
      wz1Lemma8_13FaithfulGMap_lower_lipschitz
        input hwidth point viewpoint.viewpoint

/-- The active-viewpoint sign choice commutes with the faithful endpoint
normalization: its oriented perpendicular coordinate is divided by exactly
twice the normalization width. -/
lemma wz1Lemma8_13FaithfulGMap_sub_inner_oriented
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input)
    (viewpoint :
      WZ1Lemma49ActiveViewpointData
        input.F input.G₁ input.G₂ input.H
        (Kakeya.realRpowENN delta eta)
        input.base input.direction input.width
        (wz1Lemma8_13FaithfulActiveWidth input))
    (first second : Point2) :
    inner ℝ
        (wz1Lemma8_13FaithfulGMap input hwidth first -
          wz1Lemma8_13FaithfulGMap input hwidth second)
        (wz1Perp2 viewpoint.orientedDirection) =
      inner ℝ (first - second)
          (wz1Perp2 viewpoint.orientedDirection) /
        (2 * wz1Lemma8_13FaithfulNormalizationWidth input) := by
  rcases viewpoint.orientedDirection_eq with horiented | horiented
  · simpa only [horiented] using
      wz1Lemma8_13FaithfulGMap_sub_inner_perp
        input hwidth first second
  · rw [horiented, wz1Lemma49_perp_neg,
      inner_neg_right, inner_neg_right]
    rw [wz1Lemma8_13FaithfulGMap_sub_inner_perp]
    ring

/-- The original active fiber's strip bound becomes the frozen normalized
angular-width bound. -/
lemma wz1Lemma8_13FaithfulGMap_source_strip
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input)
    (viewpoint :
      WZ1Lemma49ActiveViewpointData
        input.F input.G₁ input.G₂ input.H
        (Kakeya.realRpowENN delta eta)
        input.base input.direction input.width
        (wz1Lemma8_13FaithfulActiveWidth input))
    {point : Point2} (hpoint : point ∈ viewpoint.source) :
    |inner ℝ
        (wz1Lemma8_13FaithfulGMap input hwidth point -
          wz1Lemma8_13FaithfulGMap input hwidth input.base)
        (wz1Perp2 viewpoint.orientedDirection)| ≤
      wz1Lemma8_13FaithfulAngularScale input / 2 := by
  rw [wz1Lemma8_13FaithfulGMap_sub_inner_oriented]
  have hsource := viewpoint.source_strip point hpoint
  rw [show (2 * input.width) / 2 = input.width by ring] at hsource
  have hdenominator :
      0 < 2 * wz1Lemma8_13FaithfulNormalizationWidth input := by
    positivity
  rw [abs_div, abs_of_pos hdenominator]
  dsimp only [wz1Lemma8_13FaithfulAngularScale]
  calc
    |inner ℝ (point - input.base)
          (wz1Perp2 viewpoint.orientedDirection)| /
        (2 * wz1Lemma8_13FaithfulNormalizationWidth input)
        ≤ input.width /
          (2 * wz1Lemma8_13FaithfulNormalizationWidth input) := by
            gcongr
    _ =
      input.width /
          wz1Lemma8_13FaithfulNormalizationWidth input / 2 := by
            ring

/-- The original active fiber's one-sided viewpoint gap becomes the frozen
normalized side bound. -/
lemma wz1Lemma8_13FaithfulGMap_source_side
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input)
    (viewpoint :
      WZ1Lemma49ActiveViewpointData
        input.F input.G₁ input.G₂ input.H
        (Kakeya.realRpowENN delta eta)
        input.base input.direction input.width
        (wz1Lemma8_13FaithfulActiveWidth input))
    {point : Point2} (hpoint : point ∈ viewpoint.source) :
    wz1Lemma8_13FaithfulSide input / 2 ≤
      inner ℝ
        (wz1Lemma8_13FaithfulGMap input hwidth point -
          wz1Lemma8_13FaithfulGMap input hwidth viewpoint.viewpoint)
        (wz1Perp2 viewpoint.orientedDirection) := by
  rw [wz1Lemma8_13FaithfulGMap_sub_inner_oriented]
  have hsource := viewpoint.source_side point hpoint
  have hdenominator :
      0 < 2 * wz1Lemma8_13FaithfulNormalizationWidth input := by
    positivity
  rw [viewpoint.side_eq] at hsource
  rw [show (2 *
      (wz1Lemma8_13FaithfulActiveWidth input - input.width)) / 2 =
        wz1Lemma8_13FaithfulActiveWidth input - input.width by ring]
      at hsource
  dsimp only [wz1Lemma8_13FaithfulSide]
  calc
    (wz1Lemma8_13FaithfulActiveWidth input - input.width) /
          wz1Lemma8_13FaithfulNormalizationWidth input / 2 =
        (wz1Lemma8_13FaithfulActiveWidth input - input.width) /
          (2 * wz1Lemma8_13FaithfulNormalizationWidth input) := by
            ring
    _ ≤
      inner ℝ (point - viewpoint.viewpoint)
          (wz1Perp2 viewpoint.orientedDirection) /
        (2 * wz1Lemma8_13FaithfulNormalizationWidth input) := by
          exact div_le_div_of_nonneg_right hsource hdenominator.le

/-- A radius-two image becomes a unit-ball image after the common faithful
factor `1/2`. -/
lemma wz1Lemma8_13_half_image_in_unit_ball
    {source : DiscreteSet 2} {map : Point2 → Point2}
    (hmap : ∀ point ∈ source, dist (map point) 0 ≤ 2) :
    let mapped : DiscreteSet 2 :=
      source.image fun point =>
        wz1Lemma8_13HalfLinear (map point)
    mapped.IsInUnitBall := by
  dsimp only
  intro targetPoint htargetPoint
  rcases Finset.mem_image.mp htargetPoint with
    ⟨sourcePoint, hsourcePoint, rfl⟩
  have hsourceNorm :
      ‖map sourcePoint‖ ≤ 2 := by
    simpa [dist_zero_right] using
      hmap sourcePoint hsourcePoint
  change
    dist (wz1Lemma8_13HalfLinear (map sourcePoint)) 0 ≤ 1
  have hnorm :
      ‖wz1Lemma8_13HalfLinear (map sourcePoint)‖ =
        (1 / 2 : ℝ) * ‖map sourcePoint‖ := by
    simp [wz1Lemma8_13HalfLinear, norm_smul]
  rw [dist_zero_right, hnorm]
  linarith

/-- The faithful half-scaled first-coordinate image lies in the unit ball
whenever the source lies in the matching orthogonal normalization strip. -/
lemma wz1Lemma8_13FaithfulFMap_image_ball
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input)
    {source : DiscreteSet 2}
    (hstrip :
      ∀ point ∈ source,
        |inner ℝ point input.direction| ≤
          wz1Lemma8_13FaithfulNormalizationWidth input)
    (hball : source.IsInUnitBall) :
    let mapped : DiscreteSet 2 :=
      source.image
        (wz1Lemma8_13FaithfulFMap input hwidth)
    mapped.IsInUnitBall := by
  have hbounded :
      ∀ point ∈ source,
        dist
          (wideCoarsePhiF input.direction
            (wz1Lemma8_13FaithfulNormalizationWidth input)
            hwidth input.direction_unit point) 0 ≤ 2 :=
    wideCoarsePhiF_image_bounded hstrip hball
  have hhalf :=
    wz1Lemma8_13_half_image_in_unit_ball hbounded
  change
    DiscreteSet.IsInUnitBall
      (source.image fun point =>
        wz1Lemma8_13HalfLinear
          (wideCoarsePhiF input.direction
            (wz1Lemma8_13FaithfulNormalizationWidth input)
            hwidth input.direction_unit point))
  exact hhalf

/-- The faithful half-scaled endpoint image lies in the unit ball whenever
the source lies in the common normalization strip. -/
lemma wz1Lemma8_13FaithfulGMap_image_ball
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input)
    {source : DiscreteSet 2}
    (hstrip :
      ∀ point ∈ source,
        |inner ℝ (point - input.base)
          (wz1Perp2 input.direction)| ≤
            wz1Lemma8_13FaithfulNormalizationWidth input)
    (hball : source.IsInUnitBall) :
    let mapped : DiscreteSet 2 :=
      source.image
        (wz1Lemma8_13FaithfulGMap input hwidth)
    mapped.IsInUnitBall := by
  have hbounded :
      ∀ point ∈ source,
        dist
          (wideCoarsePhiG input.direction
            (wz1Lemma8_13FaithfulNormalizationWidth input)
            hwidth input.base 0 input.direction_unit point) 0 ≤ 2 := by
    intro point hpoint
    simpa [dist_zero_right] using
      wideCoarsePhiG_zero_anchor_image_bounded
        hstrip hball point hpoint
  have hhalf :=
    wz1Lemma8_13_half_image_in_unit_ball hbounded
  change
    DiscreteSet.IsInUnitBall
      (source.image fun point =>
        wz1Lemma8_13HalfLinear
          (wideCoarsePhiG input.direction
            (wz1Lemma8_13FaithfulNormalizationWidth input)
            hwidth input.base 0 input.direction_unit point))
  exact hhalf

/-- The faithful first-coordinate map has lower Lipschitz factor
`1 / (2 * aspect)` without assuming the normalization width is at most one. -/
lemma wz1Lemma8_13FaithfulFMap_lower_lipschitz
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input) :
    ∀ first second : Point2,
      (1 / (2 * wz1Lemma8_13FaithfulAspect input)) *
          dist first second ≤
        dist
          (wz1Lemma8_13FaithfulFMap input hwidth first)
          (wz1Lemma8_13FaithfulFMap input hwidth second) := by
  intro first second
  rw [wz1Lemma8_13FaithfulFMap_apply,
    wz1Lemma8_13FaithfulFMap_apply]
  exact
    wideCoarsePhiF_half_lower_lipschitz
      hwidth input.direction_unit first second

/-- Active first-coordinate points of a literal uniformly dense subgraph
remain `delta`-separated. -/
lemma wz1Lemma8_13_activeF_separated
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    {c : ENNReal}
    {G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hUniform :
      WZ1UniformTripleDensity c input.F G₁ G₂ H) :
    (wz1ActiveTripleProjection H 0).IsDeltaSeparated delta := by
  intro first hfirst second hsecond hne
  exact input.F_separated
    (active_triple_projection_subset hUniform 0 hfirst)
    (active_triple_projection_subset hUniform 0 hsecond)
    hne

/-- The active first-coordinate projection inherits the ambient Frostman
estimate with exactly the reciprocal graph-density loss. -/
lemma wz1Lemma8_13_activeF_frostman
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    {c : ENNReal}
    {G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hUniform :
      WZ1UniformTripleDensity c input.F G₁ G₂ H)
    (hc : c ≠ 0) :
    (wz1ActiveTripleProjection H 0).IsFrostman delta 1
      (Kakeya.realRpowENN delta (-eta) / c) := by
  exact active_projection_frostman_transfer
    0 hUniform input.F_frostman hc

/-- Concrete real Frostman constant before affine transport. -/
def wz1Lemma8_13FaithfulSourceFConstant
    (delta eta : ℝ) : ℝ :=
  16 * Real.rpow delta (-2 * eta)

/-- Concrete real Frostman constant after the half-scaled affine transport. -/
def wz1Lemma8_13FaithfulFineConstant
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta) : ℝ :=
  2 * wz1Lemma8_13FaithfulAspect input *
    wz1Lemma8_13FaithfulSourceFConstant delta eta

/-- Convert the active-projection ENNReal quotient to the concrete real
constant `16 * delta^(-2*eta)`. -/
lemma wz1Lemma8_13_sourceF_constant_eq
    {delta eta : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta (-eta) /
        (Kakeya.realRpowENN delta eta / 16) =
      ENNReal.ofReal
        (wz1Lemma8_13FaithfulSourceFConstant delta eta) := by
  have hpositiveEta :
      0 < Real.rpow delta eta :=
    Real.rpow_pos_of_pos hdelta _
  have hnegative :
      Real.rpow delta (-eta) =
        (Real.rpow delta eta)⁻¹ :=
    Real.rpow_neg hdelta.le eta
  simp only [Kakeya.realRpowENN,
    wz1Lemma8_13FaithfulSourceFConstant]
  have hreal :
      Real.rpow delta (-eta) /
          (Real.rpow delta eta / 16) =
        16 * Real.rpow delta (-2 * eta) := by
    have hnegativeTwo :
        Real.rpow delta (-2 * eta) =
          (Real.rpow delta (2 * eta))⁻¹ := by
      rw [show -2 * eta = -(2 * eta) by ring]
      exact Real.rpow_neg hdelta.le (2 * eta)
    rw [hnegative, hnegativeTwo]
    have hsum :
        Real.rpow delta eta * Real.rpow delta eta =
          Real.rpow delta (2 * eta) := by
      calc
        Real.rpow delta eta * Real.rpow delta eta =
            Real.rpow delta (eta + eta) :=
          (Real.rpow_add hdelta eta eta).symm
        _ = Real.rpow delta (2 * eta) := by
          congr 1
          ring
    field_simp [hpositiveEta.ne']
    rw [← hsum]
    field_simp [hpositiveEta.ne']
  have hdenominator :
      ENNReal.ofReal (Real.rpow delta eta / 16) =
        ENNReal.ofReal (Real.rpow delta eta) / 16 := by
    simpa using
      (ENNReal.ofReal_div_of_pos
        (x := Real.rpow delta eta)
        (y := 16) (by norm_num))
  rw [← hdenominator]
  rw [← ENNReal.ofReal_div_of_pos
      (show 0 < Real.rpow delta eta / 16 by positivity)]
  exact congrArg ENNReal.ofReal hreal

/-- The concrete active-source constant is at least one at small scales. -/
lemma wz1Lemma8_13_sourceFConstant_ge_one
    {delta eta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (heta : 0 < eta) :
    1 ≤ wz1Lemma8_13FaithfulSourceFConstant delta eta := by
  dsimp only [wz1Lemma8_13FaithfulSourceFConstant]
  have hpower :
      1 ≤ Real.rpow delta (-2 * eta) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdelta hdeltaOne (by linarith)
  nlinarith

/-- The transported concrete constant is at least one. -/
lemma wz1Lemma8_13_fineConstant_ge_one
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (heta : 0 < eta) :
    1 ≤ wz1Lemma8_13FaithfulFineConstant input := by
  have haspect :
      1 ≤ wz1Lemma8_13FaithfulAspect input :=
    le_max_left _ _
  have hsource :=
    wz1Lemma8_13_sourceFConstant_ge_one
      hdelta hdeltaOne heta
  dsimp only [wz1Lemma8_13FaithfulFineConstant]
  nlinarith

/-- The faithful half-scaled affine image of the actual active `F` class is
separated at the public fine scale. -/
lemma wz1Lemma8_13_activeF_image_separated
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input)
    {c : ENNReal}
    {G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hUniform :
      WZ1UniformTripleDensity c input.F G₁ G₂ H) :
    let mapped : DiscreteSet 2 :=
      (wz1ActiveTripleProjection H 0).image
        (wz1Lemma8_13FaithfulFMap input hwidth)
    mapped.IsDeltaSeparated
      (wz1Lemma8_13FaithfulFineScale input) := by
  dsimp only
  have hm :
      0 <
        1 / (2 * wz1Lemma8_13FaithfulAspect input) := by
    have haspect :
        0 < wz1Lemma8_13FaithfulAspect input :=
      zero_lt_one.trans_le (le_max_left _ _)
    positivity
  have hmapped :=
    DiscreteSet.isDeltaSeparated_map_expansive
      (wz1Lemma8_13_activeF_separated input hUniform)
      hm
      (wz1Lemma8_13FaithfulFMap_lower_lipschitz
        input hwidth)
  simpa [wz1Lemma8_13FaithfulFineScale,
    div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using hmapped

/-- The faithful half-scaled affine image of the actual active `F` class has
the concrete transported one-dimensional Frostman constant. -/
lemma wz1Lemma8_13_activeF_image_frostman
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (heta : 0 < eta)
    (hwidth : 0 < wz1Lemma8_13FaithfulNormalizationWidth input)
    {G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hUniform :
      WZ1UniformTripleDensity
        (Kakeya.realRpowENN delta eta / 16)
        input.F G₁ G₂ H) :
    let mapped : DiscreteSet 2 :=
      (wz1ActiveTripleProjection H 0).image
        (wz1Lemma8_13FaithfulFMap input hwidth)
    mapped.IsFrostman
      (wz1Lemma8_13FaithfulFineScale input) 1
      (ENNReal.ofReal
        (wz1Lemma8_13FaithfulFineConstant input)) := by
  dsimp only
  let sourceConstant :=
    wz1Lemma8_13FaithfulSourceFConstant delta eta
  have hc :
      Kakeya.realRpowENN delta eta / 16 ≠ 0 := by
    apply ENNReal.div_ne_zero.mpr
    constructor
    · simp [Kakeya.realRpowENN,
        Real.rpow_pos_of_pos hdelta]
    · norm_num
  have hsourceRaw :=
    wz1Lemma8_13_activeF_frostman input hUniform hc
  have hsource :
      (wz1ActiveTripleProjection H 0).IsFrostman delta 1
        (ENNReal.ofReal sourceConstant) := by
    rw [← wz1Lemma8_13_sourceF_constant_eq hdelta]
    exact hsourceRaw
  have hsourceOne :
      (1 : ENNReal) ≤ ENNReal.ofReal sourceConstant := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_mono
      (wz1Lemma8_13_sourceFConstant_ge_one
        hdelta hdeltaOne heta)
  let m :=
    1 / (2 * wz1Lemma8_13FaithfulAspect input)
  have hm : 0 < m := by
    dsimp only [m]
    have haspect :
        0 < wz1Lemma8_13FaithfulAspect input :=
      zero_lt_one.trans_le (le_max_left _ _)
    positivity
  have htransport :=
    DiscreteSet.isFrostman_equiv_contraction_s1
      (f := wz1Lemma8_13FaithfulFMap input hwidth)
      hsource hsourceOne hm
      (wz1Lemma8_13FaithfulFMap_lower_lipschitz
        input hwidth)
  have hscale :
      m * delta =
        wz1Lemma8_13FaithfulFineScale input := by
    dsimp only [m, wz1Lemma8_13FaithfulFineScale]
    ring
  have hconstant :
      ENNReal.ofReal sourceConstant / ENNReal.ofReal m =
        ENNReal.ofReal
          (wz1Lemma8_13FaithfulFineConstant input) := by
    rw [← ENNReal.ofReal_div_of_pos hm]
    congr 1
    dsimp only [sourceConstant,
      wz1Lemma8_13FaithfulFineConstant, m]
    field_simp
  rw [hscale, hconstant] at htransport
  exact htransport

/-- The transported constant fits the frozen first-stage power budget. -/
lemma wz1Lemma8_13_fineConstant_bound
    {delta epsilon eta : ℝ}
    (input : WZ1Lemma8_13ResidualInput delta epsilon eta)
    (hdelta : 0 < delta)
    (haspect :
      wz1Lemma8_13FaithfulAspect input ≤
        3 * Real.rpow delta
          (-wz1Lemma8_13FaithfulEpsilonOne epsilon)) :
    wz1Lemma8_13FaithfulFineConstant input ≤
      96 * Real.rpow delta
        (-(2 * eta +
          wz1Lemma8_13FaithfulEpsilonOne epsilon)) := by
  have hpowerNonnegative :
      0 ≤ Real.rpow delta (-2 * eta) :=
    Real.rpow_nonneg hdelta.le _
  have hproduct :
      Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
          Real.rpow delta (-2 * eta) =
        Real.rpow delta
          (-(2 * eta +
            wz1Lemma8_13FaithfulEpsilonOne epsilon)) := by
    calc
      Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
          Real.rpow delta (-2 * eta) =
        Real.rpow delta
          (-wz1Lemma8_13FaithfulEpsilonOne epsilon +
            (-2 * eta)) :=
          (Real.rpow_add hdelta _ _).symm
      _ =
        Real.rpow delta
          (-(2 * eta +
            wz1Lemma8_13FaithfulEpsilonOne epsilon)) := by
          congr 1
          ring
  dsimp only [wz1Lemma8_13FaithfulFineConstant,
    wz1Lemma8_13FaithfulSourceFConstant]
  calc
    2 * wz1Lemma8_13FaithfulAspect input *
          (16 * Real.rpow delta (-2 * eta))
        ≤
      2 *
          (3 * Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon)) *
          (16 * Real.rpow delta (-2 * eta)) := by
            gcongr
    _ =
      96 *
        (Real.rpow delta
            (-wz1Lemma8_13FaithfulEpsilonOne epsilon) *
          Real.rpow delta (-2 * eta)) := by ring
    _ =
      96 * Real.rpow delta
        (-(2 * eta +
          wz1Lemma8_13FaithfulEpsilonOne epsilon)) := by
            rw [hproduct]

end

end Kakeya.Assouad
