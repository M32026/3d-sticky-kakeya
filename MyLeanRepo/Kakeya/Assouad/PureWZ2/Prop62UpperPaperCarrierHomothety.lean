import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredLineTube
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.DirectionConstraint

/-!
# Proposition 6.2: cropped paper carrier inside a fixed ordinary homothety

The public ordinary tube remembers a unit axis segment, whereas the WZ paper
carrier uses the whole supporting line cropped to the fixed box.  For a
midpoint-centered line-class tube, the finite-capsule theorem places the
cropped carrier inside the factor-`100` homothety of its ordinary carrier.
This is the safe replacement for silently identifying the two carrier models.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

theorem wz1PaperTubeCarrier_subset_centered_homothety_hundred
    {rho : ℝ}
    (rhoPos : 0 < rho)
    (tube : Kakeya.DeltaTube rho)
    (line : WZ1PaperTubeInLineClass tube)
    (centered :
      wz2PaperCenteredLineTube (targetScale := rho) tube = tube) :
    wz1PaperTubeCarrier tube ⊆
      AffineMap.homothety
          (wz2PaperTubeMidpoint tube) (100 : ℝ) ''
        tube.carrier := by
  let midpoint := wz2PaperTubeMidpoint tube
  have zeroEqMidpoint :
      wz1TubeAxisZeroPoint tube = midpoint := by
    have midpointEq :
        wz2PaperTubeMidpoint
            (wz2PaperCenteredLineTube
              (targetScale := rho) tube) =
          wz1TubeAxisZeroPoint tube :=
      wz2PaperCenteredLineTube_midpoint tube
    rw [centered] at midpointEq
    exact midpointEq.symm
  have paperSubset :=
    (wz2_paper_tube_carrier_geometry rhoPos tube line).2
  intro point pointMem
  have thickMem := paperSubset pointMem
  rcases
      exists_dist_le_of_mem_cthickening_closed
        (isCompact_Icc.image (by fun_prop) |>.isClosed)
        (by positivity : 0 ≤ 24 * rho)
        thickMem
    with ⟨axisPoint, axisMem, pointAxisDistance⟩
  rcases axisMem with
    ⟨rawParameter, rawParameterMem, axisPointEq⟩
  let parameter := rawParameter - 2
  have parameterMem : parameter ∈ Set.Icc (-2 : ℝ) 2 := by
    exact
      ⟨by dsimp only [parameter]; linarith [rawParameterMem.1],
        by dsimp only [parameter]; linarith [rawParameterMem.2]⟩
  have axisPointEq' :
      axisPoint =
        wz1TubeAxisZeroPoint tube +
          parameter • wz1PaperDirection tube := by
    exact axisPointEq.symm
  let contractedParameter : ℝ :=
    1 / 2 + parameter / 100
  let contractedAxisPoint : Point3 :=
    tube.base + contractedParameter • tube.direction
  let contractedPoint : Point3 :=
    AffineMap.homothety midpoint (1 / 100 : ℝ) point
  have contractedParameterMem :
      contractedParameter ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [contractedParameter]
    constructor <;> linarith [parameterMem.1, parameterMem.2]
  have contractedAxisMem :
      contractedAxisPoint ∈
        Kakeya.unitSegment tube.base tube.direction :=
    ⟨contractedParameter, contractedParameterMem, rfl⟩
  have tubeDirection :
      tube.direction = wz1PaperDirection tube := by
    have directionEq :
        (wz2PaperCenteredLineTube
          (targetScale := rho) tube).direction =
          wz1PaperDirection tube := rfl
    rwa [centered] at directionEq
  have baseEq :
      tube.base =
        midpoint - (1 / 2 : ℝ) •
          wz1PaperDirection tube := by
    have midpointDefinition :
        midpoint =
          tube.base + (1 / 2 : ℝ) • tube.direction := by
      rfl
    rw [tubeDirection] at midpointDefinition
    rw [midpointDefinition]
    abel
  have contractedAxisEq :
      contractedAxisPoint =
        AffineMap.homothety midpoint (1 / 100 : ℝ)
          axisPoint := by
    rw [axisPointEq', AffineMap.homothety_apply]
    dsimp only [contractedAxisPoint, contractedParameter]
    rw [tubeDirection, baseEq, zeroEqMidpoint]
    ext coordinate
    simp only [
      PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply,
      smul_eq_mul, vsub_eq_sub, vadd_eq_add
    ]
    ring
  have contractedDistance :
      dist contractedPoint contractedAxisPoint ≤ rho := by
    rw [contractedAxisEq]
    have scaled :=
      homothety_dist (m := midpoint)
        (by norm_num : (0 : ℝ) < 1 / 100)
        point axisPoint
    dsimp only [contractedPoint]
    rw [scaled]
    calc
      (1 / 100 : ℝ) * dist point axisPoint ≤
          (1 / 100 : ℝ) * (24 * rho) := by
        gcongr
      _ ≤ rho := by nlinarith
  have contractedMem :
      contractedPoint ∈ tube.carrier :=
    Metric.mem_cthickening_of_dist_le
      contractedPoint contractedAxisPoint rho
      (Kakeya.unitSegment tube.base tube.direction)
      contractedAxisMem contractedDistance
  refine ⟨contractedPoint, contractedMem, ?_⟩
  dsimp only [contractedPoint]
  rw [AffineMap.homothety_apply,
    AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  module

end Kakeya.Assouad

end
