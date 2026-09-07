import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsOutput
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentTreeSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryRequestedFiberRoute
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AncestryFinalMetricCardinalityBin

/-!
# Proposition 6.2: ancestry metric-parent output

This module assembles the paper-facing metric-parent output from the one
complete-ancestry core.  The parent family, every genuine metric fiber, and
all nearby-scale CWA certificates are the final families produced by that
core.  No tube-family selection is performed here.

The first constructor keeps the remaining global mass inequality explicit.
Its discharge is a separate finite-loss accounting step.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62AncestryMetricPreliminaryOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        fine ambientConstant scaleWindow}
    {scheduled :
      PureWZ2Prop62ScheduledParentColoringData schedule}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {coordinateCount : ℕ}
    {Color : Fin coordinateCount → Type*}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {color : ∀ coordinate, Fin fine.card → Color coordinate}
    {weight : Fin fine.card → ENNReal}
    {preliminary :
      PureWZ2Prop62AncestryPreliminarySelectionData
        schedule scheduled rho width packetCoordinate
        Color color weight}
    {M : ℝ}
    (output :
      PureWZ2Prop62AncestryMetricPreliminaryOutput
        schedule scheduled width packetCoordinate
        Color color weight preliminary M)

/--
The pre-core factor-two `D_-` band and the one-pass core density imply final
metric-fiber uniformity with constant `2 * ancestryDensityLoss`.
-/
theorem finalMetricFiber_uniform_from_cardinalityBin
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate)) :
    ∀ first second,
      ((wz2PaperFullFiberIndices
        output.finalMetricRestriction.fineSelected.family
        output.finalMetricRestriction.coarseSelected.family first).card :
          ENNReal) ≤
        ((2 : ENNReal) * output.ancestryDensityLoss) *
          ((wz2PaperFullFiberIndices
            output.finalMetricRestriction.fineSelected.family
            output.finalMetricRestriction.coarseSelected.family second).card :
              ENNReal) := by
  intro first second
  have firstUpperNat :=
    output.finalMetricFiber_card_lt_two_fiberFloor first
  have firstUpper :
      ((wz2PaperFullFiberIndices
        output.finalMetricRestriction.fineSelected.family
        output.finalMetricRestriction.coarseSelected.family first).card :
          ENNReal) ≤
        (2 : ENNReal) *
          (output.metricFiberCardinalityBin.fiberFloor : ENNReal) := by
    exact_mod_cast Nat.le_of_lt firstUpperNat
  have secondLower :=
    output.fiberFloor_le_ancestryDensityLoss_finalMetricFiber
      rhoPos widthPos packetScaleLeRho sixWidthLe
      schedule.parent_covers allAncestryCoordinatesUpper second
  calc
    ((wz2PaperFullFiberIndices
      output.finalMetricRestriction.fineSelected.family
      output.finalMetricRestriction.coarseSelected.family first).card :
        ENNReal) ≤
        (2 : ENNReal) *
          (output.metricFiberCardinalityBin.fiberFloor : ENNReal) :=
      firstUpper
    _ ≤
        (2 : ENNReal) *
          (output.ancestryDensityLoss *
            ((wz2PaperFullFiberIndices
              output.finalMetricRestriction.fineSelected.family
              output.finalMetricRestriction.coarseSelected.family second).card :
                ENNReal)) := by
      gcongr
    _ =
        ((2 : ENNReal) * output.ancestryDensityLoss) *
          ((wz2PaperFullFiberIndices
            output.finalMetricRestriction.fineSelected.family
            output.finalMetricRestriction.coarseSelected.family second).card :
              ENNReal) := by
      ring

/--
Assemble the genuine ancestry metric-parent output once the exact global
mass-retention inequality has been supplied.  Every structural field is
canonical and refers to the same final core.
-/
theorem metricParentsOutput_of_massRetention
    (coordinates :
      PureWZ2Prop62ScheduledParentCoordinateData
        schedule scheduled (Function.Embedding.refl _)
        coordinateCount Color color)
    (conflict :
      PureWZ2Prop62SourceConflictCoordinateData Color color)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (actualScaleLeOne :
      ∀ coordinate, schedule.actualScale coordinate ≤ 1)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (allAncestryCoordinatesUpper :
      ∀ coordinate : schedule.AncestryCoordinate packetCoordinate,
        rho ≤
          schedule.actualScale
            (schedule.ancestryAmbientCoordinate
              packetCoordinate coordinate))
    (scaleSeparation : 100 * delta ≤ rho)
    (fineAxisBox :
      ∀ source,
        (output.finalMetricRestriction.fineSelected.family.tube
          source).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2)
    (fineBoundedBase : HasBoundedBase fine 4)
    (logExponent : ℕ)
    (massRetention :
      wz2PaperPureRefinementFraction delta logExponent *
          (∑ source : Fin fine.card, weight source) ≤
        ∑ source :
            Fin output.finalMetricRestriction.fineSelected.family.card,
          weight
            (output.metric.mesh.complete.selectedFine.embedding
              (output.finalMetricRestriction.fineSelected.embedding source))) :
    Nonempty
      (PureWZ2Prop62MetricParentsOutput
        (rho := rho) (schedule.scaleData packetCoordinate)
        weight logExponent) := by
  have scaleGap : 4 * delta ≤ rho := by
    have deltaPos :=
      (schedule.scaleData packetCoordinate).delta_pos
    nlinarith
  let fiberRescaling :
      ∀ parent :
          Fin output.finalMetricRestriction.coarseSelected.family.card,
        PureWZ2Prop62MetricFiberRescalingInput
          output.finalMetricRestriction.section6Cover parent
          output.finalMetricFiberRouteConstant :=
    fun parent =>
      output.finalMetricFiberRescalingInput
        coordinates conflict rhoLeOne scaleSeparation
        widthPos packetScaleLtRho.le sixWidthLe
        allAncestryCoordinatesUpper fineBoundedBase parent
  exact
    ⟨{
      width := width
      M := M
      metric := output.metric
      coreIndices := output.ancestryAuxiliaryCore.pullback.pulledBack
      core_nonempty :=
        output.ancestryAuxiliaryCore.pullback.pulledBack_nonempty
          output.ancestryAuxiliaryCore.ambientCore_nonempty
      restriction := output.finalMetricRestriction
      metric_fiber_image_eq :=
        output.finalMetricRestriction.fiber_image_eq
      parentConstant := output.finalUpperScheduleConstant
      sourceFiberConstant := output.finalMetricFiberRouteConstant
      fiberConstant :=
        (81000000 : ENNReal) * output.finalMetricFiberRouteConstant
      fiberConstant_eq := rfl
      parent_cwa :=
        output.finalMetricParents_publicPureCWA
          coordinates rhoPos rhoLeOne actualScaleLeOne
          widthPos packetScaleLtRho
          sixWidthLe allAncestryCoordinatesUpper scaleGap fineAxisBox
      parent_schedule :=
        output.finalMetricParentSchedule
          coordinates rhoPos rhoLeOne widthPos packetScaleLtRho
          sixWidthLe allAncestryCoordinatesUpper scaleGap fineAxisBox
      fiber_rescaling := fiberRescaling
      fiber_public_cwa := fun parent =>
        output.finalMetricFiberPublicPureCWA
          coordinates conflict rhoLeOne scaleSeparation
          widthPos packetScaleLtRho.le sixWidthLe
          allAncestryCoordinatesUpper fineBoundedBase parent
      fiberUniformConstant :=
        (2 : ENNReal) * output.ancestryDensityLoss
      full_fiber_uniform :=
        output.finalMetricFiber_uniform_from_cardinalityBin
          rhoPos widthPos packetScaleLtRho.le sixWidthLe
          allAncestryCoordinatesUpper
      sourceWeightLevel := preliminary.preliminary.weightLevel
      sourceWeightLevel_pos :=
        preliminary.preliminary.weightLevel_pos
      core_weight_retention := massRetention
    }⟩

end PureWZ2Prop62AncestryMetricPreliminaryOutput

end Kakeya.Assouad

end
