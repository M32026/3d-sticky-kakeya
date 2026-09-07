import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperSchedule

/-!
# Proposition 6.2 quotient upper-geometry bridge

This module isolates exactly the raw geometric input still required by the
concrete upper-schedule constructor.  It does not assume a completed upper
scale witness or nearby-scale CWA conclusion.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62ProxyQuotientUpperGeometryData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow sourceConstant : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    {SourceColor : Type*}
    [Fintype SourceColor] [DecidableEq SourceColor]
    [Nonempty SourceColor]
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {sourceColor : Fin fine.card → SourceColor}
    (adapter :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metricCore.metric coloring SourceColor sourceColor)
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho) where
  containedLeafSet :
    schedule.ProxyUpperCoordinate rho packetCoordinate →
      Fin fine.card → Set Point3 → Finset (Fin fine.card)
  contained_packet :
    ∀ coordinate :
        schedule.ProxyUpperCoordinate rho packetCoordinate,
      ∀ parent : Fin
          (metricCore.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.family.card,
        ∀ anchor ∈ metricCore.cleanup.core.core,
          ∀ convexSet,
            ∀ child ∈
                pureWZ2Prop62UpperCoverContainedAmbientFiber
                  metricCore.finalMetricParentsSubfamily
                  (metricCore.finalUpperCover
                    (adapter := adapter)
                    (preliminary_eq := preliminary_eq)
                    fineLine fineBase rhoPos coordinate).selectedParents.family
                  parent
                  (metricCore.finalUpperNormalization
                    (adapter := adapter)
                    (preliminary_eq := preliminary_eq)
                    fineLine fineBase rhoPos coordinate parent)
                  convexSet,
              ((adapter.preCore.wholeLeaves ∩
                quotient.centerPacketIndices coordinate.1
                  (quotient.leafCenter coordinate.1 anchor)).filter
                fun leaf =>
                  metricCore.metric.ambientMetricParentOf leaf = child) ⊆
                    containedLeafSet coordinate anchor convexSet
  ambient_cwa :
    ∀ coordinate :
        schedule.ProxyUpperCoordinate rho packetCoordinate,
      ∀ parent : Fin
          (metricCore.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.family.card,
        ∀ anchor ∈ metricCore.cleanup.core.core,
          ∀ convexSet, Convex ℝ convexSet →
            ((containedLeafSet
              coordinate anchor convexSet).card : ENNReal) ≤
              sourceConstant *
                (pureWZ2Prop62UpperEnvelopeGeometricLoss *
                  volume convexSet) *
                ((metricCore.cleanup.auxiliary.prefixNodeAt
                  (coordinate.1.1 + 1) anchor).card : ENNReal)

namespace PureWZ2Prop62ProxyQuotientMetricCoreOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (output :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    {SourceColor : Type*}
    [Fintype SourceColor] [DecidableEq SourceColor]
    [Nonempty SourceColor]
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {sourceColor : Fin fine.card → SourceColor}
    (adapter :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight output.metric coloring SourceColor sourceColor)

theorem finalMetricParents_publicPureCWA_of_upperGeometry
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (rhoLeOne : rho ≤ 1)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (strongSeparation :
      360 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width)
    (Bcopy Cold Λ sourceConstant : ENNReal)
    (centerCopyBound :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ center,
          ((quotient.centerActualParents
            coordinate.1 center).card : ENNReal) ≤ Bcopy)
    (ambientUniform :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        WZ2PaperPureFullFibersAreCUniform
          fine (schedule.scaleData coordinate.1).coarse Cold)
    (densityLoss_le : output.quotientDensityLoss ≤ Λ)
    (outputFinite :
      WZ2PaperFiniteErrorConstant
        (finalUpperScaleConstant Bcopy Cold Λ sourceConstant))
    (envelope_absorption :
      (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) * scaleWindow ≤
        finalUpperScaleConstant Bcopy Cold Λ sourceConstant)
    (geometry :
      PureWZ2Prop62ProxyQuotientUpperGeometryData
        (sourceConstant := sourceConstant)
        output adapter preliminary_eq fineLine fineBase rhoPos) :
    WZ2PaperPureCWAAtNearbyScales
      output.restriction.coarseSelected.family
      (finalUpperScaleConstant Bcopy Cold Λ sourceConstant) :=
  output.finalMetricParents_publicPureCWA
    adapter preliminary_eq fineLine fineBase rhoPos widthPos
    packetScaleLtRho rhoLeOne sixWidthLe strongSeparation
    Bcopy Cold Λ sourceConstant centerCopyBound ambientUniform
    densityLoss_le outputFinite envelope_absorption
    geometry.containedLeafSet geometry.contained_packet
    geometry.ambient_cwa

theorem finalMetricParents_publicPureCWA_of_upperGeometryComponents
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (rhoLeOne : rho ≤ 1)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (strongSeparation :
      360 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width)
    (Bcopy Cold Λ sourceConstant outputConstant : ENNReal)
    (centerCopyBound :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ center,
          ((quotient.centerActualParents
            coordinate.1 center).card : ENNReal) ≤ Bcopy)
    (ambientUniform :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        WZ2PaperPureFullFibersAreCUniform
          fine (schedule.scaleData coordinate.1).coarse Cold)
    (densityLoss_le : output.quotientDensityLoss ≤ Λ)
    (outputFinite :
      WZ2PaperFiniteErrorConstant outputConstant)
    (cover_absorption :
      2 * Bcopy * Cold * Λ ≤ outputConstant)
    (body_absorption :
      finalUpperBodyConstant Λ sourceConstant ≤ outputConstant)
    (rounding_absorption :
      (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) * scaleWindow ≤
        outputConstant)
    (geometry :
      PureWZ2Prop62ProxyQuotientUpperGeometryData
        (sourceConstant := sourceConstant)
        output adapter preliminary_eq fineLine fineBase rhoPos) :
    WZ2PaperPureCWAAtNearbyScales
      output.restriction.coarseSelected.family outputConstant := by
  have packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho :=
    packetScaleLtRho.le
  exact
    output.finalMetricParents_publicPureCWA_ofComponents
      (adapter := adapter)
      (preliminary_eq := preliminary_eq)
      (fineLine := fineLine)
      (fineBase := fineBase)
      (rhoPos := rhoPos)
      (outputConstant := outputConstant)
      (outputFinite := outputFinite)
      (parentDistinct :=
        output.finalMetricParents_ordinary_distinct
          fineLine widthPos strongSeparation)
      (upperNonempty :=
        schedule.proxyUpperCoordinate_nonempty
          packetCoordinate packetScaleLtRho rhoLeOne)
      (coverConstant := fun _ => 2 * Bcopy * Cold * Λ)
      (bodyConstant := fun _ =>
        finalUpperBodyConstant Λ sourceConstant)
      (fullFiberUniform := fun coordinate =>
        output.finalUpperCover_fullFibers_uniform
          (adapter := adapter)
          (preliminary_eq := preliminary_eq)
          fineLine fineBase rhoPos widthPos packetScaleLeRho sixWidthLe
          Bcopy Cold Λ centerCopyBound ambientUniform densityLoss_le
          coordinate)
      (normalization := fun coordinate parent =>
        output.finalUpperNormalization
          (adapter := adapter)
          (preliminary_eq := preliminary_eq)
          fineLine fineBase rhoPos coordinate parent)
      (fiberCWA := fun coordinate parent =>
        output.finalUpperFiber_bodyCWA
          (adapter := adapter)
          (preliminary_eq := preliminary_eq)
          fineLine fineBase rhoPos widthPos packetScaleLeRho sixWidthLe
          Λ sourceConstant densityLoss_le coordinate parent
          (geometry.containedLeafSet coordinate)
          (geometry.contained_packet coordinate parent)
          (geometry.ambient_cwa coordinate parent))
      (constant_le := fun _ =>
        max_le cover_absorption body_absorption)
      (rounding :=
        schedule.proxyUpperEnvelope_rounding
          packetCoordinate packetScaleLtRho
          outputConstant rounding_absorption)

end PureWZ2Prop62ProxyQuotientMetricCoreOutput

end Kakeya.Assouad

end
