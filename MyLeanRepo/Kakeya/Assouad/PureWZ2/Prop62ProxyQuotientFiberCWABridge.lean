import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientSourceColor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientFiberRoute

/-!
# Proposition 6.2 quotient metric-fiber CWA bridge

This module combines the source-conflict coloring on the unique pre-core, the
requested-scale route on the same quotient metric core, and the canonical
metric-fiber CWA constructor.  It performs no new selection or cleanup.
-/

noncomputable section

namespace Kakeya.Assouad

noncomputable def pureWZ2_prop62_proxy_quotient_fiber_cwa_bridge_of_adapter
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (upperColoring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate)
    {SourceColor : Type*}
    [Fintype SourceColor] [DecidableEq SourceColor] [Nonempty SourceColor]
    (sourceColor : Fin fine.card → SourceColor)
    (adapter :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metric upperColoring SourceColor sourceColor)
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (metric_eq : metricCore.metric = metric)
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        adapter.preCore.preliminary)
    (sourceConstant : ENNReal)
    (routeInput :
      PureWZ2Prop62ProxyQuotientFiberRouteInput
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metricCore sourceConstant)
    (fineLine : WZ1PaperIsLineClass fine)
    (widthPos : 0 < width)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (insertedConstantLe :
      pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        metricCore.quotientDensityLoss ≤ sourceConstant)
    (sourceStronglySeparated :
      ∀ parent :
          Fin metricCore.restriction.coarseSelected.family.card,
        ∀ first second :
            Fin
              (metricCore.restriction.metricFiberSource parent).family.card,
          first ≠ second →
            wz2PaperLiteralSourceSeparationFactor * delta <
              wz1PaperLineDistance
                ((metricCore.restriction.metricFiberSource parent).family.tube
                  first)
                ((metricCore.restriction.metricFiberSource parent).family.tube
                  second)) :
    PureWZ2Prop62ProxyQuotientFiberCWAData
      metricCore sourceConstant :=
  pureWZ2_prop62_proxy_quotient_fiber_cwa
    schedule fineNonempty quotient width packetCoordinate strideBase weight
    metricCore fineLine routeInput.fine_bounded_base
    metricCore.metric.metricInput.rho_pos widthPos
    routeInput.packet_scale_le_rho sixWidthLe
    routeInput.rho_le_one
    (schedule.scaleData packetCoordinate).delta_pos
    routeInput.scale_separation sourceConstant
    routeInput.source_constant_finite insertedConstantLe
    sourceStronglySeparated
    routeInput.toFiberRouteData

noncomputable def pureWZ2_prop62_proxy_quotient_fiber_cwa_bridge
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (upperColoring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate)
    (sourceColor :
      PureWZ2Prop62ProxyQuotientSourceColorPreCoreData
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metric upperColoring)
    (metricCore :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    (metric_eq : metricCore.metric = metric)
    (preliminary_eq :
      metricCore.cleanup.preliminary =
        sourceColor.adapter.preCore.preliminary)
    (sourceConstant : ENNReal)
    (routeInput :
      PureWZ2Prop62ProxyQuotientFiberRouteInput
        schedule fineNonempty quotient width packetCoordinate
          strideBase weight metricCore sourceConstant)
    (fineLine : WZ1PaperIsLineClass fine)
    (widthPos : 0 < width)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (insertedConstantLe :
      pureWZ2Prop62InsertedCWALoss
          rho (schedule.actualScale packetCoordinate) ambientConstant *
        metricCore.quotientDensityLoss ≤ sourceConstant) :
    PureWZ2Prop62ProxyQuotientFiberCWAData
      metricCore sourceConstant :=
  pureWZ2_prop62_proxy_quotient_fiber_cwa_bridge_of_adapter
    schedule fineNonempty quotient width packetCoordinate strideBase weight
    metric upperColoring sourceColor.sourceConflict.color sourceColor.adapter
    metricCore metric_eq preliminary_eq sourceConstant routeInput fineLine
    widthPos sixWidthLe insertedConstantLe
    (sourceColor.sourceStronglySeparated
      metricCore metric_eq preliminary_eq)

end Kakeya.Assouad

end
