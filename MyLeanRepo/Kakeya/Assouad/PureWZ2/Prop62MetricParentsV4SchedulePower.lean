import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricParentsV4SchedulePowerCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperAudit.StatementsV4

/-!
# Frozen V4 wrapper for the power-controlled parent schedule

The schedule arithmetic and its threshold certificate live in
`Prop62MetricParentsV4SchedulePowerCore`, which has no dependency on the
frozen V4 statements.  This module only connects that closed package to
`MetricParentsAtPrescribedScaleData`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace Prop62PaperAudit.V4

open Kakeya.Assouad

/--
The complete parent-schedule package consumed by the four-degree assembly.
Its family is definitionally the frozen metric-parent family.
-/
structure PureWZ2Prop62MetricParentsV4SchedulePowerData
    {D B : ℕ} {eta delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant)
    (power :
      PureWZ2Prop62MetricParentsV4SchedulePowerCertificate
        D B eta) where
  ambient_cwa :
    WZ2PaperPureCWAAtNearbyScales
      metric.scaleData.coarse
      (pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
        B eta delta)
  requested :
    PureWZ2Prop62RequestedScaleSchedule
      rho.1
      (pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
        B eta delta)
      (ENNReal.ofReal
        (pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta))
  ratio_gt_one :
    1 <
      pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta
  requested_separation :
    4 *
        (pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
          B eta delta).toReal ≤
      pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta
  reaches :
    1 ≤
      rho.1 *
        pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta ^
          pureWZ2Prop62MetricParentsV4FourDegreeReachDepth B eta
  schedule :
    PureWZ2Prop62LaminarPureSchedule
      metric.scaleData.coarse
      (pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
        B eta delta)
      (pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
          B eta delta *
        ENNReal.ofReal
          (pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta))
  schedule_eq :
    schedule = ambient_cwa.toProp62LaminarSchedule requested
  levelCount_le :
    schedule.levelCount ≤
      pureWZ2Prop62MetricParentsV4FourDegreeDepthBound D B eta
  scaleWindow_eq :
    pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
          B eta delta *
        ENNReal.ofReal
          (pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta) =
      4 *
        pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
          B eta delta ^ 2
  scaleWindow_le :
    pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
          B eta delta *
        ENNReal.ofReal
          (pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta) ≤
      Kakeya.realRpowENN delta
        (-((pureWZ2Prop62MetricParentsV4FourDegreeWindowPower
          D B : ℝ) * eta))

/--
Build the four-degree schedule directly from the frozen metric output.
The only runtime quantitative assumption is the statement's parent CWA bound.
-/
noncomputable def
    MetricParentsAtPrescribedScaleData.fourDegreeSchedulePowerData
    {D B : ℕ} {eta delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
          parentConstant fiberConstant)
    (power :
      PureWZ2Prop62MetricParentsV4SchedulePowerCertificate
        D B eta)
    (eta_pos : 0 < eta)
    (delta_pos : 0 < delta)
    (delta_le : delta ≤ power.delta0)
    (parentConstant_le :
      parentConstant ≤
        Kakeya.realRpowENN delta (-((B : ℝ) * eta))) :
    PureWZ2Prop62MetricParentsV4SchedulePowerData metric power := by
  let C1 :=
    pureWZ2Prop62MetricParentsV4FourDegreeAmbientConstant
      B eta delta
  let R :=
    pureWZ2Prop62MetricParentsV4FourDegreeRatio B eta delta
  let ambientCWA :
      WZ2PaperPureCWAAtNearbyScales
        metric.scaleData.coarse C1 :=
    metric.scaleData.coarse_cwa.mono
      (power.parentConstant_le_ambientConstant
        eta_pos delta_pos delta_le parentConstant_le)
      power.ambientConstant_finite
  let requested :=
    power.requestedScaleSchedule
      eta_pos delta_pos delta_le rho
  let schedule :
      PureWZ2Prop62LaminarPureSchedule
        metric.scaleData.coarse C1
          (C1 * ENNReal.ofReal R) :=
    pureWZ2Prop62RatioLaminarSchedule
      ambientCWA
      (pureWZ2Prop62MetricParentsV4FourDegreeReachDepth B eta)
      rho.2.2
      (power.ratio_gt_one eta_pos delta_pos delta_le)
      power.requested_separation
      (power.depth_reaches eta_pos delta_pos delta_le rho)
  refine
    {
      ambient_cwa := ambientCWA
      requested := requested
      ratio_gt_one :=
        power.ratio_gt_one eta_pos delta_pos delta_le
      requested_separation := power.requested_separation
      reaches :=
        power.depth_reaches eta_pos delta_pos delta_le rho
      schedule := schedule
      schedule_eq := ?_
      levelCount_le := ?_
      scaleWindow_eq := power.exact_scaleWindow delta_pos
      scaleWindow_le := ?_
    }
  · rfl
  · exact
      pureWZ2Prop62RatioLaminarSchedule_levelCount_le
        ambientCWA
        (pureWZ2Prop62MetricParentsV4FourDegreeReachDepth B eta)
        rho.2.2
        (power.ratio_gt_one eta_pos delta_pos delta_le)
        power.requested_separation
        (power.depth_reaches eta_pos delta_pos delta_le rho)
  · exact
      (power.exact_scaleWindow delta_pos).trans_le
        (power.scaleWindow_le delta_pos delta_le)

end Prop62PaperAudit.V4

end Kakeya.Assouad

end
