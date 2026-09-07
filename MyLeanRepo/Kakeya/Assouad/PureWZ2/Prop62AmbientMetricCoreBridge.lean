import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PacketHullCorePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62AuxiliaryPureSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricCoreRestriction

/-!
# Proposition 6.2: bridge the ambient tree core to the metric packet hull

The one tree cleanup is performed on the ambient fine family.  Metric parents
and their genuine fibers are constructed on the complete `s`-packet hull.
This package records both exact views of the same final core:

* the ambient core used by the old-tree density estimates;
* its canonical pullback to the complete packet hull;
* the final Section 6 metric restriction on that pulled-back core.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62AmbientMetricCoreBridgeData
    {delta scale rho : ℝ}
    {ambientFine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData ambientFine scale C}
    {width M : ℝ}
    (metric :
      PureWZ2Prop62MetricPacketOutput
        (rho := rho) oldData width M)
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        ambientFine ambientConstant scaleWindow)
    {Aux : Type}
    [Fintype Aux] [DecidableEq Aux]
    (auxiliary : PureWZ2Prop62AuxiliaryLevel schedule Aux)
    (preliminary : Finset (Fin ambientFine.card)) where
  preliminary_nonempty : preliminary.Nonempty
  preliminary_subset_hull :
    preliminary ⊆ metric.mesh.complete.selectedFineIndices
  ambientCore : Finset (Fin ambientFine.card)
  ambientCore_eq :
    ambientCore = auxiliary.coreIndices preliminary
  ambientCore_nonempty : ambientCore.Nonempty
  ambientCore_subset_preliminary : ambientCore ⊆ preliminary
  pullback :
    PureWZ2Prop62PacketHullCorePullbackData metric ambientCore
  metricRestriction :
    PureWZ2Prop62MetricCoreRestrictionData
      metric.section6Cover pullback.pulledBack

theorem pureWZ2_prop62_ambient_metric_core_bridge
    {delta scale rho : ℝ}
    {ambientFine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData ambientFine scale C}
    {width M : ℝ}
    (metric :
      PureWZ2Prop62MetricPacketOutput
        (rho := rho) oldData width M)
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62PureSchedule
        ambientFine ambientConstant scaleWindow)
    {Aux : Type}
    [Fintype Aux] [DecidableEq Aux]
    (auxiliary : PureWZ2Prop62AuxiliaryLevel schedule Aux)
    (preliminary : Finset (Fin ambientFine.card))
    (preliminaryNonempty : preliminary.Nonempty)
    (preliminarySubsetHull :
      preliminary ⊆ metric.mesh.complete.selectedFineIndices) :
    Nonempty
      (PureWZ2Prop62AmbientMetricCoreBridgeData
        metric schedule auxiliary preliminary) := by
  let ambientCore := auxiliary.coreIndices preliminary
  have ambientCoreNonempty : ambientCore.Nonempty :=
    auxiliary.core_nonempty preliminaryNonempty
  have ambientCoreSubset :
      ambientCore ⊆ preliminary :=
    (auxiliary.coreOutput preliminary).core_subset
  have ambientCoreSubsetHull :
      ambientCore ⊆ metric.mesh.complete.selectedFineIndices :=
    ambientCoreSubset.trans preliminarySubsetHull
  let pullback :=
    pureWZ2_prop62_packetHull_core_pullback
      metric ambientCore ambientCoreSubsetHull
  have pulledBackNonempty :
      pullback.pulledBack.Nonempty :=
    pullback.pulledBack_nonempty ambientCoreNonempty
  rcases
      pureWZ2_prop62_metric_core_restriction
        metric.section6Cover pullback.pulledBack pulledBackNonempty
    with
    ⟨metricRestriction⟩
  exact
    ⟨{
      preliminary_nonempty := preliminaryNonempty
      preliminary_subset_hull := preliminarySubsetHull
      ambientCore := ambientCore
      ambientCore_eq := rfl
      ambientCore_nonempty := ambientCoreNonempty
      ambientCore_subset_preliminary := ambientCoreSubset
      pullback := pullback
      metricRestriction := metricRestriction
    }⟩

end Kakeya.Assouad

end
