import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricAuxiliaryFiber

/-!
# Proposition 6.2 metric parents: inserted CWA on the final core

The inserted auxiliary nodes are the genuine metric fibers.  Applying the
one-pass augmented-tree density estimate therefore transfers the pre-core
inserted-level CWA to the final core with exactly
`2^(L+1) * #U / #S`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem PureWZ2Prop62MetricPacketOutput.inserted_cwa_after_core
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {width M : ℝ}
    (metric :
      PureWZ2Prop62MetricPacketOutput
        (rho := rho) oldData width M)
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule
        metric.selectedFine ambientConstant scaleWindow}
    (auxiliary :
      PureWZ2Prop62AuxiliaryLevel
        schedule (Fin metric.metricParents.card))
    (label_eq :
      ∀ source,
        auxiliary.label source =
          metric.metricInput.packetParent
            (metric.mesh.restrictedOldData.cover.parent source))
    (selected : Finset (Fin metric.selectedFine.card))
    (parent : Fin metric.metricParents.card)
    (coreFiberNonempty :
      (auxiliary.coreIndices selected ∩
        wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents parent).Nonempty)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    (((auxiliary.coreIndices selected ∩
        wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents parent).filter
        fun source =>
          wz2PaperLiteralUnitRescalingMap
              (metric.metricParents.tube parent)
              metric.metricInput.rho_pos ''
            (metric.selectedFine.tube source).carrier ⊆
              convexSet).card : ENNReal) ≤
      (pureWZ2Prop62InsertedCWALoss rho scale C *
        auxiliary.densityLoss selected) *
        volume convexSet *
        (((auxiliary.coreIndices selected ∩
          wz2PaperFullFiberIndices
            metric.selectedFine metric.metricParents parent).card :
          ENNReal)) := by
  let predicate : Fin metric.selectedFine.card → Prop :=
    fun source =>
      wz2PaperLiteralUnitRescalingMap
          (metric.metricParents.tube parent)
          metric.metricInput.rho_pos ''
        (metric.selectedFine.tube source).carrier ⊆ convexSet
  have auxiliaryFiberEq :
      auxiliary.auxiliaryFiber parent =
        wz2PaperFullFiberIndices
          metric.selectedFine metric.metricParents parent :=
    auxiliary.auxiliaryFiber_eq_metricFiber metric label_eq parent
  have ambientCWA :
      ((((auxiliary.auxiliaryFiber parent).filter predicate).card :
        ENNReal)) ≤
        pureWZ2Prop62InsertedCWALoss rho scale C *
          volume convexSet *
          ((auxiliary.auxiliaryFiber parent).card : ENNReal) := by
    rw [auxiliaryFiberEq]
    exact metric.insertedFiberCWA parent convexSet convex
  have transferred :=
    pureWZ2_prop62_inserted_cwa_after_core
      auxiliary.label selected (auxiliary.coreIndices selected)
      (auxiliary.coreOutput selected).core_subset
      (schedule.levelCount + 1)
      auxiliary.auxiliaryFiber
      (fun label => rfl)
      (fun label nonempty => by
        simpa only [
          PureWZ2Prop62AuxiliaryLevel.coreIndices,
          Fintype.card_fin
        ] using
          (auxiliary.coreOutput selected).auxiliary_density
            label nonempty)
      parent
      (by simpa only [auxiliaryFiberEq] using coreFiberNonempty)
      (pureWZ2Prop62InsertedCWALoss rho scale C)
      (volume convexSet) predicate ambientCWA
  rw [auxiliaryFiberEq] at transferred
  simpa only [
    predicate,
    PureWZ2Prop62AuxiliaryLevel.densityLoss,
    Kakeya.Streamlined.TubeFamily.enncard,
    Fintype.card_fin,
    mul_assoc
  ] using transferred

end Kakeya.Assouad

end
