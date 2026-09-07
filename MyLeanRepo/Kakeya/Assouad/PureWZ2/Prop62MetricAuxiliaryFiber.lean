import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricPreliminaryAssembly

/-!
# Proposition 6.2 metric parents: auxiliary nodes are metric fibers

After the structural color class has fixed one ancestry class in every
occupied mesh cell, the inserted auxiliary label is the metric-parent
assignment.  Hence each auxiliary node is literally the complete Section 6
metric fiber, not an assigned surrogate.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem PureWZ2Prop62AuxiliaryLevel.auxiliaryFiber_eq_metricFiber
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
    (parent : Fin metric.metricParents.card) :
    auxiliary.auxiliaryFiber parent =
      wz2PaperFullFiberIndices
        metric.selectedFine metric.metricParents parent := by
  rw [metric.metricFiber_eq_assignedPackets parent]
  ext source
  simp only [
    PureWZ2Prop62AuxiliaryLevel.auxiliaryFiber,
    Finset.mem_filter, Finset.mem_univ, true_and
  ]
  rw [label_eq source]

end Kakeya.Assouad

end
