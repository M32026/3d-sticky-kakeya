import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62SaturatedScaleRestriction

/-!
# Proposition 6.2 metric fibers: old descendant-scale witnesses

The auxiliary metric-parent level is inserted between two adjacent old
levels.  Every old node below the inserted level refines the auxiliary label,
so one metric fiber is saturated for each such old strict parent map.  The
exact-scale witness therefore restricts with no CWA loss.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem PureWZ2Prop62AuxiliaryLevel.auxiliaryFiber_saturated_for_finer_coordinate
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule fine ambientConstant scaleWindow}
    {Aux : Type}
    [Fintype Aux] [DecidableEq Aux]
    (auxiliary : PureWZ2Prop62AuxiliaryLevel schedule Aux)
    (coordinate : Fin schedule.levelCount)
    (finerThanInsertion :
      auxiliary.insertionLevel < coordinate.1)
    (label : Aux) :
    ∀ first second,
      (schedule.scaleData coordinate).cover.parent first =
          (schedule.scaleData coordinate).cover.parent second →
        (first ∈ auxiliary.auxiliaryFiber label ↔
          second ∈ auxiliary.auxiliaryFiber label) := by
  intro first second parentEq
  have nodeEq :
      schedule.nodeAt (coordinate.1 + 1) first =
        schedule.nodeAt (coordinate.1 + 1) second := by
    rw [schedule.nodeAt_succ coordinate.2,
      schedule.nodeAt_succ coordinate.2]
    ext source
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [parentEq]
  have labelEq :
      auxiliary.label first = auxiliary.label second :=
    auxiliary.next_refines_label first second <| by
      have levelEq :
          auxiliary.insertionLevel + 1 ≤ coordinate.1 + 1 := by
        omega
      have oldNodeEq :
          schedule.nodeAt (auxiliary.insertionLevel + 1) first =
            schedule.nodeAt (auxiliary.insertionLevel + 1) second :=
        schedule.tree.node_eq_of_le levelEq
          (by omega) nodeEq
      exact oldNodeEq
  simp only [PureWZ2Prop62AuxiliaryLevel.auxiliaryFiber,
    Finset.mem_filter, Finset.mem_univ, true_and]
  rw [labelEq]

noncomputable def
    PureWZ2Prop62AuxiliaryLevel.restrictFinerScaleToAuxiliaryFiber
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62PureSchedule fine ambientConstant scaleWindow}
    {Aux : Type}
    [Fintype Aux] [DecidableEq Aux]
    (auxiliary : PureWZ2Prop62AuxiliaryLevel schedule Aux)
    (coordinate : Fin schedule.levelCount)
    (finerThanInsertion :
      auxiliary.insertionLevel < coordinate.1)
    (label : Aux)
    (fiberNonempty : (auxiliary.auxiliaryFiber label).Nonempty) :
    WZ2PaperPureScaleCoverData
      (WZ2PaperPureTubeSubfamily.fromFinset fine
        (auxiliary.auxiliaryFiber label)).family
      (schedule.actualScale coordinate)
      ambientConstant :=
  pureWZ2_prop62_restrictScaleToSaturated
    (schedule.scaleData coordinate)
    (auxiliary.auxiliaryFiber label)
    fiberNonempty
    (auxiliary.auxiliaryFiber_saturated_for_finer_coordinate
      coordinate finerThanInsertion label)

end Kakeya.Assouad

end
