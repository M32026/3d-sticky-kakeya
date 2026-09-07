import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropStickyReentry

/-!
# Scheduled first coarse re-entry inside Node 3

This is a Node-3-only closure theorem.  It selects a reusable kernel schedule,
runs the synchronized root invocation below the square of that schedule's
threshold, and retargets the exact first coarse certificate to the selected
losses.

It does not claim that this coarse family is the family used by Node 4 after
fiber selection, unit rescaling, or grain refinement.
-/

noncomputable section

namespace Kakeya.Assouad

/-- One exact first coarse certificate synchronized with a reusable schedule. -/
structure PureWZ2ScheduledCoarseReentryData
    (capability : PureWZ2PropStickyCapability)
    (sigma nextOutputLoss : ℝ) where
  schedule :
    PureWZ2PropStickyTwoCallLossSchedule
      (sigma := sigma) (secondOutputLoss := nextOutputLoss)
      capability.normalizationExponent capability.logExponent
  rootDelta : ℝ
  rootFamily : Kakeya.Streamlined.TubeFamily rootDelta
  rootShading : WZ1PaperTubeShading rootFamily
  firstRho : WZ2PaperRequestedScale rootDelta
  first :
    PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      rootShading firstRho
      capability.normalizationExponent capability.logExponent
  firstScale_le_kernel :
    firstRho.1 ≤ schedule.kernel.delta₀

namespace PureWZ2ScheduledCoarseReentryData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma nextOutputLoss : ℝ}
    (data :
      PureWZ2ScheduledCoarseReentryData
        capability sigma nextOutputLoss)

abbrev scale : ℝ :=
  data.firstRho.1

abbrev family : Kakeya.Streamlined.TubeFamily data.scale :=
  data.first.data.coarse

abbrev shading : WZ1PaperTubeShading data.family :=
  data.first.data.croppedCoarseShading

/-- Retarget the exact coarse pair to the selected reusable-kernel losses. -/
noncomputable def reentry :
    PureWZ2PropStickyReentryData
      (sigma := sigma)
      data.shading capability.normalizationExponent
      data.schedule.kernel.sourceLoss
      data.schedule.kernel.normalizationLoss :=
  data.first.reentryForNext data.schedule

end PureWZ2ScheduledCoarseReentryData

namespace PureWZ2PropStickyCapability

/-- Construct the scheduled exact coarse certificate entirely inside Node 3. -/
theorem scheduledCoarseReentry
    (capability : PureWZ2PropStickyCapability)
    {sigma nextOutputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (nextOutputLoss_pos : 0 < nextOutputLoss)
    (nextOutputLoss_le_one : nextOutputLoss ≤ 1) :
    Nonempty
      (PureWZ2ScheduledCoarseReentryData
        capability sigma nextOutputLoss) := by
  rcases
      capability.kernel sigma critical nextOutputLoss
        nextOutputLoss_pos nextOutputLoss_le_one
    with
    ⟨kernelSchedule⟩
  let schedule := kernelSchedule.toTwoCallLossSchedule
  rcases
      capability.rootReentrant sigma critical
        schedule.firstOutputLoss schedule.rootScaleCeiling
        schedule.firstOutputLoss_pos schedule.rootScaleCeiling_pos
    with
    ⟨root⟩
  rcases root.realizedReentrantOutput with ⟨first⟩
  refine
    ⟨{
      schedule := schedule
      rootDelta := root.realization.delta
      rootFamily := root.realization.normalized.croppedFamily
      rootShading := root.realization.normalized.croppedRefined
      firstRho := root.realization.realizedRho
      first := first
      firstScale_le_kernel := ?_
    }⟩
  rw [root.realization.realizedRho_eq_sqrt]
  have delta_le_square :
      root.realization.delta ≤ schedule.kernel.delta₀ ^ 2 := by
    calc
      root.realization.delta ≤ schedule.rootScaleCeiling :=
        root.realization.delta_le_ceiling
      _ = schedule.kernel.delta₀ ^ 2 :=
        schedule.rootScaleCeiling_eq
  calc
    Real.sqrt root.realization.delta ≤
        Real.sqrt (schedule.kernel.delta₀ ^ 2) :=
      Real.sqrt_le_sqrt delta_le_square
    _ = |schedule.kernel.delta₀| :=
      Real.sqrt_sq_eq_abs schedule.kernel.delta₀
    _ = schedule.kernel.delta₀ :=
      abs_of_pos schedule.kernel.delta₀_pos

end PureWZ2PropStickyCapability

/-- The serial Node 3 hypothesis constructively supplies the scheduled pair. -/
theorem pureWZ2_node3_scheduled_coarse_reentry
    (hSubunit : PureWZ2SubunitPackageStatement)
    (hCriticalExtraction : PureWZ2CriticalExtractionStatement)
    (hSticky : PureWZ2PropStickyStatement)
    {sigma nextOutputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (nextOutputLoss_pos : 0 < nextOutputLoss)
    (nextOutputLoss_le_one : nextOutputLoss ≤ 1) :
    ∃ capability : PureWZ2PropStickyCapability,
      Nonempty
        (PureWZ2ScheduledCoarseReentryData
          capability sigma nextOutputLoss) := by
  rcases hSticky hSubunit hCriticalExtraction with ⟨capability⟩
  exact
    ⟨capability,
      capability.scheduledCoarseReentry critical
        nextOutputLoss_pos nextOutputLoss_le_one⟩

end Kakeya.Assouad

end
