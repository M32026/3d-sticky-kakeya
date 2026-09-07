import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCleanupSourceRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.QuotientScheduleCWAAbstract

/-!
# Requested-scale CWA on the direct half-offset terminal family

The source regularization has already restored nearby CWA on its selected
ambient-source subfamily.  This file performs only the finite-schedule
assembly for the synchronized terminal family.  The missing geometric part is
kept explicit: each target actual-John packet needs its own map-specific CWA
certificate.  In particular, no horizontal-normalized target equality and no
full-fiber equality are asserted here.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry
namespace PureWZ2ExternalWeightRegularizationData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- The cleanup-selected terminal family before the two genuine finite
regularization restrictions. -/
abbrev DirectHalfOffsetTerminalRequestedCWAPreTarget
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (data : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) :=
  (halfOffsetTerminalCleanupTargetSubfamily (commonSource := commonSource)
    data).family

/-- Finite requested-scale assembly data.  `packetCWA` is the sole
map-specific input left open by this layer: it must prove CWA for the actual
terminal target actual-John body packet indexed by one source actual parent. -/
structure DirectHalfOffsetTerminalRequestedCWAData
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount)
    (targetConstant : ENNReal) where
  /-- The second finite schedule is independent of the ambient external-weight
  regularization schedule. -/
  sourceScheduleConstant : ENNReal
  parentLevelCount : ℕ
  sourceSchedule : PureWZ2FiniteNearbyScheduleData
    (family := regularization.selected.family)
    regularization.outputConstant sourceScheduleConstant parentLevelCount
  representativeSchedule : PureWZ2FiniteRepresentativeParentScheduleData
    (sourceFine := regularization.selected.family)
    (DirectHalfOffsetTerminalRequestedCWAPreTarget
      (commonSource := commonSource) regularization)
    (Equiv.refl _) regularization.outputConstant sourceSchedule.scaleCount
  quotientSchedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
    representativeSchedule
  weight : Fin
    (DirectHalfOffsetTerminalRequestedCWAPreTarget
      (commonSource := commonSource) regularization).card → ENNReal
  /-- The joint-selection weight is exactly the cleanup mass transported to
  the source-regularization selected index; it is not an unrelated schedule
  weight. -/
  weight_provenance : ∀ index,
    weight index = cleanup.sourceWeight (regularization.selected.embedding index)
  selection : PureWZ2FiniteStrongParentSelectionData
    weight sourceSchedule.scaleCount quotientSchedule.Parent
    (fun coordinate target =>
      (quotientSchedule.quotient coordinate).assignedParent target)
    quotientSchedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree
  joint : Kakeya.Assouad.PureWZ2FiniteAnisotropicParentQuotientScheduleData.PureWZ2AnisotropicJointRegularizationData
    quotientSchedule weight selection
  targetFinite : WZ2PaperFiniteErrorConstant targetConstant
  requestedCoordinate : WZ2PaperRequestedScale terminal.targetDelta →
    Fin sourceSchedule.scaleCount
  requested_le : ∀ request, request.1 ≤
    quotientSchedule.callerRho (requestedCoordinate request)
  requested_within : ∀ request,
    ENNReal.ofReal (quotientSchedule.callerRho (requestedCoordinate request)) <
      targetConstant * ENNReal.ofReal request.1
  coverConstant : Fin sourceSchedule.scaleCount → ENNReal
  bodyConstant : Fin sourceSchedule.scaleCount → ENNReal
  coverUniform : ∀ coordinate, WZ2PaperPureFullFibersAreCUniform
    (quotientSchedule.jointlyRegularizedFine weight selection joint.selected).family
    (joint.finalCoarse coordinate) (coverConstant coordinate)
  constant_budget : ∀ coordinate,
    max (coverConstant coordinate) (bodyConstant coordinate) ≤ targetConstant
  packetCWA : ∀ coordinate
    (targetParent : Fin (joint.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((joint.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card),
    WZ2PaperBodyConvexWolffBound
      (joint.quotientTargetBodyPacket coordinate targetParent normalization
        sourceParent) (bodyConstant coordinate)

/-- The composed genuine subfamily from the cleanup-selected pre-target to
the final jointly regularized terminal target. -/
noncomputable def DirectHalfOffsetTerminalRequestedCWAData.finalTargetSubfamily
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant) :
    Kakeya.Streamlined.TubeSubfamily
      (DirectHalfOffsetTerminalRequestedCWAPreTarget
        (commonSource := commonSource) regularization) where
  family := (data.quotientSchedule.jointlyRegularizedFine data.weight
    data.selection data.joint.selected).family
  embedding :=
    (data.quotientSchedule.jointlyRegularizedFine data.weight data.selection
      data.joint.selected).embedding.trans
      (data.quotientSchedule.separatedFine data.weight data.selection).embedding
  tube_eq index := by
    rw [(data.quotientSchedule.jointlyRegularizedFine data.weight
      data.selection data.joint.selected).tube_eq]
    exact (data.quotientSchedule.separatedFine data.weight data.selection).tube_eq _

/-- The genuinely selected terminal target family after both finite
regularization passes. -/
abbrev DirectHalfOffsetTerminalRequestedCWAData.finalTarget
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant) :=
  data.finalTargetSubfamily.family

/-- Assemble public nearby-scale CWA on the final genuinely selected terminal
family. -/
theorem DirectHalfOffsetTerminalRequestedCWAData.toNearbyCWA
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight targetConstant : ENNReal}
    {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (data : DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant) :
    WZ2PaperPureCWAAtNearbyScales data.finalTarget targetConstant := by
  refine data.joint.toNearbyCWAOfPacketCWA
    data.sourceSchedule.scaleCount_pos data.targetFinite ?_
    data.requestedCoordinate data.requested_le data.requested_within
    data.coverConstant data.bodyConstant data.coverUniform data.constant_budget data.packetCWA
  exact (halfOffsetTerminalCleanupTargetSubfamily_distinct
      (commonSource := commonSource) regularization).subfamily
        (data.quotientSchedule.separatedFine data.weight data.selection) |>.subfamily
        (data.quotientSchedule.jointlyRegularizedFine data.weight
          data.selection data.joint.selected)

end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
