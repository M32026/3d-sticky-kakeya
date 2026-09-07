import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicQuotientScheduleCWA

/-!
# Map-independent nearby-CWA closure for a quotient schedule

The representative-parent, quotient, and joint-regularization layers are
independent of the affine map used to produce the target tubes.  This module
isolates their final logical assembly.  A geometric caller only has to supply
the actual-John CWA bound for each source-parent packet and the finite scalar
budgets.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2FiniteAnisotropicParentQuotientScheduleData
namespace PureWZ2AnisotropicJointRegularizationData

/-- Package one coordinate of a jointly regularized quotient schedule once
the map-specific actual-John estimates have been proved packetwise. -/
noncomputable def toOneScaleCWAAdapterDataOfPacketCWA
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant targetConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (coverConstant bodyConstant : Fin scaleCount → ENNReal)
    (hcover : ∀ coordinate, WZ2PaperPureFullFibersAreCUniform
      (schedule.jointlyRegularizedFine
        weight selection data.selected).family
      (data.finalCoarse coordinate) (coverConstant coordinate))
    (hpacket : ∀ coordinate
      (targetParent : Fin (data.finalCoarse coordinate).card)
      (normalization : WZ2PaperAssouadUnitRescalingData
        ((data.finalCoarse coordinate).tube targetParent))
      (sourceParent : Fin
        (representativeSchedule.sourceScale coordinate).coarse.card),
      WZ2PaperBodyConvexWolffBound
        (data.quotientTargetBodyPacket coordinate targetParent normalization
          sourceParent) (bodyConstant coordinate))
    (coordinate : Fin scaleCount)
    (hconstantBudget :
      max (coverConstant coordinate) (bodyConstant coordinate) ≤
        targetConstant) :
    PureWZ2AnisotropicQuotientOneScaleCWAAdapterData
      (targetRho := schedule.callerRho coordinate)
      (targetFine := (schedule.jointlyRegularizedFine
        weight selection data.selected).family)
      (targetConstant := targetConstant)
      (coverConstant := coverConstant coordinate)
      (bodyConstant := bodyConstant coordinate)
      (representativeSchedule.sourceScale coordinate) where
  targetCoarse := data.finalCoarse coordinate
  target_delta_pos :=
    (representativeSchedule.parentData coordinate).target_delta_pos
  target_rho_pos := (schedule.quotient coordinate).caller_rho_pos
  targetCover := data.finalCover coordinate
  target_full_fiber_uniform := hcover coordinate
  sourceOf := data.finalSourceIndex
  targetNormalization := fun targetParent =>
    WZ2PaperAssouadUnitRescalingData.ofTube
      ((data.finalCoarse coordinate).tube targetParent)
      (schedule.quotient coordinate).caller_rho_pos
  packetCWA := by
    intro targetParent sourceParent
    exact hpacket coordinate targetParent
      (WZ2PaperAssouadUnitRescalingData.ofTube
        ((data.finalCoarse coordinate).tube targetParent)
        (schedule.quotient coordinate).caller_rho_pos) sourceParent
  source_parent_count_pos := by
    let source : Fin sourceFine.card :=
      ⟨0, (representativeSchedule.parentData coordinate).source_nonempty⟩
    rcases (representativeSchedule.sourceScale coordinate).cover.covers source
      with ⟨sourceParent, _⟩
    exact lt_of_le_of_lt (Nat.zero_le sourceParent.val) sourceParent.isLt
  constant_budget := hconstantBudget

/-- A finite quotient schedule yields public nearby CWA once every requested
scale is assigned to a scheduled coordinate and every packet has the required
actual-John bound. -/
theorem toNearbyCWAOfPacketCWA
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant targetConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
        targetFine sourceEquiv sourceConstant scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (hscaleCount : 0 < scaleCount)
    (htargetFinite : WZ2PaperFiniteErrorConstant targetConstant)
    (htargetDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct
      (schedule.jointlyRegularizedFine
        weight selection data.selected).family)
    (coordinateOf : WZ2PaperRequestedScale targetDelta → Fin scaleCount)
    (hrequested : ∀ request, request.1 ≤
      schedule.callerRho (coordinateOf request))
    (hwithin : ∀ request,
      ENNReal.ofReal (schedule.callerRho (coordinateOf request)) <
        targetConstant * ENNReal.ofReal request.1)
    (coverConstant bodyConstant : Fin scaleCount → ENNReal)
    (hcover : ∀ coordinate, WZ2PaperPureFullFibersAreCUniform
      (schedule.jointlyRegularizedFine
        weight selection data.selected).family
      (data.finalCoarse coordinate) (coverConstant coordinate))
    (hconstantBudget : ∀ coordinate,
      max (coverConstant coordinate) (bodyConstant coordinate) ≤
        targetConstant)
    (hpacket : ∀ coordinate
      (targetParent : Fin (data.finalCoarse coordinate).card)
      (normalization : WZ2PaperAssouadUnitRescalingData
        ((data.finalCoarse coordinate).tube targetParent))
      (sourceParent : Fin
        (representativeSchedule.sourceScale coordinate).coarse.card),
      WZ2PaperBodyConvexWolffBound
        (data.quotientTargetBodyPacket coordinate targetParent normalization
          sourceParent) (bodyConstant coordinate)) :
    WZ2PaperPureCWAAtNearbyScales
      (schedule.jointlyRegularizedFine
        weight selection data.selected).family targetConstant := by
  refine ⟨(representativeSchedule.parentData
      ⟨0, hscaleCount⟩).target_delta_pos,
    htargetFinite, htargetDistinct, ?_⟩
  intro request
  let coordinate := coordinateOf request
  exact ⟨{
    rho := schedule.callerRho coordinate
    requested_le := hrequested request
    within_factor := hwithin request
    scaleData :=
      (data.toOneScaleCWAAdapterDataOfPacketCWA coverConstant bodyConstant
        hcover hpacket coordinate (hconstantBudget coordinate)).toScaleCoverData
  }⟩

end PureWZ2AnisotropicJointRegularizationData
end PureWZ2FiniteAnisotropicParentQuotientScheduleData

end Kakeya.Assouad

end
