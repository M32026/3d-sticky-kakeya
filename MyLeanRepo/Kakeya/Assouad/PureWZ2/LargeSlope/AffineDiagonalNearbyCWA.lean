import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalActualJohnPacketCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.QuotientScheduleCWAAbstract

/-!
# Nearby-scale CWA for an affine-diagonal quotient schedule

This is the logical assembly after the affine-diagonal line and actual-John
packet geometry have been proved.  The remaining hypotheses are finite scalar
absorptions.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2FiniteAnisotropicParentQuotientScheduleData
namespace PureWZ2AnisotropicJointRegularizationData

/-- Lift a finite affine-diagonal quotient schedule to public nearby CWA. -/
theorem toAffineDiagonalNearbyCWA
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant sourceScheduleConstant targetConstant : ENNReal}
    {levelCount : ℕ}
    (sourceSchedule : PureWZ2FiniteNearbyScheduleData
      (family := sourceFine) sourceConstant sourceScheduleConstant levelCount)
    {representativeSchedule : PureWZ2FiniteRepresentativeParentScheduleData
      targetFine sourceEquiv sourceConstant sourceSchedule.scaleCount}
    {schedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData
      representativeSchedule}
    {weight : Fin targetFine.card → ENNReal}
    {selection : PureWZ2FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount schedule.Parent
      (fun coordinate target =>
        (schedule.quotient coordinate).assignedParent target)
      schedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree}
    (data : PureWZ2AnisotropicJointRegularizationData schedule weight selection)
    (frameSlope : ℝ) (center : Point3)
    (heightScale transverseScale : ℝ)
    (hheight : 1 ≤ heightScale)
    (htransverse : 0 < transverseScale)
    (htransverseOne : transverseScale ≤ 1)
    (hcenter : ‖center‖ ≤ 2)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceTarget : sourceDelta ≤ targetDelta)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetLine : WZ1PaperIsLineClass targetFine)
    (htargetDirection : ∀ target,
      (targetFine.tube target).direction =
        wz1PaperDirection (targetFine.tube target))
    (htargetMidpoint : ∀ target,
      ‖wz2PaperTubeMidpoint (targetFine.tube target)‖ ≤ 3)
    (htargetAxis : ∀ target, tubeAxisLine (targetFine.tube target) =
      pureWZ2AffineDiagonalMapCentered frameSlope center heightScale
        transverseScale 1 ''
          tubeAxisLine (sourceFine.tube (sourceEquiv target)))
    (normalizationWeight retentionConstant : ENNReal)
    (hweightZero : normalizationWeight ≠ 0)
    (hweightTop : normalizationWeight ≠ ⊤)
    (hglobal : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (schedule.jointlyRegularizedFine
          weight selection data.selected).family.enncard)
    (htargetFinite : WZ2PaperFiniteErrorConstant targetConstant)
    (htargetDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct targetFine)
    (hsourceRho : ∀ coordinate,
      representativeSchedule.sourceRho coordinate =
        (sourceSchedule.witness coordinate).rho)
    (hcallerRho : ∀ coordinate, schedule.callerRho coordinate =
      affineDiagonalQuotientCallerScale targetDelta
        (representativeSchedule.sourceRho coordinate))
    (hscaleBudget : affineDiagonalQuotientScaleWindowConstant
      sourceScheduleConstant ≤ targetConstant)
    (hconstantBudget : ∀ coordinate, max
      (16 * ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
        ENNReal) *
        (Nat.log 2
          (2 * (schedule.separatedFine weight selection).family.card) + 1 :
            ENNReal) ^
          (sourceSchedule.scaleCount + sourceSchedule.scaleCount))
      (ENNReal.ofReal
          (27 * (2 * (32 * heightScale) - 1) ^ 3) *
        ((432 : ENNReal) *
          Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
          ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
          ENNReal.ofReal (1 / (heightScale * transverseScale *
            representativeSchedule.sourceRho coordinate ^ 2))) *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant *
            (16 * ((sourceSchedule.scaleCount +
                sourceSchedule.scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 *
                  (schedule.separatedFine weight selection).family.card) +
                  1 : ENNReal) ^
                (sourceSchedule.scaleCount +
                  sourceSchedule.scaleCount)))) *
          sourceConstant)) ≤ targetConstant) :
    WZ2PaperPureCWAAtNearbyScales
      (schedule.jointlyRegularizedFine
        weight selection data.selected).family targetConstant := by
  let coordinateOf : WZ2PaperRequestedScale targetDelta →
      Fin sourceSchedule.scaleCount := fun request =>
    sourceSchedule.representative
      ⟨request.1, hsourceTarget.trans request.2.1, request.2.2⟩
  let coverConstant : Fin sourceSchedule.scaleCount → ENNReal := fun _ =>
    16 * ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
      ENNReal) *
    (Nat.log 2
      (2 * (schedule.separatedFine weight selection).family.card) + 1 :
        ENNReal) ^
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
  let bodyConstant : Fin sourceSchedule.scaleCount → ENNReal :=
    fun coordinate =>
      ENNReal.ofReal (27 * (2 * (32 * heightScale) - 1) ^ 3) *
        ((432 : ENNReal) *
          Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
          ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
          ENNReal.ofReal (1 / (heightScale * transverseScale *
            representativeSchedule.sourceRho coordinate ^ 2))) *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant *
            (16 * ((sourceSchedule.scaleCount +
                sourceSchedule.scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 *
                  (schedule.separatedFine weight selection).family.card) +
                  1 : ENNReal) ^
                (sourceSchedule.scaleCount +
                  sourceSchedule.scaleCount)))) *
          sourceConstant)
  apply data.toNearbyCWAOfPacketCWA
    (coverConstant := coverConstant) (bodyConstant := bodyConstant)
    sourceSchedule.scaleCount_pos htargetFinite
    ((htargetDistinct.subfamily
      (schedule.separatedFine weight selection)).subfamily
        (schedule.jointlyRegularizedFine weight selection data.selected))
    coordinateOf
  · intro request
    let sourceRequest : WZ2PaperRequestedScale sourceDelta :=
      ⟨request.1, hsourceTarget.trans request.2.1, request.2.2⟩
    have hsourceRequest : request.1 ≤
        representativeSchedule.sourceRho (coordinateOf request) := by
      rw [hsourceRho (coordinateOf request)]
      simpa [coordinateOf, sourceRequest] using
        sourceSchedule.requested_le sourceRequest
    rw [hcallerRho (coordinateOf request)]
    exact affineDiagonalQuotientCallerScale_request_le
      (representativeSchedule.parentData (coordinateOf request)).target_delta_pos
      ((representativeSchedule.parentData (coordinateOf request)).target_delta_pos
        |>.trans_le request.2.1) request.2.1 hsourceRequest
  · intro request
    let sourceRequest : WZ2PaperRequestedScale sourceDelta :=
      ⟨request.1, hsourceTarget.trans request.2.1, request.2.2⟩
    have hsourceWithin : ENNReal.ofReal
        (representativeSchedule.sourceRho (coordinateOf request)) <
      sourceScheduleConstant * ENNReal.ofReal request.1 := by
      rw [hsourceRho (coordinateOf request)]
      simpa [coordinateOf, sourceRequest] using
        sourceSchedule.within_output sourceRequest
    have hwithin := affineDiagonalQuotientCallerScale_within
      (sourceScheduleConstant := sourceScheduleConstant)
      (sourceRho := representativeSchedule.sourceRho (coordinateOf request))
      (request := request.1) (targetDelta := targetDelta)
      (representativeSchedule.sourceScale (coordinateOf request)).rho_pos
      (representativeSchedule.parentData
        (coordinateOf request)).target_delta_pos request.2.1 hsourceWithin
    rw [hcallerRho (coordinateOf request)]
    exact hwithin.trans_le (mul_le_mul_right' hscaleBudget _)
  · intro coordinate
    exact data.quotient_uniform coordinate
  · intro coordinate
    simpa [coverConstant, bodyConstant] using hconstantBudget coordinate
  · intro coordinate targetParent normalization sourceParent
    simpa [bodyConstant] using
      data.affineDiagonalQuotientTargetBodyPacket_cwa_uniform
        frameSlope center heightScale transverseScale hheight htransverse
        htransverseOne hcenter hsourceDelta hsourceTarget hsourceBase
        htargetLine htargetDirection htargetMidpoint htargetAxis
        normalizationWeight retentionConstant hweightZero hweightTop hglobal
        coordinate targetParent normalization sourceParent

end PureWZ2AnisotropicJointRegularizationData
end PureWZ2FiniteAnisotropicParentQuotientScheduleData

end Kakeya.Assouad

end
