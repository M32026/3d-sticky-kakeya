import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalRequestedCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationRepresentativeSchedule

/-!
# Finite CWA schedule for the actual half-offset terminal

The source schedule stays on the external-weight selected source family.
The representative schedule separately targets the actual terminal cleanup
family, synchronised only by `Equiv.refl`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry
namespace PureWZ2ExternalWeightRegularizationData

variable {logExponent : ℕ} {sigma epsilon delta : ℝ}
  {commonSource : PureWZ2DirectCommonYSourceAssembly logExponent sigma epsilon delta}

def directHalfOffsetTerminalJointWeight
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight : ENNReal} {levelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount)
    (index : Fin (DirectHalfOffsetTerminalRequestedCWAPreTarget
      (commonSource := commonSource) regularization).card) : ENNReal :=
  cleanup.sourceWeight (regularization.selected.embedding index)

/-- The finite source schedule and the actual terminal quotient selections. -/
structure DirectHalfOffsetTerminalCWAScheduleData
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount) where
  lineFactor : ℝ
  lineFactor_one : 1 ≤ lineFactor
  sourceSchedule : PureWZ2FiniteNearbyScheduleData
    (family := regularization.selected.family) regularization.outputConstant
    sourceScheduleConstant parentLevelCount
  representativeSchedule : PureWZ2FiniteRepresentativeParentScheduleData
    (sourceFine := regularization.selected.family)
    (DirectHalfOffsetTerminalRequestedCWAPreTarget
      (commonSource := commonSource) regularization)
    (Equiv.refl (Fin regularization.selected.family.card))
    regularization.outputConstant sourceSchedule.scaleCount
  quotientSchedule : PureWZ2FiniteAnisotropicParentQuotientScheduleData representativeSchedule
  selection : PureWZ2FiniteStrongParentSelectionData
    (directHalfOffsetTerminalJointWeight (commonSource := commonSource) regularization)
    sourceSchedule.scaleCount quotientSchedule.Parent
    (fun coordinate target => (quotientSchedule.quotient coordinate).assignedParent target)
    quotientSchedule.conflict pureWZ2AnisotropicQuotientCenterConflictDegree
  joint : quotientSchedule.PureWZ2AnisotropicJointRegularizationData
    (directHalfOffsetTerminalJointWeight (commonSource := commonSource) regularization) selection
  sourceRho_eq : ∀ coordinate, representativeSchedule.sourceRho coordinate =
    (sourceSchedule.witness coordinate).rho
  callerRho_eq : ∀ coordinate, quotientSchedule.callerRho coordinate =
    horizontalNormalizedQuotientCallerScale terminal.targetDelta
      lineFactor
      (representativeSchedule.sourceRho coordinate)

/-- Build the finite source, representative, quotient, and joint schedule.
`hlineTransport` is the sole map-specific relation between source and actual
terminal line metrics. -/
theorem directHalfOffsetTerminal_cwa_schedule
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData commonSource terminal degreeBound}
    (regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount)
    (hsourceTwo : 2 < regularization.outputConstant)
    (hdeltaOne : delta ≤ 1)
    (hlevels : ENNReal.ofReal (1 / delta) ≤
      regularization.outputConstant ^ parentLevelCount)
    (hsourceScheduleConstant : regularization.outputConstant *
      regularization.outputConstant ≤ sourceScheduleConstant)
    (lineFactor : ℝ) (hlineFactor : 1 ≤ lineFactor)
    (hsourceLine : WZ1PaperIsLineClass regularization.selected.family)
    (hsourceBase : ∀ source, ‖(regularization.selected.family.tube source).base‖ ≤ 5)
    (htargetMidpoint : ∀ target, ‖wz2PaperTubeMidpoint
      ((DirectHalfOffsetTerminalRequestedCWAPreTarget
        (commonSource := commonSource) regularization).tube target)‖ ≤ 3)
    (htargetPackingDistinct : WZ1PaperIsEssentiallyDistinct
      (wz2PaperRelabelFamily
        (sourceScale := terminal.targetDelta)
        (targetScale := (2 / 3 : ℝ) * terminal.targetDelta)
        (DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization)))
    (htargetCarrierSubsetRelabel : ∀ {rho : ℝ}, 0 < rho → ∀ first second,
      (3 / 2 : ℝ) * wz1PaperLineDistance
          ((DirectHalfOffsetTerminalRequestedCWAPreTarget
            (commonSource := commonSource) regularization).tube first)
          ((DirectHalfOffsetTerminalRequestedCWAPreTarget
            (commonSource := commonSource) regularization).tube second) +
        terminal.targetDelta ≤ rho →
      ((DirectHalfOffsetTerminalRequestedCWAPreTarget
        (commonSource := commonSource) regularization).tube first).carrier ⊆
        (wz2PaperRelabelTube (targetScale := rho)
          ((DirectHalfOffsetTerminalRequestedCWAPreTarget
            (commonSource := commonSource) regularization).tube second)).carrier)
    (hlineTransport : ∀ first second,
      wz1PaperLineDistance
        ((DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization).tube first)
        ((DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization).tube second) ≤
        lineFactor * wz1PaperLineDistance
          (regularization.selected.family.tube first)
          (regularization.selected.family.tube second)) :
    ∃ scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (commonSource := commonSource) (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization,
      scheduleData.lineFactor = lineFactor := by
  rcases pureWZ2_finite_pure_nearby_schedule parentLevelCount
      regularization.cwa_nearby.1 hdeltaOne hsourceTwo
      regularization.cwa_nearby.2.1.2 hlevels hsourceScheduleConstant
      regularization.cwa_nearby with ⟨sourceSchedule⟩
  let targetFine := DirectHalfOffsetTerminalRequestedCWAPreTarget
    (commonSource := commonSource) regularization
  have htargetLine : WZ1PaperIsLineClass targetFine :=
    (TerminalGeometry.line_class_subfamily commonSource terminal cleanup.family).subfamily
      (halfOffsetTerminalCleanupTargetSubfamily (commonSource := commonSource) regularization)
  let representativeSchedule := pureWZ2HorizontalNormalizedRepresentativeSchedule
    sourceSchedule targetFine (Equiv.refl _) lineFactor
    (le_trans (by norm_num) hlineFactor)
    commonSource.halfOffsetLineClassTargetDelta_pos regularization.selected_nonempty
    hsourceLine hsourceBase htargetLine
    (halfOffsetTerminalCleanupTargetSubfamily_distinct
      (commonSource := commonSource) regularization)
    htargetMidpoint htargetPackingDistinct htargetCarrierSubsetRelabel hlineTransport
  let quotientSchedule := pureWZ2HorizontalNormalizedParentQuotientSchedule
    representativeSchedule lineFactor (le_trans (by norm_num) hlineFactor)
      (fun _ => rfl) (fun _ => rfl)
  rcases quotientSchedule.simultaneouslySeparate
      (directHalfOffsetTerminalJointWeight (commonSource := commonSource) regularization) with
    ⟨selection⟩
  rcases quotientSchedule.simultaneouslyRegularizeQuotientAndSource
      (directHalfOffsetTerminalJointWeight (commonSource := commonSource) regularization)
      selection with ⟨joint⟩
  refine ⟨{
      lineFactor := lineFactor
      lineFactor_one := hlineFactor
      sourceSchedule := sourceSchedule
      representativeSchedule := representativeSchedule
      quotientSchedule := quotientSchedule
      selection := selection
      joint := joint
      sourceRho_eq := fun _ => rfl
      callerRho_eq := fun _ => rfl }, rfl⟩

end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
