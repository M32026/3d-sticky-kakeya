import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCWASchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalActualJohnPacketCWA

/-!
# Requested-scale CWA constructor for the direct half-offset terminal

This module records the exact cardinality loss of the two finite selections
in the actual terminal schedule.  The weight is definitionally the terminal
cleanup weight, so no separate weight-identification hypothesis is needed.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2DirectCommonYSourceAssembly
namespace TerminalGeometry
namespace PureWZ2ExternalWeightRegularizationData
namespace DirectHalfOffsetTerminalCWAScheduleData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- Total cardinality loss of the quotient-center selection and the joint
source-parent selection for the actual terminal schedule. -/
def retentionConstant
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization) : ENNReal :=
  (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
      scheduleData.sourceSchedule.scaleCount *
    ((8 : ENNReal) *
      (Nat.log 2
        (2 * (scheduleData.quotientSchedule.separatedFine
          (directHalfOffsetTerminalJointWeight
            (commonSource := commonSource) regularization)
          scheduleData.selection).family.card) + 1 : ENNReal) ^
        (scheduleData.sourceSchedule.scaleCount +
          scheduleData.sourceSchedule.scaleCount + 1)) *
    (2 * regularization.selectedWeightLevel)

/-- The source-selected weight level bounds its total cardinality. -/
theorem selectedWeightLevel_mul_sourceCard_le
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (_scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization) :
    regularization.selectedWeightLevel *
        regularization.selected.family.enncard ≤
      regularization.selectedWeight := by
  rw [regularization.selectedWeight_eq]
  change regularization.selectedWeightLevel *
      (regularization.selected.family.card : ENNReal) ≤
    ∑ index : Fin regularization.selected.family.card,
      cleanup.sourceWeight (regularization.selected.embedding index)
  calc
    regularization.selectedWeightLevel *
        (regularization.selected.family.card : ENNReal) =
      ∑ _index : Fin regularization.selected.family.card,
        regularization.selectedWeightLevel := by simp [mul_comm]
    _ ≤ _ := Finset.sum_le_sum fun index _ =>
      (regularization.selected_weight_band index).1

/-- Both complete-fiber selections retain enough source cardinality for the
actual-John packet estimate.  The proof uses the literal direct joint weight;
its provenance is therefore definitional. -/
theorem source_cardinality_retention
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization) :
    regularization.selectedWeightLevel *
        regularization.selected.family.enncard ≤
      scheduleData.retentionConstant *
        (scheduleData.quotientSchedule.jointlyRegularizedFine
          (directHalfOffsetTerminalJointWeight
            (commonSource := commonSource) regularization)
          scheduleData.selection scheduleData.joint.selected).family.enncard := by
  let weight := directHalfOffsetTerminalJointWeight
    (commonSource := commonSource) regularization
  let separated := scheduleData.quotientSchedule.separatedFine
    weight scheduleData.selection
  let finalFine := scheduleData.quotientSchedule.jointlyRegularizedFine
    weight scheduleData.selection scheduleData.joint.selected
  have hselectedWeight : regularization.selectedWeight =
      ∑ target : Fin (DirectHalfOffsetTerminalRequestedCWAPreTarget
        (commonSource := commonSource) regularization).card, weight target := by
    rw [regularization.selectedWeight_eq]
    rfl
  have hfinalWeight :
      (∑ index ∈ scheduleData.joint.selected,
        weight (separated.embedding index)) ≤
      (2 * regularization.selectedWeightLevel) *
        finalFine.family.enncard := by
    calc
      _ ≤ ∑ _index ∈ scheduleData.joint.selected,
          2 * regularization.selectedWeightLevel := by
        apply Finset.sum_le_sum
        intro index hindex
        exact (regularization.selected_weight_band
          (separated.embedding index)).2
      _ = (2 * regularization.selectedWeightLevel) *
          finalFine.family.enncard := by
        simp only [Finset.sum_const, nsmul_eq_mul,
          Kakeya.Streamlined.TubeFamily.enncard]
        rw [show finalFine.family.card =
          scheduleData.joint.selected.card by rfl]
        exact mul_comm _ _
  calc
    regularization.selectedWeightLevel *
        regularization.selected.family.enncard ≤
      regularization.selectedWeight :=
        scheduleData.selectedWeightLevel_mul_sourceCard_le
    _ = ∑ target : Fin (DirectHalfOffsetTerminalRequestedCWAPreTarget
          (commonSource := commonSource) regularization).card,
          weight target := hselectedWeight
    _ ≤ (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
          scheduleData.sourceSchedule.scaleCount *
        ∑ index ∈ scheduleData.selection.selected, weight index :=
      scheduleData.selection.retained_weight
    _ = (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
          scheduleData.sourceSchedule.scaleCount *
        ∑ index : Fin separated.family.card,
          weight (separated.embedding index) := by
      have hsum :
          (∑ index : Fin separated.family.card,
            weight (separated.embedding index)) =
          ∑ index ∈ scheduleData.selection.selected, weight index := by
        have himageSum :
            (∑ index : Fin separated.family.card,
              weight (separated.embedding index)) =
            ∑ index ∈ Finset.image separated.embedding
                (Finset.univ : Finset (Fin separated.family.card)),
              weight index :=
          (Finset.sum_image
            (fun first _ second _ heq =>
              separated.embedding.injective heq)).symm
        have himage : Finset.image separated.embedding
            (Finset.univ : Finset (Fin separated.family.card)) =
          scheduleData.selection.selected := by
          change Finset.image
              (scheduleData.selection.selected.orderEmbOfFin rfl)
              (Finset.univ : Finset
                (Fin scheduleData.selection.selected.card)) =
            scheduleData.selection.selected
          exact Finset.image_orderEmbOfFin_univ
            scheduleData.selection.selected rfl
        exact himageSum.trans
          (congrArg (fun indices => ∑ index ∈ indices, weight index) himage)
      rw [hsum]
    _ ≤ (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
          scheduleData.sourceSchedule.scaleCount *
        (((8 : ENNReal) *
          (Nat.log 2 (2 * separated.family.card) + 1 : ENNReal) ^
            (scheduleData.sourceSchedule.scaleCount +
              scheduleData.sourceSchedule.scaleCount + 1)) *
          ∑ index ∈ scheduleData.joint.selected,
            weight (separated.embedding index)) := by
      gcongr
      exact scheduleData.joint.retained_weight
    _ ≤ (pureWZ2AnisotropicQuotientCenterConflictDegree : ENNReal) ^
          scheduleData.sourceSchedule.scaleCount *
        (((8 : ENNReal) *
          (Nat.log 2 (2 * separated.family.card) + 1 : ENNReal) ^
            (scheduleData.sourceSchedule.scaleCount +
              scheduleData.sourceSchedule.scaleCount + 1)) *
          ((2 * regularization.selectedWeightLevel) *
            finalFine.family.enncard)) := by
      gcongr
    _ = scheduleData.retentionConstant * finalFine.family.enncard := by
      unfold retentionConstant
      ring

/-- The quotient full-fiber uniformity constant at one scheduled coordinate. -/
def coverConstant
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization)
    (_coordinate : Fin scheduleData.sourceSchedule.scaleCount) : ENNReal :=
  16 *
    ((scheduleData.sourceSchedule.scaleCount +
      scheduleData.sourceSchedule.scaleCount : ℕ) : ENNReal) *
    (Nat.log 2
      (2 * (scheduleData.quotientSchedule.separatedFine
        (directHalfOffsetTerminalJointWeight
          (commonSource := commonSource) regularization)
        scheduleData.selection).family.card) + 1 : ENNReal) ^
      (scheduleData.sourceSchedule.scaleCount +
        scheduleData.sourceSchedule.scaleCount)

/-- The uniform actual-John body constant for one terminal packet. -/
def packetFactor
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (_scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization) : ℝ :=
  let equivalence := totalAffineEquiv commonSource terminal
  32 * (1 +
    ‖equivalence.linear.toContinuousLinearEquiv.toContinuousLinearMap‖ +
    ‖equivalence 0‖)

/-- The uniform actual-John body constant for one terminal packet. -/
def bodyConstant
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization)
    (coordinate : Fin scheduleData.sourceSchedule.scaleCount) : ENNReal :=
  ENNReal.ofReal (27 * (2 * scheduleData.packetFactor - 1) ^ 3) *
    ((432 : ENNReal) *
      Kakeya.realRpowENN
        (scheduleData.quotientSchedule.callerRho coordinate) 2 *
      ENNReal.ofReal
        (1 + 2 * scheduleData.quotientSchedule.callerRho coordinate) *
      ENNReal.ofReal (1 /
        (commonSource.halfOffsetAssembly.horizontalSource.m *
          pureWZ2DirectHalfOffsetTerminalLambda ^ 2 *
          scheduleData.representativeSchedule.sourceRho coordinate ^ 2))) *
    ((regularization.selectedWeightLevel⁻¹ *
      (regularization.outputConstant * scheduleData.retentionConstant *
        scheduleData.coverConstant coordinate)) *
      regularization.outputConstant)

/-- The joint schedule uses the cleanup mass weight definitionally. -/
@[simp] theorem weight_provenance
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (_scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization)
    (index : Fin (DirectHalfOffsetTerminalRequestedCWAPreTarget
      (commonSource := commonSource) regularization).card) :
    directHalfOffsetTerminalJointWeight
        (commonSource := commonSource) regularization index =
      cleanup.sourceWeight (regularization.selected.embedding index) := rfl

/-- The source finite schedule chooses the index used for a target request.
The lower endpoint is valid because the actual terminal radius dominates the
ambient source radius. -/
noncomputable def requestedCoordinate
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization)
    (request : WZ2PaperRequestedScale terminal.targetDelta) :
    Fin scheduleData.sourceSchedule.scaleCount :=
  scheduleData.sourceSchedule.representative
    ⟨request.1, by
      have hbudget := commonSource.halfOffsetLineClass_incidence_budget
      have herrorNonneg : 0 ≤ (51 / 100 : ℝ) *
          (terminal.targetDelta * Real.sqrt 3) := by
        positivity [commonSource.halfOffsetLineClassTargetDelta_pos]
      exact (show delta ≤ terminal.targetDelta by linarith) |>.trans request.2.1,
      request.2.2⟩

/-- The quotient caller scale dominates the requested terminal scale. -/
theorem requested_le
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization)
    (request : WZ2PaperRequestedScale terminal.targetDelta) :
    request.1 ≤ scheduleData.quotientSchedule.callerRho
      (scheduleData.requestedCoordinate request) := by
  let sourceRequest : WZ2PaperRequestedScale delta :=
    ⟨request.1, by
      have hbudget := commonSource.halfOffsetLineClass_incidence_budget
      have herrorNonneg : 0 ≤ (51 / 100 : ℝ) *
          (terminal.targetDelta * Real.sqrt 3) := by
        positivity [commonSource.halfOffsetLineClassTargetDelta_pos]
      exact (show delta ≤ terminal.targetDelta by linarith) |>.trans request.2.1,
      request.2.2⟩
  have hsourceRequest : request.1 ≤
      scheduleData.representativeSchedule.sourceRho
        (scheduleData.requestedCoordinate request) := by
    rw [scheduleData.sourceRho_eq]
    simpa [requestedCoordinate, sourceRequest] using
      scheduleData.sourceSchedule.requested_le sourceRequest
  rw [scheduleData.callerRho_eq]
  exact horizontalNormalizedQuotientCallerScale_request_le
    (scheduleData.representativeSchedule.parentData
      (scheduleData.requestedCoordinate request)).target_delta_pos
    scheduleData.lineFactor_one
    ((scheduleData.representativeSchedule.parentData
      (scheduleData.requestedCoordinate request)).target_delta_pos.trans_le
        request.2.1) request.2.1 hsourceRequest

/-- The quotient caller scale stays within the fixed finite schedule window. -/
theorem requested_within
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant targetConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization)
    (hscaleBudget : horizontalNormalizedQuotientScaleWindowConstant
      scheduleData.lineFactor sourceScheduleConstant ≤ targetConstant)
    (request : WZ2PaperRequestedScale terminal.targetDelta) :
    ENNReal.ofReal (scheduleData.quotientSchedule.callerRho
        (scheduleData.requestedCoordinate request)) <
      targetConstant * ENNReal.ofReal request.1 := by
  let sourceRequest : WZ2PaperRequestedScale delta :=
    ⟨request.1, by
      have hbudget := commonSource.halfOffsetLineClass_incidence_budget
      have herrorNonneg : 0 ≤ (51 / 100 : ℝ) *
          (terminal.targetDelta * Real.sqrt 3) := by
        positivity [commonSource.halfOffsetLineClassTargetDelta_pos]
      exact (show delta ≤ terminal.targetDelta by linarith) |>.trans request.2.1,
      request.2.2⟩
  have hsourceWithin : ENNReal.ofReal
      (scheduleData.representativeSchedule.sourceRho
        (scheduleData.requestedCoordinate request)) <
      sourceScheduleConstant * ENNReal.ofReal request.1 := by
    rw [scheduleData.sourceRho_eq]
    simpa [requestedCoordinate, sourceRequest] using
      scheduleData.sourceSchedule.within_output sourceRequest
  have hwithin := horizontalNormalizedQuotientCallerScale_within
    (sourceScheduleConstant := sourceScheduleConstant)
    (lineFactor := scheduleData.lineFactor)
    (sourceRho := scheduleData.representativeSchedule.sourceRho
      (scheduleData.requestedCoordinate request))
    (request := request.1) (targetDelta := terminal.targetDelta)
    (lt_of_lt_of_le (by norm_num) scheduleData.lineFactor_one)
    (scheduleData.representativeSchedule.sourceScale
      (scheduleData.requestedCoordinate request)).rho_pos
    commonSource.halfOffsetLineClassTargetDelta_pos request.2.1 hsourceWithin
  rw [scheduleData.callerRho_eq]
  exact hwithin.trans_le (by gcongr)

/-- The joint regularization supplies the final cover uniformity verbatim. -/
theorem coverUniform
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization)
    (coordinate : Fin scheduleData.sourceSchedule.scaleCount) :
    WZ2PaperPureFullFibersAreCUniform
      (scheduleData.quotientSchedule.jointlyRegularizedFine
        (directHalfOffsetTerminalJointWeight
          (commonSource := commonSource) regularization)
        scheduleData.selection scheduleData.joint.selected).family
      (scheduleData.joint.finalCoarse coordinate)
      (scheduleData.coverConstant coordinate) := by
  simpa [coverConstant,
    PureWZ2FiniteAnisotropicParentQuotientScheduleData.PureWZ2AnisotropicJointRegularizationData.finalCoarse,
    PureWZ2FiniteAnisotropicParentQuotientScheduleData.separatedSchedule] using
      scheduleData.joint.quotient_uniform coordinate

/-- The actual-John packet theorem in the exact constant shape stored by the
requested-scale record. -/
theorem packetCWA
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization)
    (coordinate : Fin scheduleData.sourceSchedule.scaleCount)
    (targetParent : Fin (scheduleData.joint.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((scheduleData.joint.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (scheduleData.representativeSchedule.sourceScale coordinate).coarse.card) :
    WZ2PaperBodyConvexWolffBound
      (scheduleData.joint.quotientTargetBodyPacket coordinate targetParent
        normalization sourceParent) (scheduleData.bodyConstant coordinate) := by
  have hraw :=
    PureWZ2FiniteAnisotropicParentQuotientScheduleData.PureWZ2AnisotropicJointRegularizationData.directHalfOffsetQuotientTargetBodyPacket_cwa
          (sourceFiberConstant := regularization.outputConstant)
          (representativeSchedule := scheduleData.representativeSchedule)
          (schedule := scheduleData.quotientSchedule)
          (weight := directHalfOffsetTerminalJointWeight
            (commonSource := commonSource) regularization)
          (selection := scheduleData.selection) commonSource regularization
          scheduleData.joint regularization.selectedWeightLevel
          scheduleData.retentionConstant
          regularization.selectedWeightLevel_pos.ne'
          regularization.selectedWeightLevel_ne_top
          scheduleData.source_cardinality_retention coordinate targetParent
          normalization sourceParent
  intro convexSet hconvex
  exact (hraw convexSet hconvex).trans <| by
    simp only [bodyConstant, coverConstant, packetFactor]
    gcongr
    exact totalJohnCoordinateChange_inverse_det_le commonSource
      (scheduleData.representativeSchedule.sourceScale coordinate).rho_pos
      (scheduleData.quotientSchedule.quotient coordinate).caller_rho_pos
      terminal
      ((scheduleData.representativeSchedule.sourceScale coordinate).coarse.tube
        sourceParent)
      ((scheduleData.joint.finalCoarse coordinate).tube targetParent)
      (Classical.choice ((scheduleData.representativeSchedule.sourceScale
        coordinate).rescaledFiber sourceParent)).normalization
      normalization
    all_goals exact le_rfl

/-- Build the literal requested-scale CWA datum from the verified finite
schedule and actual-John packet geometry.  Only the two final scalar budgets
remain inputs at this boundary. -/
theorem toRequestedCWAData
    {terminal : commonSource.TerminalGeometry} {degreeBound : ENNReal}
    {sourceConstant scheduleConstant normalizationWeight
      sourceScheduleConstant targetConstant : ENNReal}
    {levelCount parentLevelCount : ℕ}
    {cleanup : PureWZ2HalfOffsetTerminalDistinctCleanupData
      commonSource terminal degreeBound}
    {regularization : PureWZ2HalfOffsetTerminalCleanupSourceRegularizationData
      cleanup sourceConstant scheduleConstant normalizationWeight levelCount}
    (scheduleData : DirectHalfOffsetTerminalCWAScheduleData
      (sourceScheduleConstant := sourceScheduleConstant)
      (parentLevelCount := parentLevelCount) regularization)
    (htargetFinite : WZ2PaperFiniteErrorConstant targetConstant)
    (hscaleBudget : horizontalNormalizedQuotientScaleWindowConstant
      scheduleData.lineFactor sourceScheduleConstant ≤ targetConstant)
    (hconstantBudget : ∀ coordinate,
      max (scheduleData.coverConstant coordinate)
        (scheduleData.bodyConstant coordinate) ≤ targetConstant) :
    Nonempty (DirectHalfOffsetTerminalRequestedCWAData
      regularization targetConstant) := by
  exact ⟨{
    sourceScheduleConstant := sourceScheduleConstant
    parentLevelCount := parentLevelCount
    sourceSchedule := scheduleData.sourceSchedule
    representativeSchedule := scheduleData.representativeSchedule
    quotientSchedule := scheduleData.quotientSchedule
    weight := directHalfOffsetTerminalJointWeight
      (commonSource := commonSource) regularization
    weight_provenance := scheduleData.weight_provenance
    selection := scheduleData.selection
    joint := scheduleData.joint
    targetFinite := htargetFinite
    requestedCoordinate := scheduleData.requestedCoordinate
    requested_le := scheduleData.requested_le
    requested_within := scheduleData.requested_within hscaleBudget
    coverConstant := scheduleData.coverConstant
    bodyConstant := scheduleData.bodyConstant
    coverUniform := scheduleData.coverUniform
    constant_budget := hconstantBudget
    packetCWA := scheduleData.packetCWA }⟩

end DirectHalfOffsetTerminalCWAScheduleData
end PureWZ2ExternalWeightRegularizationData
end TerminalGeometry
end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
