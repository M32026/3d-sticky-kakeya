import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicQuotientScheduleCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicActualJohnPacketCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicRepresentativeSchedule

/-!
# Actual-John CWA for the final isotropic quotient schedule

The finite index and packet decomposition is shared with the preceding
exact-triangular schedule.  This file replaces only the affine geometry and
Jacobian estimates by their positive-similarity counterparts.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2FiniteAnisotropicParentQuotientScheduleData
namespace PureWZ2AnisotropicJointRegularizationData

/-- Every nonempty source-parent packet has actual-John CWA after the final
positive similarity. -/
theorem isotropicQuotientTargetBodyPacket_cwa
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule : PureWZ2FiniteRepresentativeParentScheduleData
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
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (hcenter : |center 2| ≤ 1)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : scale * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetFamilyTube : ∀ target, targetFine.tube target =
      pureWZ2PaperCenteredTube
        (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
          (sourceFine.tube (sourceEquiv target))))
    (normalizationWeight retentionConstant : ENNReal)
    (hweightZero : normalizationWeight ≠ 0)
    (hweightTop : normalizationWeight ≠ ⊤)
    (hglobal : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (schedule.jointlyRegularizedFine
          weight selection data.selected).family.enncard)
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card) :
    WZ2PaperBodyConvexWolffBound
      (data.quotientTargetBodyPacket coordinate targetParent normalization
        sourceParent)
      (ENNReal.ofReal (27 * (2 * (32 * scale) - 1) ^ 3) *
        ENNReal.ofReal |LinearMap.det
          ((pureWZ2IsotropicJohnCoordinateChange center scale
            (lt_of_lt_of_le (by norm_num) hscale)
            (Classical.choice
              ((representativeSchedule.sourceScale coordinate).rescaledFiber
                sourceParent)).normalization normalization).symm.linear :
              Point3 →ₗ[ℝ] Point3)| *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant *
            (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                  ENNReal) ^ (scaleCount + scaleCount)))) *
          sourceConstant)) := by
  let packet := data.quotientTargetBodyPacket coordinate targetParent
    normalization sourceParent
  by_cases hpacket : 0 < packet.card
  · let sourceFiber := Classical.choice
      ((representativeSchedule.sourceScale coordinate).rescaledFiber
        sourceParent)
    let sourceIndex := data.quotientTargetBodyPacketSourceIndex
      coordinate targetParent normalization sourceParent
    have hpacketCard :=
      data.jointlyRegularizedSourcePacket_card_le_quotientTargetBodyPacket
        coordinate targetParent normalization sourceParent hpacket
    have hpacketCardReverse :=
      data.quotientTargetBodyPacket_card_le_jointlyRegularizedSourcePacket
        coordinate targetParent normalization sourceParent
    have hglobalPacket : 0 < (schedule.jointlyRegularizedSourcePacket
        weight selection data.selected coordinate sourceParent).card :=
      lt_of_lt_of_le hpacket hpacketCardReverse
    have hsourceRatio :=
      data.source_fullFiber_weighted_card_le_packet coordinate
        normalizationWeight retentionConstant hglobal sourceParent
        hglobalPacket
    have hcardinality : normalizationWeight *
        ((wz2PaperOrdinaryFullFiberIndices sourceFine
          (representativeSchedule.sourceScale coordinate).coarse
          sourceParent).card : ENNReal) ≤
        (sourceConstant * retentionConstant *
          (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
            (Nat.log 2
              (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                ENNReal) ^ (scaleCount + scaleCount))) * packet.enncard := by
      have hpacketCardENN :
          ((schedule.jointlyRegularizedSourcePacket weight selection
            data.selected coordinate sourceParent).card : ENNReal) ≤
          packet.enncard := by
        change _ ≤ (packet.card : ENNReal)
        exact_mod_cast hpacketCard
      exact hsourceRatio.trans (mul_le_mul_left' hpacketCardENN _)
    have htargetMemParent : ∀ index : Fin packet.card,
        (pureWZ2PaperCenteredTube
          (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
            (sourceFine.tube (sourceIndex index)))).carrier ⊆
          ((data.finalCoarse coordinate).tube targetParent).carrier := by
      intro index
      have htargetFiber := ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
        (data.quotientTargetBodyPacketEmbedding coordinate targetParent
          normalization sourceParent index)).2
      have hcontain := (mem_wz2PaperOrdinaryFullFiberIndices_iff
        targetParent ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
          (data.quotientTargetBodyPacketEmbedding coordinate targetParent
            normalization sourceParent index)).1).mp htargetFiber
      have hfinalTube : (schedule.jointlyRegularizedFine weight selection
          data.selected).family.tube
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            (data.quotientTargetBodyPacketEmbedding coordinate targetParent
              normalization sourceParent index)).1 =
        targetFine.tube (data.finalTargetIndex
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            (data.quotientTargetBodyPacketEmbedding coordinate targetParent
              normalization sourceParent index)).1) := rfl
      rw [hfinalTube] at hcontain
      have htargetIdentity : targetFine.tube
          (data.finalTargetIndex
            ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
              (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                normalization sourceParent index)).1) =
        pureWZ2PaperCenteredTube
          (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
            (sourceFine.tube (sourceIndex index))) := by
        rw [htargetFamilyTube]
        congr 3
      rw [htargetIdentity] at hcontain
      exact hcontain
    have htargetBody : ∀ index : Fin packet.card,
        (packet.body index).carrier = normalization.map ''
          (pureWZ2PaperCenteredTube
            (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
              (sourceFine.tube (sourceIndex index)))).carrier := by
      intro index
      change normalization.map ''
        ((schedule.jointlyRegularizedFine weight selection data.selected).family.tube
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            (data.quotientTargetBodyPacketEmbedding coordinate targetParent
              normalization sourceParent index)).1).carrier = _
      rw [show (schedule.jointlyRegularizedFine weight selection
          data.selected).family.tube
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            (data.quotientTargetBodyPacketEmbedding coordinate targetParent
              normalization sourceParent index)).1 =
        targetFine.tube (data.finalTargetIndex
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            (data.quotientTargetBodyPacketEmbedding coordinate targetParent
              normalization sourceParent index)).1) by rfl]
      rw [htargetFamilyTube]
      congr 3
    have hraw := pureWZ2_isotropicCenteredTargetPacket_cwa
      sourceParent sourceFiber center hscale hcenter hsourceDelta htargetDelta
      hsourceLine hsourceBase packet sourceIndex
      (data.quotientTargetBodyPacketSourceIndex_injective
        coordinate targetParent normalization sourceParent)
      (data.quotientTargetBodyPacketSourceIndex_mem
        coordinate targetParent normalization sourceParent)
      ((data.finalCoarse coordinate).tube targetParent) normalization
      htargetMemParent htargetBody normalizationWeight
      (sourceConstant * retentionConstant *
        (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
          (Nat.log 2
            (2 * (schedule.separatedFine weight selection).family.card) + 1 :
              ENNReal) ^ (scaleCount + scaleCount)))
      hweightZero hweightTop hcardinality
    simpa [sourceFiber, packet] using hraw
  · have hcardZero : packet.card = 0 := by omega
    intro convexSet hconvex
    have hcontainedZero : packet.containedCount convexSet = 0 := by
      unfold Kakeya.Streamlined.BodyFamily.containedCount
      have hle : (packet.containedIndices convexSet).card ≤ packet.card := by
        simpa using Finset.card_le_univ (packet.containedIndices convexSet)
      have hnat : (packet.containedIndices convexSet).card = 0 := by omega
      exact_mod_cast hnat
    have henncardZero : packet.enncard = 0 := by
      change (packet.card : ENNReal) = 0
      rw [hcardZero]
      norm_num
    rw [hcontainedZero, henncardZero]
    simp

/-- Uniformize the determinant-dependent packet estimate at one final
isotropic quotient scale. -/
theorem isotropicQuotientTargetBodyPacket_cwa_uniform
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule : PureWZ2FiniteRepresentativeParentScheduleData
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
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (hcenter : |center 2| ≤ 1)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : scale * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetFamilyTube : ∀ target, targetFine.tube target =
      pureWZ2PaperCenteredTube
        (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
          (sourceFine.tube (sourceEquiv target))))
    (normalizationWeight retentionConstant : ENNReal)
    (hweightZero : normalizationWeight ≠ 0)
    (hweightTop : normalizationWeight ≠ ⊤)
    (hglobal : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (schedule.jointlyRegularizedFine
          weight selection data.selected).family.enncard)
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card) :
    WZ2PaperBodyConvexWolffBound
      (data.quotientTargetBodyPacket coordinate targetParent normalization
        sourceParent)
      (ENNReal.ofReal (27 * (2 * (32 * scale) - 1) ^ 3) *
        ((432 : ENNReal) *
          Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
          ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
          ENNReal.ofReal (1 / (scale ^ 3 *
            representativeSchedule.sourceRho coordinate ^ 2))) *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant *
            (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                  ENNReal) ^ (scaleCount + scaleCount)))) *
          sourceConstant)) := by
  let sourceFiber := Classical.choice
    ((representativeSchedule.sourceScale coordinate).rescaledFiber
      sourceParent)
  have hraw := data.isotropicQuotientTargetBodyPacket_cwa center hscale
    hcenter hsourceDelta htargetDelta hsourceLine hsourceBase
    htargetFamilyTube normalizationWeight retentionConstant hweightZero
    hweightTop hglobal coordinate targetParent normalization sourceParent
  intro convexSet hconvex
  exact (hraw convexSet hconvex).trans <| by
    gcongr
    exact pureWZ2IsotropicJohnCoordinateChange_inverse_det_le
      (representativeSchedule.sourceScale coordinate).rho_pos
      (schedule.quotient coordinate).caller_rho_pos center
      (lt_of_lt_of_le (by norm_num) hscale)
      ((representativeSchedule.sourceScale coordinate).coarse.tube sourceParent)
      ((data.finalCoarse coordinate).tube targetParent)
      sourceFiber.normalization normalization

/-- One complete target quotient fiber inherits the uniform isotropic packet
CWA bound, with no multiplicative cost for the number of source packets. -/
theorem isotropicQuotientTargetFullFiber_cwa
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule : PureWZ2FiniteRepresentativeParentScheduleData
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
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (hcenter : |center 2| ≤ 1)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : scale * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetFamilyTube : ∀ target, targetFine.tube target =
      pureWZ2PaperCenteredTube
        (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
          (sourceFine.tube (sourceEquiv target))))
    (normalizationWeight retentionConstant : ENNReal)
    (hweightZero : normalizationWeight ≠ 0)
    (hweightTop : normalizationWeight ≠ ⊤)
    (hglobal : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (schedule.jointlyRegularizedFine
          weight selection data.selected).family.enncard)
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent)) :
    WZ2PaperBodyConvexWolffBound
      (data.quotientTargetBodies coordinate targetParent normalization)
      (ENNReal.ofReal (27 * (2 * (32 * scale) - 1) ^ 3) *
        ((432 : ENNReal) *
          Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
          ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
          ENNReal.ofReal (1 / (scale ^ 3 *
            representativeSchedule.sourceRho coordinate ^ 2))) *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant *
            (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                  ENNReal) ^ (scaleCount + scaleCount)))) *
          sourceConstant)) := by
  apply pureWZ2_bodyCWA_of_parent_fibers
  · let source : Fin sourceFine.card :=
      ⟨0, (representativeSchedule.parentData coordinate).source_nonempty⟩
    rcases (representativeSchedule.sourceScale coordinate).cover.covers source
      with ⟨sourceParent, _hsourceParent⟩
    exact lt_of_le_of_lt (Nat.zero_le sourceParent.val) sourceParent.isLt
  · intro sourceParent
    exact data.isotropicQuotientTargetBodyPacket_cwa_uniform center hscale
      hcenter hsourceDelta htargetDelta hsourceLine hsourceBase
      htargetFamilyTube normalizationWeight retentionConstant hweightZero
      hweightTop hglobal coordinate targetParent normalization sourceParent

/-- Package one final-isotropic coordinate as a public one-scale CWA datum. -/
noncomputable def toIsotropicOneScaleCWAAdapterData
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant targetConstant : ENNReal} {scaleCount : ℕ}
    {representativeSchedule : PureWZ2FiniteRepresentativeParentScheduleData
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
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (hcenter : |center 2| ≤ 1)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : scale * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetFamilyTube : ∀ target, targetFine.tube target =
      pureWZ2PaperCenteredTube
        (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
          (sourceFine.tube (sourceEquiv target))))
    (normalizationWeight retentionConstant : ENNReal)
    (hweightZero : normalizationWeight ≠ 0)
    (hweightTop : normalizationWeight ≠ ⊤)
    (hglobal : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (schedule.jointlyRegularizedFine
          weight selection data.selected).family.enncard)
    (coordinate : Fin scaleCount)
    (constant_budget : max
      (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
        (Nat.log 2
          (2 * (schedule.separatedFine weight selection).family.card) + 1 :
            ENNReal) ^ (scaleCount + scaleCount))
      (ENNReal.ofReal (27 * (2 * (32 * scale) - 1) ^ 3) *
        ((432 : ENNReal) *
          Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
          ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
          ENNReal.ofReal (1 / (scale ^ 3 *
            representativeSchedule.sourceRho coordinate ^ 2))) *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant *
            (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                  ENNReal) ^ (scaleCount + scaleCount)))) *
          sourceConstant)) ≤ targetConstant) :
    PureWZ2AnisotropicQuotientOneScaleCWAAdapterData
      (targetRho := schedule.callerRho coordinate)
      (targetFine := (schedule.jointlyRegularizedFine
        weight selection data.selected).family)
      (targetConstant := targetConstant)
      (coverConstant :=
        16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
          (Nat.log 2
            (2 * (schedule.separatedFine weight selection).family.card) + 1 :
              ENNReal) ^ (scaleCount + scaleCount))
      (bodyConstant :=
        ENNReal.ofReal (27 * (2 * (32 * scale) - 1) ^ 3) *
          ((432 : ENNReal) *
            Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
            ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
            ENNReal.ofReal (1 / (scale ^ 3 *
              representativeSchedule.sourceRho coordinate ^ 2))) *
          ((normalizationWeight⁻¹ *
            (sourceConstant * retentionConstant *
              (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
                (Nat.log 2
                  (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                    ENNReal) ^ (scaleCount + scaleCount)))) *
            sourceConstant))
      (representativeSchedule.sourceScale coordinate) where
  targetCoarse := data.finalCoarse coordinate
  target_delta_pos :=
    (representativeSchedule.parentData coordinate).target_delta_pos
  target_rho_pos := (schedule.quotient coordinate).caller_rho_pos
  targetCover := data.finalCover coordinate
  target_full_fiber_uniform := data.quotient_uniform coordinate
  sourceOf := data.finalSourceIndex
  targetNormalization := fun targetParent =>
    WZ2PaperAssouadUnitRescalingData.ofTube
      ((data.finalCoarse coordinate).tube targetParent)
      (schedule.quotient coordinate).caller_rho_pos
  packetCWA := by
    intro targetParent sourceParent
    exact data.isotropicQuotientTargetBodyPacket_cwa_uniform center hscale hcenter
      hsourceDelta htargetDelta hsourceLine hsourceBase htargetFamilyTube
      normalizationWeight retentionConstant hweightZero hweightTop hglobal
      coordinate targetParent
      (WZ2PaperAssouadUnitRescalingData.ofTube
        ((data.finalCoarse coordinate).tube targetParent)
        (schedule.quotient coordinate).caller_rho_pos) sourceParent
  source_parent_count_pos := by
    let source : Fin sourceFine.card :=
      ⟨0, (representativeSchedule.parentData coordinate).source_nonempty⟩
    rcases (representativeSchedule.sourceScale coordinate).cover.covers source
      with ⟨sourceParent, _⟩
    exact lt_of_le_of_lt (Nat.zero_le sourceParent.val) sourceParent.isLt
  constant_budget := constant_budget

/-- Lift all finitely scheduled final-isotropic quotient witnesses to the
public nearby-scale CWA interface. -/
theorem toIsotropicNearbyCWA
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
    (data : PureWZ2AnisotropicJointRegularizationData
      schedule weight selection)
    (center : Point3) {scale : ℝ} (hscale : 1 ≤ scale)
    (hcenter : |center 2| ≤ 1)
    (hsourceDelta : 0 < sourceDelta)
    (hsourceTarget : sourceDelta ≤ targetDelta)
    (htargetDelta : scale * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetFamilyTube : ∀ target, targetFine.tube target =
      pureWZ2PaperCenteredTube
        (pureWZ2IsotropicPaperTube (targetDelta := targetDelta) center scale
          (sourceFine.tube (sourceEquiv target))))
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
      isotropicQuotientCallerScale targetDelta scale
        (representativeSchedule.sourceRho coordinate))
    (hscaleBudget : isotropicQuotientScaleWindowConstant
      scale sourceScheduleConstant ≤ targetConstant)
    (hconstantBudget : ∀ coordinate, max
      (16 * ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
        ENNReal) *
        (Nat.log 2
          (2 * (schedule.separatedFine weight selection).family.card) + 1 :
            ENNReal) ^
          (sourceSchedule.scaleCount + sourceSchedule.scaleCount))
      (ENNReal.ofReal (27 * (2 * (32 * scale) - 1) ^ 3) *
        ((432 : ENNReal) *
          Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
          ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
          ENNReal.ofReal (1 / (scale ^ 3 *
            representativeSchedule.sourceRho coordinate ^ 2))) *
        ((normalizationWeight⁻¹ *
          (sourceConstant * retentionConstant *
            (16 * ((sourceSchedule.scaleCount +
                sourceSchedule.scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                  ENNReal) ^
                (sourceSchedule.scaleCount + sourceSchedule.scaleCount)))) *
          sourceConstant)) ≤ targetConstant) :
    WZ2PaperPureCWAAtNearbyScales
      (schedule.jointlyRegularizedFine
        weight selection data.selected).family targetConstant := by
  let separated := schedule.separatedFine weight selection
  let finalFine := schedule.jointlyRegularizedFine
    weight selection data.selected
  have hfinalDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct finalFine.family :=
    (htargetDistinct.subfamily separated).subfamily finalFine
  refine ⟨(representativeSchedule.parentData
      ⟨0, sourceSchedule.scaleCount_pos⟩).target_delta_pos,
    htargetFinite, hfinalDistinct, ?_⟩
  intro targetRequest
  let sourceRequest : WZ2PaperRequestedScale sourceDelta :=
    ⟨targetRequest.1, hsourceTarget.trans targetRequest.2.1,
      targetRequest.2.2⟩
  let coordinate := sourceSchedule.representative sourceRequest
  have hrequestedSource : targetRequest.1 ≤
      representativeSchedule.sourceRho coordinate := by
    rw [hsourceRho coordinate]
    exact sourceSchedule.requested_le sourceRequest
  have hrequestedCaller : targetRequest.1 ≤ schedule.callerRho coordinate := by
    rw [hcallerRho coordinate]
    unfold isotropicQuotientCallerScale
    have htargetPos :=
      (representativeSchedule.parentData coordinate).target_delta_pos
    have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
    nlinarith [(representativeSchedule.sourceScale coordinate).rho_pos]
  have hsourceWithin : ENNReal.ofReal
      (representativeSchedule.sourceRho coordinate) <
      sourceScheduleConstant * ENNReal.ofReal targetRequest.1 := by
    rw [hsourceRho coordinate]
    simpa [sourceRequest, coordinate] using
      sourceSchedule.within_output sourceRequest
  have hcallerWithin : ENNReal.ofReal (schedule.callerRho coordinate) <
      targetConstant * ENNReal.ofReal targetRequest.1 := by
    have htargetPos :=
      (representativeSchedule.parentData coordinate).target_delta_pos
    have hrequestPos : 0 < targetRequest.1 :=
      htargetPos.trans_le targetRequest.2.1
    have hsourcePos : 0 < representativeSchedule.sourceRho coordinate :=
      (representativeSchedule.sourceScale coordinate).rho_pos
    have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
    have hmul : ENNReal.ofReal (12600000 * scale) *
        ENNReal.ofReal (representativeSchedule.sourceRho coordinate) <
      ENNReal.ofReal (12600000 * scale) *
        (sourceScheduleConstant * ENNReal.ofReal targetRequest.1) := by
      have hfactorZero : ENNReal.ofReal (12600000 * scale) ≠ 0 :=
        (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      have hfactorTop : ENNReal.ofReal (12600000 * scale) ≠ ⊤ :=
        ENNReal.ofReal_ne_top
      have hright := (ENNReal.mul_lt_mul_iff_right
        hfactorZero hfactorTop).2 hsourceWithin
      simpa [mul_comm] using hright
    have htargetENN : ENNReal.ofReal targetDelta ≤
        ENNReal.ofReal targetRequest.1 :=
      ENNReal.ofReal_mono targetRequest.2.1
    have hadd : ENNReal.ofReal (12600000 * scale) *
          ENNReal.ofReal (representativeSchedule.sourceRho coordinate) +
        2 * ENNReal.ofReal targetDelta <
      ENNReal.ofReal (12600000 * scale) *
          (sourceScheduleConstant * ENNReal.ofReal targetRequest.1) +
        2 * ENNReal.ofReal targetRequest.1 := by
      exact ENNReal.add_lt_add_of_lt_of_le
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hmul
        (mul_le_mul_left' htargetENN 2)
    calc
      ENNReal.ofReal (schedule.callerRho coordinate) =
          ENNReal.ofReal (12600000 * scale) *
              ENNReal.ofReal (representativeSchedule.sourceRho coordinate) +
            2 * ENNReal.ofReal targetDelta := by
        rw [hcallerRho coordinate]
        unfold isotropicQuotientCallerScale
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ < ENNReal.ofReal (12600000 * scale) *
              (sourceScheduleConstant * ENNReal.ofReal targetRequest.1) +
            2 * ENNReal.ofReal targetRequest.1 := hadd
      _ = isotropicQuotientScaleWindowConstant scale sourceScheduleConstant *
          ENNReal.ofReal targetRequest.1 := by
        unfold isotropicQuotientScaleWindowConstant
        ring
      _ ≤ targetConstant * ENNReal.ofReal targetRequest.1 := by gcongr
  exact ⟨{
    rho := schedule.callerRho coordinate
    requested_le := hrequestedCaller
    within_factor := hcallerWithin
    scaleData := (data.toIsotropicOneScaleCWAAdapterData center hscale
      hcenter hsourceDelta htargetDelta hsourceLine hsourceBase
      htargetFamilyTube normalizationWeight retentionConstant hweightZero
      hweightTop hglobal coordinate (hconstantBudget coordinate)).toScaleCoverData
  }⟩

/-- The positive-similarity quotient caller always dominates the requested
scale by its fixed first coefficient. -/
theorem isotropicQuotientCallerScale_request_le
    {targetDelta scale sourceRho request : ℝ}
    (htargetDelta : 0 < targetDelta) (hscale : 1 ≤ scale)
    (hrequestPos : 0 < request)
    (hrequest : request ≤ sourceRho) :
    request ≤ isotropicQuotientCallerScale targetDelta scale sourceRho := by
  unfold isotropicQuotientCallerScale
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  have hsourceRhoPos : 0 < sourceRho :=
    lt_of_lt_of_le hrequestPos hrequest
  nlinarith

/-- ENNReal scale-window estimate used by `toIsotropicNearbyCWA`. -/
theorem isotropicQuotientCallerScale_within
    {targetDelta scale sourceRho request : ℝ}
    {sourceScheduleConstant : ENNReal}
    (hscale : 1 ≤ scale)
    (hsourceRho : 0 < sourceRho) (htargetDelta : 0 < targetDelta)
    (htarget : targetDelta ≤ request)
    (hsource : ENNReal.ofReal sourceRho <
      sourceScheduleConstant * ENNReal.ofReal request) :
    ENNReal.ofReal (isotropicQuotientCallerScale
        targetDelta scale sourceRho) <
      isotropicQuotientScaleWindowConstant scale sourceScheduleConstant *
        ENNReal.ofReal request := by
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  have hmul : ENNReal.ofReal (12600000 * scale) * ENNReal.ofReal sourceRho <
      ENNReal.ofReal (12600000 * scale) *
        (sourceScheduleConstant * ENNReal.ofReal request) := by
    have hfactorZero : ENNReal.ofReal (12600000 * scale) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    have hfactorTop : ENNReal.ofReal (12600000 * scale) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have hright := (ENNReal.mul_lt_mul_iff_right
      hfactorZero hfactorTop).2 hsource
    simpa [mul_comm] using hright
  have htargetENN : ENNReal.ofReal targetDelta ≤ ENNReal.ofReal request :=
    ENNReal.ofReal_mono htarget
  have hadd : ENNReal.ofReal (12600000 * scale) * ENNReal.ofReal sourceRho +
      2 * ENNReal.ofReal targetDelta <
    ENNReal.ofReal (12600000 * scale) *
        (sourceScheduleConstant * ENNReal.ofReal request) +
      2 * ENNReal.ofReal request :=
    ENNReal.add_lt_add_of_lt_of_le
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hmul
      (mul_le_mul_left' htargetENN 2)
  calc
    ENNReal.ofReal (isotropicQuotientCallerScale
        targetDelta scale sourceRho) =
      ENNReal.ofReal (12600000 * scale) * ENNReal.ofReal sourceRho +
        2 * ENNReal.ofReal targetDelta := by
      unfold isotropicQuotientCallerScale
      rw [ENNReal.ofReal_add
          (mul_nonneg (mul_nonneg (by norm_num) hscalePos.le)
            hsourceRho.le)
          (mul_nonneg (by norm_num) htargetDelta.le),
        ENNReal.ofReal_mul (mul_nonneg (by norm_num) hscalePos.le),
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
    _ < ENNReal.ofReal (12600000 * scale) *
          (sourceScheduleConstant * ENNReal.ofReal request) +
        2 * ENNReal.ofReal request := hadd
    _ = isotropicQuotientScaleWindowConstant scale sourceScheduleConstant *
        ENNReal.ofReal request := by
      unfold isotropicQuotientScaleWindowConstant
      ring

end PureWZ2AnisotropicJointRegularizationData
end PureWZ2FiniteAnisotropicParentQuotientScheduleData

end Kakeya.Assouad

end
