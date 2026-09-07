import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicParentQuotientSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicQuotientOneScaleCWAAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicJohnDeterminant

/-!
# Actual-John CWA for the finite anisotropic quotient schedule

This module connects the joint quotient/source-parent regularization to the
one-scale packetwise CWA adapter.  The definitions below keep the three index
levels explicit: final fine tubes, one public quotient full fiber, and one
source-actual-parent packet inside that fiber.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2FiniteAnisotropicParentQuotientScheduleData
namespace PureWZ2AnisotropicJointRegularizationData

/-- The final coarse quotient family at one scheduled coordinate. -/
noncomputable def finalCoarse
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (coordinate : Fin scaleCount) :
    Kakeya.Streamlined.TubeFamily (schedule.callerRho coordinate) :=
  ((schedule.separatedSchedule weight selection).cover coordinate
    |>.toPartitioningCover.hitParentSubfamily
      (schedule.jointlyRegularizedFine
        weight selection data.selected)).family

/-- The final public quotient cover at one scheduled coordinate. -/
noncomputable def finalCover
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (coordinate : Fin scaleCount) :
    WZ2PaperPurePartitioningCover
      (schedule.jointlyRegularizedFine
        weight selection data.selected).family
      (data.finalCoarse coordinate) :=
  ((schedule.separatedSchedule weight selection).cover coordinate
    |>.restrictToHitParents
      (schedule.jointlyRegularizedFine weight selection data.selected))
    |>.toPartitioningCover

/-- Final target fine index viewed in the synchronized ambient target
family. -/
def finalTargetIndex
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
      schedule weight selection) :
    Fin (schedule.jointlyRegularizedFine
      weight selection data.selected).family.card ↪ Fin targetFine.card :=
  (schedule.jointlyRegularizedFine
    weight selection data.selected).embedding.trans
      (schedule.separatedFine weight selection).embedding

/-- The source fine index synchronized with one final target tube. -/
def finalSourceIndex
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
      schedule weight selection) :
    Fin (schedule.jointlyRegularizedFine
      weight selection data.selected).family.card ↪ Fin sourceFine.card :=
  data.finalTargetIndex.trans sourceEquiv.toEmbedding

/-- Final tubes with the same source actual parent have the same public
quotient parent. -/
theorem finalCover_parent_eq_of_sourceParent_eq
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (coordinate : Fin scaleCount)
    (first second : Fin (schedule.jointlyRegularizedFine
      weight selection data.selected).family.card)
    (hsource :
      (representativeSchedule.sourceScale coordinate).cover.parent
          (data.finalSourceIndex first) =
        (representativeSchedule.sourceScale coordinate).cover.parent
          (data.finalSourceIndex second)) :
    (data.finalCover coordinate).parent first =
      (data.finalCover coordinate).parent second := by
  let separated := schedule.separatedFine weight selection
  let finalFine := schedule.jointlyRegularizedFine
    weight selection data.selected
  let pre := (schedule.quotient coordinate).toPreAssignedParentCover
  let selectedCover := schedule.selectedCover weight selection coordinate
  have hfinalParent : ∀ target : Fin finalFine.family.card,
      (data.finalCover coordinate).parent target =
        selectedCover.toPartitioningCover.hitParent finalFine target := by
    intro target
    exact (selectedCover.restrictToHitParents finalFine).parent_eq_assigned target
  rw [hfinalParent first, hfinalParent second]
  apply
    (selectedCover.toPartitioningCover.hitParentSubfamily finalFine).embedding.injective
  rw [selectedCover.toPartitioningCover.hitParent_ambient finalFine first,
    selectedCover.toPartitioningCover.hitParent_ambient finalFine second]
  have hselectedAssigned : ∀ target : Fin separated.family.card,
      selectedCover.assignedParent target = pre.hitParent separated target := by
    intro target
    rfl
  rw [selectedCover.parent_eq_assigned, selectedCover.parent_eq_assigned,
    hselectedAssigned, hselectedAssigned]
  apply (pre.hitParentSubfamily separated).embedding.injective
  rw [pre.hitParent_ambient separated (finalFine.embedding first),
    pre.hitParent_ambient separated (finalFine.embedding second)]
  change (schedule.quotient coordinate).net.center
      ((representativeSchedule.sourceScale coordinate).cover.parent
        (data.finalSourceIndex first)) =
    (schedule.quotient coordinate).net.center
      ((representativeSchedule.sourceScale coordinate).cover.parent
        (data.finalSourceIndex second))
  rw [hsource]

/-- Canonical target actual-John bodies over one final quotient parent. -/
noncomputable def quotientTargetBodies
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent)) :
    Kakeya.Streamlined.BodyFamily :=
  wz2PaperPureUnitRescaledFullFiberBodyFamily
    (fine := (schedule.jointlyRegularizedFine
      weight selection data.selected).family)
    (coarse := data.finalCoarse coordinate)
    targetParent normalization

/-- Source actual parent attached to one canonical target body. -/
noncomputable def quotientTargetBodySourceParent
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent)) :
    Fin (data.quotientTargetBodies coordinate targetParent normalization).card →
      Fin (representativeSchedule.sourceScale coordinate).coarse.card :=
  fun targetBody =>
    (representativeSchedule.sourceScale coordinate).cover.parent
      (data.finalSourceIndex
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) targetBody).1)

/-- One source-parent packet inside one final quotient actual-John fiber. -/
noncomputable def quotientTargetBodyPacket
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card) :
    Kakeya.Streamlined.BodyFamily :=
  pureWZ2BodyParentFiber
    (data.quotientTargetBodies coordinate targetParent normalization)
    (data.quotientTargetBodySourceParent
      coordinate targetParent normalization) sourceParent

/-- Indices of the canonical target full-fiber bodies belonging to one source
actual parent. -/
noncomputable def quotientTargetBodyPacketIndices
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card) :
    Finset (Fin (data.quotientTargetBodies
      coordinate targetParent normalization).card) :=
  Finset.univ.filter fun targetBody =>
    data.quotientTargetBodySourceParent coordinate targetParent
      normalization targetBody = sourceParent

/-- Forget the packet enumeration and recover its canonical target-body
index. -/
noncomputable def quotientTargetBodyPacketEmbedding
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card) :
    Fin (data.quotientTargetBodyPacket coordinate targetParent
      normalization sourceParent).card ↪
      Fin (data.quotientTargetBodies coordinate targetParent normalization).card := by
  change Fin (data.quotientTargetBodyPacketIndices coordinate targetParent
      normalization sourceParent).card ↪
    Fin (data.quotientTargetBodies coordinate targetParent normalization).card
  exact ((data.quotientTargetBodyPacketIndices coordinate targetParent
    normalization sourceParent).orderEmbOfFin rfl).toEmbedding

/-- Source fine index carried by one target body in a fixed packet. -/
noncomputable def quotientTargetBodyPacketSourceIndex
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card) :
    Fin (data.quotientTargetBodyPacket coordinate targetParent
      normalization sourceParent).card → Fin sourceFine.card := fun index =>
  data.finalSourceIndex
    ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
      (data.quotientTargetBodyPacketEmbedding coordinate targetParent
        normalization sourceParent index)).1

/-- The packet source-index map is injective. -/
theorem quotientTargetBodyPacketSourceIndex_injective
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card) :
    Function.Injective (data.quotientTargetBodyPacketSourceIndex
      coordinate targetParent normalization sourceParent) := by
  intro first second heq
  apply (data.quotientTargetBodyPacketEmbedding
    coordinate targetParent normalization sourceParent).injective
  apply (wz2PaperOrdinaryFullFiberIndexEquiv targetParent).injective
  apply Subtype.ext
  exact data.finalSourceIndex.injective heq

/-- Every target body in a packet comes from the stated source actual
parent. -/
theorem quotientTargetBodyPacketSourceIndex_mem
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card)
    (index : Fin (data.quotientTargetBodyPacket coordinate targetParent
      normalization sourceParent).card) :
    data.quotientTargetBodyPacketSourceIndex coordinate targetParent
        normalization sourceParent index ∈
      wz2PaperOrdinaryFullFiberIndices sourceFine
        (representativeSchedule.sourceScale coordinate).coarse sourceParent := by
  apply (representativeSchedule.sourceScale coordinate).cover
    |>.mem_fullFiber_iff_parent_eq
      (representativeSchedule.sourceScale coordinate).rho_pos.le
    sourceParent
    (data.quotientTargetBodyPacketSourceIndex coordinate targetParent
      normalization sourceParent index) |>.mpr
  change data.quotientTargetBodySourceParent coordinate targetParent
      normalization
      (data.quotientTargetBodyPacketEmbedding coordinate targetParent
        normalization sourceParent index) = sourceParent
  exact (Finset.mem_filter.mp
    (Finset.orderEmbOfFin_mem
      (data.quotientTargetBodyPacketIndices coordinate targetParent
        normalization sourceParent) rfl index)).2

/-- If a source-parent packet occurs in a target quotient fiber, then every
final tube with that source parent lies in the same target quotient fiber.
Consequently the global selected source packet injects into the canonical
target body packet. -/
theorem jointlyRegularizedSourcePacket_card_le_quotientTargetBodyPacket
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card)
    (hpacket : 0 < (data.quotientTargetBodyPacket coordinate targetParent
      normalization sourceParent).card) :
    (schedule.jointlyRegularizedSourcePacket
      weight selection data.selected coordinate sourceParent).card ≤
      (data.quotientTargetBodyPacket coordinate targetParent
        normalization sourceParent).card := by
  let finalFine := schedule.jointlyRegularizedFine
    weight selection data.selected
  let targetFiber := wz2PaperOrdinaryFullFiberIndices
    finalFine.family (data.finalCoarse coordinate) targetParent
  let localPacket := data.quotientTargetBodyPacketIndices
    coordinate targetParent normalization sourceParent
  let globalPacket := schedule.jointlyRegularizedSourcePacket
    weight selection data.selected coordinate sourceParent
  have hlocalCard : localPacket.card =
      (data.quotientTargetBodyPacket coordinate targetParent
        normalization sourceParent).card := rfl
  have hlocalPos : 0 < localPacket.card := by simpa [hlocalCard] using hpacket
  let witnessLocal : Fin localPacket.card := ⟨0, hlocalPos⟩
  let witnessBody : Fin targetFiber.card :=
    localPacket.orderEmbOfFin rfl witnessLocal
  let witnessFinal : Fin finalFine.family.card :=
    ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) witnessBody).1
  have hwitnessFiber : witnessFinal ∈ targetFiber :=
    ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) witnessBody).2
  have hwitnessParent :
      (representativeSchedule.sourceScale coordinate).cover.parent
          (data.finalSourceIndex witnessFinal) = sourceParent := by
    have hmem := (Finset.mem_filter.mp
      (Finset.orderEmbOfFin_mem localPacket rfl witnessLocal)).2
    simpa [localPacket, quotientTargetBodyPacketIndices,
      quotientTargetBodySourceParent, witnessBody, witnessFinal] using hmem
  let globalToLocal : Fin globalPacket.card → Fin localPacket.card :=
    fun globalIndex =>
      let finalIndex := globalPacket.orderEmbOfFin rfl globalIndex
      let sourceEq :
          (representativeSchedule.sourceScale coordinate).cover.parent
              (data.finalSourceIndex finalIndex) = sourceParent :=
        (Finset.mem_filter.mp
          (Finset.orderEmbOfFin_mem globalPacket rfl globalIndex)).2
      let finalParentEq :
          (data.finalCover coordinate).parent finalIndex = targetParent := by
        have hsame := data.finalCover_parent_eq_of_sourceParent_eq coordinate
          finalIndex witnessFinal (sourceEq.trans hwitnessParent.symm)
        have hwitnessTarget :
            (data.finalCover coordinate).parent witnessFinal =
              targetParent :=
          ((data.finalCover coordinate).mem_fullFiber_iff_parent_eq
            (schedule.quotient coordinate).caller_rho_pos.le
            targetParent witnessFinal).mp hwitnessFiber
        exact hsame.trans hwitnessTarget
      let targetBody : Fin targetFiber.card :=
        (wz2PaperOrdinaryFullFiberIndexEquiv targetParent).symm
          ⟨finalIndex,
            ((data.finalCover coordinate).mem_fullFiber_iff_parent_eq
              (schedule.quotient coordinate).caller_rho_pos.le
              targetParent finalIndex).mpr finalParentEq⟩
      let targetBodyMem : targetBody ∈ localPacket := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [localPacket, quotientTargetBodyPacketIndices,
          quotientTargetBodySourceParent, targetBody] using sourceEq
      localPacket.orderIsoOfFin rfl |>.symm ⟨targetBody, targetBodyMem⟩
  have hglobalToLocal : Function.Injective globalToLocal := by
    intro first second heq
    let firstFinal := globalPacket.orderEmbOfFin rfl first
    let secondFinal := globalPacket.orderEmbOfFin rfl second
    have hwitnessTarget :
        (data.finalCover coordinate).parent witnessFinal = targetParent :=
      ((data.finalCover coordinate).mem_fullFiber_iff_parent_eq
        (schedule.quotient coordinate).caller_rho_pos.le
        targetParent witnessFinal).mp hwitnessFiber
    have hlocalValues := congrArg
      (fun index : Fin localPacket.card =>
        localPacket.orderEmbOfFin rfl index) heq
    let firstTargetBody : Fin targetFiber.card :=
      (wz2PaperOrdinaryFullFiberIndexEquiv targetParent).symm
        ⟨firstFinal, by
          apply ((data.finalCover coordinate).mem_fullFiber_iff_parent_eq
            (schedule.quotient coordinate).caller_rho_pos.le
            targetParent firstFinal).mpr
          have hfirstSource := (Finset.mem_filter.mp
            (Finset.orderEmbOfFin_mem globalPacket rfl first)).2
          exact (data.finalCover_parent_eq_of_sourceParent_eq coordinate
            firstFinal witnessFinal
            (hfirstSource.trans hwitnessParent.symm)).trans hwitnessTarget⟩
    let secondTargetBody : Fin targetFiber.card :=
      (wz2PaperOrdinaryFullFiberIndexEquiv targetParent).symm
        ⟨secondFinal, by
          apply ((data.finalCover coordinate).mem_fullFiber_iff_parent_eq
            (schedule.quotient coordinate).caller_rho_pos.le
            targetParent secondFinal).mpr
          have hsecondSource := (Finset.mem_filter.mp
            (Finset.orderEmbOfFin_mem globalPacket rfl second)).2
          exact (data.finalCover_parent_eq_of_sourceParent_eq coordinate
            secondFinal witnessFinal
            (hsecondSource.trans hwitnessParent.symm)).trans hwitnessTarget⟩
    have hfirstTargetBodyMem : firstTargetBody ∈ localPacket := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hfirstSource := (Finset.mem_filter.mp
        (Finset.orderEmbOfFin_mem globalPacket rfl first)).2
      unfold quotientTargetBodySourceParent
      rw [show
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            firstTargetBody).1 = firstFinal by
          dsimp only [firstTargetBody]
          simp]
      exact hfirstSource
    have hsecondTargetBodyMem : secondTargetBody ∈ localPacket := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hsecondSource := (Finset.mem_filter.mp
        (Finset.orderEmbOfFin_mem globalPacket rfl second)).2
      unfold quotientTargetBodySourceParent
      rw [show
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            secondTargetBody).1 = secondFinal by
          dsimp only [secondTargetBody]
          simp]
      exact hsecondSource
    have hbodyValues : firstTargetBody = secondTargetBody := by
      have hleft : globalToLocal first =
          (localPacket.orderIsoOfFin rfl).symm
            ⟨firstTargetBody, hfirstTargetBodyMem⟩ := rfl
      have hright : globalToLocal second =
          (localPacket.orderIsoOfFin rfl).symm
            ⟨secondTargetBody, hsecondTargetBodyMem⟩ := rfl
      rw [hleft, hright] at heq
      have hsubtype := congrArg
        (localPacket.orderIsoOfFin rfl) heq
      have hsubtype' :
          (⟨firstTargetBody, hfirstTargetBodyMem⟩ :
            {body // body ∈ localPacket}) =
            ⟨secondTargetBody, hsecondTargetBodyMem⟩ := by
        exact (localPacket.orderIsoOfFin rfl).symm.injective
          (by simpa only [Equiv.symm_apply_apply] using heq)
      exact congrArg (fun body : {body // body ∈ localPacket} => body.1)
        hsubtype'
    have hbodyValues' :
        (⟨firstFinal, _⟩ : {source // source ∈ targetFiber}) =
          ⟨secondFinal, _⟩ :=
      (wz2PaperOrdinaryFullFiberIndexEquiv targetParent).symm.injective
        hbodyValues
    have hfinal : firstFinal = secondFinal := by
      exact congrArg (fun source : {source // source ∈ targetFiber} =>
        source.1) hbodyValues'
    exact (globalPacket.orderEmbOfFin rfl).injective hfinal
  have hcard : Fintype.card (Fin globalPacket.card) ≤
      Fintype.card (Fin localPacket.card) :=
    Fintype.card_le_of_injective globalToLocal hglobalToLocal
  simpa [globalPacket, localPacket, hlocalCard] using hcard

/-- Every local target body in a source-parent packet forgets to a unique
member of the global selected source packet. -/
theorem quotientTargetBodyPacket_card_le_jointlyRegularizedSourcePacket
    {sourceDelta targetDelta : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (coordinate : Fin scaleCount)
    (targetParent : Fin (data.finalCoarse coordinate).card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.finalCoarse coordinate).tube targetParent))
    (sourceParent : Fin
      (representativeSchedule.sourceScale coordinate).coarse.card) :
    (data.quotientTargetBodyPacket coordinate targetParent
      normalization sourceParent).card ≤
      (schedule.jointlyRegularizedSourcePacket
        weight selection data.selected coordinate sourceParent).card := by
  let localPacket := data.quotientTargetBodyPacketIndices
    coordinate targetParent normalization sourceParent
  let globalPacket := schedule.jointlyRegularizedSourcePacket
    weight selection data.selected coordinate sourceParent
  let localToGlobal : Fin localPacket.card → Fin globalPacket.card :=
    fun localIndex =>
      let targetBody := localPacket.orderEmbOfFin rfl localIndex
      let finalIndex :=
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) targetBody).1
      let sourceEq :
          (representativeSchedule.sourceScale coordinate).cover.parent
              (data.finalSourceIndex finalIndex) = sourceParent := by
        exact (Finset.mem_filter.mp
          (Finset.orderEmbOfFin_mem localPacket rfl localIndex)).2
      globalPacket.orderIsoOfFin rfl |>.symm ⟨finalIndex, by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, sourceEq⟩⟩
  have hinjective : Function.Injective localToGlobal := by
    intro first second heq
    apply (localPacket.orderEmbOfFin rfl).injective
    have hglobal := congrArg
      (fun index : Fin globalPacket.card =>
        globalPacket.orderEmbOfFin rfl index) heq
    have hfinal :
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
          (localPacket.orderEmbOfFin rfl first)).1 =
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
          (localPacket.orderEmbOfFin rfl second)).1 := by
      simpa [localToGlobal] using hglobal
    apply (wz2PaperOrdinaryFullFiberIndexEquiv targetParent).injective
    exact Subtype.ext hfinal
  have hcard : Fintype.card (Fin localPacket.card) ≤
      Fintype.card (Fin globalPacket.card) :=
    Fintype.card_le_of_injective localToGlobal hinjective
  change localPacket.card ≤ globalPacket.card
  simpa only [Fintype.card_fin] using hcard

/-- Every nonempty source-parent packet inside a target quotient fiber has
the exact-triangular actual-John CWA bound.  The only input not intrinsic to
the finite schedule is the one global ambient-to-final cardinality retention
estimate. -/
theorem quotientTargetBodyPacket_cwa
    {sourceDelta targetDelta c d m S : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (g : SlopeFunction) (center : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hg : g.IsNormalized)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hS : S = 2 / (d - c))
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : S * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetFamilyTube : ∀ target,
      targetFine.tube target =
        anisotropicPaperTargetTube g c d m center targetDelta hcd hm
          (sourceFine.tube (sourceEquiv target)))
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
      (ENNReal.ofReal (27 * (2 * (32 * S) - 1) ^ 3) *
        ENNReal.ofReal
          |LinearMap.det
            ((pureWZ2AnisotropicJohnCoordinateChange g center hcd hm
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
    have hcardinality :
        normalizationWeight *
            ((wz2PaperOrdinaryFullFiberIndices sourceFine
              (representativeSchedule.sourceScale coordinate).coarse
              sourceParent).card : ENNReal) ≤
          (sourceConstant * retentionConstant *
            (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
              (Nat.log 2
                (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                  ENNReal) ^ (scaleCount + scaleCount))) *
            packet.enncard := by
      have hpacketCardENN :
          ((schedule.jointlyRegularizedSourcePacket
            weight selection data.selected coordinate sourceParent).card :
              ENNReal) ≤ packet.enncard := by
        change _ ≤ (packet.card : ENNReal)
        exact_mod_cast hpacketCard
      exact hsourceRatio.trans (mul_le_mul_left' hpacketCardENN _)
    have htargetMemParent : ∀ index : Fin packet.card,
        (anisotropicPaperTargetTube g c d m center targetDelta hcd hm
          (sourceFine.tube (sourceIndex index))).carrier ⊆
            ((data.finalCoarse coordinate).tube targetParent).carrier := by
      intro index
      have htargetFiber :=
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
          (data.quotientTargetBodyPacketEmbedding coordinate targetParent
            normalization sourceParent index)).2
      have hcontain :=
        (mem_wz2PaperOrdinaryFullFiberIndices_iff
          targetParent
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            (data.quotientTargetBodyPacketEmbedding coordinate targetParent
              normalization sourceParent index)).1).mp htargetFiber
      have hfinalTube :
          (schedule.jointlyRegularizedFine
            weight selection data.selected).family.tube
              ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
                (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                  normalization sourceParent index)).1 =
            targetFine.tube
              (data.finalTargetIndex
                ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
                  (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                    normalization sourceParent index)).1) := rfl
      rw [hfinalTube] at hcontain
      change (anisotropicPaperTargetTube g c d m center targetDelta hcd hm
          (sourceFine.tube (sourceIndex index))).carrier ⊆ _
      have htargetIdentity :
          targetFine.tube
              (data.finalTargetIndex
                ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
                  (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                    normalization sourceParent index)).1) =
            anisotropicPaperTargetTube g c d m center targetDelta hcd hm
              (sourceFine.tube (sourceIndex index)) := by
        rw [htargetFamilyTube]
        congr 2
      rw [htargetIdentity] at hcontain
      exact hcontain
    have htargetBody : ∀ index : Fin packet.card,
        (packet.body index).carrier = normalization.map ''
          (anisotropicPaperTargetTube g c d m center targetDelta hcd hm
            (sourceFine.tube (sourceIndex index))).carrier := by
      intro index
      change normalization.map ''
          ((schedule.jointlyRegularizedFine
            weight selection data.selected).family.tube
              ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
                (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                  normalization sourceParent index)).1).carrier = _
      have htargetIdentity :
          (schedule.jointlyRegularizedFine
            weight selection data.selected).family.tube
              ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
                (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                  normalization sourceParent index)).1 =
            anisotropicPaperTargetTube g c d m center targetDelta hcd hm
              (sourceFine.tube (sourceIndex index)) := by
        rw [show (schedule.jointlyRegularizedFine
            weight selection data.selected).family.tube
              ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
                (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                  normalization sourceParent index)).1 =
          targetFine.tube
            (data.finalTargetIndex
              ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
                (data.quotientTargetBodyPacketEmbedding coordinate targetParent
                  normalization sourceParent index)).1) by rfl]
        rw [htargetFamilyTube]
        congr 2
      rw [htargetIdentity]
    have hraw := pureWZ2_anisotropicPaperTargetPacket_cwa
      sourceParent sourceFiber g center hcd hdc hm hmOne hg hsub hS
      hsourceDelta htargetDelta hsourceLine hsourceBase packet sourceIndex
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
      have hnat : (packet.containedIndices convexSet).card = 0 := by
        omega
      exact_mod_cast hnat
    have henncardZero : packet.enncard = 0 := by
      change (packet.card : ENNReal) = 0
      rw [hcardZero]
      norm_num
    rw [hcontainedZero, henncardZero]
    simp

/-- Uniformize the determinant-dependent packet bound at one public quotient
scale. -/
theorem quotientTargetBodyPacket_cwa_uniform
    {sourceDelta targetDelta c d m S : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (g : SlopeFunction) (center : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hg : g.IsNormalized)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hS : S = 2 / (d - c))
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : S * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetFamilyTube : ∀ target,
      targetFine.tube target =
        anisotropicPaperTargetTube g c d m center targetDelta hcd hm
          (sourceFine.tube (sourceEquiv target)))
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
      (ENNReal.ofReal (27 * (2 * (32 * S) - 1) ^ 3) *
        ((432 : ENNReal) *
          Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
          ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
          ENNReal.ofReal
            (1 / (m * representativeSchedule.sourceRho coordinate ^ 2))) *
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
  have hraw := data.quotientTargetBodyPacket_cwa g center hcd hdc hm hmOne
    hg hsub hS hsourceDelta htargetDelta hsourceLine hsourceBase
    htargetFamilyTube normalizationWeight retentionConstant hweightZero
    hweightTop hglobal coordinate targetParent normalization sourceParent
  intro convexSet hconvex
  exact (hraw convexSet hconvex).trans <| by
    gcongr
    exact pureWZ2AnisotropicJohnCoordinateChange_inverse_det_le_general
      (representativeSchedule.sourceScale coordinate).rho_pos
      (schedule.quotient coordinate).caller_rho_pos
      g center hcd hm
      ((representativeSchedule.sourceScale coordinate).coarse.tube sourceParent)
      ((data.finalCoarse coordinate).tube targetParent)
      sourceFiber.normalization normalization

/-- One complete target quotient fiber has the uniform packetwise CWA bound.
No factor for the number of merged source parents is introduced. -/
theorem quotientTargetFullFiber_cwa
    {sourceDelta targetDelta c d m S : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant : ENNReal} {scaleCount : ℕ}
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
    (g : SlopeFunction) (center : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hg : g.IsNormalized)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hS : S = 2 / (d - c))
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : S * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetFamilyTube : ∀ target,
      targetFine.tube target =
        anisotropicPaperTargetTube g c d m center targetDelta hcd hm
          (sourceFine.tube (sourceEquiv target)))
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
      (ENNReal.ofReal (27 * (2 * (32 * S) - 1) ^ 3) *
        ((432 : ENNReal) *
          Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
          ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
          ENNReal.ofReal
            (1 / (m * representativeSchedule.sourceRho coordinate ^ 2))) *
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
    rcases (representativeSchedule.sourceScale coordinate).cover.covers source with
      ⟨sourceParent, _hsourceParent⟩
    exact lt_of_le_of_lt (Nat.zero_le sourceParent.val) sourceParent.isLt
  · intro sourceParent
    exact data.quotientTargetBodyPacket_cwa_uniform g center hcd hdc hm hmOne
      hg hsub hS hsourceDelta htargetDelta hsourceLine hsourceBase
      htargetFamilyTube normalizationWeight retentionConstant hweightZero
      hweightTop hglobal coordinate targetParent normalization
      sourceParent

/-- Package one coordinate of the jointly regularized exact-triangular
quotient schedule as the public one-scale Definition 2.12 adapter.  All
geometric work is supplied by the quotient schedule; the only remaining
input is the numerical absorption of its two explicit constants into the
caller's target constant. -/
noncomputable def toOneScaleCWAAdapterData
    {sourceDelta targetDelta c d m S : ℝ}
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
    (g : SlopeFunction) (center : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hg : g.IsNormalized)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hS : S = 2 / (d - c))
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : S * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetFamilyTube : ∀ target,
      targetFine.tube target =
        anisotropicPaperTargetTube g c d m center targetDelta hcd hm
          (sourceFine.tube (sourceEquiv target)))
    (normalizationWeight retentionConstant : ENNReal)
    (hweightZero : normalizationWeight ≠ 0)
    (hweightTop : normalizationWeight ≠ ⊤)
    (hglobal : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (schedule.jointlyRegularizedFine
          weight selection data.selected).family.enncard)
    (coordinate : Fin scaleCount)
    (constant_budget :
      max
          (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
            (Nat.log 2
              (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                ENNReal) ^ (scaleCount + scaleCount))
          (ENNReal.ofReal (27 * (2 * (32 * S) - 1) ^ 3) *
            ((432 : ENNReal) *
              Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
              ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
              ENNReal.ofReal
                (1 / (m * representativeSchedule.sourceRho coordinate ^ 2))) *
            ((normalizationWeight⁻¹ *
              (sourceConstant * retentionConstant *
                (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
                  (Nat.log 2
                    (2 *
                        (schedule.separatedFine weight selection).family.card) +
                      1 : ENNReal) ^ (scaleCount + scaleCount)))) *
              sourceConstant)) ≤
        targetConstant) :
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
        ENNReal.ofReal (27 * (2 * (32 * S) - 1) ^ 3) *
          ((432 : ENNReal) *
            Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
            ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
            ENNReal.ofReal
              (1 / (m * representativeSchedule.sourceRho coordinate ^ 2))) *
          ((normalizationWeight⁻¹ *
            (sourceConstant * retentionConstant *
              (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
                (Nat.log 2
                  (2 * (schedule.separatedFine weight selection).family.card) +
                    1 : ENNReal) ^ (scaleCount + scaleCount)))) *
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
    exact data.quotientTargetBodyPacket_cwa_uniform g center hcd hdc hm hmOne
      hg hsub hS hsourceDelta htargetDelta hsourceLine hsourceBase
      htargetFamilyTube normalizationWeight retentionConstant hweightZero
      hweightTop hglobal coordinate targetParent
      (WZ2PaperAssouadUnitRescalingData.ofTube
        ((data.finalCoarse coordinate).tube targetParent)
        (schedule.quotient coordinate).caller_rho_pos) sourceParent
  source_parent_count_pos := by
    let source : Fin sourceFine.card :=
      ⟨0, (representativeSchedule.parentData coordinate).source_nonempty⟩
    rcases (representativeSchedule.sourceScale coordinate).cover.covers source with
      ⟨sourceParent, _⟩
    exact lt_of_le_of_lt (Nat.zero_le sourceParent.val) sourceParent.isLt
  constant_budget := constant_budget

/-- The public one-scale Definition 2.12 datum produced by one coordinate of
the exact-triangular quotient schedule. -/
noncomputable def toScaleCoverData
    {sourceDelta targetDelta c d m S : ℝ}
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
    (g : SlopeFunction) (center : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hg : g.IsNormalized)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hS : S = 2 / (d - c))
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : S * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetFamilyTube : ∀ target,
      targetFine.tube target =
        anisotropicPaperTargetTube g c d m center targetDelta hcd hm
          (sourceFine.tube (sourceEquiv target)))
    (normalizationWeight retentionConstant : ENNReal)
    (hweightZero : normalizationWeight ≠ 0)
    (hweightTop : normalizationWeight ≠ ⊤)
    (hglobal : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (schedule.jointlyRegularizedFine
          weight selection data.selected).family.enncard)
    (coordinate : Fin scaleCount)
    (constant_budget :
      max
          (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
            (Nat.log 2
              (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                ENNReal) ^ (scaleCount + scaleCount))
          (ENNReal.ofReal (27 * (2 * (32 * S) - 1) ^ 3) *
            ((432 : ENNReal) *
              Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
              ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
              ENNReal.ofReal
                (1 / (m * representativeSchedule.sourceRho coordinate ^ 2))) *
            ((normalizationWeight⁻¹ *
              (sourceConstant * retentionConstant *
                (16 * ((scaleCount + scaleCount : ℕ) : ENNReal) *
                  (Nat.log 2
                    (2 *
                        (schedule.separatedFine weight selection).family.card) +
                      1 : ENNReal) ^ (scaleCount + scaleCount)))) *
              sourceConstant)) ≤
        targetConstant) :
    WZ2PaperPureScaleCoverData
      (schedule.jointlyRegularizedFine
        weight selection data.selected).family
      (schedule.callerRho coordinate) targetConstant :=
  (data.toOneScaleCWAAdapterData g center hcd hdc hm hmOne hg hsub hS
    hsourceDelta htargetDelta hsourceLine hsourceBase htargetFamilyTube
    normalizationWeight retentionConstant hweightZero hweightTop hglobal
    coordinate constant_budget).toScaleCoverData

/-- The fixed multiplicative scale-window loss of the quotient-parent
construction. -/
def anisotropicQuotientScaleWindowConstant
    (sourceScheduleConstant : ENNReal) : ENNReal :=
  6000000 * sourceScheduleConstant + 2

/-- Lift the finitely many exact-triangular quotient witnesses to the public
nearby-scale CWA statement.  Every target requested scale is also a legal
source request; the source finite schedule chooses its representative, and
the quotient caller radius pays the fixed `6000000` geometric enlargement. -/
theorem toNearbyCWA
    {sourceDelta targetDelta c d m S : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {targetFine : Kakeya.Streamlined.TubeFamily targetDelta}
    {sourceEquiv : Fin targetFine.card ≃ Fin sourceFine.card}
    {sourceConstant sourceScheduleConstant targetConstant : ENNReal}
    {levelCount : ℕ}
    (sourceSchedule : PureWZ2FiniteNearbyScheduleData
      (family := sourceFine) sourceConstant sourceScheduleConstant levelCount)
    {representativeSchedule :
      PureWZ2FiniteRepresentativeParentScheduleData
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
    (g : SlopeFunction) (center : Point3)
    (hcd : c < d) (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hg : g.IsNormalized)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hS : S = 2 / (d - c))
    (hsourceDelta : 0 < sourceDelta)
    (hsourceTarget : sourceDelta ≤ targetDelta)
    (htargetDelta : S * sourceDelta ≤ targetDelta)
    (hsourceLine : WZ1PaperIsLineClass sourceFine)
    (hsourceBase : ∀ source, ‖(sourceFine.tube source).base‖ ≤ 5)
    (htargetFamilyTube : ∀ target,
      targetFine.tube target =
        anisotropicPaperTargetTube g c d m center targetDelta hcd hm
          (sourceFine.tube (sourceEquiv target)))
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
    (hcallerRho : ∀ coordinate,
      schedule.callerRho coordinate =
        anisotropicQuotientCallerScale targetDelta
          (representativeSchedule.sourceRho coordinate))
    (hscaleBudget :
      anisotropicQuotientScaleWindowConstant sourceScheduleConstant ≤
        targetConstant)
    (hconstantBudget : ∀ coordinate,
      max
          (16 *
            ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
              ENNReal) *
            (Nat.log 2
              (2 * (schedule.separatedFine weight selection).family.card) + 1 :
                ENNReal) ^
              (sourceSchedule.scaleCount + sourceSchedule.scaleCount))
          (ENNReal.ofReal (27 * (2 * (32 * S) - 1) ^ 3) *
            ((432 : ENNReal) *
              Kakeya.realRpowENN (schedule.callerRho coordinate) 2 *
              ENNReal.ofReal (1 + 2 * schedule.callerRho coordinate) *
              ENNReal.ofReal
                (1 / (m * representativeSchedule.sourceRho coordinate ^ 2))) *
            ((normalizationWeight⁻¹ *
              (sourceConstant * retentionConstant *
                (16 *
                  ((sourceSchedule.scaleCount +
                      sourceSchedule.scaleCount : ℕ) : ENNReal) *
                  (Nat.log 2
                    (2 *
                        (schedule.separatedFine weight selection).family.card) +
                      1 : ENNReal) ^
                    (sourceSchedule.scaleCount +
                      sourceSchedule.scaleCount)))) *
              sourceConstant)) ≤
        targetConstant) :
    WZ2PaperPureCWAAtNearbyScales
      (schedule.jointlyRegularizedFine
        weight selection data.selected).family targetConstant := by
  let separated := schedule.separatedFine weight selection
  let finalFine := schedule.jointlyRegularizedFine
    weight selection data.selected
  have hfinalDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct finalFine.family :=
    (htargetDistinct.subfamily separated).subfamily finalFine
  refine ⟨(representativeSchedule.parentData
      ⟨0, sourceSchedule.scaleCount_pos⟩).target_delta_pos,
    htargetFinite, hfinalDistinct, ?_⟩
  intro targetRequest
  let sourceRequest : WZ2PaperRequestedScale sourceDelta :=
    ⟨targetRequest.1, hsourceTarget.trans targetRequest.2.1,
      targetRequest.2.2⟩
  let coordinate := sourceSchedule.representative sourceRequest
  have hrequestedSource :
      targetRequest.1 ≤ representativeSchedule.sourceRho coordinate := by
    rw [hsourceRho coordinate]
    exact sourceSchedule.requested_le sourceRequest
  have hrequestedCaller :
      targetRequest.1 ≤ schedule.callerRho coordinate := by
    rw [hcallerRho coordinate]
    unfold anisotropicQuotientCallerScale
    have htargetPos : 0 < targetDelta :=
      (representativeSchedule.parentData coordinate).target_delta_pos
    nlinarith [hrequestedSource,
      (representativeSchedule.sourceScale coordinate).rho_pos]
  have hsourceWithin :
      ENNReal.ofReal (representativeSchedule.sourceRho coordinate) <
        sourceScheduleConstant * ENNReal.ofReal targetRequest.1 := by
    rw [hsourceRho coordinate]
    simpa [sourceRequest, coordinate] using
      sourceSchedule.within_output sourceRequest
  have hcallerWithin :
      ENNReal.ofReal (schedule.callerRho coordinate) <
        targetConstant * ENNReal.ofReal targetRequest.1 := by
    have htargetPos : 0 < targetDelta :=
      (representativeSchedule.parentData coordinate).target_delta_pos
    have hrequestPos : 0 < targetRequest.1 :=
      htargetPos.trans_le targetRequest.2.1
    have hsourcePos : 0 < representativeSchedule.sourceRho coordinate :=
      (representativeSchedule.sourceScale coordinate).rho_pos
    have hmul :
        (6000000 : ENNReal) *
            ENNReal.ofReal (representativeSchedule.sourceRho coordinate) <
          (6000000 : ENNReal) *
            (sourceScheduleConstant * ENNReal.ofReal targetRequest.1) := by
      have h := (ENNReal.mul_lt_mul_iff_left
        (c := (6000000 : ENNReal)) (by norm_num) (by norm_num)).2
          hsourceWithin
      simpa [mul_comm] using h
    have htargetENN :
        ENNReal.ofReal targetDelta ≤ ENNReal.ofReal targetRequest.1 :=
      ENNReal.ofReal_mono targetRequest.2.1
    have hadd :
        (6000000 : ENNReal) *
              ENNReal.ofReal (representativeSchedule.sourceRho coordinate) +
            2 * ENNReal.ofReal targetDelta <
          (6000000 : ENNReal) *
              (sourceScheduleConstant * ENNReal.ofReal targetRequest.1) +
            2 * ENNReal.ofReal targetRequest.1 :=
      ENNReal.add_lt_add_of_lt_of_le
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        hmul (mul_le_mul_left' htargetENN 2)
    calc
      ENNReal.ofReal (schedule.callerRho coordinate) =
          (6000000 : ENNReal) *
              ENNReal.ofReal (representativeSchedule.sourceRho coordinate) +
            2 * ENNReal.ofReal targetDelta := by
        rw [hcallerRho coordinate]
        unfold anisotropicQuotientCallerScale
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_mul (by norm_num)]
        norm_num
      _ <
          (6000000 : ENNReal) *
              (sourceScheduleConstant * ENNReal.ofReal targetRequest.1) +
            2 * ENNReal.ofReal targetRequest.1 := hadd
      _ = anisotropicQuotientScaleWindowConstant sourceScheduleConstant *
          ENNReal.ofReal targetRequest.1 := by
        unfold anisotropicQuotientScaleWindowConstant
        ring
      _ ≤ targetConstant * ENNReal.ofReal targetRequest.1 := by
        gcongr
  exact ⟨{
    rho := schedule.callerRho coordinate
    requested_le := hrequestedCaller
    within_factor := hcallerWithin
    scaleData := data.toScaleCoverData g center hcd hdc hm hmOne hg hsub hS
      hsourceDelta htargetDelta hsourceLine hsourceBase htargetFamilyTube
      normalizationWeight retentionConstant hweightZero hweightTop hglobal
      coordinate (hconstantBudget coordinate)
  }⟩

end PureWZ2AnisotropicJointRegularizationData
end PureWZ2FiniteAnisotropicParentQuotientScheduleData

end Kakeya.Assouad

end
