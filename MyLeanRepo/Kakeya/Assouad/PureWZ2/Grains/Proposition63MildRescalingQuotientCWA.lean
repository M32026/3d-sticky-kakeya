import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingQuotientSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingScheduleAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWAFiberwiseAssembly

/-!
# Packetwise actual-John CWA for the Proposition 6.3 quotient schedule

One final quotient fiber can merge several complete source actual fibers.
This module keeps that ancestry explicit by partitioning its canonical target
John-body family by the original source-parent label.  CWA can then be proved
packetwise and summed without paying for the number of source packets.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

namespace Proposition63MildRescalingQuotientScheduleData

/-- Canonical target John bodies over one final quotient parent. -/
noncomputable def quotientTargetBodies
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent)) : Kakeya.Streamlined.BodyFamily :=
  wz2PaperPureUnitRescaledFullFiberBodyFamily
    (fine := (data.jointRegularizedTarget regularized).family)
    (coarse := (data.jointRegularizedParents regularized coordinate).family)
    targetParent normalization

/-- Source actual parent attached to one target John body. -/
noncomputable def quotientTargetBodySourceParent
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent)) :
    Fin (data.quotientTargetBodies regularized coordinate targetParent
      normalization).card →
      Fin (sourceSchedule.witness coordinate).scaleData.coarse.card :=
  fun targetBody =>
    (sourceSchedule.witness coordinate).scaleData.cover.parent
      (data.jointRegularizedSourceIndex regularized
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) targetBody).1)

/-- One original source-parent packet inside a final quotient fiber. -/
noncomputable def quotientTargetBodyPacket
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent))
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    Kakeya.Streamlined.BodyFamily :=
  wz2PaperBodyParentFiber
    (data.quotientTargetBodies regularized coordinate targetParent
      normalization)
    (data.quotientTargetBodySourceParent regularized coordinate targetParent
      normalization) sourceParent

/-- Canonical target-body indices making up one source-parent packet. -/
noncomputable def quotientTargetBodyPacketIndices
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent))
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    Finset (Fin (data.quotientTargetBodies regularized coordinate targetParent
      normalization).card) :=
  Finset.univ.filter fun targetBody =>
    data.quotientTargetBodySourceParent regularized coordinate targetParent
      normalization targetBody = sourceParent

/-- Forget the packet enumeration and recover its canonical target-body
index. -/
noncomputable def quotientTargetBodyPacketEmbedding
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent))
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    Fin (data.quotientTargetBodyPacket regularized coordinate targetParent
      normalization sourceParent).card ↪
      Fin (data.quotientTargetBodies regularized coordinate targetParent
        normalization).card := by
  change Fin (data.quotientTargetBodyPacketIndices regularized coordinate
      targetParent normalization sourceParent).card ↪
    Fin (data.quotientTargetBodies regularized coordinate targetParent
      normalization).card
  exact ((data.quotientTargetBodyPacketIndices regularized coordinate
    targetParent normalization sourceParent).orderEmbOfFin rfl).toEmbedding

/-- Exact source fine index carried by a target body in one packet. -/
noncomputable def quotientTargetBodyPacketSourceIndex
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent))
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    Fin (data.quotientTargetBodyPacket regularized coordinate targetParent
      normalization sourceParent).card → Fin sourceFine.card := fun index =>
  data.jointRegularizedSourceIndex regularized
    ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
      (data.quotientTargetBodyPacketEmbedding regularized coordinate
        targetParent normalization sourceParent index)).1

theorem quotientTargetBodyPacketSourceIndex_injective
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent))
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    Function.Injective
      (data.quotientTargetBodyPacketSourceIndex regularized coordinate
        targetParent normalization sourceParent) := by
  intro first second heq
  apply (data.quotientTargetBodyPacketEmbedding regularized coordinate
    targetParent normalization sourceParent).injective
  apply (wz2PaperOrdinaryFullFiberIndexEquiv targetParent).injective
  apply Subtype.ext
  exact data.jointRegularizedSourceIndex regularized |>.injective heq

theorem quotientTargetBodyPacketSourceIndex_mem
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent))
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card)
    (index : Fin (data.quotientTargetBodyPacket regularized coordinate
      targetParent normalization sourceParent).card) :
    data.quotientTargetBodyPacketSourceIndex regularized coordinate
        targetParent normalization sourceParent index ∈
      wz2PaperOrdinaryFullFiberIndices sourceFine
        (sourceSchedule.witness coordinate).scaleData.coarse sourceParent := by
  apply (sourceSchedule.witness coordinate).scaleData.cover
    |>.mem_fullFiber_iff_parent_eq
      (sourceSchedule.witness coordinate).scaleData.rho_pos.le
    sourceParent _ |>.mpr
  change data.quotientTargetBodySourceParent regularized coordinate
      targetParent normalization
      (data.quotientTargetBodyPacketEmbedding regularized coordinate
        targetParent normalization sourceParent index) = sourceParent
  exact (Finset.mem_filter.mp
    (Finset.orderEmbOfFin_mem
      (data.quotientTargetBodyPacketIndices regularized coordinate
        targetParent normalization sourceParent) rfl index)).2

/-- A source packet occurring in one target quotient fiber is nonempty in
the global jointly regularized source-parent partition. -/
theorem jointRegularizedSourcePacket_nonempty_of_targetPacket
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent))
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card)
    (hpacket : 0 < (data.quotientTargetBodyPacket regularized coordinate
      targetParent normalization sourceParent).card) :
    (data.jointRegularizedSourcePacket regularized coordinate
      sourceParent).Nonempty := by
  let packet := data.quotientTargetBodyPacketIndices regularized coordinate
    targetParent normalization sourceParent
  have packetPos : 0 < packet.card := hpacket
  let packetIndex : Fin packet.card := ⟨0, packetPos⟩
  let targetBody := packet.orderEmbOfFin rfl packetIndex
  let targetIndex :=
    ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) targetBody).1
  have sourceParentEq :
      (sourceSchedule.witness coordinate).scaleData.cover.parent
          (data.jointRegularizedSourceIndex regularized targetIndex) =
        sourceParent := by
    exact (Finset.mem_filter.mp
      (Finset.orderEmbOfFin_mem packet rfl packetIndex)).2
  exact ⟨targetIndex, Finset.mem_filter.mpr
    ⟨Finset.mem_univ targetIndex, sourceParentEq⟩⟩

/-- The global jointly regularized source packet injects into any nonempty
target quotient-fiber packet carrying the same source-parent label. -/
theorem jointRegularizedSourcePacket_card_le_quotientTargetBodyPacket
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent))
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card)
    (hpacket : 0 < (data.quotientTargetBodyPacket regularized coordinate
      targetParent normalization sourceParent).card) :
    (data.jointRegularizedSourcePacket regularized coordinate
      sourceParent).card ≤
      (data.quotientTargetBodyPacket regularized coordinate targetParent
        normalization sourceParent).card := by
  let targetFiber := wz2PaperOrdinaryFullFiberIndices
    (data.jointRegularizedTarget regularized).family
    (data.jointRegularizedParents regularized coordinate).family targetParent
  let localPacket := data.quotientTargetBodyPacketIndices regularized
    coordinate targetParent normalization sourceParent
  let globalPacket := data.jointRegularizedSourcePacket regularized
    coordinate sourceParent
  have localPos : 0 < localPacket.card := hpacket
  let witnessLocal : Fin localPacket.card := ⟨0, localPos⟩
  let witnessBody : Fin targetFiber.card :=
    localPacket.orderEmbOfFin rfl witnessLocal
  let witnessFinal : Fin (data.jointRegularizedTarget regularized).family.card :=
    ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) witnessBody).1
  have witnessFiber : witnessFinal ∈ targetFiber :=
    ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) witnessBody).2
  have witnessSourceParent :
      (sourceSchedule.witness coordinate).scaleData.cover.parent
          (data.jointRegularizedSourceIndex regularized witnessFinal) =
        sourceParent := by
    exact (Finset.mem_filter.mp
      (Finset.orderEmbOfFin_mem localPacket rfl witnessLocal)).2
  let globalToLocal : Fin globalPacket.card → Fin localPacket.card :=
    fun globalIndex =>
      let finalIndex := globalPacket.orderEmbOfFin rfl globalIndex
      let sourceEq :
          (sourceSchedule.witness coordinate).scaleData.cover.parent
              (data.jointRegularizedSourceIndex regularized finalIndex) =
            sourceParent :=
        (Finset.mem_filter.mp
          (Finset.orderEmbOfFin_mem globalPacket rfl globalIndex)).2
      let finalParentEq :
          (data.jointRegularizedCover regularized coordinate).parent
              finalIndex = targetParent := by
        have hsame := data.jointRegularizedCover_parent_eq_of_sourceParent_eq
          regularized coordinate finalIndex witnessFinal
          (sourceEq.trans witnessSourceParent.symm)
        have hwitness :
            (data.jointRegularizedCover regularized coordinate).parent
                witnessFinal = targetParent :=
          ((data.jointRegularizedCover regularized coordinate)
            |>.mem_fullFiber_iff_parent_eq
              (data.quotient coordinate).caller_rho_pos.le
              targetParent witnessFinal).mp witnessFiber
        exact hsame.trans hwitness
      let targetBody : Fin targetFiber.card :=
        (wz2PaperOrdinaryFullFiberIndexEquiv targetParent).symm
          ⟨finalIndex,
            ((data.jointRegularizedCover regularized coordinate)
              |>.mem_fullFiber_iff_parent_eq
                (data.quotient coordinate).caller_rho_pos.le
                targetParent finalIndex).mpr finalParentEq⟩
      let targetBodyMem : targetBody ∈ localPacket := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        simpa [localPacket, quotientTargetBodyPacketIndices,
          quotientTargetBodySourceParent, targetBody] using sourceEq
      localPacket.orderIsoOfFin rfl |>.symm ⟨targetBody, targetBodyMem⟩
  have globalToLocal_injective : Function.Injective globalToLocal := by
    intro first second heq
    let firstFinal := globalPacket.orderEmbOfFin rfl first
    let secondFinal := globalPacket.orderEmbOfFin rfl second
    have witnessTarget :
        (data.jointRegularizedCover regularized coordinate).parent
            witnessFinal = targetParent :=
      ((data.jointRegularizedCover regularized coordinate)
        |>.mem_fullFiber_iff_parent_eq
          (data.quotient coordinate).caller_rho_pos.le
          targetParent witnessFinal).mp witnessFiber
    let firstTargetBody : Fin targetFiber.card :=
      (wz2PaperOrdinaryFullFiberIndexEquiv targetParent).symm
        ⟨firstFinal, by
          apply ((data.jointRegularizedCover regularized coordinate)
            |>.mem_fullFiber_iff_parent_eq
              (data.quotient coordinate).caller_rho_pos.le
              targetParent firstFinal).mpr
          have firstSource := (Finset.mem_filter.mp
            (Finset.orderEmbOfFin_mem globalPacket rfl first)).2
          exact (data.jointRegularizedCover_parent_eq_of_sourceParent_eq
            regularized coordinate firstFinal witnessFinal
            (firstSource.trans witnessSourceParent.symm)).trans witnessTarget⟩
    let secondTargetBody : Fin targetFiber.card :=
      (wz2PaperOrdinaryFullFiberIndexEquiv targetParent).symm
        ⟨secondFinal, by
          apply ((data.jointRegularizedCover regularized coordinate)
            |>.mem_fullFiber_iff_parent_eq
              (data.quotient coordinate).caller_rho_pos.le
              targetParent secondFinal).mpr
          have secondSource := (Finset.mem_filter.mp
            (Finset.orderEmbOfFin_mem globalPacket rfl second)).2
          exact (data.jointRegularizedCover_parent_eq_of_sourceParent_eq
            regularized coordinate secondFinal witnessFinal
            (secondSource.trans witnessSourceParent.symm)).trans witnessTarget⟩
    have firstTargetBodyMem : firstTargetBody ∈ localPacket := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have firstSource := (Finset.mem_filter.mp
        (Finset.orderEmbOfFin_mem globalPacket rfl first)).2
      unfold quotientTargetBodySourceParent
      rw [show
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            firstTargetBody).1 = firstFinal by
          dsimp only [firstTargetBody]
          simp]
      exact firstSource
    have secondTargetBodyMem : secondTargetBody ∈ localPacket := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have secondSource := (Finset.mem_filter.mp
        (Finset.orderEmbOfFin_mem globalPacket rfl second)).2
      unfold quotientTargetBodySourceParent
      rw [show
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
            secondTargetBody).1 = secondFinal by
          dsimp only [secondTargetBody]
          simp]
      exact secondSource
    have targetBodyEq : firstTargetBody = secondTargetBody := by
      have leftValue : globalToLocal first =
          (localPacket.orderIsoOfFin rfl).symm
            ⟨firstTargetBody, firstTargetBodyMem⟩ := rfl
      have rightValue : globalToLocal second =
          (localPacket.orderIsoOfFin rfl).symm
            ⟨secondTargetBody, secondTargetBodyMem⟩ := rfl
      rw [leftValue, rightValue] at heq
      have subtypeEq :
          (⟨firstTargetBody, firstTargetBodyMem⟩ :
            {body // body ∈ localPacket}) =
            ⟨secondTargetBody, secondTargetBodyMem⟩ := by
        exact (localPacket.orderIsoOfFin rfl).symm.injective
          (by simpa only [Equiv.symm_apply_apply] using heq)
      exact congrArg (fun body : {body // body ∈ localPacket} => body.1)
        subtypeEq
    have finalSubtypeEq :
        (⟨firstFinal, _⟩ : {source // source ∈ targetFiber}) =
          ⟨secondFinal, _⟩ :=
      (wz2PaperOrdinaryFullFiberIndexEquiv targetParent).symm.injective
        targetBodyEq
    have hfinal : firstFinal = secondFinal := by
      exact congrArg (fun source : {source // source ∈ targetFiber} =>
        source.1) finalSubtypeEq
    exact (globalPacket.orderEmbOfFin rfl).injective hfinal
  have localCard : localPacket.card =
      (data.quotientTargetBodyPacket regularized coordinate targetParent
        normalization sourceParent).card := rfl
  have cardBound : Fintype.card (Fin globalPacket.card) ≤
      Fintype.card (Fin localPacket.card) :=
    Fintype.card_le_of_injective globalToLocal globalToLocal_injective
  simpa [globalPacket, localPacket, localCard] using cardBound

/-- Exact packetwise actual-John loss before finite uniformization. -/
noncomputable def quotientPacketConstant
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (normalizationWeight retentionConstant : ENNReal)
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent))
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) : ENNReal :=
  ENNReal.ofReal (27 * (2 * (22 * scale + 3) - 1) ^ 3) *
    ENNReal.ofReal
      |LinearMap.det
        ((proposition63MildRescalingJohnCoordinateChange sourceParent
          (Classical.choice
            ((sourceSchedule.witness coordinate).scaleData.rescaledFiber
              sourceParent)).normalization targetParent normalization center
          (lt_of_lt_of_le zero_lt_one hscale)).symm.linear :
            Point3 →ₗ[ℝ] Point3)| *
    ((normalizationWeight⁻¹ *
      (sourceConstant * retentionConstant *
        (16 *
          ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
            ENNReal) *
          (Nat.log 2
            (2 * (data.selectedTarget selection).family.card) + 1 : ENNReal) ^
            (sourceSchedule.scaleCount + sourceSchedule.scaleCount)))) *
      sourceConstant)

/-- Transfer the actual-John CWA of one complete source fiber to the packet
of target bodies carrying that source-parent label.  The global retention
receipt and the two joint uniformities are charged explicitly in the
cardinality factor. -/
theorem quotientTargetBodyPacket_cwa
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (normalizationWeight retentionConstant : ENNReal)
    (weight_ne_zero : normalizationWeight ≠ 0)
    (weight_ne_top : normalizationWeight ≠ ⊤)
    (globalRetention : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (data.jointRegularizedTarget regularized).family.enncard)
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent))
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    WZ2PaperBodyConvexWolffBound
      (data.quotientTargetBodyPacket regularized coordinate targetParent
        normalization sourceParent)
      (data.quotientPacketConstant regularized normalizationWeight
        retentionConstant coordinate targetParent normalization
        sourceParent) := by
  let packet := data.quotientTargetBodyPacket regularized coordinate
    targetParent normalization sourceParent
  by_cases packetPositive : 0 < packet.card
  · let sourceScale := (sourceSchedule.witness coordinate).scaleData
    let sourceFiber := Classical.choice (sourceScale.rescaledFiber sourceParent)
    let sourceIndex := data.quotientTargetBodyPacketSourceIndex regularized
      coordinate targetParent normalization sourceParent
    let sourceFullEquiv := wz2PaperOrdinaryFullFiberIndexEquiv
      (fine := sourceFine) (coarse := sourceScale.coarse) sourceParent
    let sourceBodyIndex : Fin packet.card →
        Fin (wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
          sourceParent).card := fun index =>
      sourceFullEquiv.symm
        ⟨sourceIndex index,
          data.quotientTargetBodyPacketSourceIndex_mem regularized coordinate
            targetParent normalization sourceParent index⟩
    have sourceBodyIndex_injective : Function.Injective sourceBodyIndex := by
      intro first second heq
      apply data.quotientTargetBodyPacketSourceIndex_injective regularized
        coordinate targetParent normalization sourceParent
      have sourceEq := congrArg sourceFullEquiv heq
      simpa [sourceBodyIndex, sourceFullEquiv] using
        congrArg Subtype.val sourceEq
    have sourceBodyIndexFiber : ∀ sourceBody,
        ((Finset.univ : Finset (Fin packet.card)).filter
          (fun targetBody => sourceBodyIndex targetBody = sourceBody)).card ≤
            1 := by
      intro sourceBody
      apply Finset.card_le_one.mpr
      intro first firstMem second secondMem
      exact sourceBodyIndex_injective
        ((Finset.mem_filter.mp firstMem).2.trans
          (Finset.mem_filter.mp secondMem).2.symm)
    have globalPacketNonempty :=
      data.jointRegularizedSourcePacket_nonempty_of_targetPacket regularized
        coordinate targetParent normalization sourceParent packetPositive
    have globalPacketPositive : 0 <
        (data.jointRegularizedSourcePacket regularized coordinate
          sourceParent).card :=
      Finset.card_pos.mpr globalPacketNonempty
    have sourceRatio := data.sourceFullFiber_weighted_card_le_packet
      regularized coordinate normalizationWeight retentionConstant
      globalRetention sourceParent globalPacketPositive
    have globalPacketCard :=
      data.jointRegularizedSourcePacket_card_le_quotientTargetBodyPacket
        regularized coordinate targetParent normalization sourceParent
          packetPositive
    let jointConstant : ENNReal :=
      16 *
        ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
          ENNReal) *
        (Nat.log 2
          (2 * (data.selectedTarget selection).family.card) + 1 : ENNReal) ^
          (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
    let cardinalityConstant : ENNReal :=
      sourceConstant * retentionConstant * jointConstant
    have weightedCardinality :
        normalizationWeight *
            ((wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
              sourceParent).card : ENNReal) ≤
          cardinalityConstant * packet.enncard := by
      have globalPacketCardENN :
          ((data.jointRegularizedSourcePacket regularized coordinate
            sourceParent).card : ENNReal) ≤ packet.enncard := by
        change _ ≤ (packet.card : ENNReal)
        exact_mod_cast globalPacketCard
      exact sourceRatio.trans (mul_le_mul_left' globalPacketCardENN _)
    have cardinality :
        ((wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
          sourceParent).card : ENNReal) ≤
          (normalizationWeight⁻¹ * cardinalityConstant) * packet.enncard := by
      calc
        ((wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
            sourceParent).card : ENNReal) =
            (normalizationWeight⁻¹ * normalizationWeight) *
              ((wz2PaperOrdinaryFullFiberIndices sourceFine
                sourceScale.coarse sourceParent).card : ENNReal) := by
          rw [ENNReal.inv_mul_cancel weight_ne_zero weight_ne_top, one_mul]
        _ = normalizationWeight⁻¹ *
            (normalizationWeight *
              ((wz2PaperOrdinaryFullFiberIndices sourceFine
                sourceScale.coarse sourceParent).card : ENNReal)) := by ring
        _ ≤ normalizationWeight⁻¹ *
            (cardinalityConstant * packet.enncard) := by gcongr
        _ = (normalizationWeight⁻¹ * cardinalityConstant) *
            packet.enncard := by ring
    have targetBody : ∀ index : Fin packet.card,
        (packet.body index).carrier = normalization.map ''
          ((data.jointRegularizedTarget regularized).family.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
              (data.quotientTargetBodyPacketEmbedding regularized coordinate
                targetParent normalization sourceParent index)).1).carrier := by
      intro index
      rfl
    have targetBodyConvex : ∀ index,
        JohnEllipsoid.IsConvexBody (packet.body index).carrier := by
      intro index
      rw [targetBody]
      let tube := (data.jointRegularizedTarget regularized).family.tube
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
          (data.quotientTargetBodyPacketEmbedding regularized coordinate
            targetParent normalization sourceParent index)).1
      let tubeBody := wz2_paper_ordinary_tube_isConvexBody tube
        (mul_pos (lt_of_lt_of_le zero_lt_one hscale) sourceScale.delta_pos)
      let homeomorph :=
        normalization.map.toHomeomorphOfFiniteDimensional
      refine ⟨tubeBody.1.affine_image normalization.map.toAffineMap, ?_, ?_⟩
      · change IsCompact (homeomorph '' tube.carrier)
        exact (homeomorph.isCompact_image).2 tubeBody.2.1
      · change (interior (homeomorph '' tube.carrier)).Nonempty
        rw [← homeomorph.image_interior]
        exact tubeBody.2.2.image homeomorph
    have targetBodyBound : ∀ index,
        (packet.body index).carrier ⊆ Metric.closedBall (0 : Point3) 1 := by
      intro index point pointMem
      rw [targetBody] at pointMem
      rcases pointMem with ⟨targetPoint, targetPointMem, rfl⟩
      have targetFiber :=
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
          (data.quotientTargetBodyPacketEmbedding regularized coordinate
            targetParent normalization sourceParent index)).2
      have targetInParent : targetPoint ∈
          ((data.jointRegularizedParents regularized coordinate).family.tube
            targetParent).carrier :=
        (mem_wz2PaperOrdinaryFullFiberIndices_iff targetParent _).mp
          targetFiber targetPointMem
      have ellipsoidMem :=
        normalization.parent_convex_body.outerJohnEllipsoid_spec.1
          targetInParent
      have imageMem : normalization.map targetPoint ∈ normalization.map ''
          normalization.parent_convex_body.outerJohnEllipsoid :=
        ⟨targetPoint, ellipsoidMem, rfl⟩
      rw [normalization.outerJohn_image] at imageMem
      exact imageMem
    let targetCenter : Fin packet.card → Point3 := fun index =>
      normalization.map
        (wz2PaperTubeMidpoint
          ((data.jointRegularizedTarget regularized).family.tube
            ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
              (data.quotientTargetBodyPacketEmbedding regularized coordinate
                targetParent normalization sourceParent index)).1))
    have targetCenterMem : ∀ index,
        targetCenter index ∈ (packet.body index).carrier := by
      intro index
      rw [targetBody]
      exact ⟨_, wz2_paper_tubeMidpoint_mem_carrier _
        (mul_pos (lt_of_lt_of_le zero_lt_one hscale)
          sourceScale.delta_pos).le, rfl⟩
    let coordinateChange := proposition63MildRescalingJohnCoordinateChange
      sourceParent sourceFiber.normalization targetParent normalization center
        (lt_of_lt_of_le zero_lt_one hscale)
    have carrier : ∀ index,
        coordinateChange ''
            ((wz2PaperPureUnitRescaledFullFiberBodyFamily
              (fine := sourceFine) (coarse := sourceScale.coarse)
              sourceParent sourceFiber.normalization).body
                (sourceBodyIndex index)).carrier ⊆
          AffineMap.homothety (targetCenter index) (22 * scale + 3) ''
            (packet.body index).carrier := by
      intro index
      let targetBodyIndex :=
        data.quotientTargetBodyPacketEmbedding regularized coordinate
          targetParent normalization sourceParent index
      let targetIndex :=
        ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent)
          targetBodyIndex).1
      have sourceIndexValue :
          (sourceFullEquiv (sourceBodyIndex index)).1 = sourceIndex index := by
        simp [sourceBodyIndex, sourceFullEquiv]
      have targetTubeEq :
          (data.jointRegularizedTarget regularized).family.tube targetIndex =
            (proposition63MildRescalingFamily hscale raw).tube
              (sourceIndex index) := by
        rw [(data.jointRegularizedTarget regularized).tube_eq,
          (data.selectedTarget selection).tube_eq]
        rfl
      have targetCenterEq : targetCenter index = normalization.map
          (wz2PaperTubeMidpoint
            ((proposition63MildRescalingFamily hscale raw).tube
              (sourceIndex index))) := by
        change normalization.map
            (wz2PaperTubeMidpoint
              ((data.jointRegularizedTarget regularized).family.tube
                targetIndex)) = _
        rw [targetTubeEq]
      rw [targetBody index]
      change coordinateChange ''
          (sourceFiber.normalization.map ''
            (sourceFine.tube
              ((sourceFullEquiv (sourceBodyIndex index)).1)).carrier) ⊆ _
      rw [sourceIndexValue, targetTubeEq]
      have physical :=
        proposition63_isotropic_source_carrier_subset_target_homothety
          sourceScale.delta_pos hscale raw
          (data.representative coordinate).source_line_class
          (data.representative coordinate).raw_line_class
          (data.representative coordinate).source_midpoint_local
          (data.representative coordinate).center_height (sourceIndex index)
      intro point pointMem
      rcases pointMem with
        ⟨sourceJohnPoint, ⟨physicalPoint, physicalPointMem, rfl⟩, rfl⟩
      have physicalTarget := physical
        ⟨physicalPoint, physicalPointMem, rfl⟩
      have normalizedTarget : normalization.map
          (proposition63IsotropicAffineEquiv center scale
            (lt_of_lt_of_le zero_lt_one hscale) physicalPoint) ∈
          normalization.map ''
            (AffineMap.homothety
              (wz2PaperTubeMidpoint
                ((proposition63MildRescalingFamily hscale raw).tube
                  (sourceIndex index)))
              (22 * scale + 3) ''
              ((proposition63MildRescalingFamily hscale raw).tube
                (sourceIndex index)).carrier) :=
        ⟨_, physicalTarget, rfl⟩
      rw [proposition63_targetNormalization_image_homothety]
        at normalizedTarget
      rw [targetCenterEq]
      simpa [coordinateChange, targetCenter, targetIndex, targetBodyIndex,
        proposition63MildRescalingJohnCoordinateChange_apply_map] using
          normalizedTarget
    have result :=
      proposition63_bodyCWA_of_bounded_fiber_affine_homothetic_envelope
        (source := wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := sourceFine) (coarse := sourceScale.coarse)
          sourceParent sourceFiber.normalization)
        (target := packet) coordinateChange sourceBodyIndex 1
        sourceBodyIndexFiber
        (normalizationWeight⁻¹ * cardinalityConstant) cardinality
        (22 * scale + 3) 1 (by linarith) (by norm_num)
        targetBodyConvex targetBodyBound targetCenter targetCenterMem carrier
        sourceFiber.convex_wolff
    simpa [packet, sourceScale, sourceFiber, coordinateChange,
      cardinalityConstant, jointConstant, quotientPacketConstant, mul_assoc]
      using result
  · have packetCardZero : packet.card = 0 := by omega
    intro convexSet _hconvex
    have containedZero : packet.containedCount convexSet = 0 := by
      unfold Kakeya.Streamlined.BodyFamily.containedCount
      have cardLe : (packet.containedIndices convexSet).card ≤ packet.card := by
        simpa using Finset.card_le_univ (packet.containedIndices convexSet)
      have cardZero : (packet.containedIndices convexSet).card = 0 := by omega
      exact_mod_cast cardZero
    have enncardZero : packet.enncard = 0 := by
      change (packet.card : ENNReal) = 0
      rw [packetCardZero]
      norm_num
    rw [containedZero, enncardZero]
    simp

/-- The common full-fiber uniformity constant produced by the joint
regularization. -/
noncomputable def quotientFiberRegularizationConstant
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    (data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule)
    {weight : Fin sourceFine.card → ENNReal}
    (selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree) : ENNReal :=
  16 * ((sourceSchedule.scaleCount + sourceSchedule.scaleCount : ℕ) :
      ENNReal) *
    (Nat.log 2 (2 * (data.selectedTarget selection).family.card) + 1 :
      ENNReal) ^ (sourceSchedule.scaleCount + sourceSchedule.scaleCount)

/-- Canonical packet constant, with the quotient parent's chosen outer-John
normalization. -/
noncomputable def quotientCanonicalPacketConstant
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (normalizationWeight retentionConstant : ENNReal)
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) : ENNReal :=
  data.quotientPacketConstant regularized normalizationWeight
    retentionConstant coordinate targetParent
    (WZ2PaperAssouadUnitRescalingData.ofTube
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent)
      (data.quotient coordinate).caller_rho_pos) sourceParent

/-- One finite constant dominates all packetwise actual-John transports in
the quotient schedule. -/
noncomputable def quotientScheduleBodyConstant
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (normalizationWeight retentionConstant : ENNReal) : ENNReal :=
  Finset.univ.sup fun coordinate : Fin sourceSchedule.scaleCount =>
    Finset.univ.sup fun targetParent : Fin
        (data.jointRegularizedParents regularized coordinate).family.card =>
      Finset.univ.sup fun sourceParent : Fin
          (sourceSchedule.witness coordinate).scaleData.coarse.card =>
        data.quotientCanonicalPacketConstant regularized normalizationWeight
          retentionConstant coordinate targetParent sourceParent

theorem quotientCanonicalPacketConstant_le_schedule
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (normalizationWeight retentionConstant : ENNReal)
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card) :
    data.quotientCanonicalPacketConstant regularized normalizationWeight
        retentionConstant coordinate targetParent sourceParent ≤
      data.quotientScheduleBodyConstant regularized normalizationWeight
        retentionConstant := by
  exact (Finset.le_sup (s := Finset.univ)
    (f := fun sourceParent : Fin
      (sourceSchedule.witness coordinate).scaleData.coarse.card =>
        data.quotientCanonicalPacketConstant regularized normalizationWeight
          retentionConstant coordinate targetParent sourceParent)
    (Finset.mem_univ sourceParent)).trans <|
      (Finset.le_sup (s := Finset.univ)
        (f := fun targetParent : Fin
          (data.jointRegularizedParents regularized coordinate).family.card =>
            Finset.univ.sup fun sourceParent : Fin
              (sourceSchedule.witness coordinate).scaleData.coarse.card =>
                data.quotientCanonicalPacketConstant regularized
                  normalizationWeight retentionConstant coordinate
                  targetParent sourceParent)
        (Finset.mem_univ targetParent)).trans <|
          Finset.le_sup (s := Finset.univ)
            (f := fun coordinate : Fin sourceSchedule.scaleCount =>
              Finset.univ.sup fun targetParent : Fin
                (data.jointRegularizedParents regularized coordinate).family.card =>
                  Finset.univ.sup fun sourceParent : Fin
                    (sourceSchedule.witness coordinate).scaleData.coarse.card =>
                      data.quotientCanonicalPacketConstant regularized
                        normalizationWeight retentionConstant coordinate
                        targetParent sourceParent)
            (Finset.mem_univ coordinate)

/-- Every quotient full fiber has one common actual-John CWA constant. -/
theorem quotientTargetFullFiber_cwa
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (normalizationWeight retentionConstant : ENNReal)
    (weight_ne_zero : normalizationWeight ≠ 0)
    (weight_ne_top : normalizationWeight ≠ ⊤)
    (globalRetention : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (data.jointRegularizedTarget regularized).family.enncard)
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card) :
    WZ2PaperBodyConvexWolffBound
      (data.quotientTargetBodies regularized coordinate targetParent
        (WZ2PaperAssouadUnitRescalingData.ofTube
          ((data.jointRegularizedParents regularized coordinate).family.tube
            targetParent)
          (data.quotient coordinate).caller_rho_pos))
      (data.quotientScheduleBodyConstant regularized normalizationWeight
        retentionConstant) := by
  let normalization := WZ2PaperAssouadUnitRescalingData.ofTube
    ((data.jointRegularizedParents regularized coordinate).family.tube
      targetParent) (data.quotient coordinate).caller_rho_pos
  let parentCount :=
    (sourceSchedule.witness coordinate).scaleData.coarse.card
  have parentCountPos : 0 < parentCount := by
    let source : Fin sourceFine.card :=
      ⟨0, (data.representative coordinate).source_nonempty⟩
    rcases (sourceSchedule.witness coordinate).scaleData.cover.covers source
      with ⟨parent, _⟩
    exact lt_of_le_of_lt (Nat.zero_le parent.val) parent.isLt
  apply wz2PaperBodyConvexWolffBound_of_parent_fibers parentCountPos
    (data.quotientTargetBodySourceParent regularized coordinate targetParent
      normalization)
  intro sourceParent convexSet convexSetConvex
  have packetCWA := data.quotientTargetBodyPacket_cwa regularized
    normalizationWeight retentionConstant weight_ne_zero weight_ne_top
    globalRetention coordinate targetParent normalization sourceParent
  have packetCWA' : WZ2PaperBodyConvexWolffBound
      (wz2PaperBodyParentFiber
        (data.quotientTargetBodies regularized coordinate targetParent
          normalization)
        (data.quotientTargetBodySourceParent regularized coordinate
          targetParent normalization) sourceParent)
      (data.quotientCanonicalPacketConstant regularized normalizationWeight
        retentionConstant coordinate targetParent sourceParent) := by
    simpa only [quotientTargetBodyPacket, quotientCanonicalPacketConstant]
      using packetCWA
  exact (packetCWA' convexSet convexSetConvex).trans <| by
    gcongr
    exact data.quotientCanonicalPacketConstant_le_schedule regularized
      normalizationWeight retentionConstant coordinate targetParent
      sourceParent

/-- Package one quotient coordinate as a genuine Definition 2.12 one-scale
witness. -/
noncomputable def quotientOneScaleData
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant targetConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (normalizationWeight retentionConstant : ENNReal)
    (weight_ne_zero : normalizationWeight ≠ 0)
    (weight_ne_top : normalizationWeight ≠ ⊤)
    (globalRetention : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (data.jointRegularizedTarget regularized).family.enncard)
    (coordinate : Fin sourceSchedule.scaleCount)
    (constantBudget : max
      (data.quotientFiberRegularizationConstant selection)
      (data.quotientScheduleBodyConstant regularized normalizationWeight
        retentionConstant) ≤ targetConstant) :
    Proposition63MildRescalingOneScaleData
      (targetRho := proposition63MildRescalingQuotientRho sourceDelta
        (sourceSchedule.witness coordinate).rho scale)
      (targetFine := (data.jointRegularizedTarget regularized).family)
      (targetConstant := targetConstant)
      (coverConstant := data.quotientFiberRegularizationConstant selection)
      (bodyConstant := data.quotientScheduleBodyConstant regularized
        normalizationWeight retentionConstant)
      (sourceSchedule.witness coordinate).scaleData where
  targetCoarse := (data.jointRegularizedParents regularized coordinate).family
  target_delta_pos := mul_pos (lt_of_lt_of_le zero_lt_one hscale)
    (sourceSchedule.witness coordinate).scaleData.delta_pos
  target_rho_pos := (data.quotient coordinate).caller_rho_pos
  target_cover := data.jointRegularizedCover regularized coordinate
  target_full_fiber_uniform := by
    simpa [quotientFiberRegularizationConstant] using
      data.jointRegularized_fullFiber_uniform regularized coordinate
  target_normalization := fun targetParent =>
    WZ2PaperAssouadUnitRescalingData.ofTube
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent)
      (data.quotient coordinate).caller_rho_pos
  source_parent := fun targetParent =>
    (data.quotient coordinate).net.centerEmbedding
      ((data.selectedParents selection coordinate).embedding
        ((data.jointRegularizedParents regularized coordinate).embedding
          targetParent))
  target_full_fiber_cwa := fun targetParent => ⟨{
    normalization := WZ2PaperAssouadUnitRescalingData.ofTube
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent)
      (data.quotient coordinate).caller_rho_pos
    convex_wolff := data.quotientTargetFullFiber_cwa regularized
      normalizationWeight retentionConstant weight_ne_zero weight_ne_top
      globalRetention coordinate targetParent
    }⟩
  constant_budget := constantBudget

/-- Fixed enlargement of the source nearby-scale window caused by the
quotient radius. -/
def quotientScaleWindowConstant (sourceWindowConstant : ENNReal) : ENNReal :=
  5200000 * sourceWindowConstant + 4

/-- Lift all quotient coordinates to the public nearby-scale CWA predicate. -/
theorem quotientNearbyScales
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant targetConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    (sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount)
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (normalizationWeight retentionConstant : ENNReal)
    (weight_ne_zero : normalizationWeight ≠ 0)
    (weight_ne_top : normalizationWeight ≠ ⊤)
    (globalRetention : normalizationWeight * sourceFine.enncard ≤
      retentionConstant *
        (data.jointRegularizedTarget regularized).family.enncard)
    (targetDistinct : WZ2PaperOrdinaryIsEssentiallyDistinct
      (data.jointRegularizedTarget regularized).family)
    (targetFinite : WZ2PaperFiniteErrorConstant targetConstant)
    (scaleBudget : quotientScaleWindowConstant sourceWindowConstant ≤
      targetConstant)
    (constantBudget : ∀ coordinate : Fin sourceSchedule.scaleCount, max
      (data.quotientFiberRegularizationConstant selection)
      (data.quotientScheduleBodyConstant regularized normalizationWeight
        retentionConstant) ≤ targetConstant) :
    WZ2PaperPureCWAAtNearbyScales
      (data.jointRegularizedTarget regularized).family targetConstant := by
  refine ⟨mul_pos (lt_of_lt_of_le zero_lt_one hscale)
      (sourceSchedule.witness
        ⟨0, sourceSchedule.scaleCount_pos⟩).scaleData.delta_pos,
    targetFinite, targetDistinct, ?_⟩
  intro target
  let sourceRequest := proposition63MildRescalingSourceRequest
    (sourceSchedule.witness
      ⟨0, sourceSchedule.scaleCount_pos⟩).scaleData.delta_pos
    hscale target
  let coordinate := sourceSchedule.representative sourceRequest
  have scaleNonnegative : 0 ≤ scale := zero_le_one.trans hscale
  have requestedSource : sourceRequest.1 ≤
      (sourceSchedule.witness coordinate).rho :=
    sourceSchedule.requested_le sourceRequest
  have requestedTarget : target.1 ≤
      proposition63MildRescalingQuotientRho sourceDelta
        (sourceSchedule.witness coordinate).rho scale := by
    calc
      target.1 ≤ scale * (sourceSchedule.witness coordinate).rho :=
        proposition63MildRescaling_requested_le_targetActual
          (sourceSchedule.witness
            ⟨0, sourceSchedule.scaleCount_pos⟩).scaleData.delta_pos
          hscale target requestedSource
      _ ≤ proposition63MildRescalingQuotientRho sourceDelta
          (sourceSchedule.witness coordinate).rho scale := by
        unfold proposition63MildRescalingQuotientRho
        have scalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
        have rhoPos := (sourceSchedule.witness coordinate).scaleData.rho_pos
        have deltaPos := (sourceSchedule.witness coordinate).scaleData.delta_pos
        nlinarith
  have sourceWithin :
      ENNReal.ofReal (scale * (sourceSchedule.witness coordinate).rho) <
        sourceWindowConstant * ENNReal.ofReal target.1 := by
    exact proposition63MildRescaling_withinFactor
      (sourceSchedule.witness
        ⟨0, sourceSchedule.scaleCount_pos⟩).scaleData.delta_pos
      hscale target (sourceSchedule.within_output sourceRequest)
  have targetDeltaLe : ENNReal.ofReal (scale * sourceDelta) ≤
      ENNReal.ofReal target.1 := ENNReal.ofReal_mono target.2.1
  have quotientWithin : ENNReal.ofReal
      (proposition63MildRescalingQuotientRho sourceDelta
        (sourceSchedule.witness coordinate).rho scale) <
      targetConstant * ENNReal.ofReal target.1 := by
    have firstTerm :
        (5200000 : ENNReal) *
            ENNReal.ofReal
              (scale * (sourceSchedule.witness coordinate).rho) <
          (5200000 : ENNReal) *
            (sourceWindowConstant * ENNReal.ofReal target.1) := by
      simpa [mul_comm] using (ENNReal.mul_lt_mul_iff_left
        (c := (5200000 : ENNReal)) (by norm_num) (by norm_num)).2
          sourceWithin
    have sumBound :
        (5200000 : ENNReal) *
              ENNReal.ofReal
                (scale * (sourceSchedule.witness coordinate).rho) +
            4 * ENNReal.ofReal (scale * sourceDelta) <
          (5200000 : ENNReal) *
              (sourceWindowConstant * ENNReal.ofReal target.1) +
            4 * ENNReal.ofReal target.1 :=
      ENNReal.add_lt_add_of_lt_of_le
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        firstTerm (mul_le_mul_left' targetDeltaLe 4)
    calc
      ENNReal.ofReal
          (proposition63MildRescalingQuotientRho sourceDelta
            (sourceSchedule.witness coordinate).rho scale) =
          (5200000 : ENNReal) *
              ENNReal.ofReal
                (scale * (sourceSchedule.witness coordinate).rho) +
            4 * ENNReal.ofReal (scale * sourceDelta) := by
        unfold proposition63MildRescalingQuotientRho
        rw [show 5200000 * scale *
              (sourceSchedule.witness coordinate).rho +
              4 * scale * sourceDelta =
            5200000 *
                (scale * (sourceSchedule.witness coordinate).rho) +
              4 * (scale * sourceDelta) by ring]
        rw [ENNReal.ofReal_add
            (mul_nonneg (by norm_num) (mul_nonneg scaleNonnegative
              (sourceSchedule.witness coordinate).scaleData.rho_pos.le))
            (mul_nonneg (by norm_num) (mul_nonneg scaleNonnegative
              (sourceSchedule.witness coordinate).scaleData.delta_pos.le)),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5200000),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      _ < (5200000 : ENNReal) *
            (sourceWindowConstant * ENNReal.ofReal target.1) +
          4 * ENNReal.ofReal target.1 := sumBound
      _ = quotientScaleWindowConstant sourceWindowConstant *
          ENNReal.ofReal target.1 := by
        unfold quotientScaleWindowConstant
        ring
      _ ≤ targetConstant * ENNReal.ofReal target.1 := by gcongr
  refine ⟨{
    rho := proposition63MildRescalingQuotientRho sourceDelta
      (sourceSchedule.witness coordinate).rho scale
    requested_le := requestedTarget
    within_factor := quotientWithin
    scaleData := (data.quotientOneScaleData regularized normalizationWeight
      retentionConstant weight_ne_zero weight_ne_top globalRetention
      coordinate (constantBudget coordinate)).toScaleCoverData
    }⟩

/-- A final quotient fiber obtains CWA by summing uniform packet estimates. -/
theorem quotientTargetFullFiber_cwa_of_packets
    {sourceDelta scale : ℝ}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFine}
    {center : Point3}
    {sourceConstant sourceWindowConstant bodyConstant : ENNReal}
    {levelCount : ℕ}
    {hscale : 1 ≤ scale}
    {raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFine sourceShading center}
    {sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sourceFine) sourceConstant sourceWindowConstant levelCount}
    {data : Proposition63MildRescalingQuotientScheduleData
      hscale raw sourceSchedule}
    {weight : Fin sourceFine.card → ENNReal}
    {selection : Proposition63FiniteStrongParentSelectionData
      weight sourceSchedule.scaleCount data.Parent data.parent data.conflict
      proposition63MildRescalingQuotientConflictDegree}
    {targetShading : WZ1PaperTubeShading
      (proposition63MildRescalingFamily hscale raw)}
    (regularized : WZ2PaperFiniteParentRegularizationData
      (restrictPaperShading
        (data.selectedTarget selection).toTubeSubfamily targetShading)
      (sourceSchedule.scaleCount + sourceSchedule.scaleCount)
      (fun _ => data.JointParent selection) (data.jointParent selection))
    (coordinate : Fin sourceSchedule.scaleCount)
    (targetParent : Fin
      (data.jointRegularizedParents regularized coordinate).family.card)
    (normalization : WZ2PaperAssouadUnitRescalingData
      ((data.jointRegularizedParents regularized coordinate).family.tube
        targetParent))
    (packetCWA : ∀ sourceParent,
      WZ2PaperBodyConvexWolffBound
        (data.quotientTargetBodyPacket regularized coordinate targetParent
          normalization sourceParent) bodyConstant) :
    WZ2PaperBodyConvexWolffBound
      (data.quotientTargetBodies regularized coordinate targetParent
        normalization) bodyConstant := by
  let parentCount :=
    (sourceSchedule.witness coordinate).scaleData.coarse.card
  have parentCountPos : 0 < parentCount := by
    let source : Fin sourceFine.card :=
      ⟨0, (data.representative coordinate).source_nonempty⟩
    rcases (sourceSchedule.witness coordinate).scaleData.cover.covers source
      with ⟨parent, _⟩
    exact lt_of_le_of_lt (Nat.zero_le parent.val) parent.isLt
  exact wz2PaperBodyConvexWolffBound_of_parent_fibers parentCountPos
    (data.quotientTargetBodySourceParent regularized coordinate targetParent
      normalization) packetCWA

end Proposition63MildRescalingQuotientScheduleData

end Kakeya.Assouad.PureWZ2

end
