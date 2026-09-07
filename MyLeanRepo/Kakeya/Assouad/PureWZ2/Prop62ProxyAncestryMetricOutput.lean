import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyUpperAncestryCellSelection

/-!
# Proposition 6.2 proxy-ancestry metric output

This module assembles the first geometric selection in the order used by the
paper:

1. choose one global packet-mesh residue;
2. choose one quotient-center upper-ancestry color in each occupied cell;
3. take the complete old-packet hull of that selected leaf set;
4. quotient its packet proxy axes by the selected mesh cells; and
5. construct the genuine Section 6 metric cover.

Packet saturation proves that step 3 loses no additional leaves.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62ProxyAncestryMetricOutput
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal) where
  selection :
    PureWZ2Prop62GlobalResiduePerCellSelectionData
      (Fin fine.card)
      (schedule.ProxyPacketCell
        (schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width))
      (Fin 4 → ZMod (strideBase + 1))
      (schedule.ProxyUpperColorVector rho packetCoordinate)
      (schedule.proxyPacketCell
        (schedule.proxyPacketLineCell
          fineNonempty packetCoordinate width))
      (fun source =>
        pureWZ2Prop62LineColor width (strideBase + 1)
          (schedule.coordinateProxyTube
            fineNonempty packetCoordinate
            ((schedule.scaleData packetCoordinate).cover.parent source)))
      (quotient.proxyUpperColorVector rho packetCoordinate)
      weight
  selection_eq :
    selection =
      quotient.selectProxyResidueUpperAncestryPerCell
        rho width packetCoordinate strideBase weight
  selected_nonempty : selection.selected.Nonempty
  selectedParents :
    Finset
      (Fin (schedule.scaleData packetCoordinate).coarse.card)
  selectedParents_eq :
    selectedParents =
      selection.selected.image
        (schedule.scaleData packetCoordinate).cover.parent
  mesh :
    PureWZ2Prop62ProxySelectedMeshCells
      (rho := rho)
      (schedule.scaleData packetCoordinate)
      (schedule.coordinateProxyTube
        fineNonempty packetCoordinate)
      width
  mesh_selectedParents_eq :
    mesh.selectedParents = selectedParents
  packet_hull_eq_selection :
    mesh.complete.selectedFineIndices =
      selection.selected
  metricInput :
    PureWZ2Prop62ProxyMetricPacketCoverInput
      (rho := rho) mesh.restrictedOldData
      (600000 * schedule.actualScale packetCoordinate +
        6 * width)
  metric_coarse_eq :
    metricInput.coarse = mesh.coarse
  metric_parent_eq_iff_proxyPacketLineCell_embedding_eq :
    ∀ first second : Fin mesh.complete.selectedFine.family.card,
      metricInput.packetParent
            (mesh.restrictedOldData.cover.parent first) =
          metricInput.packetParent
            (mesh.restrictedOldData.cover.parent second) ↔
        schedule.proxyPacketLineCell fineNonempty packetCoordinate width
            (mesh.complete.selectedFine.embedding first) =
          schedule.proxyPacketLineCell fineNonempty packetCoordinate width
            (mesh.complete.selectedFine.embedding second)

theorem pureWZ2_prop62_proxy_ancestry_metric_output
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (rho width : ℝ)
    (packetCoordinate : Fin schedule.levelCount)
    (strideBase : ℕ)
    (weight : Fin fine.card → ENNReal)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (selectionNonempty :
      (quotient.selectProxyResidueUpperAncestryPerCell
        rho width packetCoordinate strideBase weight).selected.Nonempty)
    (strongSeparation :
      6 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width)
    (packetBound :
      600000 * schedule.actualScale packetCoordinate +
          6 * width ≤
        rho / 2) :
    Nonempty
      (PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
        packetCoordinate strideBase weight) := by
  let selection :=
    quotient.selectProxyResidueUpperAncestryPerCell
      rho width packetCoordinate strideBase weight
  let selectedParents :
      Finset
        (Fin (schedule.scaleData packetCoordinate).coarse.card) :=
    selection.selected.image
      (schedule.scaleData packetCoordinate).cover.parent
  have selectedParentsNonempty :
      selectedParents.Nonempty := by
    rcases selectionNonempty with ⟨source, sourceMem⟩
    exact
      ⟨(schedule.scaleData packetCoordinate).cover.parent source,
        Finset.mem_image.mpr
          ⟨source, sourceMem, rfl⟩⟩
  rcases
      schedule.exists_coordinateProxySelectedMeshCells
        fineNonempty packetCoordinate rho width rhoPos
        selectedParents selectedParentsNonempty
    with
    ⟨mesh, meshParents⟩
  have hullEq :
      mesh.complete.selectedFineIndices =
        selection.selected := by
    ext source
    simp only [
      PureWZ2CompleteParentRestrictionData.selectedFineIndices,
      Finset.mem_filter, Finset.mem_univ, true_and
    ]
    constructor
    · intro parentMem
      rw [meshParents] at parentMem
      rcases Finset.mem_image.mp parentMem with
        ⟨witness, witnessMem, parentEq⟩
      exact
        (PureWZ2Prop62ProxyQuotientScheduleData.PureWZ2Prop62GlobalResiduePerCellSelectionData.proxyResiduePerCell_selected_packet_saturated
            (quotient := quotient)
            rho width packetCoordinate strideBase weight
            witness source parentEq).mp witnessMem
    · intro sourceMem
      rw [meshParents]
      exact
        Finset.mem_image.mpr
          ⟨source, sourceMem, rfl⟩
  have selectedFineLine :
      WZ1PaperIsLineClass mesh.complete.selectedFine.family :=
    fineLine.subfamily mesh.complete.selectedFine.toTubeSubfamily
  have sameColor :
      ∀ first second,
        first ∈ mesh.selectedParents →
        second ∈ mesh.selectedParents →
        pureWZ2Prop62LineColor width (strideBase + 1)
            (schedule.coordinateProxyTube
              fineNonempty packetCoordinate first) =
          pureWZ2Prop62LineColor width (strideBase + 1)
            (schedule.coordinateProxyTube
              fineNonempty packetCoordinate second) := by
    intro first second firstMem secondMem
    rw [meshParents] at firstMem secondMem
    rcases Finset.mem_image.mp firstMem with
      ⟨firstSource, firstSourceMem, firstEq⟩
    rcases Finset.mem_image.mp secondMem with
      ⟨secondSource, secondSourceMem, secondEq⟩
    have firstResidue :=
      selection.selected_residue firstSource firstSourceMem
    have secondResidue :=
      selection.selected_residue secondSource secondSourceMem
    simpa only [firstEq, secondEq] using
      firstResidue.trans secondResidue.symm
  have separation :
      6 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width :=
    strongSeparation
  let metricInput :=
    mesh.toLaminarScheduleMetricPacketCoverInput
      schedule fineNonempty fineLine fineBase
      packetCoordinate widthPos (strideBase + 1)
      sameColor separation packetBound
  exact
    ⟨{
      selection := selection
      selection_eq := rfl
      selected_nonempty := selectionNonempty
      selectedParents := selectedParents
      selectedParents_eq := rfl
      mesh := mesh
      mesh_selectedParents_eq := meshParents
      packet_hull_eq_selection := hullEq
      metricInput := metricInput
      metric_coarse_eq := rfl
      metric_parent_eq_iff_proxyPacketLineCell_embedding_eq := by
        intro first second
        change
          mesh.oldPacketParent
                (mesh.restrictedOldData.cover.parent first) =
              mesh.oldPacketParent
                (mesh.restrictedOldData.cover.parent second) ↔ _
        constructor
        · intro parentEq
          have cellEq := congrArg mesh.cellEquiv parentEq
          rw [mesh.oldPacketParent_cell,
            mesh.oldPacketParent_cell] at cellEq
          have rawCellEq :
              pureWZ2Prop62LineCell width
                  (schedule.coordinateProxyTube fineNonempty packetCoordinate
                    (mesh.selectedOldCoarse.embedding
                      (mesh.restrictedOldData.cover.parent first))) =
                pureWZ2Prop62LineCell width
                  (schedule.coordinateProxyTube fineNonempty packetCoordinate
                    (mesh.selectedOldCoarse.embedding
                      (mesh.restrictedOldData.cover.parent second))) :=
            congrArg Subtype.val cellEq
          simpa only [
            PureWZ2Prop62LaminarPureSchedule.proxyPacketLineCell,
            mesh.restrictedOldData_parent_ambient
          ] using rawCellEq
        · intro rawCellEq
          apply mesh.cellEquiv.injective
          rw [mesh.oldPacketParent_cell,
            mesh.oldPacketParent_cell]
          apply Subtype.ext
          simpa only [
            PureWZ2Prop62LaminarPureSchedule.proxyPacketLineCell,
            mesh.restrictedOldData_parent_ambient
          ] using rawCellEq
    }⟩

namespace PureWZ2Prop62ProxyAncestryMetricOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (output :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
        packetCoordinate strideBase weight)

abbrev selectedFine :
    Kakeya.Streamlined.TubeFamily delta :=
  output.mesh.complete.selectedFine.family

abbrev metricParents :
    Kakeya.Streamlined.TubeFamily rho :=
  output.metricInput.coarse

noncomputable def section6Cover :
    PureWZ2Section6Cover
      output.selectedFine output.metricParents :=
  output.metricInput.section6Cover

theorem selectedFineIndices_eq_selection :
    output.mesh.complete.selectedFineIndices =
      output.selection.selected :=
  output.packet_hull_eq_selection

theorem metricFiber_eq_completePacket_biUnion
    (parent : Fin output.metricParents.card) :
    wz2PaperFullFiberIndices
        output.selectedFine output.metricParents parent =
      Finset.biUnion
        (Finset.univ.filter fun oldParent =>
          output.metricInput.packetParent oldParent = parent)
        (wz2PaperOrdinaryFullFiberIndices
          output.selectedFine
          output.mesh.restrictedOldData.coarse) :=
  output.metricInput.metricFiber_eq_biUnion_oldPackets parent

end PureWZ2Prop62ProxyAncestryMetricOutput

end Kakeya.Assouad

end
