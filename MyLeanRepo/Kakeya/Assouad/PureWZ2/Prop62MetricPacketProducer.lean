import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricMeshProducer

/-!
# Proposition 6.2 metric parents: whole-packet producer

This is the assembly endpoint of the four-dimensional line mesh.  Starting
from a nonempty collection of old strict parents in one residue class, it
chooses one representative in every occupied mesh cell, retains the complete
old strict packets, and constructs the exact Section 6 metric cover at the
prescribed radius.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable
open MeasureTheory

structure PureWZ2Prop62MetricPacketOutput
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (oldData : WZ2PaperPureScaleCoverData fine scale C)
    (width M : ℝ) where
  selectedParents : Finset (Fin oldData.coarse.card)
  selectedParents_nonempty : selectedParents.Nonempty
  mesh :
    PureWZ2Prop62SelectedMeshCells
      (rho := rho) oldData width
  mesh_selectedParents_eq :
    mesh.selectedParents = selectedParents
  metricInput :
    PureWZ2Prop62MetricPacketCoverInput
      (rho := rho) mesh.restrictedOldData M (6 * width)
  metric_coarse_eq :
    metricInput.coarse = mesh.coarse
  metric_packetParent_val :
    ∀ parent,
      (metricInput.packetParent parent).1 =
        (mesh.oldPacketParent parent).1
  metricParents_ordinary_distinct :
    WZ2PaperOrdinaryIsEssentiallyDistinct metricInput.coarse

theorem pureWZ2_prop62_metric_packet_output
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (oldData : WZ2PaperPureScaleCoverData fine scale C)
    (width M : ℝ)
    (rhoPos : 0 < rho)
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineLocal :
      ∀ source,
        ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ M)
    (selectedParents : Finset (Fin oldData.coarse.card))
    (selectedParentsNonempty : selectedParents.Nonempty)
    (widthPos : 0 < width)
    (stride : ℕ)
    (sameColor :
      ∀ first second,
        first ∈ selectedParents →
        second ∈ selectedParents →
          pureWZ2Prop62LineColor width stride
              (oldData.coarse.tube first) =
            pureWZ2Prop62LineColor width stride
              (oldData.coarse.tube second))
    (strongSeparation :
      360 * rho < ((stride : ℝ) - 1) * width)
    (packetBound :
      (16 * M + 44) * scale + 6 * width ≤ rho / 2)
    (oldLine : WZ1PaperIsLineClass oldData.coarse) :
    ∃ output :
        PureWZ2Prop62MetricPacketOutput
          (rho := rho) oldData width M,
      output.selectedParents = selectedParents := by
  rcases
      exists_pureWZ2Prop62SelectedMeshCells
        oldData width rhoPos fineNonempty
        selectedParents selectedParentsNonempty
    with ⟨mesh, meshParents⟩
  have selectedFineLine :
      WZ1PaperIsLineClass mesh.complete.selectedFine.family :=
    fineLine.subfamily mesh.complete.selectedFine.toTubeSubfamily
  have selectedFineLocal :
      ∀ source,
        ‖wz2PaperTubeMidpoint
          (mesh.complete.selectedFine.family.tube source)‖ ≤ M := by
    intro source
    rw [mesh.complete.selectedFine.tube_eq]
    exact fineLocal (mesh.complete.selectedFine.embedding source)
  have meshSameColor :
      ∀ first second,
        first ∈ mesh.selectedParents →
        second ∈ mesh.selectedParents →
          pureWZ2Prop62LineColor width stride
              (oldData.coarse.tube first) =
            pureWZ2Prop62LineColor width stride
              (oldData.coarse.tube second) := by
    intro first second firstMem secondMem
    apply sameColor first second
    · rwa [← meshParents]
    · rwa [← meshParents]
  have separation :
      6 * rho < ((stride : ℝ) - 1) * width := by
    linarith [mesh.rho_pos]
  let metricInput :=
    mesh.toMetricPacketCoverInput
      oldLine selectedFineLine selectedFineLocal
      widthPos stride meshSameColor separation packetBound
  exact
    ⟨{
      selectedParents := selectedParents
      selectedParents_nonempty := selectedParentsNonempty
      mesh := mesh
      mesh_selectedParents_eq := meshParents
      metricInput := metricInput
      metric_coarse_eq := rfl
      metric_packetParent_val := fun _ => rfl
      metricParents_ordinary_distinct := by
        exact
          mesh.coarse_ordinary_essentially_distinct
            oldLine widthPos stride meshSameColor strongSeparation
    }, rfl⟩

namespace PureWZ2Prop62MetricPacketOutput

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {width M : ℝ}
    (output :
      PureWZ2Prop62MetricPacketOutput
        (rho := rho) oldData width M)

abbrev selectedFine : Kakeya.Streamlined.TubeFamily delta :=
  output.mesh.complete.selectedFine.family

abbrev metricParents : Kakeya.Streamlined.TubeFamily rho :=
  output.metricInput.coarse

noncomputable def section6Cover :
    PureWZ2Section6Cover output.selectedFine output.metricParents :=
  output.metricInput.section6Cover

theorem metricFiber_eq_assignedPackets
    (parent : Fin output.metricParents.card) :
    wz2PaperFullFiberIndices
        output.selectedFine output.metricParents parent =
      Finset.univ.filter fun source =>
        output.metricInput.packetParent
            (output.mesh.restrictedOldData.cover.parent source) =
          parent :=
  output.metricInput.metricFiber_eq_assignedPackets parent

theorem metricInput_packetParent_eq_oldPacketParent
    (parent : Fin output.mesh.restrictedOldData.coarse.card) :
    (output.metricInput.packetParent parent).1 =
      (output.mesh.oldPacketParent parent).1 :=
  output.metric_packetParent_val parent

theorem metricInput_packetParent_eq_iff_sourceCell_eq
    (first second : Fin output.selectedFine.card) :
    output.metricInput.packetParent
          (output.mesh.restrictedOldData.cover.parent first) =
        output.metricInput.packetParent
          (output.mesh.restrictedOldData.cover.parent second) ↔
      output.mesh.sourceCell first =
        output.mesh.sourceCell second := by
  constructor
  · intro metricParentEq
    have metricParentValEq :=
      congrArg Fin.val metricParentEq
    have oldParentValEq :
        (output.mesh.oldPacketParent
          (output.mesh.restrictedOldData.cover.parent first)).1 =
        (output.mesh.oldPacketParent
          (output.mesh.restrictedOldData.cover.parent second)).1 := by
      calc
        (output.mesh.oldPacketParent
            (output.mesh.restrictedOldData.cover.parent first)).1 =
            (output.metricInput.packetParent
              (output.mesh.restrictedOldData.cover.parent first)).1 :=
          (output.metricInput_packetParent_eq_oldPacketParent _).symm
        _ =
            (output.metricInput.packetParent
              (output.mesh.restrictedOldData.cover.parent second)).1 :=
          metricParentValEq
        _ =
            (output.mesh.oldPacketParent
              (output.mesh.restrictedOldData.cover.parent second)).1 :=
          output.metricInput_packetParent_eq_oldPacketParent _
    have oldParentEq :
        output.mesh.oldPacketParent
            (output.mesh.restrictedOldData.cover.parent first) =
          output.mesh.oldPacketParent
            (output.mesh.restrictedOldData.cover.parent second) :=
      Fin.ext oldParentValEq
    rw [
      output.mesh.oldPacketParent_restricted_parent_eq_packetParent,
      output.mesh.oldPacketParent_restricted_parent_eq_packetParent
    ] at oldParentEq
    exact
      (output.mesh.packetParent_eq_iff_sourceCell_eq
        first second).mp oldParentEq
  · intro sourceCellEq
    have packetParentEq :
        output.mesh.packetParent first =
          output.mesh.packetParent second :=
      (output.mesh.packetParent_eq_iff_sourceCell_eq
        first second).mpr sourceCellEq
    have oldParentEq :
        output.mesh.oldPacketParent
            (output.mesh.restrictedOldData.cover.parent first) =
          output.mesh.oldPacketParent
            (output.mesh.restrictedOldData.cover.parent second) := by
      rw [
        output.mesh.oldPacketParent_restricted_parent_eq_packetParent,
        output.mesh.oldPacketParent_restricted_parent_eq_packetParent
      ]
      exact packetParentEq
    apply Fin.ext
    calc
      (output.metricInput.packetParent
          (output.mesh.restrictedOldData.cover.parent first)).1 =
          (output.mesh.oldPacketParent
            (output.mesh.restrictedOldData.cover.parent first)).1 :=
        output.metricInput_packetParent_eq_oldPacketParent _
      _ =
          (output.mesh.oldPacketParent
            (output.mesh.restrictedOldData.cover.parent second)).1 :=
        congrArg Fin.val oldParentEq
      _ =
          (output.metricInput.packetParent
            (output.mesh.restrictedOldData.cover.parent second)).1 :=
        (output.metricInput_packetParent_eq_oldPacketParent _).symm

theorem insertedFiberCWA
    (parent : Fin output.metricParents.card)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    (((wz2PaperFullFiberIndices
        output.selectedFine output.metricParents parent).filter
        fun source =>
          wz2PaperLiteralUnitRescalingMap
              (output.metricParents.tube parent)
              output.metricInput.rho_pos ''
            (output.selectedFine.tube source).carrier ⊆
              convexSet).card : ENNReal) ≤
      pureWZ2Prop62InsertedCWALoss rho scale C *
        volume convexSet *
        ((wz2PaperFullFiberIndices
          output.selectedFine output.metricParents parent).card :
          ENNReal) :=
  output.metricInput.insertedFiberCWA parent convexSet convex

end PureWZ2Prop62MetricPacketOutput

end Kakeya.Assouad

end
