import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4RichCertificateCompanion
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperFinalV4FixedGridPreparation
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# Fixed-grid coarse cells for the rich metric certificate

The rich Target-3 companion retains the original metric certificate and its
deterministic `MetricParentsAtPrescribedScaleData` projection.  This module
connects that same witness to the fixed-grid cleanup used before Target 3.

No metric family, cover, parent map, or shading is selected again.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad

namespace Prop62V4MetricParentsRichCompanionData

variable
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {hdelta : 0 < delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (cleanup :
      FixedGridBoundaryRemovalData
        (rho := rho.1) shading hdelta)
    (companion :
      Prop62V4MetricParentsRichCompanionData
        cleanup.refined rho fineParentDistanceConstant
          parentConstant fiberConstant)

include cleanup companion

/--
The fixed-grid cleanup supplies the unique coarse cell required by the rich
four-degree producer on every cell retained by the exact metric witness.
-/
theorem fixedGrid_coarse_cell
    (scaleSeparation : 18 * delta ≤ rho.1) :
    ∀ sourceIndex cell,
      wz1PaperGridCube delta cell ⊆
          companion.metric.refinement.refined.carrier sourceIndex →
        ∃! coarseCell,
          wz1PaperGridCube delta cell ⊆
              wz1PaperGridCube rho.1 coarseCell ∧
            wz1PaperGridCube rho.1 coarseCell ⊆
              wz1PaperTubeCarrier
                (companion.metric.scaleData.coarse.tube
                  (companion.metric.scaleData.cover.parent sourceIndex)) := by
  intro sourceIndex cell wholeCell
  let metric := companion.metric
  let ambientSource :=
    metric.refinement.selected.embedding sourceIndex
  let point := cellCorner delta cell
  have pointFine :
      point ∈ wz1PaperGridCube delta cell :=
    cellCorner_mem_gridCube hdelta cell
  have pointMetric :
      point ∈ metric.refinement.refined.carrier sourceIndex :=
    wholeCell pointFine
  have pointCleanup :
      point ∈ cleanup.refined.carrier ambientSource :=
    metric.refinement.subshading sourceIndex pointMetric
  have pointRetained :
      point ∈
        wz2RetainedCellsUnion delta cleanup.retainedFineCells := by
    have carrierEq :
        cleanup.refined.carrier ambientSource =
          (wz2RefinedShading shading
            cleanup.retainedFineCells).carrier ambientSource :=
      congrArg (fun refined => refined.carrier ambientSource)
        cleanup.refined_eq
    have pointExplicit :
        point ∈
          (wz2RefinedShading shading
            cleanup.retainedFineCells).carrier ambientSource :=
      carrierEq ▸ pointCleanup
    exact pointExplicit.2
  rcases Set.mem_iUnion₂.mp pointRetained with
    ⟨retainedCell, retainedCellMem, pointRetainedCell⟩
  have retainedCellEq : retainedCell = cell := by
    have retainedIndex :
        wz1PaperGridIndex delta point = retainedCell :=
      (mem_wz1PaperGridCube delta retainedCell point).mp
        pointRetainedCell
    have cellIndex :
        wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp pointFine
    exact retainedIndex.symm.trans cellIndex
  have cellRetained : cell ∈ cleanup.retainedFineCells := by
    rwa [← retainedCellEq]
  let coarseCell := cleanup.parent cell
  refine ⟨coarseCell, ?_, ?_⟩
  · refine ⟨cleanup.parent_containment cell cellRetained, ?_⟩
    apply
      wz2_prop_sticky_coarse_cell_containment
        hdelta metric.rho_pos scaleSeparation
        (metric.refinement.selected.family.tube sourceIndex)
        (metric.scaleData.coarse.tube
          (metric.scaleData.cover.parent sourceIndex))
        (metric.scaleData.section6Cover.fine_line_class sourceIndex)
        (metric.scaleData.section6Cover.coarse_line_class
          (metric.scaleData.cover.parent sourceIndex))
        (metric.scaleData.cover.parent_covers sourceIndex)
        coarseCell
    · exact
        ⟨point,
          cleanup.parent_containment cell cellRetained pointFine,
          metric.refinement.refined.subset_body sourceIndex pointMetric⟩
    · exact cleanup.parent_crop cell cellRetained
  · intro candidate candidateData
    have candidateIndex :
        wz1PaperGridIndex rho.1 point = candidate :=
      (mem_wz1PaperGridCube rho.1 candidate point).mp
        (candidateData.1 pointFine)
    have parentIndex :
        wz1PaperGridIndex rho.1 point = coarseCell :=
      (mem_wz1PaperGridCube rho.1 coarseCell point).mp
        (cleanup.parent_containment cell cellRetained pointFine)
    exact candidateIndex.symm.trans parentIndex

end Prop62V4MetricParentsRichCompanionData

end Kakeya.Assouad.Prop62PaperAudit.V4

end
