import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedScalar
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyMultiplicity
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeightPopularity

/-!
# Source height lift from the saturated Node-5 graph

Theorem 5.2 selects graph heights.  This module first keeps every residue
graph cell at one of those heights and maps it through the source witness
already stored by the saturated graph construction.  The map has a fixed
geometric fibre bound.  We then retain the corresponding complete side-`rho`
cells of the original post-two-call source.

No artificial graph tube is promoted to a Kakeya source, and no CWA or
extremality property is asserted for the auxiliary graph.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

private theorem saturated_abs_sub_lt_of_common_interval
    {index width first second : ℝ}
    (hfirst : index * width ≤ first ∧ first < (index + 1) * width)
    (hsecond : index * width ≤ second ∧ second < (index + 1) * width) :
    |first - second| < width := by
  rw [abs_lt]
  constructor <;> nlinarith [hfirst.1, hfirst.2, hsecond.1, hsecond.2]

/-- Indexed mass of a restriction to side-`rho` cells is the sum of the
original carrier incidences in those cells.  This statement does not identify
indexed mass with union volume. -/
private theorem saturated_restrictToCells_mass_eq_sum_cells
    {scale rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily scale}
    (shading : WZ1PaperTubeShading family)
    (cells : Finset WZ2PaperCellIndex) :
    (pureWZ2Node05RestrictToCells (rho := rho) shading cells).mass =
      ∑ cell ∈ cells, wz2PaperCellIncidenceMass (rho := rho) shading cell := by
  unfold Kakeya.Streamlined.Shading.mass wz2PaperCellIncidenceMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _hsource
  have hcarrier :
      (pureWZ2Node05RestrictToCells (rho := rho) shading cells).carrier source =
        ⋃ cell ∈ cells,
          shading.carrier source ∩ wz1PaperGridCube rho cell := by
    ext point
    simp only [pureWZ2Node05RestrictToCells_carrier,
      pureWZ2Node05RetainedCellRegion, Set.mem_inter_iff, Set.mem_iUnion]
    constructor
    · rintro ⟨hsourcePoint, cell, hcell, hpointCell⟩
      exact ⟨cell, ⟨hcell, hsourcePoint, hpointCell⟩⟩
    · rintro ⟨cell, hcell, hsourcePoint, hpointCell⟩
      exact ⟨hsourcePoint, cell, hcell, hpointCell⟩
  rw [hcarrier]
  exact MeasureTheory.measure_biUnion_finset
    (fun first _ second _ hne =>
      (wz1PaperGridCube_disjoint hne).mono
        Set.inter_subset_right Set.inter_subset_right)
    (fun cell _ =>
      (shading.measurable_carrier source).inter
        (wz1PaperGridCube_measurable cell))

/-- The exact first-V4 terminal multiplicity band survives the synchronized
pullback to the original source family. -/
theorem PureWZ2Node05V4RichTwoScaleCellPullbackData.source_constantMultiplicity
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale) :
    pullback.shading.HasConstantMultiplicity
      (twoScale.first.fourDegreeReceipts.fineDegreeFloor *
        twoScale.first.fourDegreeReceipts.muFine)
      ((twoScale.first.fourDegreeReceipts.regularity *
        twoScale.first.fourDegreeReceipts.fineDegreeFloor) *
          twoScale.first.fourDegreeReceipts.muFine) := by
  intro point hpoint
  have hpostFine : point ∈ pullback.postFirstFineShading.union := by
    rw [← pullback.zeroExtension.union_eq]
    rw [← pullback.postSourceShading_eq]
    exact hpoint
  rcases hpostFine with ⟨fineIndex, hpostFineCarrier⟩
  have hretained : point ∈ pureWZ2Node05RetainedCellRegion rho
      pullback.selectedCells := by
    rw [pullback.postFirstFineShading_eq] at hpostFineCarrier
    exact hpostFineCarrier.2
  have hpostFineMultiplicity :
      pullback.postFirstFineShading.pointMultiplicity point =
        twoScale.first.refinedFineShading.pointMultiplicity point := by
    simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
    congr 1
    apply Finset.filter_congr
    intro index _
    rw [pullback.postFirstFineShading_eq,
      pureWZ2Node05RestrictToCells_carrier]
    exact and_iff_left hretained
  have hrawPoint : point ∈ twoScale.first.refinedFineShading.union :=
    ⟨fineIndex, by
      rw [pullback.postFirstFineShading_eq] at hpostFineCarrier
      exact hpostFineCarrier.1⟩
  have hlower := twoScale.first.fourDegreeReceipts
    |>.fine_pointMultiplicity_floor_on_union hrawPoint
  have hupper := twoScale.first.fourDegreeReceipts
    |>.fine_pointMultiplicity_upper point
  change
    twoScale.first.fourDegreeReceipts.fineDegreeFloor *
          twoScale.first.fourDegreeReceipts.muFine ≤
        pullback.postSourceShading.pointMultiplicity point ∧
      pullback.postSourceShading.pointMultiplicity point ≤
        (twoScale.first.fourDegreeReceipts.regularity *
          twoScale.first.fourDegreeReceipts.fineDegreeFloor) *
            twoScale.first.fourDegreeReceipts.muFine
  rw [pullback.postSourceShading_eq,
    pullback.zeroExtension.pointMultiplicity_eq, hpostFineMultiplicity]
  exact ⟨hlower, by exact_mod_cast hupper⟩

structure PureWZ2Node05V4RichSaturatedSourceCellData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.saturatedGraphScale ≤ 1}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (scheduled : PureWZ2Node05V4RichSaturatedScheduledTheorem52Data
      (eta := eta) neighborhood hbridge hgraphOne projection) where
  graphHeightIndex : Point2 → ℤ := fun point =>
    (scheduled.theorem52.output.lineData.graphCell point).2.2
  graphHeightIndex_eq : ∀ point, graphHeightIndex point =
    (scheduled.theorem52.output.lineData.graphCell point).2.2
  graphHeightIndices : Finset ℤ :=
    scheduled.theorem52.output.lineData.richF.image graphHeightIndex
  graphHeightIndices_eq : graphHeightIndices =
    scheduled.theorem52.output.lineData.richF.image graphHeightIndex
  graphHeightIndices_card : graphHeightIndices.card =
    scheduled.theorem52.output.lineData.richF.card
  graphCells : Finset WZ2PaperCellIndex :=
    scheduled.finite.finiteGraph.graph.residue.cells.filter fun cell =>
      cell.2.2 ∈ graphHeightIndices
  graphCells_eq : graphCells =
    scheduled.finite.finiteGraph.graph.residue.cells.filter fun cell =>
      cell.2.2 ∈ graphHeightIndices
  graphCells_subset :
    graphCells ⊆ scheduled.finite.finiteGraph.graph.residue.cells
  graphCells_nonempty : graphCells.Nonempty
  graphCells_card_retention :
    graphHeightIndices.card *
          scheduled.finite.finiteGraph.graph.residue.cells.card ≤
      scheduled.finite.finiteGraph.graph.residue.heightFiberCost *
        (wz1Lemma23SnappedHeights
          scheduled.finite.finiteGraph.graph.residue.cells).card *
        graphCells.card
  sourceCells : Finset WZ2PaperCellIndex :=
    graphCells.image scheduled.finite.parents.sourceCell
  sourceCells_eq : sourceCells =
    graphCells.image scheduled.finite.parents.sourceCell
  sourceCells_subset_slab : sourceCells ⊆
    pullback.standardSqrtSlabRhoCells neighborhood.heightIndex.1
  graphCell_source_fiber_card : ∀ sourceCell ∈ sourceCells,
    (graphCells.filter fun graphCell =>
      scheduled.finite.parents.sourceCell graphCell = sourceCell).card ≤ 27
  graphCells_card_le_sourceCells : graphCells.card ≤ 27 * sourceCells.card
  sourceCells_nonempty : sourceCells.Nonempty

/-- Complete source-height fibres in the original post-two-call source.

The sparse cells above certify which genuine source height indices occur
behind the selected graph heights.  Here every side-`rho` source cell in the
same retained slab at one of those indices is restored before restricting the
original source shading. -/
structure PureWZ2Node05V4RichSaturatedCompleteHeightData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.saturatedGraphScale ≤ 1}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {scheduled : PureWZ2Node05V4RichSaturatedScheduledTheorem52Data
      (eta := eta) neighborhood hbridge hgraphOne projection}
    (sparse : PureWZ2Node05V4RichSaturatedSourceCellData scheduled) where
  sourceHeightIndices : Finset ℤ := sparse.sourceCells.image fun cell => cell.2.2
  sourceHeightIndices_eq : sourceHeightIndices =
    sparse.sourceCells.image fun cell => cell.2.2
  sourceHeightIndices_nonempty : sourceHeightIndices.Nonempty
  completeSourceCells : Finset WZ2PaperCellIndex :=
    (pullback.standardSqrtSlabRhoCells neighborhood.heightIndex.1).filter
      fun cell => cell.2.2 ∈ sourceHeightIndices
  completeSourceCells_eq : completeSourceCells =
    (pullback.standardSqrtSlabRhoCells neighborhood.heightIndex.1).filter
      fun cell => cell.2.2 ∈ sourceHeightIndices
  sourceCells_subset_complete : sparse.sourceCells ⊆ completeSourceCells
  completeSourceCells_subset_slab : completeSourceCells ⊆
    pullback.standardSqrtSlabRhoCells neighborhood.heightIndex.1
  completeSourceCells_subset_selected : completeSourceCells ⊆ pullback.selectedCells
  completeSourceCells_nonempty : completeSourceCells.Nonempty
  graphCells_card_le_completeSourceCells :
    sparse.graphCells.card ≤ 27 * completeSourceCells.card
  source_height_close : ∀ cell ∈ completeSourceCells,
    ∀ point ∈ wz1PaperGridCube rho cell,
      ∃ richPoint ∈ scheduled.theorem52.output.lineData.richF,
        |point (2 : Fin 3) -
            scheduled.theorem52.output.lineData.sourceHeight richPoint| <
          rho + neighborhood.graphScale / 2
  sourceRestriction : WZ1PaperTubeShading current.grain.family :=
    pureWZ2Node05RestrictToCells (rho := rho) pullback.shading completeSourceCells
  sourceRestriction_eq : sourceRestriction =
    pureWZ2Node05RestrictToCells (rho := rho) pullback.shading completeSourceCells
  sourceRestriction_sub_source :
    PureWZ2PaperIsSubshading sourceRestriction current.grain.shading
  sourceRestriction_whole_delta_cells :
    WZ1PaperIsCubicalShading sourceRestriction
  sourceRestriction_union_eq : sourceRestriction.union =
    pullback.selectedRhoCellsSourceRegion completeSourceCells
  sourceRestriction_height_window : ∀ point ∈ sourceRestriction.union,
    point (2 : Fin 3) ∈
      Set.Ico
        ((neighborhood.heightIndex.1 : ℝ) * Real.sqrt rho)
        ((neighborhood.heightIndex.1 : ℝ) * Real.sqrt rho + Real.sqrt rho)
  sourceRestriction_slope_approximation : ∀ point ∈ sourceRestriction.union,
    |current.grain.globalGrains.slope (point (2 : Fin 3)) -
        scheduled.theorem52.output.lineData.L_S (point (2 : Fin 3))| ≤
      5 * neighborhood.graphScale
  sourceRestriction_volume_eq :
    volume sourceRestriction.union =
      (completeSourceCells.card : ENNReal) *
        pullback.firstPostBalanced.cellMass
  sourceRestriction_mass_eq :
    sourceRestriction.mass =
      ∑ cell ∈ completeSourceCells,
        wz2PaperCellIncidenceMass
          (rho := rho) pullback.shading cell
  multiplicityFloor : ℕ :=
    twoScale.first.fourDegreeReceipts.fineDegreeFloor *
      twoScale.first.fourDegreeReceipts.muFine
  multiplicityFloor_eq : multiplicityFloor =
    twoScale.first.fourDegreeReceipts.fineDegreeFloor *
      twoScale.first.fourDegreeReceipts.muFine
  multiplicityCeiling : ℕ :=
    (twoScale.first.fourDegreeReceipts.regularity *
      twoScale.first.fourDegreeReceipts.fineDegreeFloor) *
        twoScale.first.fourDegreeReceipts.muFine
  multiplicityCeiling_eq : multiplicityCeiling =
    (twoScale.first.fourDegreeReceipts.regularity *
      twoScale.first.fourDegreeReceipts.fineDegreeFloor) *
        twoScale.first.fourDegreeReceipts.muFine
  sourceRestriction_constantMultiplicity :
    sourceRestriction.HasConstantMultiplicity
      multiplicityFloor multiplicityCeiling
  sourceRestriction_mass_lower :
    (multiplicityFloor : ENNReal) * volume sourceRestriction.union ≤
      sourceRestriction.mass
  sourceRestriction_mass_upper :
    sourceRestriction.mass ≤
      (multiplicityCeiling : ENNReal) * volume sourceRestriction.union

namespace PureWZ2Node05V4RichSaturatedScheduledTheorem52Data

/-- Pull every graph cell on a selected Theorem-5.2 height back to the genuine
side-`rho` cell containing its stored same-height source witness. -/
theorem sourceCells
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.saturatedGraphScale ≤ 1}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (scheduled : PureWZ2Node05V4RichSaturatedScheduledTheorem52Data
      (eta := eta) neighborhood hbridge hgraphOne projection) :
    Nonempty (PureWZ2Node05V4RichSaturatedSourceCellData scheduled) := by
  let output := scheduled.theorem52.output
  let provenance := scheduled.theorem52.provenance
  let graphHeightIndex : Point2 → ℤ := fun point =>
    (output.lineData.graphCell point).2.2
  let graphHeightIndices := output.lineData.richF.image graphHeightIndex
  have hheightInjective : Set.InjOn graphHeightIndex output.lineData.richF := by
    intro first hfirst second hsecond heq
    apply output.lineData.sourceHeight_injective hfirst hsecond
    rw [output.lineData.sourceHeight_eq, output.lineData.sourceHeight_eq]
    simp [wz1Lemma23SnappedPoint, wz1Lemma23CellCenter, point3,
      graphHeightIndex, heq]
  have hheightCard : graphHeightIndices.card = output.lineData.richF.card :=
    Finset.card_image_of_injOn hheightInjective
  let graphCells := scheduled.finite.finiteGraph.graph.residue.cells.filter
    fun cell => cell.2.2 ∈ graphHeightIndices
  have hgraphSubset : graphCells ⊆
      scheduled.finite.finiteGraph.graph.residue.cells :=
    Finset.filter_subset _ _
  have hrichGraphCell : ∀ point (hpoint : point ∈ output.lineData.richF),
      output.lineData.graphCell point ∈ graphCells := by
    intro point hpoint
    apply Finset.mem_filter.mpr
    refine ⟨output.lineData.graphCell_mem_residue point hpoint, ?_⟩
    exact Finset.mem_image.mpr ⟨point, hpoint, rfl⟩
  have hgraphNonempty : graphCells.Nonempty := by
    rcases output.lineData.richF_nonempty with ⟨point, hpoint⟩
    exact ⟨output.lineData.graphCell point, hrichGraphCell point hpoint⟩
  have hheightSubset : graphHeightIndices ⊆
      wz1Lemma23SnappedHeights
        scheduled.finite.finiteGraph.graph.residue.cells := by
    intro height hheight
    rcases Finset.mem_image.mp hheight with ⟨point, hpoint, rfl⟩
    exact Finset.mem_image.mpr
      ⟨output.lineData.graphCell point,
        output.lineData.graphCell_mem_residue point hpoint, rfl⟩
  have hgraphCardRetention :
      graphHeightIndices.card *
            scheduled.finite.finiteGraph.graph.residue.cells.card ≤
        scheduled.finite.finiteGraph.graph.residue.heightFiberCost *
          (wz1Lemma23SnappedHeights
            scheduled.finite.finiteGraph.graph.residue.cells).card *
          graphCells.card :=
    finset_selected_fibers_card_lower
      scheduled.finite.finiteGraph.graph.residue.cells
      (fun cell => cell.2.2) graphHeightIndices hheightSubset
      scheduled.finite.finiteGraph.graph.residue.heightFiberCost
      scheduled.finite.finiteGraph.graph.residue.height_uniform
  let sourceCells := graphCells.image scheduled.finite.parents.sourceCell
  have hsourceSubset : sourceCells ⊆
      pullback.standardSqrtSlabRhoCells neighborhood.heightIndex.1 := by
    intro sourceCell hsourceCell
    rcases Finset.mem_image.mp hsourceCell with ⟨graphCell, hgraphCell, rfl⟩
    have hgraphGlobal :=
      scheduled.finite.finiteGraph.graph.residue.cells_subset
        (hgraphSubset hgraphCell)
    have hparent := scheduled.finite.parents.sourceCell_mem_parent
      graphCell hgraphGlobal
    have hparentData := Finset.mem_filter.mp hparent
    apply pullback.mem_standardSqrtSlabRhoCells.mpr
    refine ⟨hparentData.1, ?_⟩
    unfold PureWZ2Node05V4RichTwoScaleCellPullbackData.standardSqrtSlabIndex
    rw [hparentData.2]
    exact pullback.standardSqrtSlabParent_height
      (neighborhood.cube_mem
        (scheduled.finite.parents.parentY graphCell)
        (scheduled.finite.parents.parentY_mem graphCell hgraphGlobal))
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hgraphMesh : 5 * rho < gridSide (neighborhood.graphScale / 2) := by
    rw [show gridSide (neighborhood.graphScale / 2) =
      neighborhood.graphScale / Real.sqrt 3 by simp [gridSide]; ring]
    dsimp only [PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
      PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]
    have hsqrt3 : Real.sqrt (3 : ℝ) < 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
        Real.sqrt_nonneg (3 : ℝ)]
    rw [lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num))]
    nlinarith
  have hsourceFiber : ∀ sourceCell ∈ sourceCells,
      (graphCells.filter fun graphCell =>
        scheduled.finite.parents.sourceCell graphCell = sourceCell).card ≤ 27 := by
    intro sourceCell hsourceCell
    rcases Finset.mem_image.mp hsourceCell with
      ⟨baseCell, hbaseCell, hbaseSourceCell⟩
    let fiber := graphCells.filter fun graphCell =>
      scheduled.finite.parents.sourceCell graphCell = sourceCell
    let allowed : Finset WZ2PaperCellIndex :=
      (Finset.Icc (baseCell.1 - 1) (baseCell.1 + 1)).product
        ((Finset.Icc (baseCell.2.1 - 1) (baseCell.2.1 + 1)).product
          (Finset.Icc (baseCell.2.2 - 1) (baseCell.2.2 + 1)))
    have hfiberSubset : fiber ⊆ allowed := by
      intro graphCell hgraphCellFiber
      have hgraphCellData := Finset.mem_filter.mp hgraphCellFiber
      have hgraphCell := hgraphCellData.1
      have hgraphGlobal :=
        scheduled.finite.finiteGraph.graph.residue.cells_subset
          (hgraphSubset hgraphCell)
      have hbaseGlobal :=
        scheduled.finite.finiteGraph.graph.residue.cells_subset
          (hgraphSubset hbaseCell)
      have hsourceCellEq :
          scheduled.finite.parents.sourceCell graphCell =
            scheduled.finite.parents.sourceCell baseCell :=
        hgraphCellData.2.trans hbaseSourceCell.symm
      have hgraphSource :=
        scheduled.finite.parents.sourceWitness_mem_sourceCell
          graphCell hgraphGlobal
      have hbaseSource :=
        scheduled.finite.parents.sourceWitness_mem_sourceCell
          baseCell hbaseGlobal
      rw [hsourceCellEq] at hgraphSource
      have hcoordClose : ∀ coordinate : Fin 3,
          |scheduled.finite.parents.representative graphCell coordinate -
            scheduled.finite.parents.representative baseCell coordinate| <
              gridSide (neighborhood.graphScale / 2) := by
        intro coordinate
        have hfirst :
            |scheduled.finite.parents.representative graphCell coordinate -
              scheduled.finite.parents.sourceWitness graphCell coordinate| ≤
                2 * rho :=
          (PiLp.dist_apply_le _ _ coordinate).trans
            (scheduled.finite.parents.representative_source_dist
              graphCell hgraphGlobal)
        have hlast :
            |scheduled.finite.parents.sourceWitness baseCell coordinate -
              scheduled.finite.parents.representative baseCell coordinate| ≤
                2 * rho :=
          by
            simpa only [Real.dist_eq, abs_sub_comm] using
              (PiLp.dist_apply_le
                  (scheduled.finite.parents.representative baseCell)
                  (scheduled.finite.parents.sourceWitness baseCell) coordinate).trans
                (scheduled.finite.parents.representative_source_dist
                  baseCell hbaseGlobal)
        have hmiddle :
            |scheduled.finite.parents.sourceWitness graphCell coordinate -
              scheduled.finite.parents.sourceWitness baseCell coordinate| <
                rho := by
          rw [wz1PaperGridCube_eq_Ico hrho] at hgraphSource hbaseSource
          fin_cases coordinate
          · exact saturated_abs_sub_lt_of_common_interval
              ⟨hgraphSource.1, hgraphSource.2.1⟩
              ⟨hbaseSource.1, hbaseSource.2.1⟩
          · exact saturated_abs_sub_lt_of_common_interval
              ⟨hgraphSource.2.2.1, hgraphSource.2.2.2.1⟩
              ⟨hbaseSource.2.2.1, hbaseSource.2.2.2.1⟩
          · exact saturated_abs_sub_lt_of_common_interval
              ⟨hgraphSource.2.2.2.2.1, hgraphSource.2.2.2.2.2⟩
              ⟨hbaseSource.2.2.2.2.1, hbaseSource.2.2.2.2.2⟩
        have htriangle :
            |scheduled.finite.parents.representative graphCell coordinate -
                scheduled.finite.parents.representative baseCell coordinate| ≤
              |scheduled.finite.parents.representative graphCell coordinate -
                scheduled.finite.parents.sourceWitness graphCell coordinate| +
              |scheduled.finite.parents.sourceWitness graphCell coordinate -
                scheduled.finite.parents.sourceWitness baseCell coordinate| +
              |scheduled.finite.parents.sourceWitness baseCell coordinate -
                scheduled.finite.parents.representative baseCell coordinate| := by
          calc
            _ = |(scheduled.finite.parents.representative graphCell coordinate -
                    scheduled.finite.parents.sourceWitness graphCell coordinate) +
                  (scheduled.finite.parents.sourceWitness graphCell coordinate -
                    scheduled.finite.parents.sourceWitness baseCell coordinate) +
                  (scheduled.finite.parents.sourceWitness baseCell coordinate -
                    scheduled.finite.parents.representative baseCell coordinate)| := by
                      ring_nf
            _ ≤ _ := abs_add_three _ _ _
        exact (htriangle.trans_lt (by linarith)).trans hgraphMesh
      have hgraphIndex := scheduled.finite.parents.representative_index
        graphCell hgraphGlobal
      have hbaseIndex := scheduled.finite.parents.representative_index
        baseCell hbaseGlobal
      have hgraphIndex0 :
          ⌊scheduled.finite.parents.representative graphCell 0 /
              gridSide (neighborhood.graphScale / 2)⌋ = graphCell.1 := by
        simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
          congrArg Prod.fst hgraphIndex
      have hgraphIndex1 :
          ⌊scheduled.finite.parents.representative graphCell 1 /
              gridSide (neighborhood.graphScale / 2)⌋ = graphCell.2.1 := by
        simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
          congrArg (fun index : WZ2PaperCellIndex => index.2.1) hgraphIndex
      have hgraphIndex2 :
          ⌊scheduled.finite.parents.representative graphCell 2 /
              gridSide (neighborhood.graphScale / 2)⌋ = graphCell.2.2 := by
        simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
          congrArg (fun index : WZ2PaperCellIndex => index.2.2) hgraphIndex
      have hbaseIndex0 :
          ⌊scheduled.finite.parents.representative baseCell 0 /
              gridSide (neighborhood.graphScale / 2)⌋ = baseCell.1 := by
        simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
          congrArg Prod.fst hbaseIndex
      have hbaseIndex1 :
          ⌊scheduled.finite.parents.representative baseCell 1 /
              gridSide (neighborhood.graphScale / 2)⌋ = baseCell.2.1 := by
        simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
          congrArg (fun index : WZ2PaperCellIndex => index.2.1) hbaseIndex
      have hbaseIndex2 :
          ⌊scheduled.finite.parents.representative baseCell 2 /
              gridSide (neighborhood.graphScale / 2)⌋ = baseCell.2.2 := by
        simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
          congrArg (fun index : WZ2PaperCellIndex => index.2.2) hbaseIndex
      have hindexClose : ∀ coordinate : Fin 3,
          |(match coordinate with
              | 0 => graphCell.1
              | 1 => graphCell.2.1
              | 2 => graphCell.2.2) -
            (match coordinate with
              | 0 => baseCell.1
              | 1 => baseCell.2.1
              | 2 => baseCell.2.2)| ≤ 1 := by
        intro coordinate
        have hmeshPos : 0 < gridSide (neighborhood.graphScale / 2) := by
          exact div_pos
            (mul_pos (by norm_num) (half_pos neighborhood.graphScale_pos))
            (Real.sqrt_pos.mpr (by norm_num))
        have hratio :
            |scheduled.finite.parents.representative graphCell coordinate /
                  gridSide (neighborhood.graphScale / 2) -
              scheduled.finite.parents.representative baseCell coordinate /
                  gridSide (neighborhood.graphScale / 2)| < 1 := by
          rw [← sub_div, abs_div, abs_of_pos hmeshPos]
          exact (div_lt_one hmeshPos).2 (hcoordClose coordinate)
        have hratio' :
            |scheduled.finite.parents.representative graphCell coordinate /
                  gridSide (neighborhood.graphScale / 2) -
              scheduled.finite.parents.representative baseCell coordinate /
                  gridSide (neighborhood.graphScale / 2)| < (1 : ℝ) :=
          hratio
        have hfloor :
            |⌊scheduled.finite.parents.representative graphCell coordinate /
                  gridSide (neighborhood.graphScale / 2)⌋ -
              ⌊scheduled.finite.parents.representative baseCell coordinate /
                  gridSide (neighborhood.graphScale / 2)⌋| ≤ (1 : ℤ) :=
          wz1_abs_floor_sub_lt_le
          (x := scheduled.finite.parents.representative graphCell coordinate /
            gridSide (neighborhood.graphScale / 2))
          (y := scheduled.finite.parents.representative baseCell coordinate /
            gridSide (neighborhood.graphScale / 2))
          (N := (1 : ℕ)) (by norm_num) (by simpa using hratio')
        fin_cases coordinate
        · simpa [hgraphIndex0, hbaseIndex0] using hfloor
        · simpa [hgraphIndex1, hbaseIndex1] using hfloor
        · simpa [hgraphIndex2, hbaseIndex2] using hfloor
      have hx := abs_le.mp (by simpa using hindexClose (0 : Fin 3))
      have hy := abs_le.mp (by simpa using hindexClose (1 : Fin 3))
      have hz := abs_le.mp (by simpa using hindexClose (2 : Fin 3))
      dsimp only [allowed]
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_Icc.mpr (by omega), ?_⟩
      apply Finset.mem_product.mpr
      exact ⟨Finset.mem_Icc.mpr (by omega), Finset.mem_Icc.mpr (by omega)⟩
    calc
      fiber.card ≤ allowed.card := Finset.card_le_card hfiberSubset
      _ = 27 := by
        have hcardThree (index : ℤ) :
            (Finset.Icc (index - 1) (index + 1)).card = 3 := by
          simp [Int.card_Icc]
          omega
        simp [allowed, hcardThree]
  have hgraphSourceCard : graphCells.card ≤ 27 * sourceCells.card :=
    Finset.card_le_mul_card_image graphCells 27 hsourceFiber
  exact ⟨{
    graphHeightIndex := graphHeightIndex
    graphHeightIndex_eq := fun _ => rfl
    graphHeightIndices := graphHeightIndices
    graphHeightIndices_eq := rfl
    graphHeightIndices_card := hheightCard
    graphCells := graphCells
    graphCells_eq := rfl
    graphCells_subset := hgraphSubset
    graphCells_nonempty := hgraphNonempty
    graphCells_card_retention := hgraphCardRetention
    sourceCells := sourceCells
    sourceCells_eq := rfl
    sourceCells_subset_slab := hsourceSubset
    graphCell_source_fiber_card := hsourceFiber
    graphCells_card_le_sourceCells := hgraphSourceCard
    sourceCells_nonempty := hgraphNonempty.image
      scheduled.finite.parents.sourceCell
  }⟩

/-- Restore the complete side-`rho` source-height fibres selected by the
Theorem-5.2 graph output, and restrict the literal post-two-call source to
those cells. -/
theorem completeSourceHeights
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.saturatedGraphScale ≤ 1}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {scheduled : PureWZ2Node05V4RichSaturatedScheduledTheorem52Data
      (eta := eta) neighborhood hbridge hgraphOne projection}
    (sparse : PureWZ2Node05V4RichSaturatedSourceCellData scheduled) :
    Nonempty (PureWZ2Node05V4RichSaturatedCompleteHeightData sparse) := by
  let sourceHeightIndices := sparse.sourceCells.image fun cell => cell.2.2
  have hheightNonempty : sourceHeightIndices.Nonempty :=
    sparse.sourceCells_nonempty.image fun cell => cell.2.2
  let completeSourceCells :=
    (pullback.standardSqrtSlabRhoCells neighborhood.heightIndex.1).filter
      fun cell => cell.2.2 ∈ sourceHeightIndices
  have hsourceComplete : sparse.sourceCells ⊆ completeSourceCells := by
    intro cell hcell
    apply Finset.mem_filter.mpr
    exact ⟨sparse.sourceCells_subset_slab hcell,
      Finset.mem_image.mpr ⟨cell, hcell, rfl⟩⟩
  have hcompleteSlab : completeSourceCells ⊆
      pullback.standardSqrtSlabRhoCells neighborhood.heightIndex.1 :=
    Finset.filter_subset _ _
  have hcompleteSelected : completeSourceCells ⊆ pullback.selectedCells :=
    hcompleteSlab.trans
      (pullback.standardSqrtSlabRhoCells_subset neighborhood.heightIndex.1)
  have hcompleteNonempty : completeSourceCells.Nonempty :=
    sparse.sourceCells_nonempty.mono hsourceComplete
  have hsourceCard : sparse.sourceCells.card ≤ completeSourceCells.card :=
    Finset.card_le_card hsourceComplete
  have hgraphComplete : sparse.graphCells.card ≤
      27 * completeSourceCells.card :=
    sparse.graphCells_card_le_sourceCells.trans
      (Nat.mul_le_mul_left 27 hsourceCard)
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hsourceHeightClose : ∀ cell ∈ completeSourceCells,
      ∀ point ∈ wz1PaperGridCube rho cell,
        ∃ richPoint ∈ scheduled.theorem52.output.lineData.richF,
          |point (2 : Fin 3) -
              scheduled.theorem52.output.lineData.sourceHeight richPoint| <
            rho + neighborhood.graphScale / 2 := by
    intro cell hcell point hpointCell
    have hheightMem : cell.2.2 ∈ sourceHeightIndices :=
      (Finset.mem_filter.mp hcell).2
    rcases Finset.mem_image.mp hheightMem with
      ⟨sourceCell, hsourceCell, hsourceHeight⟩
    rw [sparse.sourceCells_eq] at hsourceCell
    rcases Finset.mem_image.mp hsourceCell with
      ⟨graphCell, hgraphCell, hsourceCellEq⟩
    have hgraphCellData := Finset.mem_filter.mp (by
      rw [sparse.graphCells_eq] at hgraphCell
      exact hgraphCell)
    have hgraphHeightMem : graphCell.2.2 ∈ sparse.graphHeightIndices :=
      hgraphCellData.2
    rw [sparse.graphHeightIndices_eq] at hgraphHeightMem
    rcases Finset.mem_image.mp hgraphHeightMem with
      ⟨richPoint, hrichPoint, hgraphHeight⟩
    refine ⟨richPoint, hrichPoint, ?_⟩
    have hgraphGlobal :=
      scheduled.finite.finiteGraph.graph.residue.cells_subset
        (sparse.graphCells_subset hgraphCell)
    have hsourceWitnessCell :=
      scheduled.finite.parents.sourceWitness_mem_sourceCell
        graphCell hgraphGlobal
    have hsourceCellIndex :
        scheduled.finite.parents.sourceCell graphCell = sourceCell :=
      hsourceCellEq
    rw [hsourceCellIndex] at hsourceWitnessCell
    have hcellIndex : cell.2.2 = sourceCell.2.2 := hsourceHeight.symm
    have hpointInterval := hpointCell
    have hwitnessInterval := hsourceWitnessCell
    rw [wz1PaperGridCube_eq_Ico hrho] at hpointInterval hwitnessInterval
    have hpointWitness :
        |point (2 : Fin 3) -
            scheduled.finite.parents.sourceWitness graphCell (2 : Fin 3)| < rho := by
      apply saturated_abs_sub_lt_of_common_interval
      · exact ⟨by simpa [hcellIndex] using hpointInterval.2.2.2.2.1,
          by simpa [hcellIndex] using hpointInterval.2.2.2.2.2⟩
      · exact ⟨hwitnessInterval.2.2.2.2.1,
          hwitnessInterval.2.2.2.2.2⟩
    have hrepresentativeCenter :=
      ((wz1_lemma23_snapped_cell_geometry neighborhood.graphScale
        neighborhood.graphScale_pos hgraphOne).2.1
        graphCell (scheduled.finite.parents.representative graphCell)
        (scheduled.finite.parents.representative_index
          graphCell hgraphGlobal)).1 (2 : Fin 3)
    have hsourceRepresentative :
        scheduled.finite.parents.sourceWitness graphCell (2 : Fin 3) =
          scheduled.finite.parents.representative graphCell (2 : Fin 3) :=
      scheduled.finite.parents.sourceWitness_height graphCell hgraphGlobal
    have hcenterEq :
        (wz1Lemma23CellCenter neighborhood.graphScale graphCell) (2 : Fin 3) =
          scheduled.theorem52.output.lineData.sourceHeight richPoint := by
      rw [sparse.graphHeightIndex_eq richPoint] at hgraphHeight
      rw [scheduled.theorem52.output.lineData.sourceHeight_eq richPoint]
      simp [wz1Lemma23SnappedPoint, wz1Lemma23CellCenter, point3,
        hgraphHeight.symm]
    have hpointRepresentative :
        |point (2 : Fin 3) -
            scheduled.finite.parents.representative graphCell (2 : Fin 3)| <
          rho := by
      rw [← hsourceRepresentative]
      exact hpointWitness
    calc
      |point (2 : Fin 3) -
          scheduled.theorem52.output.lineData.sourceHeight richPoint| ≤
        |point (2 : Fin 3) -
            scheduled.finite.parents.sourceWitness graphCell (2 : Fin 3)| +
          |scheduled.finite.parents.sourceWitness graphCell (2 : Fin 3) -
            scheduled.theorem52.output.lineData.sourceHeight richPoint| :=
        abs_sub_le _ _ _
      _ < rho + neighborhood.graphScale / 2 := by
        rw [hsourceRepresentative, ← hcenterEq]
        exact add_lt_add_of_lt_of_le hpointRepresentative hrepresentativeCenter
  let sourceRestriction :=
    pureWZ2Node05RestrictToCells (rho := rho)
      pullback.shading completeSourceCells
  have hsourceSub : PureWZ2PaperIsSubshading
      sourceRestriction current.grain.shading := by
    intro source point hpoint
    exact pullback.subshading source hpoint.1
  have hsourceWhole : WZ1PaperIsCubicalShading sourceRestriction := by
    intro source point hpoint other hother
    have hotherSource := pullback.whole_cells source point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨retainedCell, hretainedCell, hpointRetained⟩
    rcases pullback.source_fine_cell_nested source point hpoint.1 with
      ⟨sourceCell, _hsourceCell, hnested⟩
    have hpointFine :
        point ∈ wz1PaperGridCube delta (wz1PaperGridIndex delta point) :=
      (mem_wz1PaperGridCube delta _ point).mpr rfl
    have hpointSourceCell := hnested hpointFine
    have hcellEq : sourceCell = retainedCell :=
      ((mem_wz1PaperGridCube rho sourceCell point).mp hpointSourceCell).symm.trans
        ((mem_wz1PaperGridCube rho retainedCell point).mp hpointRetained)
    have hotherRetained : other ∈ wz1PaperGridCube rho retainedCell := by
      rw [← hcellEq]
      exact hnested hother
    exact ⟨hotherSource, Set.mem_iUnion₂.mpr
      ⟨retainedCell, hretainedCell, hotherRetained⟩⟩
  have hsourceUnion : sourceRestriction.union =
      pullback.selectedRhoCellsSourceRegion completeSourceCells := by
    exact pureWZ2Node05RestrictToCells_union
      pullback.shading completeSourceCells
  have hsourceHeightWindow : ∀ point ∈ sourceRestriction.union,
      point (2 : Fin 3) ∈
        Set.Ico
          ((neighborhood.heightIndex.1 : ℝ) * Real.sqrt rho)
          ((neighborhood.heightIndex.1 : ℝ) * Real.sqrt rho + Real.sqrt rho) := by
    intro point hpoint
    rw [hsourceUnion] at hpoint
    exact pullback.standardSqrtSlabSourceRegion_height
      ⟨hpoint.1, by
        rcases Set.mem_iUnion₂.mp hpoint.2 with
          ⟨cell, hcell, hpointCell⟩
        exact Set.mem_iUnion₂.mpr
          ⟨cell, hcompleteSlab hcell, hpointCell⟩⟩
  have hsourceApprox : ∀ point ∈ sourceRestriction.union,
      |current.grain.globalGrains.slope (point (2 : Fin 3)) -
          scheduled.theorem52.output.lineData.L_S (point (2 : Fin 3))| ≤
        5 * neighborhood.graphScale := by
    intro point hpoint
    have hregion : point ∈ pureWZ2Node05RetainedCellRegion
        rho completeSourceCells := by
      rw [hsourceUnion] at hpoint
      exact hpoint.2
    rcases Set.mem_iUnion₂.mp hregion with
      ⟨cell, hcell, hpointCell⟩
    rcases hsourceHeightClose cell hcell point hpointCell with
      ⟨richPoint, hrichPoint, hheightClose⟩
    let graphHeight :=
      scheduled.theorem52.output.lineData.sourceHeight richPoint
    have hheightCloseLe :
        |point (2 : Fin 3) - graphHeight| ≤
          rho + neighborhood.graphScale / 2 :=
      le_of_lt hheightClose
    have hslopeLip :
        |scheduled.finite.prep.windowed.global.extendedSlope
              (point (2 : Fin 3)) -
            scheduled.finite.prep.windowed.global.extendedSlope graphHeight| ≤
          |point (2 : Fin 3) - graphHeight| := by
      simpa [Real.dist_eq] using
        scheduled.finite.prep.windowed.global.extendedSlope_lipschitz.dist_le_mul
          (point (2 : Fin 3)) (by simp) graphHeight (by simp)
    have hlineLip :
        |scheduled.theorem52.output.lineData.L_S graphHeight -
            scheduled.theorem52.output.lineData.L_S (point (2 : Fin 3))| ≤
          2 * |point (2 : Fin 3) - graphHeight| := by
      rw [scheduled.theorem52.output.lineData.L_S_eq]
      have heq :
          scheduled.theorem52.output.lineData.L_S_slope * graphHeight +
                scheduled.theorem52.output.lineData.L_S_intercept -
              (scheduled.theorem52.output.lineData.L_S_slope *
                  point (2 : Fin 3) +
                scheduled.theorem52.output.lineData.L_S_intercept) =
            scheduled.theorem52.output.lineData.L_S_slope *
              (graphHeight - point (2 : Fin 3)) := by ring
      rw [heq, abs_mul, abs_sub_comm]
      exact mul_le_mul
        scheduled.theorem52.output.lineData.L_S_slope_bound le_rfl
        (abs_nonneg _) (by norm_num)
    have hsharp := scheduled.theorem52.output.lineData.L_S_approximation_sharp
      richPoint hrichPoint
    have hpointSource : point ∈ current.grain.shading.union :=
      hsourceSub.union_subset hpoint
    have hbox := shading_union_subset_axisBox hpointSource
    have hheightDomain : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
    have hslopeEq :
        scheduled.finite.prep.windowed.global.extendedSlope
            (point (2 : Fin 3)) =
          current.grain.globalGrains.slope (point (2 : Fin 3)) := by
      rw [scheduled.finite.prep.windowed.global.extendedSlope_eq
        (point (2 : Fin 3)) hheightDomain, scheduled.finite.prep.sourceSlope_eq]
      rfl
    rw [← hslopeEq]
    have htriangle :
        |scheduled.finite.prep.windowed.global.extendedSlope
              (point (2 : Fin 3)) -
            scheduled.theorem52.output.lineData.L_S (point (2 : Fin 3))| ≤
          |scheduled.finite.prep.windowed.global.extendedSlope
              (point (2 : Fin 3)) -
            scheduled.finite.prep.windowed.global.extendedSlope graphHeight| +
          |scheduled.finite.prep.windowed.global.extendedSlope graphHeight -
            scheduled.theorem52.output.lineData.L_S graphHeight| +
          |scheduled.theorem52.output.lineData.L_S graphHeight -
            scheduled.theorem52.output.lineData.L_S (point (2 : Fin 3))| := by
      calc
        _ ≤ |scheduled.finite.prep.windowed.global.extendedSlope
                (point (2 : Fin 3)) -
              scheduled.finite.prep.windowed.global.extendedSlope graphHeight| +
            |scheduled.finite.prep.windowed.global.extendedSlope graphHeight -
              scheduled.theorem52.output.lineData.L_S (point (2 : Fin 3))| :=
          abs_sub_le _ _ _
        _ ≤ _ := by
          have hsecond :
              |scheduled.finite.prep.windowed.global.extendedSlope graphHeight -
                  scheduled.theorem52.output.lineData.L_S
                    (point (2 : Fin 3))| ≤
                |scheduled.finite.prep.windowed.global.extendedSlope graphHeight -
                  scheduled.theorem52.output.lineData.L_S graphHeight| +
                |scheduled.theorem52.output.lineData.L_S graphHeight -
                  scheduled.theorem52.output.lineData.L_S
                    (point (2 : Fin 3))| :=
            abs_sub_le _ _ _
          calc
            _ ≤ |scheduled.finite.prep.windowed.global.extendedSlope
                    (point (2 : Fin 3)) -
                  scheduled.finite.prep.windowed.global.extendedSlope graphHeight| +
                (|scheduled.finite.prep.windowed.global.extendedSlope graphHeight -
                    scheduled.theorem52.output.lineData.L_S graphHeight| +
                  |scheduled.theorem52.output.lineData.L_S graphHeight -
                    scheduled.theorem52.output.lineData.L_S
                      (point (2 : Fin 3))|) :=
              by linarith
            _ = _ := by ring
    calc
      _ ≤ |scheduled.finite.prep.windowed.global.extendedSlope
              (point (2 : Fin 3)) -
            scheduled.finite.prep.windowed.global.extendedSlope graphHeight| +
          |scheduled.finite.prep.windowed.global.extendedSlope graphHeight -
            scheduled.theorem52.output.lineData.L_S graphHeight| +
          |scheduled.theorem52.output.lineData.L_S graphHeight -
            scheduled.theorem52.output.lineData.L_S (point (2 : Fin 3))| :=
        htriangle
      _ ≤ |point (2 : Fin 3) - graphHeight| +
          3 * neighborhood.graphScale +
          2 * |point (2 : Fin 3) - graphHeight| := by
        exact add_le_add (add_le_add hslopeLip hsharp) hlineLip
      _ ≤ (rho + neighborhood.graphScale / 2) +
          3 * neighborhood.graphScale +
          2 * (rho + neighborhood.graphScale / 2) := by gcongr
      _ ≤ 5 * neighborhood.graphScale := by
        dsimp only [PureWZ2PreCommonBinGlobalGrainNeighborhoodData.graphScale,
          PureWZ2PreCommonBinGlobalGrainNeighborhoodData.saturatedGraphScale]
        nlinarith [hrho]
  have hsourceVolume : volume sourceRestriction.union =
      (completeSourceCells.card : ENNReal) *
        pullback.firstPostBalanced.cellMass := by
    rw [hsourceUnion]
    exact pullback.selectedRhoCellsSourceRegion_volume
      completeSourceCells hcompleteSelected
  have hsourceMass : sourceRestriction.mass =
      ∑ cell ∈ completeSourceCells,
        wz2PaperCellIncidenceMass (rho := rho) pullback.shading cell := by
    exact saturated_restrictToCells_mass_eq_sum_cells
      pullback.shading completeSourceCells
  let multiplicityFloor : ℕ :=
    twoScale.first.fourDegreeReceipts.fineDegreeFloor *
      twoScale.first.fourDegreeReceipts.muFine
  let multiplicityCeiling : ℕ :=
    (twoScale.first.fourDegreeReceipts.regularity *
      twoScale.first.fourDegreeReceipts.fineDegreeFloor) *
        twoScale.first.fourDegreeReceipts.muFine
  have hpullbackConstant : pullback.shading.HasConstantMultiplicity
      multiplicityFloor multiplicityCeiling := by
    simpa [multiplicityFloor, multiplicityCeiling] using
      pullback.source_constantMultiplicity
  have hsourceConstant : sourceRestriction.HasConstantMultiplicity
      multiplicityFloor multiplicityCeiling :=
    pureWZ2Node05RestrictToCells_constantMultiplicity hpullbackConstant
  have hmassLower : (multiplicityFloor : ENNReal) *
      volume sourceRestriction.union ≤ sourceRestriction.mass :=
    multiplicity_floor_le_mass fun point hpoint =>
      by exact_mod_cast (hsourceConstant point hpoint).1
  have hmassUpper : sourceRestriction.mass ≤
      (multiplicityCeiling : ENNReal) * volume sourceRestriction.union :=
    mass_le_of_pointMultiplicity_le fun point hpoint =>
      by exact_mod_cast (hsourceConstant point hpoint).2
  exact ⟨{
    sourceHeightIndices := sourceHeightIndices
    sourceHeightIndices_eq := rfl
    sourceHeightIndices_nonempty := hheightNonempty
    completeSourceCells := completeSourceCells
    completeSourceCells_eq := rfl
    sourceCells_subset_complete := hsourceComplete
    completeSourceCells_subset_slab := hcompleteSlab
    completeSourceCells_subset_selected := hcompleteSelected
    completeSourceCells_nonempty := hcompleteNonempty
    graphCells_card_le_completeSourceCells := hgraphComplete
    source_height_close := hsourceHeightClose
    sourceRestriction := sourceRestriction
    sourceRestriction_eq := rfl
    sourceRestriction_sub_source := hsourceSub
    sourceRestriction_whole_delta_cells := hsourceWhole
    sourceRestriction_union_eq := hsourceUnion
    sourceRestriction_height_window := hsourceHeightWindow
    sourceRestriction_slope_approximation := hsourceApprox
    sourceRestriction_volume_eq := hsourceVolume
    sourceRestriction_mass_eq := hsourceMass
    multiplicityFloor := multiplicityFloor
    multiplicityFloor_eq := rfl
    multiplicityCeiling := multiplicityCeiling
    multiplicityCeiling_eq := rfl
    sourceRestriction_constantMultiplicity := hsourceConstant
    sourceRestriction_mass_lower := hmassLower
    sourceRestriction_mass_upper := hmassUpper
  }⟩

end PureWZ2Node05V4RichSaturatedScheduledTheorem52Data

namespace PureWZ2Node05V4RichSaturatedCompleteHeightData

/-- The selected graph-height count and the fixed `27`-fibre bound control
indexed mass on the complete source-height restriction. -/
theorem graph_cells_to_source_mass
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss finalLoss eta : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma stickyLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.saturatedGraphScale ≤ 1}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    {scheduled : PureWZ2Node05V4RichSaturatedScheduledTheorem52Data
      (eta := eta) neighborhood hbridge hgraphOne projection}
    {sparse : PureWZ2Node05V4RichSaturatedSourceCellData scheduled}
    (complete : PureWZ2Node05V4RichSaturatedCompleteHeightData sparse) :
    Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale neighborhood.graphScale)
          (finalLoss - 1) *
        (scheduled.finite.finiteGraph.graph.residue.cells.card : ENNReal) *
        (complete.multiplicityFloor : ENNReal) *
        pullback.firstPostBalanced.cellMass ≤
      54 *
        ((wz1Lemma23SnappedHeights
          scheduled.finite.finiteGraph.graph.residue.cells).card : ENNReal) *
        complete.sourceRestriction.mass := by
  have hrich : Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale neighborhood.graphScale)
        (finalLoss - 1) ≤
      (scheduled.theorem52.output.lineData.richF.card : ENNReal) := by
    simpa only [scheduled.theorem52.output.ready.ready.deltaGraph_eq] using
      scheduled.theorem52.output.lineData.richF_card
  have hcardNat :
      scheduled.theorem52.output.lineData.richF.card *
          scheduled.finite.finiteGraph.graph.residue.cells.card ≤
        54 *
          (wz1Lemma23SnappedHeights
            scheduled.finite.finiteGraph.graph.residue.cells).card *
          complete.completeSourceCells.card := by
    calc
      scheduled.theorem52.output.lineData.richF.card *
            scheduled.finite.finiteGraph.graph.residue.cells.card =
          sparse.graphHeightIndices.card *
            scheduled.finite.finiteGraph.graph.residue.cells.card := by
        rw [sparse.graphHeightIndices_card]
      _ ≤ scheduled.finite.finiteGraph.graph.residue.heightFiberCost *
          (wz1Lemma23SnappedHeights
            scheduled.finite.finiteGraph.graph.residue.cells).card *
          sparse.graphCells.card := sparse.graphCells_card_retention
      _ = 2 *
          (wz1Lemma23SnappedHeights
            scheduled.finite.finiteGraph.graph.residue.cells).card *
          sparse.graphCells.card := by
        rw [scheduled.finite.finiteGraph.heightFiberCost_eq]
      _ ≤ 2 *
          (wz1Lemma23SnappedHeights
            scheduled.finite.finiteGraph.graph.residue.cells).card *
          (27 * complete.completeSourceCells.card) := by
        exact Nat.mul_le_mul_left
          (2 * (wz1Lemma23SnappedHeights
            scheduled.finite.finiteGraph.graph.residue.cells).card)
          complete.graphCells_card_le_completeSourceCells
      _ = 54 *
          (wz1Lemma23SnappedHeights
            scheduled.finite.finiteGraph.graph.residue.cells).card *
          complete.completeSourceCells.card := by ring
  have hcard :
      ((scheduled.theorem52.output.lineData.richF.card : ENNReal) *
          scheduled.finite.finiteGraph.graph.residue.cells.card) ≤
        54 *
          (wz1Lemma23SnappedHeights
            scheduled.finite.finiteGraph.graph.residue.cells).card *
          complete.completeSourceCells.card := by
    exact_mod_cast hcardNat
  calc
    Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale neighborhood.graphScale)
          (finalLoss - 1) *
        (scheduled.finite.finiteGraph.graph.residue.cells.card : ENNReal) *
        (complete.multiplicityFloor : ENNReal) *
        pullback.firstPostBalanced.cellMass ≤
      ((scheduled.theorem52.output.lineData.richF.card : ENNReal) *
        scheduled.finite.finiteGraph.graph.residue.cells.card) *
        (complete.multiplicityFloor : ENNReal) *
        pullback.firstPostBalanced.cellMass := by gcongr
    _ ≤ (54 *
          ((wz1Lemma23SnappedHeights
            scheduled.finite.finiteGraph.graph.residue.cells).card : ENNReal) *
          complete.completeSourceCells.card) *
        (complete.multiplicityFloor : ENNReal) *
        pullback.firstPostBalanced.cellMass := by gcongr
    _ = 54 *
        ((wz1Lemma23SnappedHeights
          scheduled.finite.finiteGraph.graph.residue.cells).card : ENNReal) *
        ((complete.multiplicityFloor : ENNReal) *
          ((complete.completeSourceCells.card : ENNReal) *
            pullback.firstPostBalanced.cellMass)) := by ring
    _ ≤ 54 *
        ((wz1Lemma23SnappedHeights
          scheduled.finite.finiteGraph.graph.residue.cells).card : ENNReal) *
        complete.sourceRestriction.mass := by
      gcongr
      rw [← complete.sourceRestriction_volume_eq]
      exact complete.sourceRestriction_mass_lower

end PureWZ2Node05V4RichSaturatedCompleteHeightData

end Kakeya.Assouad

end
