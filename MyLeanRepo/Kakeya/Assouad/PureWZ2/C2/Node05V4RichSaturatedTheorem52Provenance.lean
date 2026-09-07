import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedFiniteGraph

/-!
# Source provenance after the saturated Node-5 Theorem-5.2 graph

The graph carrier is an auxiliary same-height saturation rather than the
original tube shading.  This module records the exact route back from every
`richF` point selected by Theorem 5.2 to a genuine point of the post-two-call
source and to one retained first-cover `rho` cell.  The genuine source height
is not identified with the snapped graph height: it is proved to lie in the
corresponding complete graph-height interval.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichSaturatedTheorem52Provenance
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
    {data : PureWZ2Node05V4RichSaturatedFiniteGraphData
      (eta := eta) neighborhood hbridge hgraphOne}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (output : PureWZ2AnchoredTheorem52Output data.finiteGraph projection) where
  graphCell :
    {point // point ∈ output.lineData.richF} → WZ2PaperCellIndex :=
      fun point => output.lineData.graphCell point.1
  graphCell_eq : ∀ point : {point // point ∈ output.lineData.richF},
    graphCell point = output.lineData.graphCell point.1
  graphCell_mem_window : ∀ point : {point // point ∈ output.lineData.richF},
    graphCell point ∈ data.prep.windowed.global.cells
  representative :
    {point // point ∈ output.lineData.richF} → Point3 :=
      fun point => data.parents.representative (graphCell point)
  representative_eq : ∀ point : {point // point ∈ output.lineData.richF},
    representative point = data.parents.representative (graphCell point)
  representative_mem_saturation :
    ∀ point : {point // point ∈ output.lineData.richF},
    representative point ∈
      pullback.sameHeightParentSaturation
        (neighborhood.cube (data.parents.parentY (graphCell point)))
  sourcePoint :
    {point // point ∈ output.lineData.richF} → Point3 :=
      fun point => data.parents.sourceWitness (graphCell point)
  sourcePoint_eq : ∀ point : {point // point ∈ output.lineData.richF},
    sourcePoint point = data.parents.sourceWitness (graphCell point)
  sourcePoint_mem_pullback :
    ∀ point : {point // point ∈ output.lineData.richF},
    sourcePoint point ∈
      pullback.preCommonBinFinePullback
        (neighborhood.cube (data.parents.parentY (graphCell point)))
  sourcePoint_height : ∀ point : {point // point ∈ output.lineData.richF},
    sourcePoint point (2 : Fin 3) = representative point (2 : Fin 3)
  sourceCell :
    {point // point ∈ output.lineData.richF} → WZ2PaperCellIndex :=
      fun point => data.parents.sourceCell (graphCell point)
  sourceCell_eq : ∀ point : {point // point ∈ output.lineData.richF},
    sourceCell point = data.parents.sourceCell (graphCell point)
  sourceCell_mem_parent : ∀ point : {point // point ∈ output.lineData.richF},
    sourceCell point ∈ pullback.preCommonBinRhoCells
      (neighborhood.cube (data.parents.parentY (graphCell point)))
  sourceCell_mem_selected : ∀ point : {point // point ∈ output.lineData.richF},
    sourceCell point ∈ pullback.selectedCells
  sourcePoint_mem_cell : ∀ point : {point // point ∈ output.lineData.richF},
    sourcePoint point ∈ wz1PaperGridCube rho (sourceCell point)
  actualHeight_close_graphHeight :
    ∀ point : {point // point ∈ output.lineData.richF},
    |sourcePoint point (2 : Fin 3) - output.lineData.sourceHeight point.1| ≤
      neighborhood.graphScale / 2
  graphHeight_mem_Z_lin :
    ∀ point : {point // point ∈ output.lineData.richF},
    output.lineData.sourceHeight point.1 ∈ output.lineData.Z_lin
  actualHeight_mem_Z_lin_intervals :
    ∀ point : {point // point ∈ output.lineData.richF},
    sourcePoint point (2 : Fin 3) ∈ output.lineData.Z_lin_intervals

namespace PureWZ2AnchoredTheorem52Output

/-- Recover the source point and retained first-cover cell behind every
Theorem-5.2 `richF` point of the saturated graph.  No graph choice or source
choice is repeated. -/
theorem saturatedProvenance
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
    {data : PureWZ2Node05V4RichSaturatedFiniteGraphData
      (eta := eta) neighborhood hbridge hgraphOne}
    {projection :
      PureWZ2SourceHorizontalProjectionThreshold sigma finalLoss}
    (output : PureWZ2AnchoredTheorem52Output data.finiteGraph projection) :
    Nonempty
      (PureWZ2Node05V4RichSaturatedTheorem52Provenance output) := by
  let graphCell :
      {point // point ∈ output.lineData.richF} → WZ2PaperCellIndex :=
    fun point => output.lineData.graphCell point.1
  have hgraphCellMem : ∀ point,
      graphCell point ∈ data.prep.windowed.global.cells := by
    intro point
    exact data.finiteGraph.graph.residue.cells_subset
      (output.lineData.graphCell_mem_residue point.1 point.2)
  let representative :
      {point // point ∈ output.lineData.richF} → Point3 :=
    fun point => data.parents.representative (graphCell point)
  let sourcePoint :
      {point // point ∈ output.lineData.richF} → Point3 :=
    fun point => data.parents.sourceWitness (graphCell point)
  let sourceCell :
      {point // point ∈ output.lineData.richF} → WZ2PaperCellIndex :=
    fun point => data.parents.sourceCell (graphCell point)
  have hsourceCellMem : ∀ point,
      sourceCell point ∈ pullback.preCommonBinRhoCells
        (neighborhood.cube (data.parents.parentY (graphCell point))) := by
    intro point
    exact data.parents.sourceCell_mem_parent
      (graphCell point) (hgraphCellMem point)
  have hsourcePointCell : ∀ point,
      sourcePoint point ∈ wz1PaperGridCube rho (sourceCell point) := by
    intro point
    exact data.parents.sourceWitness_mem_sourceCell
      (graphCell point) (hgraphCellMem point)
  have hheightClose : ∀ point,
      |sourcePoint point (2 : Fin 3) -
          output.lineData.sourceHeight point.1| ≤
        neighborhood.graphScale / 2 := by
    intro point
    have hcenter :=
      ((wz1_lemma23_snapped_cell_geometry neighborhood.graphScale
        neighborhood.graphScale_pos hgraphOne).2.1
        (graphCell point) (representative point)
        (data.parents.representative_index
          (graphCell point) (hgraphCellMem point))).1 (2 : Fin 3)
    rw [data.parents.sourceWitness_height
      (graphCell point) (hgraphCellMem point)]
    rw [output.lineData.sourceHeight_eq point.1]
    exact hcenter
  have hheightMem : ∀ point : {point // point ∈ output.lineData.richF},
      output.lineData.sourceHeight point.1 ∈ output.lineData.Z_lin := by
    intro point
    rw [output.lineData.Z_lin_eq]
    exact Finset.mem_image.mpr ⟨point.1, point.2, rfl⟩
  have hactualInterval : ∀ point,
      sourcePoint point (2 : Fin 3) ∈ output.lineData.Z_lin_intervals := by
    intro point
    rw [output.lineData.Z_lin_intervals_eq]
    refine Set.mem_iUnion₂.mpr
      ⟨output.lineData.sourceHeight point.1, hheightMem point, ?_⟩
    rw [Set.mem_Icc]
    have hbounds := abs_le.mp (hheightClose point)
    constructor <;> linarith
  exact ⟨{
    graphCell := graphCell
    graphCell_eq := fun _ => rfl
    graphCell_mem_window := hgraphCellMem
    representative := representative
    representative_eq := fun _ => rfl
    representative_mem_saturation := fun point =>
      data.parents.representative_mem_saturation
        (graphCell point) (hgraphCellMem point)
    sourcePoint := sourcePoint
    sourcePoint_eq := fun _ => rfl
    sourcePoint_mem_pullback := fun point =>
      data.parents.sourceWitness_mem_pullback
        (graphCell point) (hgraphCellMem point)
    sourcePoint_height := fun point =>
      data.parents.sourceWitness_height
        (graphCell point) (hgraphCellMem point)
    sourceCell := sourceCell
    sourceCell_eq := fun _ => rfl
    sourceCell_mem_parent := hsourceCellMem
    sourceCell_mem_selected := fun point =>
      pullback.preCommonBinRhoCells_subset _ (hsourceCellMem point)
    sourcePoint_mem_cell := hsourcePointCell
    actualHeight_close_graphHeight := hheightClose
    graphHeight_mem_Z_lin := hheightMem
    actualHeight_mem_Z_lin_intervals := hactualInterval
  }⟩

end PureWZ2AnchoredTheorem52Output

end Kakeya.Assouad

end
