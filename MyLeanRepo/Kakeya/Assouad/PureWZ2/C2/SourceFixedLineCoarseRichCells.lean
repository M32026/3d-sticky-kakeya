import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarseAlternativeA
import MyLeanRepo.Kakeya.Assouad.WZ1.NeighborPackingBound

/-!
# Genuine coarse owner cells selected by `Z_lin`

The graph grid has side `256 * rho`, whereas the balanced-cover cells have
side `rho`.  This module maps the Alternative-A height cells back to their
actual side-`rho` owners and records the bounded geometric fibre.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private lemma coarseRich_abs_floor_sub_le
    {x y : ℝ} {N : ℕ} (_hN : 0 < N)
    (h : |x - y| ≤ (N : ℝ)) :
    |(Int.floor x : ℤ) - (Int.floor y : ℤ)| ≤ (N : ℤ) := by
  have hxy : x - y ≤ (N : ℝ) := (abs_le.mp h).2
  have hyx : y - x ≤ (N : ℝ) := by
    have h' : |y - x| ≤ (N : ℝ) := by
      simpa [abs_sub_comm] using h
    exact (abs_le.mp h').2
  have hupper : (Int.floor x : ℤ) - Int.floor y ≤ (N : ℤ) := by
    by_contra hnot
    have hint : (N : ℤ) + 1 ≤ Int.floor x - Int.floor y := by omega
    have hreal : (N : ℝ) + 1 ≤
        (Int.floor x : ℝ) - Int.floor y := by exact_mod_cast hint
    linarith [Int.floor_le x, Int.lt_floor_add_one y]
  have hlower : -(N : ℤ) ≤ (Int.floor x : ℤ) - Int.floor y := by
    by_contra hnot
    have hint : (N : ℤ) + 1 ≤ Int.floor y - Int.floor x := by omega
    have hreal : (N : ℝ) + 1 ≤
        (Int.floor y : ℝ) - Int.floor x := by exact_mod_cast hint
    linarith [Int.floor_le y, Int.lt_floor_add_one x]
  exact abs_le.mpr ⟨hlower, hupper⟩

structure PureWZ2SourceFixedBinCoarseRichCells
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale} {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared} {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line} {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection} {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue} {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph (theoremEta := theoremEta) sharp}
    (rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready epsilon) where
  graphCells : Finset (ℤ × ℤ × ℤ) :=
    preparedGraph.graph.residue.cells.filter fun cell =>
      cell.2.2 ∈ rich.heightIndices
  graphCells_eq : graphCells =
    preparedGraph.graph.residue.cells.filter fun cell =>
      cell.2.2 ∈ rich.heightIndices
  graphCells_subset : graphCells ⊆ preparedGraph.graph.residue.cells
  graphCells_height : ∀ cell ∈ graphCells,
    cell.2.2 ∈ rich.heightIndices
  graphCells_nonempty : graphCells.Nonempty
  graphCells_card_lower :
    rich.heightIndices.card * preparedGraph.graph.residue.cells.card ≤
      preparedGraph.graph.residue.heightFiberCost *
        (wz1Lemma23SnappedHeights
          preparedGraph.graph.residue.cells).card * graphCells.card
  cells : Finset (ℤ × ℤ × ℤ) := graphCells.image graphParents.ownerCell
  cells_eq : cells = graphCells.image graphParents.ownerCell
  cells_subset : cells ⊆
    fineWitnesses.coarseWitnesses.activeCells
  cells_active_carrier : cells ⊆ wz1PaperActiveCells
    carrier.shading
      twoScale.coarseGrains.extremal.delta_pos
  graphCells_card : graphCells.card ≤ 27 * cells.card
  cells_nonempty : cells.Nonempty

abbrev PureWZ2SourceFixedLineCoarseRichCells
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta epsilon : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate (eta := eta) carriers.fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedLineCoarsePreparedGraphData graphParents normalFirst}
    {sharp : PureWZ2SourceFixedLineCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedLineCoarseReadyGraph (theoremEta := theoremEta) sharp}
    (rich : PureWZ2SourceFixedLineCoarseAlternativeAHeightData ready epsilon) : Type :=
  PureWZ2SourceFixedBinCoarseRichCells rich

theorem PureWZ2SourceFixedBinCoarseAlternativeAHeightData.toRichCellsFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale} {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared} {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line} {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection} {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue} {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    (graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep)
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate (eta := eta) fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData graphParents normalFirst}
    {sharp : PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedBinCoarseReadyGraph (theoremEta := theoremEta) sharp}
    (rich : PureWZ2SourceFixedBinCoarseAlternativeAHeightData ready epsilon) :
    Nonempty (PureWZ2SourceFixedBinCoarseRichCells
      (graphParents := graphParents) rich) := by
  let graphCells := preparedGraph.graph.residue.cells.filter fun cell =>
    cell.2.2 ∈ rich.heightIndices
  have hrichGraphCell : ∀ point (hpoint : point ∈ rich.richF),
      (rich.pathFor point).2.1 ∈ graphCells := by
    intro point hpoint
    apply Finset.mem_filter.mpr
    refine ⟨rich.cell_mem point hpoint, ?_⟩
    rw [rich.heightIndices_eq]
    exact Finset.mem_image.mpr
      ⟨point, hpoint, by rw [rich.heightIndex_eq point hpoint]⟩
  have hgraphNonempty : graphCells.Nonempty := by
    rcases rich.richF_nonempty with ⟨point, hpoint⟩
    exact ⟨(rich.pathFor point).2.1, hrichGraphCell point hpoint⟩
  have hheightSubset : rich.heightIndices ⊆
      wz1Lemma23SnappedHeights preparedGraph.graph.residue.cells := by
    intro height hheight
    rw [rich.heightIndices_eq] at hheight
    rcases Finset.mem_image.mp hheight with ⟨point, hpoint, rfl⟩
    exact Finset.mem_image.mpr
      ⟨(rich.pathFor point).2.1, rich.cell_mem point hpoint,
        rich.heightIndex_eq point hpoint |>.symm⟩
  have hgraphCardLower :
      rich.heightIndices.card * preparedGraph.graph.residue.cells.card ≤
        preparedGraph.graph.residue.heightFiberCost *
          (wz1Lemma23SnappedHeights
            preparedGraph.graph.residue.cells).card * graphCells.card :=
    finset_selected_fibers_card_lower
      preparedGraph.graph.residue.cells (fun cell => cell.2.2)
      rich.heightIndices hheightSubset
      preparedGraph.graph.residue.heightFiberCost
      preparedGraph.graph.residue.height_uniform
  let cells := graphCells.image graphParents.ownerCell
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hownerFiber : ∀ owner ∈ graphCells.image graphParents.ownerCell,
      (graphCells.filter fun cell => graphParents.ownerCell cell = owner).card ≤
        27 := by
    intro owner howner
    rcases Finset.mem_image.mp howner with ⟨baseCell, hbaseCell, hbaseOwner⟩
    let ownerFiber := graphCells.filter fun cell =>
      graphParents.ownerCell cell = owner
    let allowed : Finset (ℤ × ℤ × ℤ) :=
      (Finset.Icc (baseCell.1 - 1) (baseCell.1 + 1)).product
        ((Finset.Icc (baseCell.2.1 - 1) (baseCell.2.1 + 1)).product
          (Finset.Icc (baseCell.2.2 - 1) (baseCell.2.2 + 1)))
    have hrhoMesh : rho < gridSide (prep.graphScale / 2) := by
      rw [show gridSide (prep.graphScale / 2) =
        prep.graphScale / Real.sqrt 3 by simp [gridSide] <;> ring,
        prep.graphScale_eq]
      have hsqrt3 : Real.sqrt (3 : ℝ) < 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
          Real.sqrt_nonneg (3 : ℝ)]
      rw [lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num))]
      nlinarith
    have hfiberSubset : ownerFiber ⊆ allowed := by
      intro cell hcell
      have hcellData := Finset.mem_filter.mp hcell
      have hcellGraph : cell ∈ prep.windowed.global.cells :=
        preparedGraph.graph.residue.cells_subset
          (Finset.mem_filter.mp hcellData.1).1
      have hbaseGraph : baseCell ∈ prep.windowed.global.cells :=
        preparedGraph.graph.residue.cells_subset
          (Finset.mem_filter.mp hbaseCell).1
      have hcellRep := graphParents.representative_mem_owner cell hcellGraph
      have hbaseRep := graphParents.representative_mem_owner
        baseCell hbaseGraph
      rw [hcellData.2] at hcellRep
      rw [hbaseOwner] at hbaseRep
      rw [wz1PaperGridCube_eq_Ico hrho owner] at hcellRep hbaseRep
      have hxCoord :
          |graphParents.representative cell (0 : Fin 3) -
            graphParents.representative baseCell (0 : Fin 3)| < rho := by
        rw [abs_lt]
        exact ⟨by linarith [hcellRep.1, hbaseRep.2.1],
          by linarith [hbaseRep.1, hcellRep.2.1]⟩
      have hyCoord :
          |graphParents.representative cell (1 : Fin 3) -
            graphParents.representative baseCell (1 : Fin 3)| < rho := by
        rw [abs_lt]
        exact ⟨by linarith [hcellRep.2.2.1, hbaseRep.2.2.2.1],
          by linarith [hbaseRep.2.2.1, hcellRep.2.2.2.1]⟩
      have hzCoord :
          |graphParents.representative cell (2 : Fin 3) -
            graphParents.representative baseCell (2 : Fin 3)| < rho := by
        rw [abs_lt]
        exact ⟨by linarith [hcellRep.2.2.2.2.1, hbaseRep.2.2.2.2.2],
          by linarith [hbaseRep.2.2.2.2.1, hcellRep.2.2.2.2.2]⟩
      have hcoordClose : ∀ coordinate : Fin 3,
          |graphParents.representative cell coordinate -
            graphParents.representative baseCell coordinate| < rho := by
        intro coordinate
        fin_cases coordinate
        · exact hxCoord
        · exact hyCoord
        · exact hzCoord
      have hcellIndex := graphParents.representative_index cell hcellGraph
      have hbaseIndex := graphParents.representative_index baseCell hbaseGraph
      have hcellIndex0 :
          ⌊graphParents.representative cell 0 /
              gridSide (prep.graphScale / 2)⌋ = cell.1 := by
        simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
          congrArg Prod.fst hcellIndex
      have hcellIndex1 :
          ⌊graphParents.representative cell 1 /
              gridSide (prep.graphScale / 2)⌋ = cell.2.1 := by
        simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
          congrArg (fun index : ℤ × ℤ × ℤ => index.2.1) hcellIndex
      have hcellIndex2 :
          ⌊graphParents.representative cell 2 /
              gridSide (prep.graphScale / 2)⌋ = cell.2.2 := by
        simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
          congrArg (fun index : ℤ × ℤ × ℤ => index.2.2) hcellIndex
      have hbaseIndex0 :
          ⌊graphParents.representative baseCell 0 /
              gridSide (prep.graphScale / 2)⌋ = baseCell.1 := by
        simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
          congrArg Prod.fst hbaseIndex
      have hbaseIndex1 :
          ⌊graphParents.representative baseCell 1 /
              gridSide (prep.graphScale / 2)⌋ = baseCell.2.1 := by
        simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
          congrArg (fun index : ℤ × ℤ × ℤ => index.2.1) hbaseIndex
      have hbaseIndex2 :
          ⌊graphParents.representative baseCell 2 /
              gridSide (prep.graphScale / 2)⌋ = baseCell.2.2 := by
        simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using
          congrArg (fun index : ℤ × ℤ × ℤ => index.2.2) hbaseIndex
      have hindexClose : ∀ coordinate : Fin 3,
          |(match coordinate with
              | 0 => cell.1
              | 1 => cell.2.1
              | 2 => cell.2.2) -
            (match coordinate with
              | 0 => baseCell.1
              | 1 => baseCell.2.1
              | 2 => baseCell.2.2)| ≤ 1 := by
        intro coordinate
        have hmeshPos : 0 < gridSide (prep.graphScale / 2) := by
          exact div_pos
            (mul_pos (by norm_num) (div_pos prep.graphScale_pos (by norm_num)))
            (Real.sqrt_pos.2 (by norm_num))
        have hratio :
            |graphParents.representative cell coordinate /
                  gridSide (prep.graphScale / 2) -
              graphParents.representative baseCell coordinate /
                  gridSide (prep.graphScale / 2)| < 1 := by
          rw [← sub_div, abs_div, abs_of_pos hmeshPos]
          exact (div_lt_one hmeshPos).2
            ((hcoordClose coordinate).trans hrhoMesh)
        have hfloor := coarseRich_abs_floor_sub_le
          (x := graphParents.representative cell coordinate /
            gridSide (prep.graphScale / 2))
          (y := graphParents.representative baseCell coordinate /
            gridSide (prep.graphScale / 2))
          (N := 1) (by omega) (by norm_num; exact hratio.le)
        fin_cases coordinate
        · simpa [hcellIndex0, hbaseIndex0] using hfloor
        · simpa [hcellIndex1, hbaseIndex1] using hfloor
        · simpa [hcellIndex2, hbaseIndex2] using hfloor
      have hxClose : |cell.1 - baseCell.1| ≤ 1 := by
        simpa using hindexClose (0 : Fin 3)
      have hyClose : |cell.2.1 - baseCell.2.1| ≤ 1 := by
        simpa using hindexClose (1 : Fin 3)
      have hzClose : |cell.2.2 - baseCell.2.2| ≤ 1 := by
        simpa using hindexClose (2 : Fin 3)
      have hx := abs_le.mp hxClose
      have hy := abs_le.mp hyClose
      have hz := abs_le.mp hzClose
      dsimp only [allowed]
      apply Finset.mem_product.mpr
      constructor
      · rw [Finset.mem_Icc]
        omega
      · apply Finset.mem_product.mpr
        constructor
        · rw [Finset.mem_Icc]
          omega
        · rw [Finset.mem_Icc]
          omega
    calc
      ownerFiber.card ≤ allowed.card := Finset.card_le_card hfiberSubset
      _ = 27 := by
        have hcardThree (index : ℤ) :
            (Finset.Icc (index - 1) (index + 1)).card = 3 := by
          simp [Int.card_Icc] <;> omega
        simp [allowed, hcardThree]
  have hgraphCellsCard : graphCells.card ≤ 27 * cells.card :=
    Finset.card_le_mul_card_image graphCells 27 hownerFiber
  have hcellsSubset : cells ⊆
      fineWitnesses.coarseWitnesses.activeCells := by
    intro cell hcell
    rcases Finset.mem_image.mp hcell with ⟨graphCell, hgraphCell, rfl⟩
    exact graphParents.owner_active graphCell
      (preparedGraph.graph.residue.cells_subset
        (Finset.mem_filter.mp hgraphCell).1)
  have hcellsCarrier : cells ⊆ wz1PaperActiveCells
      carrier.shading
        twoScale.coarseGrains.extremal.delta_pos := by
    intro owner howner
    rcases Finset.mem_image.mp howner with ⟨graphCell, hgraphCell, rfl⟩
    have hgraphGlobal : graphCell ∈ prep.windowed.global.cells :=
      preparedGraph.graph.residue.cells_subset
        (Finset.mem_filter.mp hgraphCell).1
    have hrepresentative : graphParents.representative graphCell ∈
        carrier.shading.union := by
      exact prep.shadow_union_subset
        (graphParents.representative_mem graphCell hgraphGlobal)
    have hownerCube := graphParents.representative_mem_owner
      graphCell hgraphGlobal
    rw [mem_wz1PaperActiveCells]
    refine ⟨?_, ⟨graphParents.representative graphCell,
      hrepresentative, ?_⟩⟩
    · have hbox := shading_union_subset_axisBox
        (carrier.subshading.union_subset hrepresentative)
      have hindex : wz1PaperGridIndex rho
          (graphParents.representative graphCell) =
            graphParents.ownerCell graphCell :=
        (mem_wz1PaperGridCube rho _ _).mp hownerCube
      rw [← hindex]
      simpa only [twoScale.rhoRequested_eq] using
        paper_point_gridIndex_in_window hrho hbox
    · simpa only [twoScale.rhoRequested_eq] using hownerCube
  exact ⟨{
    graphCells := graphCells
    graphCells_eq := rfl
    graphCells_subset := Finset.filter_subset _ _
    graphCells_height := by
      intro cell hcell
      exact (Finset.mem_filter.mp hcell).2
    graphCells_nonempty := hgraphNonempty
    graphCells_card_lower := hgraphCardLower
    cells := cells
    cells_eq := rfl
    cells_subset := hcellsSubset
    cells_active_carrier := hcellsCarrier
    graphCells_card := hgraphCellsCard
    cells_nonempty := hgraphNonempty.image graphParents.ownerCell
  }⟩

theorem PureWZ2SourceFixedLineCoarseAlternativeAHeightData.toRichCells
    {sigma inputLoss delta rho middleLoss stickyLoss eta theoremEta epsilon : ℝ}
    {logExponent : ℕ} {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    (graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep)
    {normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate (eta := eta) carriers.fineWitnesses}
    {preparedGraph : PureWZ2SourceFixedLineCoarsePreparedGraphData graphParents normalFirst}
    {sharp : PureWZ2SourceFixedLineCoarseSharpGeometry preparedGraph}
    {ready : PureWZ2SourceFixedLineCoarseReadyGraph (theoremEta := theoremEta) sharp}
    (rich : PureWZ2SourceFixedLineCoarseAlternativeAHeightData ready epsilon) :
    Nonempty (PureWZ2SourceFixedLineCoarseRichCells (graphParents := graphParents) rich) :=
  PureWZ2SourceFixedBinCoarseAlternativeAHeightData.toRichCellsFixedBin
    graphParents rich

end Kakeya.Assouad

end
