import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalAlternativeA

/-!
# Balanced source rho cells selected by Alternative-A heights
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private lemma pureWZ2_abs_floor_sub_le
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

structure PureWZ2SourceAlternativeARichCells
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    {graphParents : PureWZ2SourceHorizontalGraphParentData prep}
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    (rich : PureWZ2SourceAlternativeAHeightData ready epsilon) where
  rhoCell : Point2 → (ℤ × ℤ × ℤ) := fun point =>
    graphParents.rhoCellOf (rich.pathFor point).2.1
  rhoCell_eq : ∀ point ∈ rich.richF, rhoCell point =
    graphParents.rhoCellOf (rich.pathFor point).2.1
  rhoCell_mem : ∀ point ∈ rich.richF, rhoCell point ∈ retained.selectedCells
  point_mem_rhoCell : ∀ point ∈ rich.richF,
    graphParents.representative (rich.pathFor point).2.1 ∈
      wz1PaperGridCube rho (rhoCell point)
  graphCells : Finset (ℤ × ℤ × ℤ) :=
    graph.residue.cells.filter fun cell => cell.2.2 ∈ rich.heightIndices
  graphCells_eq : graphCells =
    graph.residue.cells.filter fun cell => cell.2.2 ∈ rich.heightIndices
  graphCells_subset : graphCells ⊆ graph.residue.cells
  graphCells_height : ∀ cell ∈ graphCells, cell.2.2 ∈ rich.heightIndices
  graphCells_nonempty : graphCells.Nonempty
  graphCells_card_lower :
    rich.heightIndices.card * graph.residue.cells.card ≤
      graph.residue.heightFiberCost *
        (wz1Lemma23SnappedHeights graph.residue.cells).card *
          graphCells.card
  cells : Finset (ℤ × ℤ × ℤ) :=
    graphCells.image graphParents.rhoCellOf
  cells_eq : cells = graphCells.image graphParents.rhoCellOf
  cells_subset : cells ⊆ retained.selectedCells
  graphCells_card : graphCells.card ≤ 27 * cells.card
  witness_cells_subset : rich.richF.image rhoCell ⊆ cells
  cells_card : rich.richF.card ≤ 5 * cells.card
  cells_nonempty : cells.Nonempty

theorem PureWZ2SourceAlternativeAHeightData.toRichCells
    {sigma inputLoss delta rho middleLoss outputLoss theoremEta epsilon : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    (graphParents : PureWZ2SourceHorizontalGraphParentData prep)
    {graph : WZ1Lemma23WindowedPreparedGraph prep.windowed}
    {sharp : PureWZ2SourceHorizontalSharpGeometry graph}
    {ready : PureWZ2SourceHorizontalReadyGraph
      (theoremEta := theoremEta) sharp}
    (rich : PureWZ2SourceAlternativeAHeightData ready epsilon) :
    Nonempty (PureWZ2SourceAlternativeARichCells
      (graphParents := graphParents) rich) := by
  let rhoCell : Point2 → (ℤ × ℤ × ℤ) := fun point =>
    graphParents.rhoCellOf (rich.pathFor point).2.1
  have hrhoCellMem : ∀ point (hpoint : point ∈ rich.richF),
      rhoCell point ∈ retained.selectedCells := by
    intro point hpoint
    exact graphParents.rhoCell_mem _
      (graph.residue.cells_subset (rich.cell_mem point hpoint))
  have hpointCell : ∀ point (hpoint : point ∈ rich.richF),
      graphParents.representative (rich.pathFor point).2.1 ∈
        wz1PaperGridCube rho (rhoCell point) := by
    intro point hpoint
    exact graphParents.representative_mem_rhoCell _
      (graph.residue.cells_subset (rich.cell_mem point hpoint))
  have hfiber : ∀ rhoCellValue ∈ rich.richF.image rhoCell,
      (rich.richF.filter fun point => rhoCell point = rhoCellValue).card ≤ 5 := by
    intro rhoCellValue hrhoCellValue
    rcases Finset.mem_image.mp hrhoCellValue with
      ⟨basePoint, hbasePoint, hbaseEq⟩
    let fiber := rich.richF.filter fun point => rhoCell point = rhoCellValue
    have hheightInjective : Set.InjOn rich.heightIndex fiber :=
      rich.heightIndex_injective.mono (Finset.filter_subset _ _)
    have hheightRange : fiber.image rich.heightIndex ⊆
        Finset.Icc (rich.heightIndex basePoint - 2)
          (rich.heightIndex basePoint + 2) := by
      intro height hheight
      rcases Finset.mem_image.mp hheight with ⟨point, hpointFiber, rfl⟩
      have hpoint : point ∈ rich.richF := (Finset.mem_filter.mp hpointFiber).1
      have hcellEq : rhoCell point = rhoCell basePoint := by
        exact (Finset.mem_filter.mp hpointFiber).2.trans hbaseEq.symm
      have hfirstGraph := graphParents.representative_index
        (rich.pathFor point).2.1
        (graph.residue.cells_subset (rich.cell_mem point hpoint))
      have hsecondGraph := graphParents.representative_index
        (rich.pathFor basePoint).2.1
        (graph.residue.cells_subset (rich.cell_mem basePoint hbasePoint))
      have hfirstRho := hpointCell point hpoint
      have hsecondRho := hpointCell basePoint hbasePoint
      rw [hcellEq] at hfirstRho
      have hzClose :
          |graphParents.representative (rich.pathFor point).2.1 2 -
            graphParents.representative (rich.pathFor basePoint).2.1 2| < rho := by
        rw [wz1PaperGridCube_eq_Ico line.rho_pos (rhoCell basePoint)] at hfirstRho
        rw [wz1PaperGridCube_eq_Ico line.rho_pos (rhoCell basePoint)] at hsecondRho
        rw [abs_lt]
        constructor <;>
          linarith [hfirstRho.2.2.2.2.1, hfirstRho.2.2.2.2.2,
            hsecondRho.2.2.2.2.1, hsecondRho.2.2.2.2.2]
      have hcloseFirst :=
        ((wz1_lemma23_snapped_cell_geometry prep.graphScale
          prep.graphScale_pos prep.graphScale_one).2.1
          (rich.pathFor point).2.1
          (graphParents.representative (rich.pathFor point).2.1)
          hfirstGraph).1 (2 : Fin 3)
      have hcloseSecond :=
        ((wz1_lemma23_snapped_cell_geometry prep.graphScale
          prep.graphScale_pos prep.graphScale_one).2.1
          (rich.pathFor basePoint).2.1
          (graphParents.representative (rich.pathFor basePoint).2.1)
          hsecondGraph).1 (2 : Fin 3)
      have hcenterClose :
          |(wz1Lemma23CellCenter prep.graphScale (rich.pathFor point).2.1) 2 -
            (wz1Lemma23CellCenter prep.graphScale (rich.pathFor basePoint).2.1) 2| <
              prep.graphScale + rho := by
        have htriangle :
            |(wz1Lemma23CellCenter prep.graphScale (rich.pathFor point).2.1) 2 -
              (wz1Lemma23CellCenter prep.graphScale (rich.pathFor basePoint).2.1) 2| ≤
            |(wz1Lemma23CellCenter prep.graphScale (rich.pathFor point).2.1) 2 -
              graphParents.representative (rich.pathFor point).2.1 2| +
            |graphParents.representative (rich.pathFor point).2.1 2 -
              graphParents.representative (rich.pathFor basePoint).2.1 2| +
            |graphParents.representative (rich.pathFor basePoint).2.1 2 -
              (wz1Lemma23CellCenter prep.graphScale (rich.pathFor basePoint).2.1) 2| := by
          calc
            _ = |((wz1Lemma23CellCenter prep.graphScale (rich.pathFor point).2.1) 2 -
                    graphParents.representative (rich.pathFor point).2.1 2) +
                  (graphParents.representative (rich.pathFor point).2.1 2 -
                    graphParents.representative (rich.pathFor basePoint).2.1 2) +
                  (graphParents.representative (rich.pathFor basePoint).2.1 2 -
                    (wz1Lemma23CellCenter prep.graphScale (rich.pathFor basePoint).2.1) 2)| := by ring_nf
            _ ≤ _ := by
              calc
                _ ≤ |((wz1Lemma23CellCenter prep.graphScale (rich.pathFor point).2.1) 2 -
                        graphParents.representative (rich.pathFor point).2.1 2) +
                      (graphParents.representative (rich.pathFor point).2.1 2 -
                        graphParents.representative (rich.pathFor basePoint).2.1 2)| +
                    |graphParents.representative (rich.pathFor basePoint).2.1 2 -
                      (wz1Lemma23CellCenter prep.graphScale (rich.pathFor basePoint).2.1) 2| := abs_add_le _ _
                _ ≤ _ := by gcongr; exact abs_add_le _ _
        have hfirstClose :
            |(wz1Lemma23CellCenter prep.graphScale (rich.pathFor point).2.1) 2 -
              graphParents.representative (rich.pathFor point).2.1 2| ≤
                prep.graphScale / 2 := by
          simpa [abs_sub_comm] using hcloseFirst
        linarith [htriangle, hfirstClose, hcloseSecond, hzClose]
      have hmesh : gridSide (prep.graphScale / 2) =
          prep.graphScale / Real.sqrt 3 := by
        simp [gridSide]
        ring
      have hindexReal :
          |((rich.heightIndex point : ℝ) -
            (rich.heightIndex basePoint : ℝ))| < 3 := by
        have hcenterFormula :
            (wz1Lemma23CellCenter prep.graphScale (rich.pathFor point).2.1) 2 -
                (wz1Lemma23CellCenter prep.graphScale (rich.pathFor basePoint).2.1) 2 =
              ((rich.heightIndex point : ℝ) -
                (rich.heightIndex basePoint : ℝ)) *
                gridSide (prep.graphScale / 2) := by
          simp [wz1Lemma23CellCenter, point3, rich.heightIndex_eq,
            rich.heightIndex_eq point hpoint, rich.heightIndex_eq basePoint hbasePoint]
          ring
        have hsqrt3_pos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
        have hmesh_pos : 0 < prep.graphScale / Real.sqrt 3 :=
          div_pos prep.graphScale_pos hsqrt3_pos
        rw [hcenterFormula, abs_mul, hmesh, abs_of_pos hmesh_pos] at hcenterClose
        have hratio : prep.graphScale + rho <
            3 * (prep.graphScale / Real.sqrt 3) := by
          rw [prep.graphScale_eq]
          have hsqrt3 : Real.sqrt (3 : ℝ) < 2 := by
            have hsqrt3_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
              Real.sq_sqrt (by norm_num)
            nlinarith [Real.sqrt_nonneg (3 : ℝ)]
          rw [show 3 * (256 * rho / Real.sqrt 3) =
              (768 * rho) / Real.sqrt 3 by ring]
          rw [lt_div_iff₀ hsqrt3_pos]
          have hrhoSqrt : rho * Real.sqrt 3 < rho * 2 :=
            mul_lt_mul_of_pos_left hsqrt3 line.rho_pos
          nlinarith
        have hscaled := hcenterClose.trans hratio
        rw [mul_comm 3 (prep.graphScale / Real.sqrt 3)] at hscaled
        nlinarith
      have hindexInt :
          |rich.heightIndex point - rich.heightIndex basePoint| ≤ 2 := by
        have hcast :
            (|rich.heightIndex point - rich.heightIndex basePoint| : ℝ) < 3 := by
          exact_mod_cast hindexReal
        have hindexIntLt :
            |rich.heightIndex point - rich.heightIndex basePoint| < (3 : ℤ) := by
          exact_mod_cast hcast
        omega
      rw [Finset.mem_Icc]
      rcases abs_le.mp hindexInt with ⟨hlower, hupper⟩
      constructor <;> omega
    rw [← Finset.card_image_of_injOn hheightInjective]
    exact (Finset.card_le_card hheightRange).trans_eq (by simp; omega)
  have hcard : rich.richF.card ≤ 5 * (rich.richF.image rhoCell).card :=
    Finset.card_le_mul_card_image rich.richF 5 hfiber
  let graphCells := graph.residue.cells.filter fun cell =>
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
  have hheightSubset :
      rich.heightIndices ⊆ wz1Lemma23SnappedHeights graph.residue.cells := by
    intro height hheight
    rw [rich.heightIndices_eq] at hheight
    rcases Finset.mem_image.mp hheight with ⟨point, hpoint, rfl⟩
    exact Finset.mem_image.mpr
      ⟨(rich.pathFor point).2.1, rich.cell_mem point hpoint,
        rich.heightIndex_eq point hpoint |>.symm⟩
  have hgraphCardLower :
      rich.heightIndices.card * graph.residue.cells.card ≤
        graph.residue.heightFiberCost *
          (wz1Lemma23SnappedHeights graph.residue.cells).card *
            graphCells.card := by
    have hraw := finset_selected_fibers_card_lower
      graph.residue.cells (fun cell => cell.2.2) rich.heightIndices
      hheightSubset graph.residue.heightFiberCost
      graph.residue.height_uniform
    exact hraw
  let cells := graphCells.image graphParents.rhoCellOf
  have hownerFiber : ∀ owner ∈ graphCells.image graphParents.rhoCellOf,
      (graphCells.filter fun cell => graphParents.rhoCellOf cell = owner).card ≤
        27 := by
    intro owner howner
    rcases Finset.mem_image.mp howner with ⟨baseCell, hbaseCell, hbaseOwner⟩
    let ownerFiber := graphCells.filter fun cell =>
      graphParents.rhoCellOf cell = owner
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
      nlinarith [line.rho_pos]
    have hfiberSubset : ownerFiber ⊆ allowed := by
      intro cell hcell
      have hcellData := Finset.mem_filter.mp hcell
      have hcellGraph : cell ∈ prep.windowed.global.cells :=
        graph.residue.cells_subset (Finset.mem_filter.mp hcellData.1).1
      have hbaseGraph : baseCell ∈ prep.windowed.global.cells :=
        graph.residue.cells_subset (Finset.mem_filter.mp hbaseCell).1
      have hcellRep := graphParents.representative_mem_rhoCell cell hcellGraph
      have hbaseRep := graphParents.representative_mem_rhoCell baseCell hbaseGraph
      rw [hcellData.2] at hcellRep
      rw [hbaseOwner] at hbaseRep
      rw [wz1PaperGridCube_eq_Ico line.rho_pos owner] at hcellRep hbaseRep
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
          rw [← sub_div, abs_div,
            abs_of_pos hmeshPos]
          exact (div_lt_one hmeshPos).2
            ((hcoordClose coordinate).trans hrhoMesh)
        have hfloor := pureWZ2_abs_floor_sub_le
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
  have hcellsSubset : cells ⊆ retained.selectedCells := by
    intro cell hcell
    rcases Finset.mem_image.mp hcell with ⟨graphCell, hgraphCell, rfl⟩
    exact graphParents.rhoCell_mem graphCell
      (graph.residue.cells_subset (Finset.mem_filter.mp hgraphCell).1)
  have hwitnessSubset : rich.richF.image rhoCell ⊆ cells := by
    intro cell hcell
    rcases Finset.mem_image.mp hcell with ⟨point, hpoint, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(rich.pathFor point).2.1, hrichGraphCell point hpoint, ?_⟩
    rfl
  have hcard' : rich.richF.card ≤ 5 * cells.card :=
    hcard.trans (Nat.mul_le_mul_left 5 (Finset.card_le_card hwitnessSubset))
  exact ⟨{
    rhoCell := rhoCell
    rhoCell_eq := by intro point hpoint; rfl
    rhoCell_mem := hrhoCellMem
    point_mem_rhoCell := hpointCell
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
    graphCells_card := hgraphCellsCard
    witness_cells_subset := hwitnessSubset
    cells_card := hcard'
    cells_nonempty := hgraphNonempty.image graphParents.rhoCellOf
  }⟩

end Kakeya.Assouad
