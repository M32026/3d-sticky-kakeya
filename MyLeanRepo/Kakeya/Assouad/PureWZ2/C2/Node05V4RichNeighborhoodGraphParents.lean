import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichNeighborhoodGraphPreparation

/-!
# Graph cells and their selected saturated parents

Every occupied `256 * rho` graph cell is represented by an actual point of
the aggregate source shading.  The aggregate-union identity then recovers a
selected side-`sqrt rho` parent containing that point.  The mod-`512` parent
separation forces all graph cells in one snapped y-layer to choose the same
parent.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichNeighborhoodGraphParentData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
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
    (prep : PureWZ2AnchoredGraphPreparationData
      (neighborhood.graphInput hbridge hgraphOne)) where
  representative : WZ2PaperCellIndex → Point3
  representative_mem :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈ neighborhood.graphShadow.union
  representative_index :
    ∀ cell ∈ prep.windowed.global.cells,
      wz1Lemma23CellIndex neighborhood.saturatedGraphScale
        (representative cell) = cell
  parentY : WZ2PaperCellIndex → ℝ
  parentY_mem :
    ∀ cell ∈ prep.windowed.global.cells,
      parentY cell ∈ neighborhood.sample
  representative_mem_saturation :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈
        pullback.sameHeightParentSaturation
          (neighborhood.cube (parentY cell))
  sourceWitness : WZ2PaperCellIndex → Point3
  sourceWitness_mem_pullback :
    ∀ cell ∈ prep.windowed.global.cells,
      sourceWitness cell ∈
        pullback.preCommonBinFinePullback
          (neighborhood.cube (parentY cell))
  sourceWitness_height :
    ∀ cell ∈ prep.windowed.global.cells,
      sourceWitness cell (2 : Fin 3) = representative cell (2 : Fin 3)
  sourceCell : WZ2PaperCellIndex → WZ2PaperCellIndex := fun cell =>
    wz1PaperGridIndex rho (sourceWitness cell)
  sourceCell_eq :
    ∀ cell ∈ prep.windowed.global.cells,
      sourceCell cell = wz1PaperGridIndex rho (sourceWitness cell)
  sourceCell_mem_parent :
    ∀ cell ∈ prep.windowed.global.cells,
      sourceCell cell ∈ pullback.preCommonBinRhoCells
        (neighborhood.cube (parentY cell))
  sourceWitness_mem_sourceCell :
    ∀ cell ∈ prep.windowed.global.cells,
      sourceWitness cell ∈ wz1PaperGridCube rho (sourceCell cell)
  representative_source_dist :
    ∀ cell ∈ prep.windowed.global.cells,
      dist (representative cell) (sourceWitness cell) ≤ 2 * rho
  graphScale_le_fourteen_root :
    neighborhood.saturatedGraphScale ≤ 14 * Real.sqrt rho
  same_y_parentY :
    ∀ first ∈ prep.windowed.global.cells,
      ∀ second ∈ prep.windowed.global.cells,
        first.2.1 = second.2.1 → parentY first = parentY second

namespace PureWZ2PreCommonBinGlobalGrainNeighborhoodData

theorem graphParents
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
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
    (neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback)
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : neighborhood.saturatedGraphScale ≤ 1}
    (prep : PureWZ2AnchoredGraphPreparationData
      (neighborhood.graphInput hbridge hgraphOne))
    (hheightAbsorb :
      neighborhood.saturatedGraphScale + 2 * Real.sqrt rho ≤
        16 * Real.sqrt rho) :
    Nonempty (PureWZ2Node05V4RichNeighborhoodGraphParentData prep) := by
  let cells := prep.windowed.global.cells
  let representative : WZ2PaperCellIndex → Point3 := fun cell =>
    if hcell : cell ∈ cells then
      wz1Lemma23CellRepresentative neighborhood.graphShadow
        neighborhood.graphScale_pos
        ⟨cell, prep.windowed.global.cells_active hcell⟩
    else 0
  have hrepresentativeMem : ∀ cell (hcell : cell ∈ cells),
      representative cell ∈ neighborhood.graphShadow.union := by
    intro cell hcell
    simp only [representative, dif_pos hcell]
    exact wz1Lemma23CellRepresentative_mem_union
      neighborhood.graphShadow neighborhood.graphScale_pos _
  have hrepresentativeIndex : ∀ cell (hcell : cell ∈ cells),
      wz1Lemma23CellIndex neighborhood.graphScale (representative cell) =
        cell := by
    intro cell hcell
    simp only [representative, dif_pos hcell]
    exact wz1Lemma23CellRepresentative_index
      neighborhood.graphShadow neighborhood.graphScale_pos _
  have hparentExists : ∀ cell (hcell : cell ∈ cells),
      ∃ y ∈ neighborhood.sample,
        representative cell ∈
            pullback.sameHeightParentSaturation (neighborhood.cube y) ∧
          ∃ sourcePoint : Point3,
            sourcePoint ∈
                pullback.preCommonBinFinePullback (neighborhood.cube y) ∧
              sourcePoint (2 : Fin 3) = representative cell (2 : Fin 3) ∧
              dist (representative cell) sourcePoint ≤ 2 * rho := by
    intro cell hcell
    have hpoint := hrepresentativeMem cell hcell
    rw [neighborhood.graphShadow_union] at hpoint
    exact neighborhood.saturatedUnion_exists_source_same_height hpoint
  let defaultY := Classical.choose neighborhood.sample_nonempty
  let parentY : WZ2PaperCellIndex → ℝ := fun cell =>
    if hcell : cell ∈ cells then
      Classical.choose (hparentExists cell hcell)
    else defaultY
  have hparentYMem : ∀ cell (hcell : cell ∈ cells),
      parentY cell ∈ neighborhood.sample := by
    intro cell hcell
    simp only [parentY, dif_pos hcell]
    exact (Classical.choose_spec (hparentExists cell hcell)).1
  have hrepresentativeSaturation : ∀ cell (hcell : cell ∈ cells),
      representative cell ∈
        pullback.sameHeightParentSaturation
          (neighborhood.cube (parentY cell)) := by
    intro cell hcell
    simp only [parentY, dif_pos hcell]
    exact (Classical.choose_spec (hparentExists cell hcell)).2.1
  let sourceWitness : WZ2PaperCellIndex → Point3 := fun cell =>
    if hcell : cell ∈ cells then
      Classical.choose
        (Classical.choose_spec (hparentExists cell hcell)).2.2
    else 0
  have hsourceSpec : ∀ cell (hcell : cell ∈ cells),
      sourceWitness cell ∈
          pullback.preCommonBinFinePullback
            (neighborhood.cube (parentY cell)) ∧
        sourceWitness cell (2 : Fin 3) = representative cell (2 : Fin 3) ∧
        dist (representative cell) (sourceWitness cell) ≤ 2 * rho := by
    intro cell hcell
    simp only [sourceWitness, parentY, dif_pos hcell]
    exact Classical.choose_spec
      (Classical.choose_spec (hparentExists cell hcell)).2.2
  let sourceCell : WZ2PaperCellIndex → WZ2PaperCellIndex := fun cell =>
    wz1PaperGridIndex rho (sourceWitness cell)
  have hsourceCellMem : ∀ cell (hcell : cell ∈ cells),
      sourceCell cell ∈ pullback.preCommonBinRhoCells
        (neighborhood.cube (parentY cell)) := by
    intro cell hcell
    have hsource := (hsourceSpec cell hcell).1
    change sourceWitness cell ∈ pullback.shading.union ∩
      wz2RetainedCellsUnion rho
        (pullback.preCommonBinRhoCells
          (neighborhood.cube (parentY cell))) at hsource
    rw [wz2RetainedCellsUnion] at hsource
    rcases Set.mem_iUnion₂.mp hsource.2 with
      ⟨selectedCell, hselectedCell, hpointCell⟩
    have hindex : sourceCell cell = selectedCell :=
      (mem_wz1PaperGridCube rho selectedCell (sourceWitness cell)).mp
        hpointCell
    rwa [hindex]
  have hsourceWitnessCell : ∀ cell (hcell : cell ∈ cells),
      sourceWitness cell ∈ wz1PaperGridCube rho (sourceCell cell) := by
    intro cell _hcell
    exact (mem_wz1PaperGridCube rho (sourceCell cell) _).mpr rfl
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hgraphSmall : neighborhood.graphScale ≤ 14 * Real.sqrt rho := by
    linarith
  have hsameY : ∀ first (hfirst : first ∈ cells),
      ∀ second (hsecond : second ∈ cells),
        first.2.1 = second.2.1 → parentY first = parentY second := by
    intro first hfirst second hsecond hyIndex
    by_contra hparentYNe
    have hparentCubeNe :
        neighborhood.cube (parentY first) ≠
          neighborhood.cube (parentY second) := by
      intro hcube
      exact hparentYNe (neighborhood.cube_injective
        (hparentYMem first hfirst) (hparentYMem second hsecond) hcube)
    have hseparation :
        500 * sqrtRequested.1 ≤ |parentY first - parentY second| :=
      neighborhood.cube_separated
        (parentY first) (hparentYMem first hfirst)
        (parentY second) (hparentYMem second hsecond) hparentYNe
    have hfirstParent := pullback.sameHeightParentSaturation_subset_parent
      (hrepresentativeSaturation first hfirst)
    have hsecondParent := pullback.sameHeightParentSaturation_subset_parent
      (hrepresentativeSaturation second hsecond)
    have hrootRequested : 0 < sqrtRequested.1 :=
      twoScale.secondSticky.coarse_extremal.delta_pos
    rw [wz1PaperGridCube_eq_Ico hrootRequested] at hfirstParent hsecondParent
    have hfirstParentClose :
        |representative first 1 - parentY first| ≤ sqrtRequested.1 / 2 := by
      rw [neighborhood.sample_eq_cube_center_y
        (parentY first) (hparentYMem first hfirst)]
      rw [abs_le]
      constructor <;> linarith
        [hfirstParent.2.2.1, hfirstParent.2.2.2.1]
    have hsecondParentClose :
        |representative second 1 - parentY second| ≤
          sqrtRequested.1 / 2 := by
      rw [neighborhood.sample_eq_cube_center_y
        (parentY second) (hparentYMem second hsecond)]
      rw [abs_le]
      constructor <;> linarith
        [hsecondParent.2.2.1, hsecondParent.2.2.2.1]
    have hgraphCenters :
        (wz1Lemma23CellCenter neighborhood.graphScale first) 1 =
          (wz1Lemma23CellCenter neighborhood.graphScale second) 1 :=
      (wz1_lemma23_snapped_cell_geometry neighborhood.graphScale
        neighborhood.graphScale_pos hgraphOne).2.2.1 first second hyIndex
    have hfirstGraph :=
      ((wz1_lemma23_snapped_cell_geometry neighborhood.graphScale
        neighborhood.graphScale_pos hgraphOne).2.1
        first (representative first) (hrepresentativeIndex first hfirst)).1
        (1 : Fin 3)
    have hsecondGraph :=
      ((wz1_lemma23_snapped_cell_geometry neighborhood.graphScale
        neighborhood.graphScale_pos hgraphOne).2.1
        second (representative second)
          (hrepresentativeIndex second hsecond)).1 (1 : Fin 3)
    have hrepresentativeClose :
        |representative first 1 - representative second 1| ≤
          neighborhood.graphScale := by
      calc
        |representative first 1 - representative second 1| =
            |(representative first 1 -
                (wz1Lemma23CellCenter neighborhood.graphScale first) 1) +
              ((wz1Lemma23CellCenter neighborhood.graphScale second) 1 -
                representative second 1)| := by
          rw [hgraphCenters]
          ring_nf
        _ ≤
            |representative first 1 -
              (wz1Lemma23CellCenter neighborhood.graphScale first) 1| +
            |(wz1Lemma23CellCenter neighborhood.graphScale second) 1 -
              representative second 1| := abs_add_le _ _
        _ ≤ neighborhood.graphScale / 2 + neighborhood.graphScale / 2 := by
          exact add_le_add hfirstGraph
            (by simpa [abs_sub_comm] using hsecondGraph)
        _ = neighborhood.graphScale := by ring
    have hparentDistance :
        |parentY first - parentY second| ≤
          |representative first 1 - representative second 1| +
            sqrtRequested.1 := by
      calc
        |parentY first - parentY second| =
            |(parentY first - representative first 1) +
              (representative first 1 - representative second 1) +
              (representative second 1 - parentY second)| := by ring_nf
        _ ≤ |parentY first - representative first 1| +
              |representative first 1 - representative second 1| +
              |representative second 1 - parentY second| := by
          calc
            _ ≤ |(parentY first - representative first 1) +
                    (representative first 1 - representative second 1)| +
                  |representative second 1 - parentY second| :=
              abs_add_le _ _
            _ ≤ _ := by
              gcongr
              exact abs_add_le _ _
        _ ≤ |representative first 1 - representative second 1| +
              sqrtRequested.1 := by
          rw [abs_sub_comm (parentY first) (representative first 1)]
          linarith [hfirstParentClose, hsecondParentClose]
    have hupper :
        |parentY first - parentY second| ≤ 15 * Real.sqrt rho := by
      calc
        _ ≤ |representative first 1 - representative second 1| +
              sqrtRequested.1 := hparentDistance
        _ ≤ neighborhood.graphScale + sqrtRequested.1 := by gcongr
        _ ≤ 15 * Real.sqrt rho := by
          rw [pullback.sqrtRequested_eq]
          linarith [hgraphSmall]
    rw [pullback.sqrtRequested_eq] at hseparation
    linarith
  exact ⟨{
    representative := representative
    representative_mem := hrepresentativeMem
    representative_index := hrepresentativeIndex
    parentY := parentY
    parentY_mem := hparentYMem
    representative_mem_saturation := hrepresentativeSaturation
    sourceWitness := sourceWitness
    sourceWitness_mem_pullback := fun cell hcell => (hsourceSpec cell hcell).1
    sourceWitness_height := fun cell hcell => (hsourceSpec cell hcell).2.1
    sourceCell := sourceCell
    sourceCell_eq := fun _ _ => rfl
    sourceCell_mem_parent := hsourceCellMem
    sourceWitness_mem_sourceCell := hsourceWitnessCell
    representative_source_dist := fun cell hcell => (hsourceSpec cell hcell).2.2
    graphScale_le_fourteen_root := hgraphSmall
    same_y_parentY := hsameY
  }⟩

end PureWZ2PreCommonBinGlobalGrainNeighborhoodData

namespace PureWZ2Node05V4RichNeighborhoodGraphParentData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho outputLoss : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
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
    {hgraphOne : neighborhood.graphScale ≤ 1}
    {prep : PureWZ2AnchoredGraphPreparationData
      (neighborhood.graphInput hbridge hgraphOne)}
    (data : PureWZ2Node05V4RichNeighborhoodGraphParentData prep)

/-- The selected fixed-line witnesses, reindexed by graph cells, obey the
constant-four distortion required by the local graph extension. -/
theorem witness_dist
    (first : WZ2PaperCellIndex)
    (hfirst : first ∈ prep.windowed.global.cells)
    (second : WZ2PaperCellIndex)
    (hsecond : second ∈ prep.windowed.global.cells) :
    dist (neighborhood.witness (data.parentY first))
        (neighborhood.witness (data.parentY second)) ≤
      4 *
        |wz1Lemma23SnappedYValue neighborhood.graphScale first.2.1 -
          wz1Lemma23SnappedYValue neighborhood.graphScale second.2.1| := by
  by_cases hparent : data.parentY first = data.parentY second
  · rw [hparent, dist_self]
    positivity
  · let root := Real.sqrt rho
    let parentDistance := |data.parentY first - data.parentY second|
    let graphDistance :=
      |wz1Lemma23SnappedYValue neighborhood.graphScale first.2.1 -
        wz1Lemma23SnappedYValue neighborhood.graphScale second.2.1|
    have hroot : 0 < root := by
      apply Real.sqrt_pos.mpr
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos
    have hfirstParent := pullback.sameHeightParentSaturation_subset_parent
      (data.representative_mem_saturation first hfirst)
    have hsecondParent := pullback.sameHeightParentSaturation_subset_parent
      (data.representative_mem_saturation second hsecond)
    have hrootRequested : 0 < sqrtRequested.1 :=
      twoScale.secondSticky.coarse_extremal.delta_pos
    rw [wz1PaperGridCube_eq_Ico hrootRequested] at hfirstParent hsecondParent
    have hfirstParentClose :
        |data.representative first 1 - data.parentY first| ≤
          sqrtRequested.1 / 2 := by
      rw [neighborhood.sample_eq_cube_center_y
        (data.parentY first) (data.parentY_mem first hfirst)]
      rw [abs_le]
      constructor <;> linarith
        [hfirstParent.2.2.1, hfirstParent.2.2.2.1]
    have hsecondParentClose :
        |data.representative second 1 - data.parentY second| ≤
          sqrtRequested.1 / 2 := by
      rw [neighborhood.sample_eq_cube_center_y
        (data.parentY second) (data.parentY_mem second hsecond)]
      rw [abs_le]
      constructor <;> linarith
        [hsecondParent.2.2.1, hsecondParent.2.2.2.1]
    have hfirstGraph :=
      ((wz1_lemma23_snapped_cell_geometry neighborhood.graphScale
        neighborhood.graphScale_pos hgraphOne).2.1 first
        (data.representative first)
        (data.representative_index first hfirst)).1 (1 : Fin 3)
    have hsecondGraph :=
      ((wz1_lemma23_snapped_cell_geometry neighborhood.graphScale
        neighborhood.graphScale_pos hgraphOne).2.1 second
        (data.representative second)
        (data.representative_index second hsecond)).1 (1 : Fin 3)
    have hfirstGraphClose :
        |data.representative first 1 -
            wz1Lemma23SnappedYValue neighborhood.graphScale first.2.1| ≤
          neighborhood.graphScale / 2 := by
      simpa [wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]
        using hfirstGraph
    have hsecondGraphClose :
        |data.representative second 1 -
            wz1Lemma23SnappedYValue neighborhood.graphScale second.2.1| ≤
          neighborhood.graphScale / 2 := by
      simpa [wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]
        using hsecondGraph
    have hfirstParentClose' :
        |data.parentY first - data.representative first 1| ≤
          sqrtRequested.1 / 2 := by
      simpa [abs_sub_comm] using hfirstParentClose
    have hsecondGraphClose' :
        |wz1Lemma23SnappedYValue neighborhood.graphScale second.2.1 -
            data.representative second 1| ≤
          neighborhood.graphScale / 2 := by
      simpa [abs_sub_comm] using hsecondGraphClose
    have hparentSeparation : 500 * root ≤ parentDistance := by
      dsimp only [parentDistance, root]
      simpa only [pullback.sqrtRequested_eq] using
        neighborhood.cube_separated
          (data.parentY first) (data.parentY_mem first hfirst)
          (data.parentY second) (data.parentY_mem second hsecond) hparent
    have hrepresentativeToGraph :
        |data.representative first 1 - data.representative second 1| ≤
          graphDistance + neighborhood.graphScale := by
      calc
        |data.representative first 1 - data.representative second 1| =
            |(data.representative first 1 -
                wz1Lemma23SnappedYValue neighborhood.graphScale first.2.1) +
              (wz1Lemma23SnappedYValue neighborhood.graphScale first.2.1 -
                wz1Lemma23SnappedYValue neighborhood.graphScale second.2.1) +
              (wz1Lemma23SnappedYValue neighborhood.graphScale second.2.1 -
                data.representative second 1)| := by
          ring_nf
        _ ≤
            (|data.representative first 1 -
                wz1Lemma23SnappedYValue neighborhood.graphScale first.2.1| +
              graphDistance) +
              |wz1Lemma23SnappedYValue neighborhood.graphScale second.2.1 -
                data.representative second 1| +
              0 := by
          have hthree := abs_add_three
            (data.representative first 1 -
              wz1Lemma23SnappedYValue neighborhood.graphScale first.2.1)
            (wz1Lemma23SnappedYValue neighborhood.graphScale first.2.1 -
              wz1Lemma23SnappedYValue neighborhood.graphScale second.2.1)
            (wz1Lemma23SnappedYValue neighborhood.graphScale second.2.1 -
              data.representative second 1)
          simpa only [graphDistance, add_zero] using hthree
        _ ≤ graphDistance + neighborhood.graphScale := by
          dsimp only [graphDistance]
          linarith [hfirstGraphClose, hsecondGraphClose']
    have hparentToGraph :
        parentDistance ≤ graphDistance +
          neighborhood.graphScale + sqrtRequested.1 := by
      calc
        parentDistance =
            |(data.parentY first - data.representative first 1) +
              (data.representative first 1 - data.representative second 1) +
              (data.representative second 1 - data.parentY second)| := by
          dsimp only [parentDistance]
          ring_nf
        _ ≤ |data.parentY first - data.representative first 1| +
              |data.representative first 1 - data.representative second 1| +
              |data.representative second 1 - data.parentY second| :=
          abs_add_three _ _ _
        _ ≤ graphDistance + neighborhood.graphScale +
              sqrtRequested.1 := by
          linarith [hfirstParentClose', hsecondParentClose,
            hrepresentativeToGraph]
        _ ≤ graphDistance + neighborhood.graphScale +
              sqrtRequested.1 := by
          dsimp only [graphDistance]
          linarith [hfirstParentClose', hsecondParentClose,
            hfirstGraphClose, hsecondGraphClose']
    have hrootBound : root ≤ parentDistance / 500 := by
      linarith
    have hparentGraph : parentDistance ≤ (100 / 97 : ℝ) * graphDistance := by
      have hrootRequested : sqrtRequested.1 = root := by
        exact pullback.sqrtRequested_eq
      rw [hrootRequested] at hparentToGraph
      have hgraph := data.graphScale_le_fourteen_root
      dsimp only [root] at hgraph hrootBound ⊢
      nlinarith
    have hanchor := neighborhood.witness_dist_strong
      (data.parentY first) (data.parentY_mem first hfirst)
      (data.parentY second) (data.parentY_mem second hsecond)
    dsimp only [parentDistance, graphDistance] at hparentGraph
    calc
      _ ≤ (33 / 10 : ℝ) *
          |data.parentY first - data.parentY second| := hanchor
      _ ≤ 4 *
          |wz1Lemma23SnappedYValue neighborhood.graphScale first.2.1 -
            wz1Lemma23SnappedYValue neighborhood.graphScale second.2.1| := by
        nlinarith [abs_nonneg
          (wz1Lemma23SnappedYValue neighborhood.graphScale first.2.1 -
            wz1Lemma23SnappedYValue neighborhood.graphScale second.2.1)]

end PureWZ2Node05V4RichNeighborhoodGraphParentData

end Kakeya.Assouad

end
