import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightSeparatedGraph

/-!
# Source and parent provenance for the final joint-height graph

Every graph cell retains its same-height fixed-bin source witness and the
literal second-cover parent of that witness.  The mod-512 separation and
graph-cell geometry imply that graph cells with the same y-index have parent
cells with the same y-index.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichJointGraphParentData
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
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    {B₀ threshold : ENNReal}
    {block : volumePopular.JointHeightCommonBinData B₀ threshold}
    {oneParent : block.JointOneParentPerYData}
    {separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent}
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : separated.graphScale ≤ 1}
    (prep : PureWZ2AnchoredGraphPreparationData
      (separated.graphInput hbridge hgraphOne)) where
  representative : WZ2PaperCellIndex → Point3
  representative_mem :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈ separated.graphShading.union
  representative_index :
    ∀ cell ∈ prep.windowed.global.cells,
      wz1Lemma23CellIndex separated.graphScale (representative cell) = cell
  sourceCell : WZ2PaperCellIndex → WZ2PaperCellIndex
  sourceCell_mem :
    ∀ cell ∈ prep.windowed.global.cells,
      sourceCell cell ∈ separated.selectedCells
  representative_mem_saturation :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈ block.jointCellSaturation (sourceCell cell)
  sourceWitness : WZ2PaperCellIndex → Point3
  sourceWitness_mem :
    ∀ cell ∈ prep.windowed.global.cells,
      sourceWitness cell ∈ block.jointCellSource (sourceCell cell)
  sourceWitness_height :
    ∀ cell ∈ prep.windowed.global.cells,
      sourceWitness cell (2 : Fin 3) = representative cell (2 : Fin 3)
  parentCell : WZ2PaperCellIndex → WZ2PaperCellIndex := fun cell =>
    pullback.standardSecondParent (sourceCell cell)
  parentCell_eq :
    ∀ cell ∈ prep.windowed.global.cells,
      parentCell cell = pullback.standardSecondParent (sourceCell cell)
  parentCell_active :
    ∀ cell ∈ prep.windowed.global.cells,
      parentCell cell ∈ twoScale.secondBalancedCover.activeCells
  parentCell_selected :
    ∀ cell ∈ prep.windowed.global.cells,
      parentCell cell ∈ separated.selectedParents
  representative_mem_parent :
    ∀ cell ∈ prep.windowed.global.cells,
      representative cell ∈ wz1PaperGridCube sqrtRequested.1 (parentCell cell)
  sourceWitness_mem_sourceCell :
    ∀ cell ∈ prep.windowed.global.cells,
      sourceWitness cell ∈ wz1PaperGridCube rho (sourceCell cell)
  same_y_parentCell :
    ∀ first ∈ prep.windowed.global.cells,
      ∀ second ∈ prep.windowed.global.cells,
        first.2.1 = second.2.1 →
          parentCell first = parentCell second

namespace PureWZ2Node05V4RichJointSeparatedParentData

variable
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
    {pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale}
    {heightIndex : {heightIndex //
      heightIndex ∈ pureWZ2Node05V4RichHeavySlabs pullback}}
    {volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    {B₀ threshold : ENNReal}
    {block : volumePopular.JointHeightCommonBinData B₀ threshold}
    {oneParent : block.JointOneParentPerYData}
    (separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent)
    {hbridge : PureWZ2PaperADBridgeStatement}
    {hgraphOne : separated.graphScale ≤ 1}

theorem graphParents
    (prep : PureWZ2AnchoredGraphPreparationData
      (separated.graphInput hbridge hgraphOne)) :
    Nonempty (PureWZ2Node05V4RichJointGraphParentData prep) := by
  let cells := prep.windowed.global.cells
  let representative : WZ2PaperCellIndex → Point3 := fun cell =>
    if hcell : cell ∈ cells then
      wz1Lemma23CellRepresentative separated.graphShading
        separated.graphScale_pos
        ⟨cell, prep.windowed.global.cells_active hcell⟩
    else 0
  have hrepresentativeMem : ∀ cell (hcell : cell ∈ cells),
      representative cell ∈ separated.graphShading.union := by
    intro cell hcell
    simp only [representative, dif_pos hcell]
    exact wz1Lemma23CellRepresentative_mem_union
      separated.graphShading separated.graphScale_pos _
  have hrepresentativeIndex : ∀ cell (hcell : cell ∈ cells),
      wz1Lemma23CellIndex separated.graphScale (representative cell) = cell := by
    intro cell hcell
    simp only [representative, dif_pos hcell]
    exact wz1Lemma23CellRepresentative_index
      separated.graphShading separated.graphScale_pos _
  have hsourceExists : ∀ cell (hcell : cell ∈ cells),
      ∃ sourceCell ∈ separated.selectedCells,
        representative cell ∈ block.jointCellSaturation sourceCell ∧
          ∃ sourcePoint ∈ block.jointCellSource sourceCell,
            sourcePoint (2 : Fin 3) = representative cell (2 : Fin 3) := by
    intro cell hcell
    have hpoint := hrepresentativeMem cell hcell
    rw [separated.graphShading_union] at hpoint
    rcases separated.saturatedUnion_exists_source_same_height hpoint with
      ⟨sourceCell, hsourceCell, hsaturation, sourcePoint,
        hsourcePoint, hheight⟩
    exact ⟨sourceCell, hsourceCell, hsaturation,
      sourcePoint, hsourcePoint, hheight⟩
  let defaultSource := Classical.choose separated.selectedCells_nonempty
  let sourceCell : WZ2PaperCellIndex → WZ2PaperCellIndex := fun cell =>
    if hcell : cell ∈ cells then
      Classical.choose (hsourceExists cell hcell)
    else defaultSource
  have hsourceCellMem : ∀ cell (hcell : cell ∈ cells),
      sourceCell cell ∈ separated.selectedCells := by
    intro cell hcell
    simp only [sourceCell, dif_pos hcell]
    exact (Classical.choose_spec (hsourceExists cell hcell)).1
  have hrepresentativeSaturation : ∀ cell (hcell : cell ∈ cells),
      representative cell ∈ block.jointCellSaturation (sourceCell cell) := by
    intro cell hcell
    simp only [sourceCell, dif_pos hcell]
    exact (Classical.choose_spec (hsourceExists cell hcell)).2.1
  let sourceWitness : WZ2PaperCellIndex → Point3 := fun cell =>
    if hcell : cell ∈ cells then
      Classical.choose
        (Classical.choose_spec (hsourceExists cell hcell)).2.2
    else 0
  have hsourceSpec : ∀ cell (hcell : cell ∈ cells),
      sourceWitness cell ∈ block.jointCellSource (sourceCell cell) ∧
        sourceWitness cell (2 : Fin 3) = representative cell (2 : Fin 3) := by
    intro cell hcell
    simp only [sourceWitness, sourceCell, dif_pos hcell]
    exact Classical.choose_spec
      (Classical.choose_spec (hsourceExists cell hcell)).2.2
  let parentCell : WZ2PaperCellIndex → WZ2PaperCellIndex := fun cell =>
    pullback.standardSecondParent (sourceCell cell)
  have hsourceSelected : ∀ cell (hcell : cell ∈ cells),
      sourceCell cell ∈ pullback.selectedCells := by
    intro cell hcell
    exact block.jointFixedBinRhoCells_subset_selected
      (oneParent.selectedCells_subset
        (separated.selectedCells_subset (hsourceCellMem cell hcell)))
  have hparentActive : ∀ cell (hcell : cell ∈ cells),
      parentCell cell ∈ twoScale.secondBalancedCover.activeCells := by
    intro cell hcell
    exact pullback.standardSecondParent_active (hsourceSelected cell hcell)
  have hparentSelected : ∀ cell (hcell : cell ∈ cells),
      parentCell cell ∈ separated.selectedParents := by
    intro cell hcell
    rw [separated.selectedParents_eq]
    exact Finset.mem_image.mpr
      ⟨sourceCell cell, hsourceCellMem cell hcell, rfl⟩
  have hsourceWitnessCell : ∀ cell (hcell : cell ∈ cells),
      sourceWitness cell ∈ wz1PaperGridCube rho (sourceCell cell) := by
    intro cell hcell
    exact (hsourceSpec cell hcell).1.2
  have hrepresentativeParent : ∀ cell (hcell : cell ∈ cells),
      representative cell ∈
        wz1PaperGridCube sqrtRequested.1 (parentCell cell) := by
    intro cell hcell
    have hpointRho :=
      wz1PaperGridCubeSameHeightSaturation_subset_cube
        rho (sourceCell cell) (block.jointCellSource (sourceCell cell))
        (hrepresentativeSaturation cell hcell)
    exact pullback.standardSecondParent_cell_subset
      (hsourceSelected cell hcell) hpointRho
  have hsameY : ∀ first (hfirst : first ∈ cells),
      ∀ second (hsecond : second ∈ cells),
        first.2.1 = second.2.1 →
          (parentCell first).2.1 = (parentCell second).2.1 := by
    intro first hfirst second hsecond hyIndex
    by_contra hyNe
    have hresidueFirst := separated.parent_y_residue
      (sourceCell first) (hsourceCellMem first hfirst)
    have hresidueSecond := separated.parent_y_residue
      (sourceCell second) (hsourceCellMem second hsecond)
    have hmod :
        ((parentCell first).2.1 - (parentCell second).2.1) % (512 : ℤ) = 0 := by
      change
        ((pullback.standardSecondParent (sourceCell first)).2.1 -
          (pullback.standardSecondParent (sourceCell second)).2.1) %
            (512 : ℤ) = 0
      rw [Int.sub_emod, hresidueFirst, hresidueSecond]
      simp
    have hdiv : (512 : ℤ) ∣
        (parentCell first).2.1 - (parentCell second).2.1 := by
      rwa [Int.dvd_iff_emod_eq_zero]
    have hindexGap :
        (512 : ℤ) ≤
          |(parentCell first).2.1 - (parentCell second).2.1| :=
      Int.le_abs_of_dvd (sub_ne_zero.mpr hyNe) hdiv
    have hfirstParent := hrepresentativeParent first hfirst
    have hsecondParent := hrepresentativeParent second hsecond
    rw [wz1PaperGridCube_eq_Ico
      twoScale.secondSticky.coarse_extremal.delta_pos] at hfirstParent hsecondParent
    rw [twoScale.sqrtRequested_eq, pullback.rhoRequested_eq] at hfirstParent hsecondParent
    have hgraphCenters :=
      (wz1_lemma23_snapped_cell_geometry separated.graphScale
        separated.graphScale_pos hgraphOne).2.2.1 first second hyIndex
    have hfirstGraph :=
      ((wz1_lemma23_snapped_cell_geometry separated.graphScale
        separated.graphScale_pos hgraphOne).2.1
        first (representative first)
          (hrepresentativeIndex first hfirst)).1 (1 : Fin 3)
    have hsecondGraph :=
      ((wz1_lemma23_snapped_cell_geometry separated.graphScale
        separated.graphScale_pos hgraphOne).2.1
        second (representative second)
          (hrepresentativeIndex second hsecond)).1 (1 : Fin 3)
    have hrepresentativeClose :
        |representative first 1 - representative second 1| ≤
          separated.graphScale := by
      calc
        _ = |(representative first 1 -
              (wz1Lemma23CellCenter separated.graphScale first) 1) +
            ((wz1Lemma23CellCenter separated.graphScale second) 1 -
              representative second 1)| := by
          rw [hgraphCenters]
          ring_nf
        _ ≤ |representative first 1 -
              (wz1Lemma23CellCenter separated.graphScale first) 1| +
            |(wz1Lemma23CellCenter separated.graphScale second) 1 -
              representative second 1| := abs_add_le _ _
        _ ≤ separated.graphScale / 2 + separated.graphScale / 2 := by
          exact add_le_add hfirstGraph
            (by simpa [abs_sub_comm] using hsecondGraph)
        _ = separated.graphScale := by ring
    have hrootPos : 0 < Real.sqrt rho := by
      rw [← pullback.rhoRequested_eq]
      exact Real.sqrt_pos.mpr
        twoScale.first.publicSticky.coarse_extremal.delta_pos
    have hfirstBounds := hfirstParent.2.2
    have hsecondBounds := hsecondParent.2.2
    have hfirstNear :
        |((parentCell first).2.1 : ℝ) * Real.sqrt rho -
          representative first 1| ≤ Real.sqrt rho := by
      rw [abs_le]
      constructor <;> nlinarith [hfirstBounds.1, hfirstBounds.2.1]
    have hsecondNear :
        |representative second 1 -
          ((parentCell second).2.1 : ℝ) * Real.sqrt rho| ≤
            Real.sqrt rho := by
      rw [abs_le]
      constructor <;> nlinarith [hsecondBounds.1, hsecondBounds.2.1]
    have hparentPhysical :
        |((parentCell first).2.1 : ℝ) * Real.sqrt rho -
          ((parentCell second).2.1 : ℝ) * Real.sqrt rho| ≤
            258 * Real.sqrt rho := by
      calc
        _ = |(((parentCell first).2.1 : ℝ) * Real.sqrt rho -
              representative first 1) +
            (representative first 1 - representative second 1) +
            (representative second 1 -
              ((parentCell second).2.1 : ℝ) * Real.sqrt rho)| := by ring
        _ ≤ |(((parentCell first).2.1 : ℝ) * Real.sqrt rho -
              representative first 1) +
            (representative first 1 - representative second 1)| +
            |representative second 1 -
              ((parentCell second).2.1 : ℝ) * Real.sqrt rho| :=
          abs_add_le _ _
        _ ≤ (|((parentCell first).2.1 : ℝ) * Real.sqrt rho -
                representative first 1| +
              |representative first 1 - representative second 1|) +
            |representative second 1 -
              ((parentCell second).2.1 : ℝ) * Real.sqrt rho| := by
          gcongr
          exact abs_add_le _ _
        _ ≤ |representative first 1 - representative second 1| +
            2 * Real.sqrt rho := by linarith
        _ ≤ separated.graphScale + 2 * Real.sqrt rho := by gcongr
        _ = 256 * rho + 2 * Real.sqrt rho := rfl
        _ ≤ 258 * Real.sqrt rho := by
          have hrho : 0 < rho := by
            rw [← pullback.rhoRequested_eq]
            exact twoScale.first.publicSticky.coarse_extremal.delta_pos
          have hrhoOne : rho ≤ 1 := by
            rw [← pullback.rhoRequested_eq]
            exact rhoRequested.property.2
          have hrhoRoot : rho ≤ Real.sqrt rho := by
            nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho]
          nlinarith
    have hscale :
        |((parentCell first).2.1 : ℝ) -
          ((parentCell second).2.1 : ℝ)| ≤ 258 := by
      have hmul :
          |((parentCell first).2.1 : ℝ) -
              ((parentCell second).2.1 : ℝ)| * Real.sqrt rho ≤
            258 * Real.sqrt rho := by
        calc
          _ = |((parentCell first).2.1 : ℝ) -
                ((parentCell second).2.1 : ℝ)| * |Real.sqrt rho| := by
            rw [abs_of_pos hrootPos]
          _ = |(((parentCell first).2.1 : ℝ) -
                ((parentCell second).2.1 : ℝ)) * Real.sqrt rho| := by
            rw [abs_mul]
          _ = |((parentCell first).2.1 : ℝ) * Real.sqrt rho -
                ((parentCell second).2.1 : ℝ) * Real.sqrt rho| := by
            congr 1
            ring
          _ ≤ 258 * Real.sqrt rho := hparentPhysical
      nlinarith
    have hindexUpper :
        |(parentCell first).2.1 - (parentCell second).2.1| ≤ (258 : ℤ) := by
      exact_mod_cast hscale
    omega
  exact ⟨{
    representative := representative
    representative_mem := hrepresentativeMem
    representative_index := hrepresentativeIndex
    sourceCell := sourceCell
    sourceCell_mem := hsourceCellMem
    representative_mem_saturation := hrepresentativeSaturation
    sourceWitness := sourceWitness
    sourceWitness_mem := fun cell hcell => (hsourceSpec cell hcell).1
    sourceWitness_height := fun cell hcell => (hsourceSpec cell hcell).2
    parentCell := parentCell
    parentCell_eq := fun _ _ => rfl
    parentCell_active := hparentActive
    parentCell_selected := hparentSelected
    representative_mem_parent := hrepresentativeParent
    sourceWitness_mem_sourceCell := hsourceWitnessCell
    same_y_parentCell := by
      intro first hfirst second hsecond hy
      exact separated.selectedParents_y_injective
        (hparentSelected first hfirst) (hparentSelected second hsecond)
        (hsameY first hfirst second hsecond hy)
  }⟩

end PureWZ2Node05V4RichJointSeparatedParentData

end Kakeya.Assouad

end
