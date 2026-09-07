import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichCoarseCellWitness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichTwoScaleCellPullback

/-!
# Direct-rich second-stage coarse sources

For an active side-`sqrt rho` cell of the second Proposition 6.2 call, the
paper carrier in WZ Lemma 5.3 is the corresponding portion of the first
coarse `rho`-shading.  Its volume is exactly the second balanced cell mass.
The plane normal is still sampled at a genuine point of the original
`delta`-source, selected in one of the first balanced `rho`-cells inside the
same parent.

This is the heterogeneous carrier used in the paper.  In particular, it does
not replace the coarse carrier by its much smaller final-`delta` pullback.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichSecondStageSourceData
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta rho : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (witnesses : PureWZ2Node05V4RichCoarseCellWitnessData twoScale)
    (parent : WZ2PaperCellIndex) where
  parent_active : parent ∈ twoScale.secondBalancedCover.activeCells
  fullSource : Set Point3 :=
    twoScale.secondRefinedFineShading.union ∩
      wz1PaperGridCube sqrtRequested.1 parent
  fullSource_eq :
    fullSource = twoScale.secondRefinedFineShading.union ∩
      wz1PaperGridCube sqrtRequested.1 parent
  fullSource_measurable : MeasurableSet fullSource
  fullSource_nonempty : fullSource.Nonempty
  fullSource_volume :
    volume fullSource = twoScale.secondBalancedCover.cellMass
  fullSource_subset_first_coarse :
    fullSource ⊆ twoScale.first.finalCoarseShading.union
  ownerCell : Point3 → WZ2PaperCellIndex
  owner_active :
    ∀ point ∈ fullSource, ownerCell point ∈ witnesses.activeCells
  point_mem_owner :
    ∀ point ∈ fullSource,
      point ∈ wz1PaperGridCube rhoRequested.1 (ownerCell point)
  owner_witness_mem_parent :
    ∀ point ∈ fullSource,
      witnesses.witness (ownerCell point) ∈
        wz1PaperGridCube sqrtRequested.1 parent
  anchorCell : WZ2PaperCellIndex
  anchor_selected : anchorCell ∈ pullback.selectedCells
  anchor_active : anchorCell ∈ witnesses.activeCells
  anchor_witness_mem_parent :
    witnesses.witness anchorCell ∈
      wz1PaperGridCube sqrtRequested.1 parent
  fullSource_in_anchor_ball :
    fullSource ⊆
      Metric.closedBall (witnesses.witness anchorCell)
        (2 * sqrtRequested.1)
  owner_witness_in_anchor_ball :
    ∀ point ∈ fullSource,
      witnesses.witness (ownerCell point) ∈
        Metric.closedBall (witnesses.witness anchorCell)
          (2 * sqrtRequested.1)
  heightLeft : ℝ := (parent.2.2 : ℝ) * sqrtRequested.1
  source_height :
    ∀ point ∈ fullSource,
      point (2 : Fin 3) ∈
        Set.Ico heightLeft (heightLeft + sqrtRequested.1)
  height_window :
    Set.Ico heightLeft (heightLeft + sqrtRequested.1) ⊆
      Set.Icc (-1 : ℝ) 1

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta rho : ℝ}
    {schedule : PureWZ2Node05V4RichSecondCallSchedule sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource
      sigma inputLoss delta capability.normalizationExponent}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {inputLossLe :
      inputLoss ≤ (schedule.firstCallSchedule capability).kernel.sourceLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {twoScale : PureWZ2Node05V4RichSecondCallData
      schedule current rhoRequested inputLossLe sqrtRequested}
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (witnesses : PureWZ2Node05V4RichCoarseCellWitnessData twoScale)

/-- Construct the genuine first-coarse source in one active second-cover cell.
The only choices are points from positive-measure balanced cells. -/
theorem secondStageSourceAt
    (parent : WZ2PaperCellIndex)
    (hparent : parent ∈ twoScale.secondBalancedCover.activeCells) :
    Nonempty
      (PureWZ2Node05V4RichSecondStageSourceData
        pullback witnesses parent) := by
  let fullSource := twoScale.secondRefinedFineShading.union ∩
    wz1PaperGridCube sqrtRequested.1 parent
  have hfullMeasurable : MeasurableSet fullSource :=
    (measurableSet_shading_union twoScale.secondRefinedFineShading).inter
      (wz1PaperGridCube_measurable parent)
  have hfullVolume :
      volume fullSource = twoScale.secondBalancedCover.cellMass := by
    exact twoScale.secondBalancedCover.fine_cell_mass parent hparent
  have hfullNonempty : fullSource.Nonempty := by
    by_contra hempty
    have hzero : volume fullSource = 0 := by
      rw [Set.not_nonempty_iff_eq_empty.mp hempty]
      simp
    rw [hfullVolume] at hzero
    exact twoScale.secondBalancedCover.cellMass_pos.ne' hzero
  have hfullFirst :
      fullSource ⊆ twoScale.first.finalCoarseShading.union := by
    intro point hpoint
    rcases hpoint.1 with ⟨index, hindex⟩
    exact ⟨twoScale.secondSticky.selected.embedding index,
      twoScale.secondSticky.subshading index hindex⟩
  let ownerCell : Point3 → WZ2PaperCellIndex := fun point =>
    wz1PaperGridIndex rhoRequested.1 point
  have hownerSelected :
      ∀ point ∈ fullSource, ownerCell point ∈ pullback.selectedCells := by
    intro point hpoint
    rw [pullback.selectedCells_eq, mem_wz1PaperActiveCells]
    refine ⟨?_, point, hpoint.1, ?_⟩
    · apply paper_point_gridIndex_in_window
        twoScale.first.publicSticky.coarse_extremal.delta_pos
      exact shading_union_subset_axisBox (hfullFirst hpoint)
    · exact (mem_wz1PaperGridCube _ _ _).mpr rfl
  have hownerActive :
      ∀ point ∈ fullSource, ownerCell point ∈ witnesses.activeCells := by
    intro point hpoint
    rw [witnesses.activeCells_eq]
    exact pullback.selectedCells_subset_first (hownerSelected point hpoint)
  have hpointOwner :
      ∀ point ∈ fullSource,
        point ∈ wz1PaperGridCube rhoRequested.1 (ownerCell point) := by
    intro point _
    exact (mem_wz1PaperGridCube _ _ _).mpr rfl
  have hownerWitnessParent :
      ∀ point ∈ fullSource,
        witnesses.witness (ownerCell point) ∈
          wz1PaperGridCube sqrtRequested.1 parent := by
    intro point hpoint
    rcases hpoint.1 with ⟨index, hindex⟩
    rcases twoScale.second.terminal.fine_cell_nested index point hindex with
      ⟨nestedParent, hnestedActive, hnested⟩
    have hpointNested :
        point ∈ wz1PaperGridCube sqrtRequested.1 nestedParent :=
      hnested ((mem_wz1PaperGridCube _ _ _).mpr rfl)
    have hnestedEq : nestedParent = parent :=
      ((mem_wz1PaperGridCube _ nestedParent point).mp hpointNested).symm.trans
        ((mem_wz1PaperGridCube _ parent point).mp hpoint.2)
    rw [← hnestedEq]
    exact hnested (witnesses.witness_mem_cell _ (hownerActive point hpoint))
  let firstPoint := Classical.choose hfullNonempty
  have hfirstPoint : firstPoint ∈ fullSource :=
    Classical.choose_spec hfullNonempty
  let anchorCell := ownerCell firstPoint
  have hanchorActive : anchorCell ∈ witnesses.activeCells :=
    hownerActive firstPoint hfirstPoint
  have hanchorSelected : anchorCell ∈ pullback.selectedCells :=
    hownerSelected firstPoint hfirstPoint
  have hanchorParent :
      witnesses.witness anchorCell ∈
        wz1PaperGridCube sqrtRequested.1 parent :=
    hownerWitnessParent firstPoint hfirstPoint
  have hroot : 0 < sqrtRequested.1 :=
    twoScale.secondSticky.coarse_extremal.delta_pos
  have hfullBall :
      fullSource ⊆ Metric.closedBall (witnesses.witness anchorCell)
        (2 * sqrtRequested.1) := by
    intro point hpoint
    rw [Metric.mem_closedBall]
    exact le_of_lt
      (wz1_paper_grid_cube_diameter_lt_two_rho hroot hpoint.2 hanchorParent)
  have hownerWitnessBall :
      ∀ point ∈ fullSource,
        witnesses.witness (ownerCell point) ∈
          Metric.closedBall (witnesses.witness anchorCell)
            (2 * sqrtRequested.1) := by
    intro point hpoint
    rw [Metric.mem_closedBall]
    exact le_of_lt
      (wz1_paper_grid_cube_diameter_lt_two_rho hroot
        (hownerWitnessParent point hpoint) hanchorParent)
  let heightLeft := (parent.2.2 : ℝ) * sqrtRequested.1
  have hsourceHeight :
      ∀ point ∈ fullSource,
        point (2 : Fin 3) ∈
          Set.Ico heightLeft (heightLeft + sqrtRequested.1) := by
    intro point hpoint
    have hcell := hpoint.2
    rw [wz1PaperGridCube_eq_Ico hroot parent] at hcell
    exact ⟨hcell.2.2.2.2.1, by
      dsimp only [heightLeft]
      have hupper := hcell.2.2.2.2.2
      nlinarith⟩
  have hheightWindow :
      Set.Ico heightLeft (heightLeft + sqrtRequested.1) ⊆
        Set.Icc (-1 : ℝ) 1 := by
    intro height hheight
    let point : Point3 :=
      point3 (((parent.1 : ℝ) + 1 / 2) * sqrtRequested.1)
        (((parent.2.1 : ℝ) + 1 / 2) * sqrtRequested.1) height
    have hpointCell :
        point ∈ wz1PaperGridCube sqrtRequested.1 parent := by
      rw [wz1PaperGridCube_eq_Ico hroot parent]
      change
        (parent.1 : ℝ) * sqrtRequested.1 ≤ point 0 ∧
        point 0 < ((parent.1 : ℝ) + 1) * sqrtRequested.1 ∧
        (parent.2.1 : ℝ) * sqrtRequested.1 ≤ point 1 ∧
        point 1 < ((parent.2.1 : ℝ) + 1) * sqrtRequested.1 ∧
        (parent.2.2 : ℝ) * sqrtRequested.1 ≤ point 2 ∧
        point 2 < ((parent.2.2 : ℝ) + 1) * sqrtRequested.1
      have hp0 :
          point 0 = ((parent.1 : ℝ) + 1 / 2) * sqrtRequested.1 := by
        simp [point, point3]
      have hp1 :
          point 1 = ((parent.2.1 : ℝ) + 1 / 2) * sqrtRequested.1 := by
        simp [point, point3]
      have hp2 : point 2 = height := by simp [point, point3]
      rw [hp0, hp1, hp2]
      dsimp only [heightLeft] at hheight
      constructor
      · nlinarith
      constructor
      · nlinarith
      constructor
      · nlinarith
      constructor
      · nlinarith
      constructor
      · exact hheight.1
      · nlinarith [hheight.2]
    have hcoarse : point ∈ twoScale.secondFinalCoarseShading.union := by
      rw [twoScale.secondBalancedCover.coarse_union_eq]
      exact Set.mem_iUnion₂.mpr ⟨parent, hparent, hpointCell⟩
    have hbox := shading_union_subset_axisBox hcoarse
    have hp2 : point (2 : Fin 3) = height := by simp [point, point3]
    rw [← hp2]
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
  exact
    ⟨{ parent_active := hparent
       fullSource := fullSource
       fullSource_eq := rfl
       fullSource_measurable := hfullMeasurable
       fullSource_nonempty := hfullNonempty
       fullSource_volume := hfullVolume
       fullSource_subset_first_coarse := hfullFirst
       ownerCell := ownerCell
       owner_active := hownerActive
       point_mem_owner := hpointOwner
       owner_witness_mem_parent := hownerWitnessParent
       anchorCell := anchorCell
       anchor_selected := hanchorSelected
       anchor_active := hanchorActive
       anchor_witness_mem_parent := hanchorParent
       fullSource_in_anchor_ball := hfullBall
       owner_witness_in_anchor_ball := hownerWitnessBall
       heightLeft := heightLeft
       source_height := hsourceHeight
       height_window := hheightWindow }⟩

end PureWZ2Node05V4RichTwoScaleCellPullbackData

namespace PureWZ2Node05V4RichSecondStageSourceData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma outputLoss inputLoss delta rho : ℝ}
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
    {witnesses : PureWZ2Node05V4RichCoarseCellWitnessData twoScale}
    {parent : WZ2PaperCellIndex}
    (source : PureWZ2Node05V4RichSecondStageSourceData
      pullback witnesses parent)

/-- The chosen P1 anchor belongs to the synchronized final source pullback.
This keeps the later fixed-line geometry on the same literal witness chain. -/
theorem anchor_mem_pullback :
    witnesses.witness source.anchorCell ∈ pullback.shading.union := by
  rcases witnesses.witness_mem_refined source.anchorCell source.anchor_active with
    ⟨selectedIndex, hselected⟩
  have hregion : witnesses.witness source.anchorCell ∈
      pullback.retainedRegion := by
    rw [pullback.retainedRegion_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨source.anchorCell, source.anchor_selected, by
        simpa only [pullback.rhoRequested_eq] using
          witnesses.witness_mem_cell source.anchorCell source.anchor_active⟩
  have hpostFine : witnesses.witness source.anchorCell ∈
      pullback.postFirstFineShading.union := by
    refine ⟨selectedIndex, ?_⟩
    rw [pullback.postFirstFineShading_eq]
    exact ⟨hselected, by
      rw [← pullback.retainedRegion_eq]
      exact hregion⟩
  change witnesses.witness source.anchorCell ∈
    pullback.postSourceShading.union
  rw [pullback.postSourceShading_eq, pullback.zeroExtension.union_eq]
  exact hpostFine

/-- The second balanced cell alone supplies the paper-sized coarse source.
The first cell mass is reserved for the later pullback to the final
`delta`-source and does not enter this local-grain lower bound. -/
theorem fullSource_rho_power_lower :
    Kakeya.realRpowENN rhoRequested.1
        (3 / 2 + sigma / 2 + twoScale.second.terminalLoss) ≤
      volume source.fullSource := by
  calc
    _ ≤ twoScale.secondBalancedCover.cellMass :=
      twoScale.second_cellMass_rho_power_lower
    _ = volume source.fullSource := source.fullSource_volume.symm

end PureWZ2Node05V4RichSecondStageSourceData

end Kakeya.Assouad

end
