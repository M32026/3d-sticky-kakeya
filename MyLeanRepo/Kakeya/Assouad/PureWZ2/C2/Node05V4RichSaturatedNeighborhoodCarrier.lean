import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedNeighborhoodFullGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredPreparationABI

/-!
# The same-height saturated neighborhood as a graph carrier

This module packages the union of the selected parents' same-height
saturations as an ordinary finite shading solely for the WZ Lemma 5.3 graph.
Each occupied graph cell is made into one artificial tube whose carrier
contains that cell; no CWA, extremality, or original-tube provenance is
asserted for this auxiliary family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

namespace PureWZ2PreCommonBinGlobalGrainNeighborhoodData

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
    (neighborhood : PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback)

def saturatedGraphScale
    (_neighborhood :
      PureWZ2PreCommonBinGlobalGrainNeighborhoodData pullback) : ℝ :=
  256 * rho

theorem saturatedGraphScale_pos : 0 < neighborhood.saturatedGraphScale := by
  dsimp only [saturatedGraphScale]
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  positivity

/-- Union of the same-height saturated carriers over the selected parents. -/
def saturatedUnion : Set Point3 :=
  ⋃ y ∈ neighborhood.sample,
    pullback.sameHeightParentSaturation (neighborhood.cube y)

theorem saturatedUnion_measurable :
    MeasurableSet neighborhood.saturatedUnion := by
  exact MeasurableSet.biUnion neighborhood.sample.finite_toSet.countable
    (fun y _ => pullback.sameHeightParentSaturation_measurable
      (neighborhood.cube y))

theorem saturatedUnion_subset_secondRefined :
    neighborhood.saturatedUnion ⊆
      twoScale.secondRefinedFineShading.union := by
  intro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨y, _hy, hpointParent⟩
  exact pullback.sameHeightParentSaturation_subset_secondRefined
    (neighborhood.cube y) hpointParent

theorem saturatedUnion_height :
    ∀ point ∈ neighborhood.saturatedUnion,
      point (2 : Fin 3) ∈
        Set.Ico
          ((neighborhood.heightIndex.1 : ℝ) * Real.sqrt rho)
          ((neighborhood.heightIndex.1 : ℝ) * Real.sqrt rho +
            Real.sqrt rho) := by
  intro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨y, hy, hpointParent⟩
  have hpointCube :=
    pullback.sameHeightParentSaturation_subset_parent hpointParent
  have hparentHeight := pullback.standardSqrtSlabParent_height
    (neighborhood.cube_mem y hy)
  have hroot : 0 < sqrtRequested.1 :=
    twoScale.secondSticky.coarse_extremal.delta_pos
  rw [wz1PaperGridCube_eq_Ico hroot] at hpointCube
  rw [hparentHeight] at hpointCube
  change
    (neighborhood.heightIndex.1 : ℝ) * Real.sqrt rho ≤
        point (2 : Fin 3) ∧
      point (2 : Fin 3) <
        (neighborhood.heightIndex.1 : ℝ) * Real.sqrt rho +
          Real.sqrt rho
  simpa only [pullback.sqrtRequested_eq,
    show (((neighborhood.heightIndex.1 : ℝ) + 1) * Real.sqrt rho) =
      (neighborhood.heightIndex.1 : ℝ) * Real.sqrt rho +
        Real.sqrt rho by ring] using hpointCube.2.2.2.2

/-- Every point of the saturated carrier has an actual source point at the
same height in the same selected parent. -/
theorem saturatedUnion_exists_source_same_height
    {point : Point3} (hpoint : point ∈ neighborhood.saturatedUnion) :
    ∃ y ∈ neighborhood.sample,
      point ∈ pullback.sameHeightParentSaturation (neighborhood.cube y) ∧
      ∃ sourcePoint : Point3,
        sourcePoint ∈ pullback.preCommonBinFinePullback (neighborhood.cube y) ∧
        sourcePoint (2 : Fin 3) = point (2 : Fin 3) ∧
        dist point sourcePoint ≤ 2 * rho := by
  rcases Set.mem_iUnion₂.mp hpoint with ⟨y, hy, hpointParent⟩
  rcases Set.mem_iUnion₂.mp hpointParent with ⟨cell, hcell, hpointCell⟩
  rcases wz1PaperGridCubeSameHeightSaturation_exists_source_same_height
      (pullback.sameHeightSourceCell_subset_cube cell) hpointCell with
    ⟨sourcePoint, hsourcePoint, hheight⟩
  have hsourcePullback : sourcePoint ∈
      pullback.preCommonBinFinePullback (neighborhood.cube y) :=
    ⟨hsourcePoint.1.1, Set.mem_iUnion₂.mpr ⟨cell, hcell, hsourcePoint.2⟩⟩
  have hpointCell : point ∈ wz1PaperGridCube rho cell :=
    wz1PaperGridCubeSameHeightSaturation_subset_cube rho cell
      (pullback.sameHeightSourceCell cell) hpointCell
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  exact ⟨y, hy, hpointParent, sourcePoint, hsourcePullback, hheight,
    (wz1_paper_grid_cube_diameter_lt_two_rho hrho
      hpointCell hsourcePoint.2).le⟩

theorem saturatedUnion_projection_subset_source_thickening
    {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope z))
        (horizontalSlice neighborhood.saturatedUnion z) ⊆
      Metric.cthickening (4 * rho)
        (scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope z))
          (horizontalSlice pullback.shading.union z)) := by
  rintro value ⟨point, hpoint, rfl⟩
  rcases Set.mem_iUnion₂.mp hpoint.1 with ⟨y, _hy, hpointParent⟩
  exact
    (pullback.sameHeightParentSaturation_projection_subset_source_thickening
      hz) ⟨point, ⟨hpointParent, hpoint.2⟩, rfl⟩

theorem saturatedUnion_exactAD
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : neighborhood.saturatedGraphScale ≤ 1)
    (z : ℝ) (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    IsADSet1
      (scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope z))
        (horizontalSlice neighborhood.saturatedUnion z))
      neighborhood.saturatedGraphScale (1 - sigma)
      (160 * Kakeya.realRpowENN delta (-inputLoss)) := by
  let sourceProjection :=
    scalarProjection
      (globalGrainDirection (current.grain.globalGrains.slope z))
      (horizontalSlice pullback.shading.union z)
  let saturatedProjection :=
    scalarProjection
      (globalGrainDirection (current.grain.globalGrains.slope z))
      (horizontalSlice neighborhood.saturatedUnion z)
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hpaper : PureWZ2PaperADSet1 sourceProjection delta (1 - sigma)
      (Kakeya.realRpowENN delta (-inputLoss)) := by
    apply (current.grain.globalGrains.global_ad z hz).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point, ⟨pullback.subshading.union_subset hpoint.1, hpoint.2⟩, rfl⟩
  have hsourceBounded : sourceProjection ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hbox := shading_union_subset_axisBox
      (pullback.subshading.union_subset hpoint.1)
    have hx : |point 0| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have hy : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hslope := current.grain.globalGrains.slope_bound z hz
    have hformula :
        inner ℝ point
            (globalGrainDirection (current.grain.globalGrains.slope z)) =
          point 0 + current.grain.globalGrains.slope z * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    change inner ℝ point
        (globalGrainDirection (current.grain.globalGrains.slope z)) ∈
      Set.Icc (-4 : ℝ) 4
    rw [hformula]
    apply abs_le.mp
    calc
      |point 0 + current.grain.globalGrains.slope z * point 1| ≤
          |point 0| + |current.grain.globalGrains.slope z| * |point 1| := by
        simpa [abs_mul] using
          abs_add_le (point 0)
            (current.grain.globalGrains.slope z * point 1)
      _ ≤ 1 + 3 * 1 := by gcongr
      _ = 4 := by norm_num
  have hinternal : IsADSet1 sourceProjection delta (1 - sigma)
      (10 * Kakeya.realRpowENN delta (-inputLoss)) :=
    hbridge.1 _ delta (1 - sigma)
      (Kakeya.realRpowENN delta (-inputLoss)) hsourceBounded hpaper
  have hfourOne : 4 * rho ≤ 1 := by
    calc
      4 * rho ≤ neighborhood.saturatedGraphScale := by
        dsimp only [saturatedGraphScale]
        nlinarith
      _ ≤ 1 := hgraphOne
  have hsourceAtFour : IsADSet1 sourceProjection (4 * rho) (1 - sigma)
      (10 * Kakeya.realRpowENN delta (-inputLoss)) :=
    hinternal.coarsen_scale (by positivity)
      (by
        have hdeltaRho : delta ≤ rho := by
          rw [← pullback.rhoRequested_eq]
          exact rhoRequested.property.1
        linarith) hfourOne
  have hsaturatedBounded : saturatedProjection ⊆ Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hcoarsePoint : point ∈ twoScale.secondRefinedFineShading.union :=
      neighborhood.saturatedUnion_subset_secondRefined hpoint.1
    have hbox := shading_union_subset_axisBox hcoarsePoint
    have hx : |point 0| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have hy : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hslope := current.grain.globalGrains.slope_bound z hz
    have hformula :
        inner ℝ point
            (globalGrainDirection (current.grain.globalGrains.slope z)) =
          point 0 + current.grain.globalGrains.slope z * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    change inner ℝ point
        (globalGrainDirection (current.grain.globalGrains.slope z)) ∈
      Set.Icc (-4 : ℝ) 4
    rw [hformula]
    apply abs_le.mp
    calc
      |point 0 + current.grain.globalGrains.slope z * point 1| ≤
          |point 0| + |current.grain.globalGrains.slope z| * |point 1| := by
        simpa [abs_mul] using
          abs_add_le (point 0)
            (current.grain.globalGrains.slope z * point 1)
      _ ≤ 1 + 3 * 1 := by gcongr
      _ = 4 := by norm_num
  have hthick : saturatedProjection ⊆
      Metric.cthickening (4 * rho) sourceProjection := by
    simpa only [saturatedProjection, sourceProjection] using
      neighborhood.saturatedUnion_projection_subset_source_thickening hz
  have hdirect := hsourceAtFour.generalized_thickening
    hthick hsaturatedBounded (by positivity : 0 < 4 * rho)
      (by positivity : 0 < 4 * rho)
  have hratioOne : (4 * rho) / (4 * rho) = (1 : ℝ) := by
    field_simp [hrho.ne']
  rw [hratioOne] at hdirect
  have hceil : Nat.ceil (1 : ℝ) = 1 := by norm_num
  rw [hceil] at hdirect
  have hfourAD : IsADSet1 saturatedProjection (4 * rho) (1 - sigma)
      (160 * Kakeya.realRpowENN delta (-inputLoss)) := by
    convert hdirect using 1 <;> norm_num <;> ring
  exact hfourAD.coarsen_scale neighborhood.saturatedGraphScale_pos
    (by dsimp only [saturatedGraphScale]; nlinarith) hgraphOne

theorem saturatedUnion_volume_lower
    (target : ENNReal)
    (hparentFloor : ∀ y ∈ neighborhood.sample,
      target ≤ volume
        (pullback.sameHeightParentSaturation (neighborhood.cube y))) :
    (neighborhood.K : ENNReal) * target ≤
      volume neighborhood.saturatedUnion := by
  rw [show neighborhood.K = neighborhood.sample.card from neighborhood.K_eq]
  rw [show neighborhood.saturatedUnion =
      ⋃ y ∈ neighborhood.sample,
        pullback.sameHeightParentSaturation (neighborhood.cube y) from rfl]
  rw [MeasureTheory.measure_biUnion_finset]
  · calc
      (neighborhood.sample.card : ENNReal) * target =
          ∑ _y ∈ neighborhood.sample, target := by
        simp [Finset.sum_const]
      _ ≤ _ := Finset.sum_le_sum fun y hy => hparentFloor y hy
  · intro first hfirst second hsecond hne
    exact (wz1PaperGridCube_disjoint
      (fun hcube => hne (neighborhood.cube_injective hfirst hsecond hcube))).mono
      pullback.sameHeightParentSaturation_subset_parent
      pullback.sameHeightParentSaturation_subset_parent
  · intro y _
    exact pullback.sameHeightParentSaturation_measurable
      (neighborhood.cube y)

def saturatedGraphCells : Finset WZ2PaperCellIndex :=
  (wz1Lemma23BoundedCells neighborhood.saturatedGraphScale
      neighborhood.saturatedGraphScale_pos).filter fun cell =>
      (neighborhood.saturatedUnion ∩
        wz1Lemma23Cell neighborhood.saturatedGraphScale cell).Nonempty

abbrev SaturatedGraphCell :=
  {cell : WZ2PaperCellIndex // cell ∈ neighborhood.saturatedGraphCells}

def saturatedGraphCellTube
    (cell : neighborhood.SaturatedGraphCell) :
    Kakeya.DeltaTube neighborhood.saturatedGraphScale where
  base := Classical.choose
      (Finset.mem_filter.mp cell.property).2 -
    (1 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  direction := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  direction_unit := by simp

theorem saturatedGraphCell_subset_tube
    (cell : neighborhood.SaturatedGraphCell) :
    wz1Lemma23Cell neighborhood.saturatedGraphScale cell.1 ⊆
      (neighborhood.saturatedGraphCellTube cell).carrier := by
  intro point hpoint
  let tube := neighborhood.saturatedGraphCellTube cell
  let center := Classical.choose (Finset.mem_filter.mp cell.property).2
  have hcenterCell : center ∈
      wz1Lemma23Cell neighborhood.saturatedGraphScale cell.1 :=
    (Classical.choose_spec (Finset.mem_filter.mp cell.property).2).2
  have hcenter : center ∈ Kakeya.unitSegment tube.base tube.direction := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    dsimp [tube, center, saturatedGraphCellTube]
    module
  apply Metric.mem_cthickening_of_dist_le point center
    neighborhood.saturatedGraphScale
    (Kakeya.unitSegment tube.base tube.direction) hcenter
  apply wz1Lemma23_same_cell_dist neighborhood.saturatedGraphScale_pos
  exact hpoint.trans
    hcenterCell.symm

def saturatedGraphFamily : Kakeya.Streamlined.TubeFamily
    neighborhood.saturatedGraphScale where
  card := neighborhood.saturatedGraphCells.card
  tube index := neighborhood.saturatedGraphCellTube
    ((neighborhood.saturatedGraphCells.equivFin.symm index))

def saturatedGraphShading : Kakeya.Streamlined.TubeShading
    neighborhood.saturatedGraphFamily where
  carrier index :=
    neighborhood.saturatedUnion ∩
      wz1Lemma23Cell neighborhood.saturatedGraphScale
        ((neighborhood.saturatedGraphCells.equivFin.symm index).1)
  measurable_carrier index :=
    neighborhood.saturatedUnion_measurable.inter
      (wz1Lemma23Cell_measurable neighborhood.saturatedGraphScale_pos _)
  subset_body index := by
    intro point hpoint
    exact neighborhood.saturatedGraphCell_subset_tube
      (neighborhood.saturatedGraphCells.equivFin.symm index) hpoint.2

theorem saturatedGraphShading_union :
    neighborhood.saturatedGraphShading.union =
      neighborhood.saturatedUnion := by
  apply Set.Subset.antisymm
  · rintro point ⟨index, hpoint⟩
    change point ∈ neighborhood.saturatedUnion ∩
      wz1Lemma23Cell neighborhood.saturatedGraphScale
        ((neighborhood.saturatedGraphCells.equivFin.symm index).1) at hpoint
    exact hpoint.1
  · intro point hpoint
    let cell := wz1Lemma23CellIndex neighborhood.saturatedGraphScale point
    have hsource := neighborhood.saturatedUnion_subset_secondRefined hpoint
    have hnorm := norm_le_two_of_mem_paperShading hsource
    have hcellBounded : cell ∈
        wz1Lemma23BoundedCells neighborhood.saturatedGraphScale
          neighborhood.saturatedGraphScale_pos :=
      wz1Lemma23_index_mem_bounded_two
        neighborhood.saturatedGraphScale_pos hnorm
    have hpointCell : point ∈
        wz1Lemma23Cell neighborhood.saturatedGraphScale cell := rfl
    have hcell : cell ∈ neighborhood.saturatedGraphCells := by
      exact Finset.mem_filter.mpr
        ⟨hcellBounded, ⟨point, hpoint, hpointCell⟩⟩
    let index : Fin neighborhood.saturatedGraphCells.card :=
      neighborhood.saturatedGraphCells.equivFin ⟨cell, hcell⟩
    refine ⟨index, ?_⟩
    change point ∈ neighborhood.saturatedUnion ∩
      wz1Lemma23Cell neighborhood.saturatedGraphScale
        ((neighborhood.saturatedGraphCells.equivFin.symm index).1)
    refine ⟨hpoint, ?_⟩
    change point ∈ wz1Lemma23Cell neighborhood.saturatedGraphScale
      ((neighborhood.saturatedGraphCells.equivFin.symm index).1)
    simpa [index] using hpointCell

end PureWZ2PreCommonBinGlobalGrainNeighborhoodData

end Kakeya.Assouad

end
