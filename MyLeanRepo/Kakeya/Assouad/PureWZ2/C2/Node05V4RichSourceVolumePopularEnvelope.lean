import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSourceVolumePopularHeights

/-!
# Complete source-cell envelope of V4 volume-popular heights

The exact source-volume-popular shading is enlarged only to complete current
source `delta` cells which meet its height region.  Every envelope point stays
within one source-cell diameter of a genuinely volume-popular point.  This is
the V4 analogue of `PureWZ2SourceWindowHeightPopularData`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichSourceVolumePopularEnvelopeData
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
    (popular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex) where
  heightCells : Finset WZ2PaperCellIndex :=
    (wz1PaperActiveCells current.grain.shading
      current.grain.extremal.delta_pos).filter fun cell =>
        (wz1PaperGridCube delta cell ∩ popular.popular.heightRegion).Nonempty
  heightCells_eq :
    heightCells =
      (wz1PaperActiveCells current.grain.shading
        current.grain.extremal.delta_pos).filter fun cell =>
          (wz1PaperGridCube delta cell ∩ popular.popular.heightRegion).Nonempty
  region : Set Point3 :=
    ⋃ cell ∈ heightCells, wz1PaperGridCube delta cell
  region_eq :
    region = ⋃ cell ∈ heightCells, wz1PaperGridCube delta cell
  region_measurable : MeasurableSet region
  shading : WZ1PaperTubeShading current.grain.family
  carrier_eq : ∀ index,
    shading.carrier index = current.grain.shading.carrier index ∩ region
  subshading_current :
    PureWZ2PaperIsSubshading shading current.grain.shading
  union_eq : shading.union = current.grain.shading.union ∩ region
  popular_subset : popular.popular.shading.union ⊆ shading.union
  volume_pos : 0 < volume shading.union
  volume_ne_top : volume shading.union ≠ ⊤
  whole_cells : WZ1PaperIsCubicalShading shading
  source_volume_retention :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 ≤
      (popular.popular.bins : ENNReal) * volume shading.union
  point_near_height_region :
    ∀ point ∈ shading.union,
      ∃ anchor ∈ popular.popular.heightRegion,
        dist point anchor < 2 * delta

namespace PureWZ2Node05V4RichSourceVolumePopularHeightData

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
    (popular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex)

/-- Build the complete current-source cell envelope before any fixed-line or
graph choice. -/
theorem wholeCellEnvelope :
    Nonempty
      (PureWZ2Node05V4RichSourceVolumePopularEnvelopeData popular) := by
  let heightCells :=
    (wz1PaperActiveCells current.grain.shading
      current.grain.extremal.delta_pos).filter fun cell =>
        (wz1PaperGridCube delta cell ∩ popular.popular.heightRegion).Nonempty
  let region : Set Point3 :=
    ⋃ cell ∈ heightCells, wz1PaperGridCube delta cell
  have hregionMeas : MeasurableSet region :=
    MeasurableSet.biUnion heightCells.finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  let shading : WZ1PaperTubeShading current.grain.family :=
    { carrier := fun index => current.grain.shading.carrier index ∩ region
      measurable_carrier := fun index =>
        (current.grain.shading.measurable_carrier index).inter hregionMeas
      subset_body := fun index => Set.inter_subset_left.trans
        (current.grain.shading.subset_body index) }
  have hunion :
      shading.union = current.grain.shading.union ∩ region := by
    ext point
    constructor
    · rintro ⟨index, hsource, hregion⟩
      exact ⟨⟨index, hsource⟩, hregion⟩
    · rintro ⟨⟨index, hsource⟩, hregion⟩
      exact ⟨index, hsource, hregion⟩
  have hpopularSubset :
      popular.popular.shading.union ⊆ shading.union := by
    intro point hpoint
    rw [popular.popular.union_eq] at hpoint
    have hpopularSource :
        point ∈ popular.sourcePopularShading.union :=
      hpoint.1
    have hslabSource :
        point ∈
          (pullback.standardSqrtSlabSourceShading heightIndex.1.1).union :=
      popular.sourcePopularShading_sub_slab.union_subset hpopularSource
    have hcurrent :
        point ∈ current.grain.shading.union :=
      (pullback.standardSqrtSlabSourceShading_sub_source
        heightIndex.1.1).union_subset hslabSource
    rcases hcurrent with ⟨index, hindex⟩
    have hactive :
        wz1PaperGridIndex delta point ∈
          wz1PaperActiveCells current.grain.shading
            current.grain.extremal.delta_pos := by
      have hsourceCells : point ∈ current.grain.shading.union := ⟨index, hindex⟩
      rw [current.grain.cubical.union_eq_activeCells
        current.grain.extremal.delta_pos] at hsourceCells
      rcases Set.mem_iUnion₂.mp hsourceCells with
        ⟨cell, hcell, hpointCell⟩
      have hcellEq : cell = wz1PaperGridIndex delta point :=
        (mem_wz1PaperGridCube delta cell point).mp hpointCell |>.symm
      rwa [← hcellEq]
    have hheightCell :
        wz1PaperGridIndex delta point ∈ heightCells := by
      change wz1PaperGridIndex delta point ∈
        (wz1PaperActiveCells current.grain.shading
          current.grain.extremal.delta_pos).filter _
      rw [Finset.mem_filter]
      exact ⟨hactive, point,
        (mem_wz1PaperGridCube delta _ point).mpr rfl, hpoint.2⟩
    rw [hunion]
    exact ⟨⟨index, hindex⟩, Set.mem_iUnion₂.mpr
      ⟨wz1PaperGridIndex delta point, hheightCell,
        (mem_wz1PaperGridCube delta _ point).mpr rfl⟩⟩
  have hvolumePos : 0 < volume shading.union := by
    have hpopularPos : 0 < volume popular.popular.shading.union := by
      rcases popular.popular.heightIndices_nonempty with
        ⟨selectedHeight, hselectedHeight⟩
      apply popular.popular.layerMass_pos.trans_le
      calc
        popular.popular.layerMass ≤
            volume
              (popular.sourcePopularShading.union ∩
                wz1Lemma23HeightSlab (256 * rho) selectedHeight) :=
          (popular.popular.layer_volume_band
            selectedHeight hselectedHeight).1
        _ ≤ ∑ selectedHeight ∈ popular.popular.heightIndices,
            volume
              (popular.sourcePopularShading.union ∩
                wz1Lemma23HeightSlab (256 * rho) selectedHeight) :=
          Finset.single_le_sum
            (f := fun selectedHeight =>
              volume
                (popular.sourcePopularShading.union ∩
                  wz1Lemma23HeightSlab (256 * rho) selectedHeight))
            (fun _ _ => bot_le) hselectedHeight
        _ = volume popular.popular.shading.union :=
          popular.popular.volume_eq_sum.symm
    exact hpopularPos.trans_le (measure_mono hpopularSubset)
  have hvolumeTop : volume shading.union ≠ ⊤ := by
    have hball : shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
      intro point hpoint
      rw [hunion] at hpoint
      have hnorm := norm_le_two_of_mem_paperShading hpoint.1
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    exact ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint other hother
    have hsourceOther :=
      current.grain.cubical index point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    have hcellEq :
        cell = wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta cell point).mp hpointCell |>.symm
    exact ⟨hsourceOther, Set.mem_iUnion₂.mpr
      ⟨cell, hcell, by simpa [hcellEq] using hother⟩⟩
  have hretention :
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 ≤
        (popular.popular.bins : ENNReal) * volume shading.union := by
    calc
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) / 2 / 2 ≤
          volume popular.continuous.popularRegion / 2 := by
        gcongr
        exact popular.continuous.popularRegion_half_volume
      _ = volume popular.sourcePopularShading.union / 2 := by
        rw [popular.sourcePopularShading_union]
      _ ≤ (popular.popular.bins : ENNReal) *
          volume popular.popular.shading.union :=
        popular.popular.retained_volume
      _ ≤ (popular.popular.bins : ENNReal) * volume shading.union := by
        simpa [mul_comm] using
          mul_le_mul_right (measure_mono hpopularSubset)
            (popular.popular.bins : ENNReal)
  have hnear :
      ∀ point ∈ shading.union,
        ∃ anchor ∈ popular.popular.heightRegion,
          dist point anchor < 2 * delta := by
    intro point hpoint
    rw [hunion] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    have hmeeting := (Finset.mem_filter.mp hcell).2
    rcases hmeeting with ⟨anchor, hanchorCell, hanchorHeight⟩
    exact ⟨anchor, hanchorHeight,
      wz1_paper_grid_cube_diameter_lt_two_rho
        current.grain.extremal.delta_pos hpointCell hanchorCell⟩
  exact ⟨{
    heightCells := heightCells
    heightCells_eq := rfl
    region := region
    region_eq := rfl
    region_measurable := hregionMeas
    shading := shading
    carrier_eq := fun _ => rfl
    subshading_current := fun _ => Set.inter_subset_left
    union_eq := hunion
    popular_subset := hpopularSubset
    volume_pos := hvolumePos
    volume_ne_top := hvolumeTop
    whole_cells := hwhole
    source_volume_retention := hretention
    point_near_height_region := hnear
  }⟩

end PureWZ2Node05V4RichSourceVolumePopularHeightData

end Kakeya.Assouad

end
