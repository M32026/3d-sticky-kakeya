import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightCommonBin

/-!
# Whole-cell graph envelope of the joint-height fixed bin

The integrated fixed-bin region is enlarged only to complete current-source
`delta` cells meeting it.  This is the production graph carrier.  Its volume
dominates the integrated bin mass, and every graph point is within `2 * delta`
of the same fixed-bin witness and hence of the preselected source-volume band.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

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
    {volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    {B₀ threshold : ENNReal}
    (block : volumePopular.JointHeightCommonBinData B₀ threshold)

theorem jointFixedBinHeightRegion_measurable :
    MeasurableSet
      (volumePopular.jointFixedBinHeightRegion
        block.referenceHeight block.bin) := by
  apply (measurableSet_pureWZ2FixedCommonBinRegion
    volumePopular.jointSourceSet_measurable
    current.grain.globalGrains.slope block.referenceHeight
    (Real.sqrt rho) block.bin).inter
  exact volumePopular.jointPopularHeights_measurable.preimage (by fun_prop)

theorem jointFixedBinHeightRegion_volume :
    volume (volumePopular.jointFixedBinHeightRegion
        block.referenceHeight block.bin) =
      volumePopular.jointIntegratedBinMass
        block.referenceHeight block.bin := by
  let fixedRegion :=
    pureWZ2FixedCommonBinRegion volumePopular.jointSourceSet
      current.grain.globalGrains.slope block.referenceHeight
      (Real.sqrt rho) block.bin
  let heights := volumePopular.jointPopularHeights
  let restricted :=
    volumePopular.jointFixedBinHeightRegion
      block.referenceHeight block.bin
  have hslice : ∀ height : ℝ,
      wz1Lemma23PlanarSlice restricted height =
        if height ∈ heights then
          wz1Lemma23PlanarSlice fixedRegion height
        else ∅ := by
    intro height
    by_cases hheight : height ∈ heights
    · rw [if_pos hheight]
      ext point
      simp only [wz1Lemma23_mem_planarSlice_iff]
      constructor
      · exact fun hpoint => hpoint.1
      · intro hpoint
        exact ⟨hpoint, by simpa [point3] using hheight⟩
    · rw [if_neg hheight]
      ext point
      simp only [Set.notMem_empty, iff_false]
      rw [wz1Lemma23_mem_planarSlice_iff]
      exact fun hpoint => hheight (by simpa [point3] using hpoint.2)
  rw [wz1_lemma23_volume_eq_lintegral_planarSlice restricted
    (volumePopular.jointFixedBinHeightRegion_measurable block)]
  change
    (∫⁻ height : ℝ,
      volume (wz1Lemma23PlanarSlice restricted height)) =
    ∫⁻ height in heights,
      volume (wz1Lemma23PlanarSlice fixedRegion height)
  rw [← lintegral_indicator
    (by simpa [heights] using volumePopular.jointPopularHeights_measurable)]
  apply lintegral_congr
  intro height
  rw [hslice height]
  by_cases hheight : height ∈ heights
  · simp [hheight, fixedRegion, heights]
  · simp [hheight]

theorem jointFixedBinHeightRegion_subset_source :
    volumePopular.jointFixedBinHeightRegion
        block.referenceHeight block.bin ⊆ current.grain.shading.union := by
  intro point hpoint
  exact volumePopular.jointSourceSet_subset_current hpoint.1.1

theorem jointFixedBinHeightRegion_subset_volumePopular :
    volumePopular.jointFixedBinHeightRegion
        block.referenceHeight block.bin ⊆
      volumePopular.popular.heightRegion := by
  intro point hpoint
  have hsource : point ∈ volumePopular.jointSourceSet := hpoint.1.1
  rw [jointSourceSet, volumePopular.popular.union_eq] at hsource
  exact hsource.2

/-- Whole current-source `delta` cells meeting the selected fixed-bin
restriction. -/
def jointGraphCells : Finset WZ2PaperCellIndex :=
  (wz1PaperActiveCells current.grain.shading
    current.grain.extremal.delta_pos).filter fun cell =>
      (wz1PaperGridCube delta cell ∩
        volumePopular.jointFixedBinHeightRegion
          block.referenceHeight block.bin).Nonempty

def jointGraphRegion : Set Point3 :=
  ⋃ cell ∈ volumePopular.jointGraphCells block,
    wz1PaperGridCube delta cell

structure JointHeightGraphEnvelopeData where
  cells : Finset WZ2PaperCellIndex := volumePopular.jointGraphCells block
  cells_eq : cells = volumePopular.jointGraphCells block
  region : Set Point3 := volumePopular.jointGraphRegion block
  region_eq : region = volumePopular.jointGraphRegion block
  region_measurable : MeasurableSet region
  shading : WZ1PaperTubeShading current.grain.family
  carrier_eq : ∀ index,
    shading.carrier index = current.grain.shading.carrier index ∩ region
  subshading_current :
    PureWZ2PaperIsSubshading shading current.grain.shading
  union_eq : shading.union = current.grain.shading.union ∩ region
  whole_cells : WZ1PaperIsCubicalShading shading
  fixedBin_subset :
    volumePopular.jointFixedBinHeightRegion
        block.referenceHeight block.bin ⊆ shading.union
  fixedBin_volume_lower :
    volumePopular.jointIntegratedBinMass
        block.referenceHeight block.bin ≤ volume shading.union
  source_average :
    volume volumePopular.jointSourceSet ≤
      4 * ((volumePopular.jointRichCommonBinLabels
        block.referenceHeight threshold).card : ENNReal) *
        volume shading.union
  volume_pos : 0 < volume shading.union
  volume_ne_top : volume shading.union ≠ ⊤
  point_near_fixedBin :
    ∀ point ∈ shading.union,
      ∃ anchor ∈ volumePopular.jointFixedBinHeightRegion
          block.referenceHeight block.bin,
        dist point anchor < 2 * delta
  point_near_volumePopular :
    ∀ point ∈ shading.union,
      ∃ anchor ∈ volumePopular.popular.heightRegion,
        dist point anchor < 2 * delta

theorem jointHeightGraphEnvelope :
    Nonempty (volumePopular.JointHeightGraphEnvelopeData block) := by
  let cells := volumePopular.jointGraphCells block
  let region := volumePopular.jointGraphRegion block
  have hregionMeas : MeasurableSet region :=
    MeasurableSet.biUnion cells.finite_toSet.countable
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
  have hfixedSubset :
      volumePopular.jointFixedBinHeightRegion
          block.referenceHeight block.bin ⊆ shading.union := by
    intro point hpoint
    have hsource :=
      volumePopular.jointFixedBinHeightRegion_subset_source block hpoint
    rcases hsource with ⟨index, hindex⟩
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
    have hcell :
        wz1PaperGridIndex delta point ∈ cells := by
      change wz1PaperGridIndex delta point ∈
        (wz1PaperActiveCells current.grain.shading
          current.grain.extremal.delta_pos).filter _
      rw [Finset.mem_filter]
      exact ⟨hactive, point,
        (mem_wz1PaperGridCube delta _ point).mpr rfl, hpoint⟩
    rw [hunion]
    exact ⟨⟨index, hindex⟩, Set.mem_iUnion₂.mpr
      ⟨wz1PaperGridIndex delta point, hcell,
        (mem_wz1PaperGridCube delta _ point).mpr rfl⟩⟩
  have hwhole : WZ1PaperIsCubicalShading shading := by
    intro index point hpoint other hother
    have hsourceOther :=
      current.grain.cubical index point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    have hcellEq : cell = wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta cell point).mp hpointCell |>.symm
    exact ⟨hsourceOther, Set.mem_iUnion₂.mpr
      ⟨cell, hcell, by simpa [hcellEq] using hother⟩⟩
  have hfixedVolume :
      volumePopular.jointIntegratedBinMass
          block.referenceHeight block.bin ≤ volume shading.union := by
    rw [← volumePopular.jointFixedBinHeightRegion_volume block]
    exact measure_mono hfixedSubset
  have hsourceAverage :
      volume volumePopular.jointSourceSet ≤
        4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
          volume shading.union :=
    block.source_average.trans (by gcongr)
  have hvolumePos : 0 < volume shading.union := by
    have hproductPos :
        0 < 4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
          volume shading.union :=
      volumePopular.jointSourceSet_volume_pos.trans_le hsourceAverage
    by_contra hnot
    have hzero : volume shading.union = 0 :=
      bot_unique (not_lt.mp hnot)
    rw [hzero, mul_zero] at hproductPos
    exact (lt_irrefl 0 hproductPos)
  have hvolumeTop : volume shading.union ≠ ⊤ := by
    have hball : shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
      intro point hpoint
      rw [hunion] at hpoint
      have hnorm := norm_le_two_of_mem_paperShading hpoint.1
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    exact ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  have hnearFixed :
      ∀ point ∈ shading.union,
        ∃ anchor ∈ volumePopular.jointFixedBinHeightRegion
            block.referenceHeight block.bin,
          dist point anchor < 2 * delta := by
    intro point hpoint
    rw [hunion] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    have hmeeting := (Finset.mem_filter.mp hcell).2
    rcases hmeeting with ⟨anchor, hanchorCell, hanchorFixed⟩
    exact ⟨anchor, hanchorFixed,
      wz1_paper_grid_cube_diameter_lt_two_rho
        current.grain.extremal.delta_pos hpointCell hanchorCell⟩
  exact ⟨{
    cells := cells
    cells_eq := rfl
    region := region
    region_eq := rfl
    region_measurable := hregionMeas
    shading := shading
    carrier_eq := fun _ => rfl
    subshading_current := fun _ => Set.inter_subset_left
    union_eq := hunion
    whole_cells := hwhole
    fixedBin_subset := hfixedSubset
    fixedBin_volume_lower := hfixedVolume
    source_average := hsourceAverage
    volume_pos := hvolumePos
    volume_ne_top := hvolumeTop
    point_near_fixedBin := hnearFixed
    point_near_volumePopular := fun point hpoint => by
      rcases hnearFixed point hpoint with ⟨anchor, hanchor, hdist⟩
      exact ⟨anchor,
        volumePopular.jointFixedBinHeightRegion_subset_volumePopular
          block hanchor, hdist⟩
  }⟩

end PureWZ2Node05V4RichSourceVolumePopularHeightData

end Kakeya.Assouad

end
