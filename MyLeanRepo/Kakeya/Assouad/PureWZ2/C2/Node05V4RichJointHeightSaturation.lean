import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightGraphCarrier

/-!
# Same-height saturation of the joint fixed-bin source

The saturated horizontal base at every positive source height contains the
entire source slice.  Besides the resulting monotonicity, the paper's sharp
Fubini estimate records the horizontal gain `rho^2 / sliceCap`; the latter is
the quantitative input used to pay for the auxiliary Theorem-5.2 graph.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Same-height saturation of a measurable source piece inside one cube
dominates its source volume. -/
theorem source_volume_le_sameHeightSaturation_volume
    {rho : ℝ} {cell : WZ2PaperCellIndex} {source : Set Point3}
    (hsourceMeasurable : MeasurableSet source)
    (hsource : source ⊆ wz1PaperGridCube rho cell) :
    volume source ≤
      volume (wz1PaperGridCubeSameHeightSaturation rho cell source) := by
  rw [wz1_lemma23_volume_eq_lintegral_planarSlice source hsourceMeasurable]
  rw [wz1_lemma23_volume_eq_lintegral_planarSlice
    (wz1PaperGridCubeSameHeightSaturation rho cell source)
    (measurableSet_wz1PaperGridCubeSameHeightSaturation
      rho cell source hsourceMeasurable)]
  apply lintegral_mono
  intro height
  by_cases hzero : volume (wz1Lemma23PlanarSlice source height) = 0
  · change volume (wz1Lemma23PlanarSlice source height) ≤ _
    rw [hzero]
    exact bot_le
  · apply measure_mono
    intro planar hplanar
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hplanar
    apply wz1Lemma23_mem_planarSlice_iff.mpr
    constructor
    · exact hsource hlift
    · simpa [wz1Lemma23PositiveSliceHeights, point3] using
        (bot_lt_iff_ne_bot.mpr hzero :
          0 < volume (wz1Lemma23PlanarSlice source height))

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

namespace JointHeightCommonBinData

def jointFixedBinRhoCells : Finset WZ2PaperCellIndex :=
  (pullback.standardSqrtSlabRhoCells heightIndex.1.1).filter fun cell =>
    (volumePopular.jointFixedBinHeightRegion
      block.referenceHeight block.bin ∩
        wz1PaperGridCube rho cell).Nonempty

def jointCellSource (cell : WZ2PaperCellIndex) : Set Point3 :=
  volumePopular.jointFixedBinHeightRegion
      block.referenceHeight block.bin ∩
    wz1PaperGridCube rho cell

def jointCellSaturation (cell : WZ2PaperCellIndex) : Set Point3 :=
  wz1PaperGridCubeSameHeightSaturation rho cell
    (block.jointCellSource cell)

def jointSaturatedUnion : Set Point3 :=
  ⋃ cell ∈ block.jointFixedBinRhoCells,
    block.jointCellSaturation cell

theorem jointFixedBinRhoCells_subset_standard :
    block.jointFixedBinRhoCells ⊆
      pullback.standardSqrtSlabRhoCells heightIndex.1.1 :=
  Finset.filter_subset _ _

theorem jointFixedBinRhoCells_subset_selected :
    block.jointFixedBinRhoCells ⊆ pullback.selectedCells := by
  intro cell hcell
  exact pullback.standardSqrtSlabRhoCells_subset heightIndex.1.1
    (block.jointFixedBinRhoCells_subset_standard hcell)

theorem jointCellSource_measurable (cell : WZ2PaperCellIndex) :
    MeasurableSet (block.jointCellSource cell) :=
  (volumePopular.jointFixedBinHeightRegion_measurable block).inter
    (wz1PaperGridCube_measurable cell)

theorem jointCellSource_subset_cube (cell : WZ2PaperCellIndex) :
    block.jointCellSource cell ⊆ wz1PaperGridCube rho cell :=
  Set.inter_subset_right

theorem jointCellSource_volume_le_saturation
    (cell : WZ2PaperCellIndex) :
    volume (block.jointCellSource cell) ≤
      volume (block.jointCellSaturation cell) :=
  source_volume_le_sameHeightSaturation_volume
    (block.jointCellSource_measurable cell)
    (block.jointCellSource_subset_cube cell)

/-- The joint fixed-bin source inherits the same planar slice cap as the
complete post-two-call source cell containing it. -/
theorem jointCellSource_slice_volume_le
    {cell : WZ2PaperCellIndex}
    (hcell : cell ∈ block.jointFixedBinRhoCells)
    (z : ℝ)
    (hz : z ∈ wz1Lemma23PositiveSliceHeights
      (block.jointCellSource cell)) :
    volume (wz1Lemma23PlanarSlice (block.jointCellSource cell) z) ≤
      32 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN delta sigma *
        Kakeya.realRpowENN rho (2 - sigma) := by
  have hsubset :
      wz1Lemma23PlanarSlice (block.jointCellSource cell) z ⊆
        wz1Lemma23PlanarSlice (pullback.sameHeightSourceCell cell) z := by
    intro point hpoint
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hstandard :=
      volumePopular.jointSourceSet_subset_standardSlab hlift.1.1.1
    apply wz1Lemma23_mem_planarSlice_iff.mpr
    exact ⟨hstandard.1, hlift.2⟩
  have hzFull :
      z ∈ wz1Lemma23PositiveSliceHeights
        (pullback.sameHeightSourceCell cell) :=
    hz.trans_le (measure_mono hsubset)
  exact (measure_mono hsubset).trans
    (pullback.sameHeightSourceCell_slice_volume_le
      (block.jointFixedBinRhoCells_subset_selected hcell) z hzFull)

/-- Division-free horizontal amplification for one cell of the joint
fixed-bin source. -/
theorem jointCellSource_volume_mul_square_le_saturation
    {cell : WZ2PaperCellIndex}
    (hcell : cell ∈ block.jointFixedBinRhoCells) :
    volume (block.jointCellSource cell) * ENNReal.ofReal (rho ^ 2) ≤
      (32 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta sigma *
          Kakeya.realRpowENN rho (2 - sigma)) *
        volume (block.jointCellSaturation cell) := by
  exact source_volume_mul_square_le_sliceCap_mul_saturation_volume
    (by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
    cell (block.jointCellSource cell)
    (block.jointCellSource_measurable cell)
    (block.jointCellSource_subset_cube cell) _
    (block.jointCellSource_slice_volume_le hcell)

theorem jointFixedBinRegion_eq_biUnion_cells :
    volumePopular.jointFixedBinHeightRegion
        block.referenceHeight block.bin =
      ⋃ cell ∈ block.jointFixedBinRhoCells,
        block.jointCellSource cell := by
  apply Set.Subset.antisymm
  · intro point hpoint
    have hstandard :=
      volumePopular.jointSourceSet_subset_standardSlab hpoint.1.1
    change point ∈ pullback.shading.union ∩
      pureWZ2Node05RetainedCellRegion rho
        (pullback.standardSqrtSlabRhoCells heightIndex.1.1) at hstandard
    rcases Set.mem_iUnion₂.mp hstandard.2 with
      ⟨cell, hcell, hpointCell⟩
    have hselected : cell ∈ block.jointFixedBinRhoCells := by
      rw [jointFixedBinRhoCells, Finset.mem_filter]
      exact ⟨hcell, point, hpoint, hpointCell⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, hselected, hpoint, hpointCell⟩
  · intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨_cell, _hcell, hsource⟩
    exact hsource.1

theorem jointFixedBinRhoCells_nonempty :
    block.jointFixedBinRhoCells.Nonempty := by
  have hintegratedPos :
      0 < volumePopular.jointIntegratedBinMass
        block.referenceHeight block.bin := by
    have hproductPos :
        0 < 4 * ((volumePopular.jointRichCommonBinLabels
          block.referenceHeight threshold).card : ENNReal) *
            volumePopular.jointIntegratedBinMass
              block.referenceHeight block.bin :=
      volumePopular.jointSourceSet_volume_pos.trans_le block.source_average
    by_contra hnot
    have hzero :
        volumePopular.jointIntegratedBinMass
          block.referenceHeight block.bin = 0 :=
      bot_unique (not_lt.mp hnot)
    rw [hzero, mul_zero] at hproductPos
    exact (lt_irrefl 0 hproductPos)
  have hfixedPos :
      0 < volume (volumePopular.jointFixedBinHeightRegion
        block.referenceHeight block.bin) := by
    rwa [volumePopular.jointFixedBinHeightRegion_volume block]
  have hfixedNonempty :
      (volumePopular.jointFixedBinHeightRegion
        block.referenceHeight block.bin).Nonempty :=
    nonempty_of_measure_ne_zero hfixedPos.ne'
  rcases hfixedNonempty with ⟨point, hpoint⟩
  have hstandard :=
    volumePopular.jointSourceSet_subset_standardSlab hpoint.1.1
  change point ∈ pullback.shading.union ∩
    pureWZ2Node05RetainedCellRegion rho
      (pullback.standardSqrtSlabRhoCells heightIndex.1.1) at hstandard
  rcases Set.mem_iUnion₂.mp hstandard.2 with
    ⟨cell, hcell, hpointCell⟩
  exact ⟨cell, Finset.mem_filter.mpr
    ⟨hcell, point, hpoint, hpointCell⟩⟩

theorem jointFixedBinRegion_volume_eq_sum_cells :
    volume (volumePopular.jointFixedBinHeightRegion
        block.referenceHeight block.bin) =
      ∑ cell ∈ block.jointFixedBinRhoCells,
        volume (block.jointCellSource cell) := by
  rw [block.jointFixedBinRegion_eq_biUnion_cells]
  exact MeasureTheory.measure_biUnion_finset
    (fun first _ second _ hne =>
      (wz1PaperGridCube_disjoint hne).mono
        (block.jointCellSource_subset_cube first)
        (block.jointCellSource_subset_cube second))
    (fun cell _ => block.jointCellSource_measurable cell)

theorem jointSaturatedUnion_measurable :
    MeasurableSet block.jointSaturatedUnion :=
  MeasurableSet.biUnion block.jointFixedBinRhoCells.finite_toSet.countable
    (fun cell _ =>
      measurableSet_wz1PaperGridCubeSameHeightSaturation
        rho cell (block.jointCellSource cell)
        (block.jointCellSource_measurable cell))

theorem jointSaturatedUnion_volume :
    volume block.jointSaturatedUnion =
      ∑ cell ∈ block.jointFixedBinRhoCells,
        volume (block.jointCellSaturation cell) := by
  unfold jointSaturatedUnion
  exact MeasureTheory.measure_biUnion_finset
    (fun first _ second _ hne =>
      (wz1PaperGridCube_disjoint hne).mono
        (wz1PaperGridCubeSameHeightSaturation_subset_cube
          rho first (block.jointCellSource first))
        (wz1PaperGridCubeSameHeightSaturation_subset_cube
          rho second (block.jointCellSource second)))
    (fun cell _ =>
      measurableSet_wz1PaperGridCubeSameHeightSaturation
        rho cell (block.jointCellSource cell)
        (block.jointCellSource_measurable cell))

/-- Aggregate the sharp horizontal amplification over the disjoint joint
fixed-bin cells. -/
theorem jointFixedBin_volume_mul_square_le_saturation :
    volume (volumePopular.jointFixedBinHeightRegion
          block.referenceHeight block.bin) * ENNReal.ofReal (rho ^ 2) ≤
      (32 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN delta sigma *
          Kakeya.realRpowENN rho (2 - sigma)) *
        volume block.jointSaturatedUnion := by
  let cap :=
    32 * Kakeya.realRpowENN delta (-inputLoss) *
      Kakeya.realRpowENN delta sigma *
      Kakeya.realRpowENN rho (2 - sigma)
  rw [block.jointFixedBinRegion_volume_eq_sum_cells,
    block.jointSaturatedUnion_volume]
  calc
    (∑ cell ∈ block.jointFixedBinRhoCells,
        volume (block.jointCellSource cell)) * ENNReal.ofReal (rho ^ 2) =
      ∑ cell ∈ block.jointFixedBinRhoCells,
        volume (block.jointCellSource cell) * ENNReal.ofReal (rho ^ 2) := by
          rw [Finset.sum_mul]
    _ ≤ ∑ cell ∈ block.jointFixedBinRhoCells,
        cap * volume (block.jointCellSaturation cell) :=
      Finset.sum_le_sum fun cell hcell =>
        block.jointCellSource_volume_mul_square_le_saturation hcell
    _ = cap * ∑ cell ∈ block.jointFixedBinRhoCells,
        volume (block.jointCellSaturation cell) := by
      rw [Finset.mul_sum]

/-- The production saturation has no polynomial volume deficit. -/
theorem jointFixedBin_volume_le_saturation :
    volumePopular.jointIntegratedBinMass
        block.referenceHeight block.bin ≤
      volume block.jointSaturatedUnion := by
  rw [← volumePopular.jointFixedBinHeightRegion_volume block]
  rw [block.jointFixedBinRegion_volume_eq_sum_cells]
  rw [block.jointSaturatedUnion_volume]
  exact Finset.sum_le_sum fun cell _ =>
    block.jointCellSource_volume_le_saturation cell

theorem jointSaturatedUnion_exists_source_same_height
    {point : Point3} (hpoint : point ∈ block.jointSaturatedUnion) :
    ∃ cell ∈ block.jointFixedBinRhoCells,
      ∃ sourcePoint ∈ block.jointCellSource cell,
        sourcePoint (2 : Fin 3) = point (2 : Fin 3) := by
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hsat⟩
  rcases wz1PaperGridCubeSameHeightSaturation_exists_source_same_height
      (block.jointCellSource_subset_cube cell) hsat with
    ⟨sourcePoint, hsourcePoint, hheight⟩
  exact ⟨cell, hcell, sourcePoint, hsourcePoint.1, hheight⟩

theorem jointSaturatedUnion_height_mem_ZS
    {point : Point3} (hpoint : point ∈ block.jointSaturatedUnion) :
    point (2 : Fin 3) ∈ volumePopular.continuous.popularHeights := by
  rcases block.jointSaturatedUnion_exists_source_same_height hpoint with
    ⟨_cell, _hcell, sourcePoint, hsourcePoint, hheight⟩
  rw [← hheight]
  exact volumePopular.jointSourceSet_height_mem_ZS hsourcePoint.1.1.1

theorem jointSaturatedUnion_height_mem_volumePopular
    {point : Point3} (hpoint : point ∈ block.jointSaturatedUnion) :
    ∃ sourcePoint ∈ volumePopular.popular.heightRegion,
      sourcePoint (2 : Fin 3) = point (2 : Fin 3) := by
  rcases block.jointSaturatedUnion_exists_source_same_height hpoint with
    ⟨_cell, _hcell, sourcePoint, hsourcePoint, hheight⟩
  have hregion :=
    volumePopular.jointFixedBinHeightRegion_subset_volumePopular
      block hsourcePoint.1
  exact ⟨sourcePoint, hregion, hheight⟩

end JointHeightCommonBinData

end PureWZ2Node05V4RichSourceVolumePopularHeightData

end Kakeya.Assouad

end
