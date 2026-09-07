import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSourcePopularIntegratedBin

/-!
# Direct-rich integrated-bin source envelope

After the fixed common-bin label has been selected by its mass integrated
over `Z_S`, this module retains the exact participating side-`rho` cells.
The source shading, whole-cell envelope, and their volume cross identity are
all projections of the same post-two-call pullback.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichSourcePopularIntegratedEnvelopeData
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
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (heightIndex :
      {heightIndex // heightIndex ∈ pullback.standardSqrtSlabIndices})
    (B₀ threshold : ENNReal) where
  popular : pullback.SourcePopularHeightData heightIndex
  bin : ℤ
  bin_mem :
    bin ∈ pullback.sourcePopularRichCommonBinLabels
      heightIndex.1 popular.referenceHeight threshold
  source_average :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) ≤
      4 * ((pullback.sourcePopularRichCommonBinLabels
        heightIndex.1 popular.referenceHeight threshold).card : ENNReal) *
        pullback.sourcePopularIntegratedBinMass
          heightIndex.1 popular.referenceHeight bin
  cells : Finset WZ2PaperCellIndex :=
    pullback.sourcePopularFixedBinRhoCells
      heightIndex.1 popular.referenceHeight bin
  cells_eq :
    cells = pullback.sourcePopularFixedBinRhoCells
      heightIndex.1 popular.referenceHeight bin
  cells_subset_standard :
    cells ⊆ pullback.standardSqrtSlabRhoCells heightIndex.1
  cells_subset_selected : cells ⊆ pullback.selectedCells
  cells_nonempty : cells.Nonempty
  fixedBinRegion : Set Point3 :=
    pullback.sourcePopularFixedBinHeightRegion
      heightIndex.1 popular.referenceHeight bin
  fixedBinRegion_eq :
    fixedBinRegion = pullback.sourcePopularFixedBinHeightRegion
      heightIndex.1 popular.referenceHeight bin
  fixedBinRegion_measurable : MeasurableSet fixedBinRegion
  fixedBinRegion_volume :
    volume fixedBinRegion =
      pullback.sourcePopularIntegratedBinMass
        heightIndex.1 popular.referenceHeight bin
  fixedBinRegion_subset_envelope :
    fixedBinRegion ⊆
      pullback.sourcePopularFixedBinWholeCellEnvelope
        heightIndex.1 popular.referenceHeight bin
  sourceShading : WZ1PaperTubeShading current.grain.family :=
    pureWZ2Node05RestrictToCells (rho := rho) pullback.shading cells
  sourceShading_eq :
    sourceShading =
      pureWZ2Node05RestrictToCells (rho := rho) pullback.shading cells
  source_sub_pullback :
    PureWZ2PaperIsSubshading sourceShading pullback.shading
  source_sub_current :
    PureWZ2PaperIsSubshading sourceShading current.grain.shading
  source_union_eq :
    sourceShading.union = pullback.selectedRhoCellsSourceRegion cells
  source_volume :
    volume sourceShading.union =
      (cells.card : ENNReal) * pullback.firstPostBalanced.cellMass
  envelope_volume :
    volume (pullback.sourcePopularFixedBinWholeCellEnvelope
      heightIndex.1 popular.referenceHeight bin) =
      (cells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0))
  source_envelope_cross :
    volume sourceShading.union *
        volume (wz1PaperGridCube rho (0, 0, 0)) =
      volume (pullback.sourcePopularFixedBinWholeCellEnvelope
        heightIndex.1 popular.referenceHeight bin) *
        pullback.firstPostBalanced.cellMass

namespace PureWZ2Node05V4RichTwoScaleCellPullbackData

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
    (pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)

theorem sourcePopularFixedBinHeightRegion_subset_envelope
    (heightIndex : ℤ) (referenceHeight : ℝ) (bin : ℤ) :
    pullback.sourcePopularFixedBinHeightRegion
        heightIndex referenceHeight bin ⊆
      pullback.sourcePopularFixedBinWholeCellEnvelope
        heightIndex referenceHeight bin := by
  intro point hpoint
  have hslab :
      point ∈ pullback.standardSqrtSlabSourceRegion heightIndex :=
    hpoint.1.1
  change point ∈ pullback.shading.union ∩
      pureWZ2Node05RetainedCellRegion rho
        (pullback.standardSqrtSlabRhoCells heightIndex) at hslab
  rcases Set.mem_iUnion₂.mp hslab.2 with
    ⟨cell, hcell, hpointCell⟩
  unfold sourcePopularFixedBinWholeCellEnvelope
    pureWZ2Node05RetainedCellRegion
  exact Set.mem_iUnion₂.mpr
    ⟨cell, Finset.mem_filter.mpr
      ⟨hcell, ⟨point, hpoint, hpointCell⟩⟩, hpointCell⟩

/-- Construct the integrated source envelope from an already fixed paper
`Z_S` witness.  The subtype equality records that no second popular-height
witness, and hence no second outer reference height, is selected. -/
theorem sourcePopularIntegratedEnvelopeOfPopular
    (heightIndex :
      {heightIndex // heightIndex ∈ pullback.standardSqrtSlabIndices})
    (popular : pullback.SourcePopularHeightData heightIndex)
    (B₀ threshold : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          (pullback.standardSqrtSlabSourceRegion heightIndex.1)
          (Real.sqrt rho)) :
    Nonempty { envelope :
      PureWZ2Node05V4RichSourcePopularIntegratedEnvelopeData
        pullback heightIndex B₀ threshold // envelope.popular = popular } := by
  rcases pullback.exists_sourcePopularIntegratedCommonBin
      heightIndex popular.referenceHeight
      (by simpa [popular.popularHeights_eq] using popular.referenceHeight_mem)
      B₀ threshold hB₀ hthresholdBudget with
    ⟨bin, hbin, hsourceAverage⟩
  let cells := pullback.sourcePopularFixedBinRhoCells
    heightIndex.1 popular.referenceHeight bin
  let fixedBinRegion := pullback.sourcePopularFixedBinHeightRegion
    heightIndex.1 popular.referenceHeight bin
  let envelope := pullback.sourcePopularFixedBinWholeCellEnvelope
    heightIndex.1 popular.referenceHeight bin
  have hcellsStandard :
      cells ⊆ pullback.standardSqrtSlabRhoCells heightIndex.1 := by
    exact Finset.filter_subset _ _
  have hcellsSelected : cells ⊆ pullback.selectedCells :=
    hcellsStandard.trans
      (pullback.standardSqrtSlabRhoCells_subset heightIndex.1)
  have hfixedVolume :
      volume fixedBinRegion =
        pullback.sourcePopularIntegratedBinMass
          heightIndex.1 popular.referenceHeight bin := by
    simpa [fixedBinRegion] using
      pullback.sourcePopularFixedBinHeightRegion_volume
        heightIndex.1 popular.referenceHeight bin
  have hfixedPos :
      0 < volume fixedBinRegion := by
    have hsourcePos :=
      pullback.standardSqrtSlabSourceRegion_volume_pos heightIndex.2
    have hrightPos :
        0 < 4 *
          ((pullback.sourcePopularRichCommonBinLabels
            heightIndex.1 popular.referenceHeight threshold).card : ENNReal) *
          pullback.sourcePopularIntegratedBinMass
            heightIndex.1 popular.referenceHeight bin :=
      hsourcePos.trans_le hsourceAverage
    have hmassPos :
        0 < pullback.sourcePopularIntegratedBinMass
          heightIndex.1 popular.referenceHeight bin := by
      by_contra hzero
      have hzero' :
          pullback.sourcePopularIntegratedBinMass
            heightIndex.1 popular.referenceHeight bin = 0 :=
        le_antisymm (le_of_not_gt hzero) bot_le
      rw [hzero', mul_zero] at hrightPos
      exact (lt_irrefl 0) hrightPos
    rwa [hfixedVolume]
  have hcellsNonempty : cells.Nonempty := by
    by_contra hempty
    have hcellsEmpty := Finset.not_nonempty_iff_eq_empty.mp hempty
    have hsubset := pullback.sourcePopularFixedBinHeightRegion_subset_envelope
      heightIndex.1 popular.referenceHeight bin
    have henvelopeEmpty : envelope = ∅ := by
      simp [envelope, sourcePopularFixedBinWholeCellEnvelope,
        pureWZ2Node05RetainedCellRegion, cells, hcellsEmpty]
    have hfixedEmpty : fixedBinRegion = ∅ := by
      apply Set.Subset.antisymm
      · intro point hpoint
        have hemptyMem := hsubset hpoint
        have hemptyMem' : point ∈ envelope := by
          simpa [envelope] using hemptyMem
        rw [henvelopeEmpty] at hemptyMem'
        exact hemptyMem'.elim
      · exact Set.empty_subset _
    rw [hfixedEmpty] at hfixedPos
    simp at hfixedPos
  let sourceShading :=
    pureWZ2Node05RestrictToCells (rho := rho) pullback.shading cells
  have hsourceUnion :
      sourceShading.union = pullback.selectedRhoCellsSourceRegion cells := by
    exact pureWZ2Node05RestrictToCells_union pullback.shading cells
  have hsourceVolume :
      volume sourceShading.union =
        (cells.card : ENNReal) * pullback.firstPostBalanced.cellMass := by
    rw [hsourceUnion]
    exact pullback.selectedRhoCellsSourceRegion_volume cells hcellsSelected
  have henvelopeVolume :
      volume envelope =
        (cells.card : ENNReal) *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by
    simpa [envelope, cells] using
      pullback.sourcePopularFixedBinWholeCellEnvelope_volume
        heightIndex.1 popular.referenceHeight bin
  exact ⟨⟨{
    popular := popular
    bin := bin
    bin_mem := hbin
    source_average := hsourceAverage
    cells := cells
    cells_eq := rfl
    cells_subset_standard := hcellsStandard
    cells_subset_selected := hcellsSelected
    cells_nonempty := hcellsNonempty
    fixedBinRegion := fixedBinRegion
    fixedBinRegion_eq := rfl
    fixedBinRegion_measurable :=
      pullback.measurableSet_sourcePopularFixedBinHeightRegion
        heightIndex.1 popular.referenceHeight bin
    fixedBinRegion_volume := hfixedVolume
    fixedBinRegion_subset_envelope := by
      simpa [fixedBinRegion, envelope] using
        pullback.sourcePopularFixedBinHeightRegion_subset_envelope
          heightIndex.1 popular.referenceHeight bin
    sourceShading := sourceShading
    sourceShading_eq := rfl
    source_sub_pullback := fun _ => Set.inter_subset_left
    source_sub_current := fun index =>
      (show sourceShading.carrier index ⊆ pullback.shading.carrier index from
        Set.inter_subset_left).trans (pullback.subshading index)
    source_union_eq := hsourceUnion
    source_volume := hsourceVolume
    envelope_volume := henvelopeVolume
    source_envelope_cross := by
      rw [hsourceVolume, henvelopeVolume]
      ring
  }, rfl⟩⟩

/-- Compatibility wrapper which selects the paper `Z_S` witness internally. -/
theorem sourcePopularIntegratedEnvelope
    (heightIndex :
      {heightIndex // heightIndex ∈ pullback.standardSqrtSlabIndices})
    (B₀ threshold : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          (pullback.standardSqrtSlabSourceRegion heightIndex.1)
          (Real.sqrt rho)) :
    Nonempty (PureWZ2Node05V4RichSourcePopularIntegratedEnvelopeData
      pullback heightIndex B₀ threshold) := by
  rcases pullback.sourcePopularHeightData heightIndex with ⟨popular⟩
  rcases pullback.sourcePopularIntegratedEnvelopeOfPopular
      heightIndex popular B₀ threshold hB₀ hthresholdBudget with
    ⟨envelope⟩
  exact ⟨envelope.1⟩

end PureWZ2Node05V4RichTwoScaleCellPullbackData

namespace PureWZ2Node05V4RichSourcePopularIntegratedEnvelopeData

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
    {heightIndex :
      {heightIndex // heightIndex ∈ pullback.standardSqrtSlabIndices}}
    {B₀ threshold : ENNReal}
    (envelope :
      PureWZ2Node05V4RichSourcePopularIntegratedEnvelopeData
        pullback heightIndex B₀ threshold)

/-- The fixed-bin source region remains inside the source shading restricted
to exactly the rho-cells used by the whole-cell envelope. -/
theorem fixedBinRegion_subset_sourceShading :
    envelope.fixedBinRegion ⊆ envelope.sourceShading.union := by
  intro point hpoint
  rw [envelope.source_union_eq]
  refine ⟨?_, ?_⟩
  · have hfixed := hpoint
    rw [envelope.fixedBinRegion_eq,
      PureWZ2Node05V4RichTwoScaleCellPullbackData.sourcePopularFixedBinHeightRegion]
      at hfixed
    exact pullback.standardSqrtSlabSourceRegion_subset_source
      heightIndex.1 hfixed.1.1
  · change point ∈ pureWZ2Node05RetainedCellRegion rho envelope.cells
    have henvelope := envelope.fixedBinRegion_subset_envelope hpoint
    rw [PureWZ2Node05V4RichTwoScaleCellPullbackData.sourcePopularFixedBinWholeCellEnvelope,
      ← envelope.cells_eq] at henvelope
    exact henvelope

/-- The integrated mass in the selected bin is paid by the exact source mass
of its participating rho-cells. -/
theorem fixedBinMass_le_cells_mul_firstCellMass :
    pullback.sourcePopularIntegratedBinMass
        heightIndex.1 envelope.popular.referenceHeight envelope.bin ≤
      (envelope.cells.card : ENNReal) *
        pullback.firstPostBalanced.cellMass := by
  rw [← envelope.fixedBinRegion_volume, ← envelope.source_volume]
  exact measure_mono envelope.fixedBinRegion_subset_sourceShading

def parentCells : Finset WZ2PaperCellIndex :=
  envelope.cells.image pullback.standardSecondParent

def coarseRegion : Set Point3 :=
  twoScale.secondRefinedFineShading.union ∩
    ⋃ parent ∈ envelope.parentCells,
      wz1PaperGridCube sqrtRequested.1 parent

theorem parentCells_subset_active :
    envelope.parentCells ⊆ twoScale.secondBalancedCover.activeCells := by
  intro parent hparent
  rw [parentCells] at hparent
  rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
  exact pullback.standardSecondParent_active
    (envelope.cells_subset_selected hcell)

theorem coarseRegion_volume :
    volume envelope.coarseRegion =
      (envelope.parentCells.card : ENNReal) *
        twoScale.secondBalancedCover.cellMass := by
  exact twoScale.secondBalancedCover.selected_cells_volume
    envelope.parentCells envelope.parentCells_subset_active

/-- Every rich side-`sqrt rho` spatial cell at the selected witness height is
the canonical second-cover parent of a participating integrated-bin rho cell. -/
theorem richSpatialCells_subset_parentImage :
    pullback.sourcePopularRichCommonBinSpatialCells
        heightIndex.1 envelope.popular.referenceHeight threshold envelope.bin ⊆
      envelope.cells.image pullback.standardSecondParent := by
  intro parent hparent
  let witnessHeight :=
    pullback.sourcePopularRichCommonBinWitnessHeight
      heightIndex.1 envelope.popular.referenceHeight threshold envelope.bin
  have hwitness :=
    pullback.sourcePopularRichCommonBinWitnessHeight_spec
      heightIndex.1 envelope.popular.referenceHeight threshold envelope.bin_mem
  rw [PureWZ2Node05V4RichTwoScaleCellPullbackData.sourcePopularRichCommonBinSpatialCells,
    pureWZ2PreCommonBinSpatialCellsAtHeight, Finset.mem_filter] at hparent
  rcases hparent.2 with ⟨planar, hplanar⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hplanar
  let sourcePoint : Point3 :=
    point3 (planar 0) (planar 1) witnessHeight
  have hsourcePoint :
      sourcePoint ∈
        pullback.standardSqrtSlabSourceRegion heightIndex.1 := by
    simpa [sourcePoint, witnessHeight] using hlift.1.1
  have hpointParent :
      sourcePoint ∈ wz1PaperGridCube (Real.sqrt rho) parent := by
    simpa [sourcePoint, witnessHeight] using hlift.2
  have hfixed :
      sourcePoint ∈ pullback.sourcePopularFixedBinHeightRegion
        heightIndex.1 envelope.popular.referenceHeight envelope.bin := by
    refine ⟨?_, ?_⟩
    · simpa [sourcePoint, witnessHeight] using hlift.1
    · simpa [sourcePoint, witnessHeight, point3] using hwitness.1
  change sourcePoint ∈ pullback.shading.union ∩
      pureWZ2Node05RetainedCellRegion rho
        (pullback.standardSqrtSlabRhoCells heightIndex.1) at hsourcePoint
  rcases Set.mem_iUnion₂.mp hsourcePoint.2 with
    ⟨cell, hcellStandard, hpointCell⟩
  have hcellEnvelope :
      cell ∈ envelope.cells := by
    rw [envelope.cells_eq,
      PureWZ2Node05V4RichTwoScaleCellPullbackData.sourcePopularFixedBinRhoCells,
      Finset.mem_filter]
    exact ⟨hcellStandard, ⟨sourcePoint, hfixed, hpointCell⟩⟩
  have hcellSelected : cell ∈ pullback.selectedCells :=
    envelope.cells_subset_selected hcellEnvelope
  have hpointCanonical :
      sourcePoint ∈ wz1PaperGridCube (Real.sqrt rho)
        (pullback.standardSecondParent cell) := by
    have hraw :=
      pullback.standardSecondParent_cell_subset hcellSelected hpointCell
    simpa only [twoScale.sqrtRequested_eq, pullback.rhoRequested_eq] using hraw
  have hparentEq : pullback.standardSecondParent cell = parent :=
    ((mem_wz1PaperGridCube (Real.sqrt rho)
      (pullback.standardSecondParent cell) sourcePoint).mp
        hpointCanonical).symm.trans
      ((mem_wz1PaperGridCube (Real.sqrt rho) parent sourcePoint).mp
        hpointParent)
  exact Finset.mem_image.mpr ⟨cell, hcellEnvelope, hparentEq⟩

/-- The integrated envelope retains at least `K` distinct genuine second-cover
parents whenever the scalar source-slice cap pays `K`. -/
theorem K_le_parentImage_card
    (K : ℕ)
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold) :
    K ≤ (envelope.cells.image pullback.standardSecondParent).card := by
  have hrich :=
    pullback.sourcePopularRichCommonBinSpatialCells_card_lower
      heightIndex.1 envelope.popular.referenceHeight threshold K hK
        envelope.bin_mem
  exact hrich.trans <|
    Finset.card_le_card envelope.richSpatialCells_subset_parentImage

/-- The `K` rich spatial parents give the exact second-cover mass floor for
the integrated coarse carrier. -/
theorem K_mul_secondCellMass_le_coarseRegion
    (K : ℕ)
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold) :
    (K : ENNReal) * twoScale.secondBalancedCover.cellMass ≤
      volume envelope.coarseRegion := by
  rw [envelope.coarseRegion_volume]
  gcongr
  exact_mod_cast envelope.K_le_parentImage_card K hK

/-- First exact cancellation in the distinct-bin argument.  The full-slab
coarse mass is cancelled, while the selected integrated fixed-bin mass is
deliberately retained for the subsequent same-height saturation step. -/
theorem firstCellMass_mul_K_mul_secondCellMass_le_fixedBinMass_mul_cube
    (K : ℕ)
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold) :
    pullback.firstPostBalanced.cellMass *
          ((K : ENNReal) * twoScale.secondBalancedCover.cellMass) ≤
      20 * pullback.sourcePopularIntegratedBinMass
          heightIndex.1 envelope.popular.referenceHeight envelope.bin *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  have hreference :
      envelope.popular.referenceHeight ∈ Set.Icc (-1 : ℝ) 1 :=
    pullback.sourcePopularHeight_mem_paperRange heightIndex.2 <| by
      simpa [envelope.popular.popularHeights_eq] using
        envelope.popular.referenceHeight_mem
  have hincidence :=
    pullback.sourcePopularRichCommonBin_incidence
      heightIndex.1 envelope.popular.referenceHeight hreference
      threshold K hK
  have hsourceCoarseCross :
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
        volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1) *
          pullback.firstPostBalanced.cellMass := by
    exact pullback.selectedRhoCells_source_coarse_cross
      (pullback.standardSqrtSlabRhoCells heightIndex.1)
      (pullback.standardSqrtSlabRhoCells_subset heightIndex.1)
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hcoarsePos :
      0 < volume
        (pullback.standardSqrtSlabCoarseRegion heightIndex.1) := by
    rw [pullback.standardSqrtSlabCoarseRegion_volume]
    exact ENNReal.mul_pos
      (by
        exact_mod_cast
          (Nat.ne_of_gt
            (pullback.standardSqrtSlabRhoCells_nonempty
              heightIndex.2).card_pos))
      (wz1PaperGridCube_volume_pos hrho (0, 0, 0)).ne'
  have hcoarseTop :
      volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1) ≠ ⊤ := by
    rw [pullback.standardSqrtSlabCoarseRegion_volume]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (wz1PaperGridCube_volume_ne_top hrho (0, 0, 0))
  apply (ENNReal.mul_le_mul_iff_right hcoarsePos.ne' hcoarseTop).mp
  calc
    volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1) *
          (pullback.firstPostBalanced.cellMass *
            ((K : ENNReal) * twoScale.secondBalancedCover.cellMass)) =
        (volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1) *
          pullback.firstPostBalanced.cellMass) *
            ((K : ENNReal) * twoScale.secondBalancedCover.cellMass) := by ring
    _ = (volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
            ((K : ENNReal) * twoScale.secondBalancedCover.cellMass) := by
      rw [hsourceCoarseCross]
    _ ≤ (4 *
          ((pullback.sourcePopularRichCommonBinLabels heightIndex.1
            envelope.popular.referenceHeight threshold).card : ENNReal) *
          pullback.sourcePopularIntegratedBinMass heightIndex.1
            envelope.popular.referenceHeight envelope.bin *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
            ((K : ENNReal) * twoScale.secondBalancedCover.cellMass) := by
      gcongr
      exact envelope.source_average
    _ = (4 * pullback.sourcePopularIntegratedBinMass heightIndex.1
          envelope.popular.referenceHeight envelope.bin *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
        (((pullback.sourcePopularRichCommonBinLabels heightIndex.1
          envelope.popular.referenceHeight threshold).card : ENNReal) *
          K * twoScale.secondBalancedCover.cellMass) := by ring
    _ ≤ (4 * pullback.sourcePopularIntegratedBinMass heightIndex.1
          envelope.popular.referenceHeight envelope.bin *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
        (5 * volume
          (pullback.standardSqrtSlabCoarseRegion heightIndex.1)) := by
      gcongr
    _ = volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1) *
        (20 * pullback.sourcePopularIntegratedBinMass heightIndex.1
          envelope.popular.referenceHeight envelope.bin *
          volume (wz1PaperGridCube rho (0, 0, 0))) := by ring

/-- Sharp whole-cell envelope lower bound obtained by cancelling the distinct
label count through the genuine full-slab incidence estimate and the two exact
source/coarse cross identities.  No geometric upper bound on the number of
labels is used. -/
theorem K_mul_secondCellMass_le_twenty_mul_wholeCellEnvelope
    (K : ℕ)
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold) :
    (K : ENNReal) * twoScale.secondBalancedCover.cellMass ≤
      20 * volume (pullback.sourcePopularFixedBinWholeCellEnvelope
        heightIndex.1 envelope.popular.referenceHeight envelope.bin) := by
  have hreference :
      envelope.popular.referenceHeight ∈ Set.Icc (-1 : ℝ) 1 :=
    pullback.sourcePopularHeight_mem_paperRange heightIndex.2 <| by
      simpa [envelope.popular.popularHeights_eq] using
        envelope.popular.referenceHeight_mem
  have hincidence :=
    pullback.sourcePopularRichCommonBin_incidence
      heightIndex.1 envelope.popular.referenceHeight hreference
      threshold K hK
  have hsourceCoarseCross :
      volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
        volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1) *
          pullback.firstPostBalanced.cellMass := by
    exact pullback.selectedRhoCells_source_coarse_cross
      (pullback.standardSqrtSlabRhoCells heightIndex.1)
      (pullback.standardSqrtSlabRhoCells_subset heightIndex.1)
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hcoarsePos :
      0 < volume
        (pullback.standardSqrtSlabCoarseRegion heightIndex.1) := by
    rw [pullback.standardSqrtSlabCoarseRegion_volume]
    exact ENNReal.mul_pos
      (by
        exact_mod_cast
          (Nat.ne_of_gt
            (pullback.standardSqrtSlabRhoCells_nonempty
              heightIndex.2).card_pos))
      (wz1PaperGridCube_volume_pos hrho (0, 0, 0)).ne'
  have hcoarseTop :
      volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1) ≠ ⊤ := by
    rw [pullback.standardSqrtSlabCoarseRegion_volume]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (wz1PaperGridCube_volume_ne_top hrho (0, 0, 0))
  have hsharp :=
    CommonBinDistinctIncidence.whole_cell_volume_lower_of_exact_cross
      (pullback.sourcePopularRichCommonBinLabels
        heightIndex.1 envelope.popular.referenceHeight threshold).card
      K 5 envelope.cells.card
      (volume (pullback.standardSqrtSlabSourceRegion heightIndex.1))
      (pullback.sourcePopularIntegratedBinMass
        heightIndex.1 envelope.popular.referenceHeight envelope.bin)
      (volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1))
      twoScale.secondBalancedCover.cellMass
      pullback.firstPostBalanced.cellMass
      (volume (wz1PaperGridCube rho (0, 0, 0)))
      envelope.source_average hincidence hsourceCoarseCross
      envelope.fixedBinMass_le_cells_mul_firstCellMass
      hcoarsePos hcoarseTop
      pullback.firstPostBalanced.cellMass_pos
      pullback.firstPostBalanced.cellMass_ne_top
  calc
    (K : ENNReal) * twoScale.secondBalancedCover.cellMass ≤
        4 * 5 * ((envelope.cells.card : ENNReal) *
          volume (wz1PaperGridCube rho (0, 0, 0))) := hsharp
    _ = 20 * ((envelope.cells.card : ENNReal) *
          volume (wz1PaperGridCube rho (0, 0, 0))) := by norm_num
    _ = 20 * volume (pullback.sourcePopularFixedBinWholeCellEnvelope
        heightIndex.1 envelope.popular.referenceHeight envelope.bin) := by
      rw [envelope.envelope_volume]

end PureWZ2Node05V4RichSourcePopularIntegratedEnvelopeData

end Kakeya.Assouad

end
