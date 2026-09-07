import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinPopularHalfMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinSpatialCellIncidence
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinSecondCoverCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinDistinctIncidence

/-!
# Distinct rich common-bin labels across heights

For one source window and one fixed reference height, this module forms the
finite set of common-bin labels which are rich at at least one height in a
supplied height set.  Each label occurs once.  We choose one witnessing
height for each label and count its active side-`sqrt rho` spatial cells.

Every participating cell belongs to the second balanced cover and meets at
most five distinct fixed labels.  Consequently the exact restriction of
`twoScale.fine.refined.union` to the participating cells satisfies the
required slab-local incidence estimate.  No independent fixed line, shifted
window volume, global parent mass, graph budget, or joint-density hypothesis
is used.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2SourceCarrierWindow

/-- Distinct fixed common-bin labels which are rich at some admissible
height.  The finite ambient set consists of the labels actually occupied by
the source window, while the filter records a witness in both `heights` and
the paper height range. -/
def distinctRichCommonBinLabels
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) : Finset ℤ :=
  (pureWZ2OccupiedCommonBins
      window.shading.union source.globalGrains.slope
      referenceHeight (Real.sqrt rho)).filter fun bin =>
    ∃ height,
      height ∈ heights ∧
      height ∈ Set.Icc (-1 : ℝ) 1 ∧
      threshold ≤
        pureWZ2FixedCommonBinSliceMass
          window.shading.union source.globalGrains.slope
          referenceHeight (Real.sqrt rho) height bin

/-- One witnessing height for a distinct rich label.  Outside the rich-label
set its value is irrelevant. -/
def distinctRichCommonBinWitnessHeight
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) (bin : ℤ) : ℝ :=
  if hbin :
      bin ∈ window.distinctRichCommonBinLabels
        referenceHeight heights threshold then
    Classical.choose
      (Finset.mem_filter.mp hbin).2
  else
    0

/-- Active side-`sqrt rho` spatial cells at the selected witnessing height
of one distinct rich label. -/
def distinctRichCommonBinActiveSpatialCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) (bin : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  pureWZ2FixedCommonBinActiveSpatialCells
    window.shading.union source.globalGrains.slope
    referenceHeight (Real.sqrt rho)
    (Real.sqrt_pos.mpr <| by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.coarseGrains.extremal.delta_pos)
    (window.distinctRichCommonBinWitnessHeight
      referenceHeight heights threshold bin)
    bin

/-- The union of the witnessing active-cell families over the distinct rich
labels. -/
def distinctRichCommonBinParticipatingSpatialCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) : Finset (ℤ × ℤ × ℤ) :=
  (window.distinctRichCommonBinLabels
      referenceHeight heights threshold).biUnion
    (window.distinctRichCommonBinActiveSpatialCells
      referenceHeight heights threshold)

/-- The exact second-cover refined volume on the participating side-`sqrt
rho` cells.  This is the local quantity `G_R`. -/
def distinctRichCommonBinRestrictionVolume
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) : ENNReal :=
  volume
    (twoScale.fine.refined.union ∩
      ⋃ cell ∈
          window.distinctRichCommonBinParticipatingSpatialCells
            referenceHeight heights threshold,
        wz1PaperGridCube (Real.sqrt rho) cell)

theorem distinctRichCommonBinWitnessHeight_spec
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) {bin : ℤ}
    (hbin :
      bin ∈ window.distinctRichCommonBinLabels
        referenceHeight heights threshold) :
    window.distinctRichCommonBinWitnessHeight
          referenceHeight heights threshold bin ∈ heights ∧
      window.distinctRichCommonBinWitnessHeight
          referenceHeight heights threshold bin ∈
        Set.Icc (-1 : ℝ) 1 ∧
      threshold ≤
        pureWZ2FixedCommonBinSliceMass
          window.shading.union source.globalGrains.slope
          referenceHeight (Real.sqrt rho)
          (window.distinctRichCommonBinWitnessHeight
            referenceHeight heights threshold bin)
          bin := by
  rw [distinctRichCommonBinWitnessHeight, dif_pos hbin]
  exact Classical.choose_spec (Finset.mem_filter.mp hbin).2

private theorem union_subset_source
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared) :
    window.shading.union ⊆ source.shading.union := by
  intro point hpoint
  have hshadow : point ∈ prepared.shadow.union :=
    window.subshading.union_subset hpoint
  have hpullback : point ∈ pullback.shading.union := by
    rwa [prepared.shadow_union] at hshadow
  exact pullback.subshading.union_subset hpullback

private theorem union_norm_le_two
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (point : Point3) (hpoint : point ∈ window.shading.union) :
    ‖point‖ ≤ 2 :=
  norm_le_two_of_mem_paperShading
    (window.union_subset_source hpoint)

private theorem fixedCommonBinSpatialCellSliceMass_le
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight height : ℝ)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (bin : ℤ) (cell : ℤ × ℤ × ℤ) :
    pureWZ2FixedCommonBinSpatialCellSliceMass
        window.shading.union source.globalGrains.slope
        referenceHeight (Real.sqrt rho) height bin cell ≤
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
        sigma inputLoss delta rho := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrhoRoot : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho]
  have hdeltaRoot : delta ≤ Real.sqrt rho :=
    hdeltaRho.trans hrhoRoot
  have hsubset :
      wz1Lemma23PlanarSlice
          (pureWZ2FixedCommonBinRegion
              window.shading.union source.globalGrains.slope
              referenceHeight (Real.sqrt rho) bin ∩
            wz1PaperGridCube (Real.sqrt rho) cell)
          height ⊆
        wz1Lemma23PlanarSlice
          (source.shading.union ∩
            wz1PaperGridCube (Real.sqrt rho) cell)
          height := by
    intro point hpoint
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hregion := hlift.1
    rw [pureWZ2FixedCommonBinRegion] at hregion
    apply wz1Lemma23_mem_planarSlice_iff.mpr
    exact ⟨window.union_subset_source hregion.1, hlift.2⟩
  calc
    pureWZ2FixedCommonBinSpatialCellSliceMass
          window.shading.union source.globalGrains.slope
          referenceHeight (Real.sqrt rho) height bin cell =
        volume
          (wz1Lemma23PlanarSlice
            (pureWZ2FixedCommonBinRegion
                window.shading.union source.globalGrains.slope
                referenceHeight (Real.sqrt rho) bin ∩
              wz1PaperGridCube (Real.sqrt rho) cell)
            height) := rfl
    _ ≤ volume
          (wz1Lemma23PlanarSlice
            (source.shading.union ∩
              wz1PaperGridCube (Real.sqrt rho) cell)
            height) :=
      measure_mono hsubset
    _ ≤
        PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
          sigma inputLoss delta rho := by
      simpa
        [PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap] using
        source.sourceCommonBinSpatialCellSliceBound
          hrho hdeltaRoot cell height hheight

/-- Under `K * a₀ ≤ threshold`, every distinct rich label contributes at
least `K` active side-`sqrt rho` cells at its selected witnessing height. -/
theorem distinctRichCommonBin_activeSpatialCells_card_lower
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) (K : ℕ)
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤
        threshold)
    {bin : ℤ}
    (hbin :
      bin ∈ window.distinctRichCommonBinLabels
        referenceHeight heights threshold) :
    K ≤
      (window.distinctRichCommonBinActiveSpatialCells
        referenceHeight heights threshold bin).card := by
  let height :=
    window.distinctRichCommonBinWitnessHeight
      referenceHeight heights threshold bin
  have hwitness :=
    window.distinctRichCommonBinWitnessHeight_spec
      referenceHeight heights threshold hbin
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  apply CommonBinRichSelection.cell_card_lower_of_rich
    (window.distinctRichCommonBinActiveSpatialCells
      referenceHeight heights threshold bin)
    (pureWZ2FixedCommonBinSpatialCellSliceMass
      window.shading.union source.globalGrains.slope
      referenceHeight (Real.sqrt rho) height bin)
    (pureWZ2FixedCommonBinSliceMass
      window.shading.union source.globalGrains.slope
      referenceHeight (Real.sqrt rho) height bin)
    threshold
    (PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      sigma inputLoss delta rho)
    K
  · exact hwitness.2.2
  · exact le_of_eq <| by
      simpa [distinctRichCommonBinActiveSpatialCells, height] using
        pureWZ2_fixed_common_bin_sliceMass_eq_sum_activeSpatialCells
          (measurableSet_shading_union window.shading)
          source.globalGrains.slope referenceHeight
          (Real.sqrt_pos.mpr hrho) height bin
          window.union_norm_le_two
  · intro cell _hcell
    exact window.fixedCommonBinSpatialCellSliceMass_le
      referenceHeight height hwitness.2.1 bin cell
  · exact hK
  · have hdeltaLoss :
        0 < Kakeya.realRpowENN delta (-inputLoss) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos source.extremal.delta_pos _)
    have hdeltaSigma :
        0 < Kakeya.realRpowENN delta sigma :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos source.extremal.delta_pos _)
    have hrhoPower :
        0 < Kakeya.realRpowENN rho (1 - sigma / 2) :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hrho _)
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos
          (by norm_num : (32 : ENNReal) ≠ 0)
          hdeltaLoss.ne').ne'
        hdeltaSigma.ne').ne'
      hrhoPower.ne'
  · simp only
      [PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap,
        Kakeya.realRpowENN]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top

/-- At most five selected distinct rich labels can use one spatial cell. -/
theorem distinctRichCommonBin_cellDegree_le_five
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (heights : Set ℝ) (threshold : ENNReal)
    (cell : ℤ × ℤ × ℤ) :
    ((window.distinctRichCommonBinLabels
        referenceHeight heights threshold).filter fun bin =>
      cell ∈ window.distinctRichCommonBinActiveSpatialCells
        referenceHeight heights threshold bin).card ≤ 5 := by
  let bins :=
    window.distinctRichCommonBinLabels
      referenceHeight heights threshold
  have hsubset :
      (bins.filter fun bin =>
          cell ∈ window.distinctRichCommonBinActiveSpatialCells
            referenceHeight heights threshold bin) ⊆
        pureWZ2CommonBinsMeetingSpatialCell bins
          source.globalGrains.slope referenceHeight
          (Real.sqrt rho) cell := by
    intro bin hbin
    rw [Finset.mem_filter] at hbin
    rw [pureWZ2CommonBinsMeetingSpatialCell, Finset.mem_filter]
    refine ⟨hbin.1, ?_⟩
    have hactive := hbin.2
    rw [distinctRichCommonBinActiveSpatialCells,
      pureWZ2FixedCommonBinActiveSpatialCells,
      Finset.mem_filter] at hactive
    rcases hactive.2 with ⟨point, hpoint⟩
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hregion := hlift.1
    rw [pureWZ2FixedCommonBinRegion] at hregion
    refine
      ⟨point3 (point 0) (point 1)
          (window.distinctRichCommonBinWitnessHeight
            referenceHeight heights threshold bin),
        hlift.2, hregion.2⟩
  calc
    ((window.distinctRichCommonBinLabels
          referenceHeight heights threshold).filter fun bin =>
        cell ∈ window.distinctRichCommonBinActiveSpatialCells
          referenceHeight heights threshold bin).card =
        (bins.filter fun bin =>
          cell ∈ window.distinctRichCommonBinActiveSpatialCells
            referenceHeight heights threshold bin).card := by rfl
    _ ≤
        (pureWZ2CommonBinsMeetingSpatialCell bins
          source.globalGrains.slope referenceHeight
          (Real.sqrt rho) cell).card :=
      Finset.card_le_card hsubset
    _ ≤ 5 :=
      commonBinsMeetingSpatialCell_card_le_five
        (Real.sqrt_pos.mpr <| by
          rw [← twoScale.rhoRequested_eq]
          exact twoScale.coarseGrains.extremal.delta_pos)
        bins source.globalGrains.slope referenceHeight
        (source.globalGrains.slope_bound
          referenceHeight hreference)
        cell

/-- Every participating cell is an active cell of the second balanced
cover. -/
theorem distinctRichCommonBinParticipatingSpatialCells_subset_fine_balanced
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) :
    window.distinctRichCommonBinParticipatingSpatialCells
        referenceHeight heights threshold ⊆
      twoScale.fine.balanced.activeCells := by
  intro cell hcell
  rw [distinctRichCommonBinParticipatingSpatialCells,
    Finset.mem_biUnion] at hcell
  rcases hcell with ⟨bin, _hbin, hcell⟩
  rw [distinctRichCommonBinActiveSpatialCells,
    pureWZ2FixedCommonBinActiveSpatialCells,
    Finset.mem_filter] at hcell
  rcases hcell.2 with ⟨point, hpoint⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
  have hregion := hlift.1
  rw [pureWZ2FixedCommonBinRegion] at hregion
  let height :=
    window.distinctRichCommonBinWitnessHeight
      referenceHeight heights threshold bin
  let liftedPoint : Point3 :=
    point3 (point 0) (point 1) height
  have hpointWindow : liftedPoint ∈ window.shading.union := hregion.1
  have hpointCell :
      liftedPoint ∈ wz1PaperGridCube (Real.sqrt rho) cell := hlift.2
  have hactive :=
    window.sqrt_gridIndex_mem_fine_balanced_activeCells hpointWindow
  have hpointCell' :
      liftedPoint ∈
        wz1PaperGridCube twoScale.sqrtRequested.1 cell := by
    simpa only [twoScale.sqrtRequested_eq] using hpointCell
  have hindex :
      wz1PaperGridIndex twoScale.sqrtRequested.1 liftedPoint = cell :=
    (mem_wz1PaperGridCube
      twoScale.sqrtRequested.1 cell liftedPoint).mp hpointCell'
  rwa [hindex] at hactive

/-- Exact evaluation of `G_R` by the uniform second-cover cell mass. -/
theorem distinctRichCommonBinRestrictionVolume_eq
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) :
    window.distinctRichCommonBinRestrictionVolume
        referenceHeight heights threshold =
      ((window.distinctRichCommonBinParticipatingSpatialCells
          referenceHeight heights threshold).card : ENNReal) *
        twoScale.fine.balanced.cellMass := by
  unfold distinctRichCommonBinRestrictionVolume
  simpa only [twoScale.sqrtRequested_eq] using
    twoScale.fine.balanced.commonBinParticipatingCells_volume
      (window.distinctRichCommonBinParticipatingSpatialCells
        referenceHeight heights threshold)
      (window.distinctRichCommonBinParticipatingSpatialCells_subset_fine_balanced
        referenceHeight heights threshold)

/-- Cross-height distinct-label incidence:

`|R| * K * w_s ≤ 5 * G_R`,

where `G_R` is exactly the refined second-cover volume restricted to the
participating side-`sqrt rho` cells. -/
theorem distinctRichCommonBin_incidence
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (heights : Set ℝ) (threshold : ENNReal) (K : ℕ)
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤
        threshold) :
    ((window.distinctRichCommonBinLabels
        referenceHeight heights threshold).card : ENNReal) *
        K * twoScale.fine.balanced.cellMass ≤
      5 * window.distinctRichCommonBinRestrictionVolume
        referenceHeight heights threshold := by
  let bins :=
    window.distinctRichCommonBinLabels
      referenceHeight heights threshold
  let cells : ℤ → Finset (ℤ × ℤ × ℤ) :=
    window.distinctRichCommonBinActiveSpatialCells
      referenceHeight heights threshold
  apply CommonBinDistinctIncidence.card_mul_cellMass_le_degree_mul_totalMass
    bins cells K 5 twoScale.fine.balanced.cellMass
    (window.distinctRichCommonBinRestrictionVolume
      referenceHeight heights threshold)
  · intro bin hbin
    exact window.distinctRichCommonBin_activeSpatialCells_card_lower
      referenceHeight heights threshold K hK hbin
  · intro cell _hcell
    simpa [bins, cells] using
      window.distinctRichCommonBin_cellDegree_le_five
        referenceHeight hreference heights threshold cell
  · rw [window.distinctRichCommonBinRestrictionVolume_eq
      referenceHeight heights threshold]
    have hcells :
        (@Finset.biUnion ℤ (ℤ × ℤ × ℤ)
            (fun first second =>
              Classical.propDecidable (first = second))
            bins cells) =
          window.distinctRichCommonBinParticipatingSpatialCells
            referenceHeight heights threshold := by
      ext cell
      simp only [Finset.mem_biUnion, bins, cells,
        distinctRichCommonBinParticipatingSpatialCells]
    rw [hcells]

end PureWZ2SourceCarrierWindow

end Kakeya.Assouad

end
