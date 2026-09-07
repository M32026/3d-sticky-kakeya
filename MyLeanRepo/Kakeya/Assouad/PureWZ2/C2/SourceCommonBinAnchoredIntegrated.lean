import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinAnchoredScalar
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinRichSpatialCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinOccupiedBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinPopularHalfMass

/-!
# Construction-independent anchored integrated envelope
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2AnchoredPreBinRhoHeightRegularizedData

variable
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈
      selected.standardSqrtSlabIndices}}
    (data : PureWZ2AnchoredPreBinRhoHeightRegularizedData
      selected heightIndex)

def sourceSet : Set Point3 := data.sourcePullback.shading.union

def slabLeft
    (_data : PureWZ2AnchoredPreBinRhoHeightRegularizedData
      selected heightIndex) : ℝ :=
  (heightIndex.1 : ℝ) * Real.sqrt rhoRequested.1

def popularHeights : Set ℝ :=
  pureWZ2SourceCommonBinPopularHeights data.sourceSet data.slabLeft
    (Real.sqrt rhoRequested.1)

def distinctRichCommonBinLabels
    (referenceHeight : ℝ) (threshold : ENNReal) : Finset ℤ :=
  (pureWZ2OccupiedCommonBins data.sourceSet source.globalGrains.slope
      referenceHeight (Real.sqrt rhoRequested.1)).filter fun bin =>
    ∃ height,
      height ∈ data.popularHeights ∧
      height ∈ Set.Icc (-1 : ℝ) 1 ∧
      threshold ≤ pureWZ2FixedCommonBinSliceMass
        data.sourceSet source.globalGrains.slope referenceHeight
        (Real.sqrt rhoRequested.1) height bin

def distinctRichCommonBinWitnessHeight
    (referenceHeight : ℝ) (threshold : ENNReal) (bin : ℤ) : ℝ :=
  if hbin : bin ∈ data.distinctRichCommonBinLabels referenceHeight threshold then
    Classical.choose (Finset.mem_filter.mp hbin).2
  else 0

def distinctRichCommonBinActiveSpatialCells
    (referenceHeight : ℝ) (threshold : ENNReal) (bin : ℤ) :
    Finset (ℤ × ℤ × ℤ) :=
  pureWZ2FixedCommonBinActiveSpatialCells
    data.sourceSet source.globalGrains.slope referenceHeight
    (Real.sqrt rhoRequested.1)
    (Real.sqrt_pos.mpr <|
      source.extremal.delta_pos.trans_le rhoRequested.property.1)
    (data.distinctRichCommonBinWitnessHeight
      referenceHeight threshold bin) bin

def integratedBinMass (referenceHeight : ℝ) (bin : ℤ) : ENNReal :=
  ∫⁻ height in data.popularHeights,
    pureWZ2FixedCommonBinSliceMass data.sourceSet
      source.globalGrains.slope referenceHeight
      (Real.sqrt rhoRequested.1) height bin

def fixedBinHeightRegion (referenceHeight : ℝ) (bin : ℤ) : Set Point3 :=
  pureWZ2FixedCommonBinRegion data.sourceSet source.globalGrains.slope
      referenceHeight (Real.sqrt rhoRequested.1) bin ∩
    {point | point (2 : Fin 3) ∈ data.popularHeights}

def fixedBinRhoCells (referenceHeight : ℝ) (bin : ℤ) :
    Finset (ℤ × ℤ × ℤ) :=
  data.cells.filter fun cell =>
    (data.fixedBinHeightRegion referenceHeight bin ∩
      wz1PaperGridCube rhoRequested.1 cell).Nonempty

def fixedBinWholeCellEnvelope (referenceHeight : ℝ) (bin : ℤ) :
    Set Point3 :=
  wz2RetainedCellsUnion rhoRequested.1
    (data.fixedBinRhoCells referenceHeight bin)

def standardParents
    (_data : PureWZ2AnchoredPreBinRhoHeightRegularizedData
      selected heightIndex) : Finset (ℤ × ℤ × ℤ) :=
  (selected.standardSqrtSlabRhoCells heightIndex.1).image
    selected.standardSecondParent

def standardSecondRegion
    (data : PureWZ2AnchoredPreBinRhoHeightRegularizedData
      selected heightIndex) : Set Point3 :=
  fine.refined.union ∩
    ⋃ parent ∈ data.standardParents,
      wz1PaperGridCube sqrtRequested.1 parent

def standardCoarseRegion
    (_data : PureWZ2AnchoredPreBinRhoHeightRegularizedData
      selected heightIndex) : Set Point3 :=
  wz2RetainedCellsUnion rhoRequested.1
    (selected.standardSqrtSlabRhoCells heightIndex.1)

theorem standardSecondRegion_eq_coarseRegion :
    data.standardSecondRegion = data.standardCoarseRegion := by
  have hrho : 0 < rhoRequested.1 := coarse.coarse_extremal.delta_pos
  have hfull := fine.refined_cubical.union_eq_activeCells hrho
  ext point
  constructor
  · rintro ⟨hpointFine, hpointParentUnion⟩
    rcases Set.mem_iUnion₂.mp hpointParentUnion with
      ⟨parent, hparent, hpointParent⟩
    rw [standardParents] at hparent
    rcases Finset.mem_image.mp hparent with
      ⟨witnessCell, hwitnessSlab, rfl⟩
    have hpointFine' := hpointFine
    rw [hfull] at hpointFine'
    rcases Set.mem_iUnion₂.mp hpointFine' with
      ⟨rhoCell, hrhoCellActive, hpointRhoCell⟩
    have hrhoCellSelected : rhoCell ∈ selected.selectedCells := by
      simpa only [selected.selectedCells_eq] using hrhoCellActive
    have hpointCanonical :
        point ∈ wz1PaperGridCube sqrtRequested.1
          (selected.standardSecondParent rhoCell) :=
      selected.standardSecondParent_cell_subset
        hrhoCellSelected hpointRhoCell
    have hcanonicalEq :
        selected.standardSecondParent rhoCell =
          selected.standardSecondParent witnessCell :=
      ((mem_wz1PaperGridCube sqrtRequested.1
        (selected.standardSecondParent rhoCell) point).mp
          hpointCanonical).symm.trans
        ((mem_wz1PaperGridCube sqrtRequested.1
          (selected.standardSecondParent witnessCell) point).mp
            hpointParent)
    have hwitnessHeight :
        selected.standardSqrtSlabIndex witnessCell = heightIndex.1 :=
      (Finset.mem_filter.mp hwitnessSlab).2
    have hrhoCellSlab :
        rhoCell ∈ selected.standardSqrtSlabRhoCells heightIndex.1 := by
      rw [PureWZ2AnchoredSourceRelativeFineSelection.standardSqrtSlabRhoCells,
        Finset.mem_filter]
      refine ⟨hrhoCellSelected, ?_⟩
      rw [PureWZ2AnchoredSourceRelativeFineSelection.standardSqrtSlabIndex,
        hcanonicalEq]
      exact hwitnessHeight
    rw [standardCoarseRegion, wz2RetainedCellsUnion]
    exact Set.mem_iUnion₂.mpr
      ⟨rhoCell, hrhoCellSlab, hpointRhoCell⟩
  · intro hpoint
    rw [standardCoarseRegion, wz2RetainedCellsUnion] at hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨rhoCell, hrhoCellSlab, hpointRhoCell⟩
    have hrhoCellSelected :=
      selected.standardSqrtSlabRhoCells_subset heightIndex.1 hrhoCellSlab
    have hrhoCellActive : rhoCell ∈
        wz1PaperActiveCells fine.refined hrho := by
      simpa only [selected.selectedCells_eq] using hrhoCellSelected
    have hpointFine : point ∈ fine.refined.union := by
      rw [hfull]
      exact Set.mem_iUnion₂.mpr
        ⟨rhoCell, hrhoCellActive, hpointRhoCell⟩
    have hpointParent :=
      selected.standardSecondParent_cell_subset
        hrhoCellSelected hpointRhoCell
    exact ⟨hpointFine, Set.mem_iUnion₂.mpr
      ⟨selected.standardSecondParent rhoCell,
        Finset.mem_image.mpr ⟨rhoCell, hrhoCellSlab, rfl⟩,
        hpointParent⟩⟩

theorem standardParentMass_eq_coarseVolume :
    ((data.standardParents.card : ENNReal) * fine.balanced.cellMass) =
      volume data.standardCoarseRegion := by
  rw [← data.standardSecondRegion_eq_coarseRegion]
  exact (fine.balanced.selected_cells_volume data.standardParents (by
    intro parent hparent
    rw [standardParents] at hparent
    rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
    exact selected.standardSecondParent_active
      (selected.standardSqrtSlabRhoCells_subset heightIndex.1 hcell))).symm

theorem standardCoarseRegion_volume :
    volume data.standardCoarseRegion =
      ((selected.standardSqrtSlabRhoCells heightIndex.1).card : ENNReal) *
        volume (wz1PaperGridCube rhoRequested.1 (0, 0, 0)) := by
  exact wz1PaperGridCube_volume_biUnion
    coarse.coarse_extremal.delta_pos _

theorem sourceSet_measurable : MeasurableSet data.sourceSet :=
  data.sourcePullback.shading.union_measurable

theorem sourceSet_subset_source : data.sourceSet ⊆ source.shading.union :=
  data.sourcePullback.subshading.union_subset

theorem sourceSet_volume_pos : 0 < volume data.sourceSet := by
  rw [sourceSet, data.source_volume]
  exact ENNReal.mul_pos
    (by exact_mod_cast data.cells_nonempty.card_pos.ne')
    coarse.balanced.cellMass_pos.ne'

theorem sourceSet_volume_ne_top : volume data.sourceSet ≠ ⊤ := by
  rw [sourceSet, data.source_volume]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    coarse.balanced.cellMass_ne_top

theorem sourceSet_height :
    ∀ point ∈ data.sourceSet,
      point (2 : Fin 3) ∈
        Set.Ico data.slabLeft
          (data.slabLeft + Real.sqrt rhoRequested.1) := by
  intro point hpoint
  change point ∈ data.sourcePullback.shading.union at hpoint
  rw [data.sourcePullback.union_eq, data.sourcePullback.region_eq] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint.2 with ⟨cell, hcell, hpointCell⟩
  have hselected := data.cells_subset_selected hcell
  have hparent := selected.standardSecondParent_cell_subset hselected hpointCell
  have hstandard := data.cells_subset_standard hcell
  have hindex :
      selected.standardSqrtSlabIndex cell = heightIndex.1 :=
    (Finset.mem_filter.mp hstandard).2
  have hparentHeight :
      (selected.standardSecondParent cell).2.2 = heightIndex.1 := by
    simpa [PureWZ2AnchoredSourceRelativeFineSelection.standardSqrtSlabIndex]
      using hindex
  rw [wz1PaperGridCube_eq_Ico fine.coarse_extremal.delta_pos] at hparent
  have hz := hparent.2.2.2.2
  rw [hparentHeight, data.sqrtRequested_eq] at hz
  change
    (heightIndex.1 : ℝ) * Real.sqrt rhoRequested.1 ≤ point 2 ∧
      point 2 <
        (heightIndex.1 : ℝ) * Real.sqrt rhoRequested.1 +
          Real.sqrt rhoRequested.1
  exact ⟨hz.1, hz.2.trans_eq (by ring)⟩

theorem popularHalfMass :
    volume data.sourceSet / 2 ≤
      ∫⁻ z in data.popularHeights,
        pureWZ2SourceCommonBinSliceMass data.sourceSet z := by
  exact pureWZ2SourceCommonBinPopularHalfMass data.sourceSet
    data.sourceSet_measurable data.sourceSet_volume_ne_top
    (Real.sqrt_pos.mpr <|
      source.extremal.delta_pos.trans_le rhoRequested.property.1)
    data.sourceSet_height

theorem exists_referenceHeight :
    ∃ referenceHeight,
      referenceHeight ∈ data.popularHeights ∧
      referenceHeight ∈ Set.Icc (-1 : ℝ) 1 := by
  have hmassPos :
      0 < ∫⁻ z in data.popularHeights,
        pureWZ2SourceCommonBinSliceMass data.sourceSet z :=
    (ENNReal.div_pos data.sourceSet_volume_pos.ne' (by norm_num)).trans_le
      data.popularHalfMass
  have hpopular : data.popularHeights.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hmassPos
    simp at hmassPos
  let referenceHeight := Classical.choose hpopular
  have hreference : referenceHeight ∈ data.popularHeights :=
    Classical.choose_spec hpopular
  refine ⟨referenceHeight, hreference, ?_⟩
  have hthresholdPos :
      0 < pureWZ2SourceCommonBinPopularThreshold
        data.sourceSet (Real.sqrt rhoRequested.1) := by
    unfold pureWZ2SourceCommonBinPopularThreshold
      pureWZ2CommonBinPopularThreshold
    exact ENNReal.div_pos
      (ENNReal.div_pos data.sourceSet_volume_pos.ne' (by norm_num)).ne'
      ENNReal.ofReal_ne_top
  have hslicePos :
      0 < pureWZ2SourceCommonBinSliceMass data.sourceSet referenceHeight :=
    hthresholdPos.trans_le hreference.2
  rcases nonempty_of_measure_ne_zero hslicePos.ne' with
    ⟨planarPoint, hplanarPoint⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hplanarPoint
  have hbox := shading_union_subset_axisBox
    (data.sourceSet_subset_source hlift)
  simpa [point3, Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2

theorem popularHeights_close
    {first second : ℝ}
    (hfirst : first ∈ data.popularHeights)
    (hsecond : second ∈ data.popularHeights) :
    |first - second| ≤ Real.sqrt rhoRequested.1 := by
  rw [abs_le]
  constructor <;>
    linarith [hfirst.1.1, hfirst.1.2, hsecond.1.1, hsecond.1.2]

theorem popularHeight_mem_paperRange
    {height : ℝ} (hheight : height ∈ data.popularHeights) :
    height ∈ Set.Icc (-1 : ℝ) 1 := by
  have hthresholdPos :
      0 < pureWZ2SourceCommonBinPopularThreshold
        data.sourceSet (Real.sqrt rhoRequested.1) := by
    unfold pureWZ2SourceCommonBinPopularThreshold
      pureWZ2CommonBinPopularThreshold
    exact ENNReal.div_pos
      (ENNReal.div_pos data.sourceSet_volume_pos.ne' (by norm_num)).ne'
      ENNReal.ofReal_ne_top
  have hslicePos :
      0 < pureWZ2SourceCommonBinSliceMass data.sourceSet height :=
    hthresholdPos.trans_le hheight.2
  rcases nonempty_of_measure_ne_zero hslicePos.ne' with
    ⟨planarPoint, hplanarPoint⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hplanarPoint
  have hbox := shading_union_subset_axisBox
    (data.sourceSet_subset_source hlift)
  simpa [point3, Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2

private theorem slice_y_abs_le_one (height : ℝ) :
    ∀ point ∈ horizontalSlice data.sourceSet height,
      |point (1 : Fin 3)| ≤ 1 := by
  intro point hpoint
  have hbox := shading_union_subset_axisBox
    (data.sourceSet_subset_source hpoint.1)
  simpa [Kakeya.Streamlined.axisBox] using hbox.2.1

private theorem slice_projection_bounded
    (height : ℝ) (hheight : height ∈ Set.Icc (-1 : ℝ) 1) :
    scalarProjection
        (globalGrainDirection (source.globalGrains.slope height))
        (horizontalSlice data.sourceSet height) ⊆ Set.Icc (-4 : ℝ) 4 := by
  rintro value ⟨point, hpoint, rfl⟩
  have hbox := shading_union_subset_axisBox
    (data.sourceSet_subset_source hpoint.1)
  have hslope := source.globalGrains.slope_bound height hheight
  have hformula :
      inner ℝ point (globalGrainDirection
          (source.globalGrains.slope height)) =
        point 0 + source.globalGrains.slope height * point 1 := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
  have habs :
      |inner ℝ point (globalGrainDirection
          (source.globalGrains.slope height))| ≤ 4 := by
    rw [hformula]
    calc
      |point 0 + source.globalGrains.slope height * point 1| ≤
          |point 0| + |source.globalGrains.slope height| * |point 1| := by
        simpa [abs_mul] using abs_add_le (point 0)
          (source.globalGrains.slope height * point 1)
      _ ≤ 1 + 3 * 1 := by
        gcongr
        · simpa [Kakeya.Streamlined.axisBox] using hbox.1
        · simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
      _ = 4 := by norm_num
  exact abs_le.mp habs

private theorem slice_ad_root
    (height : ℝ) (hheight : height ∈ Set.Icc (-1 : ℝ) 1) :
    IsADSet1
      (scalarProjection
        (globalGrainDirection (source.globalGrains.slope height))
        (horizontalSlice data.sourceSet height))
      (Real.sqrt rhoRequested.1) (1 - sigma)
      (2 * Kakeya.realRpowENN delta (-inputLoss)) := by
  have hrho : 0 < rhoRequested.1 :=
    source.extremal.delta_pos.trans_le rhoRequested.property.1
  have hrhoRoot : rhoRequested.1 ≤ Real.sqrt rhoRequested.1 := by
    nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rhoRequested.1,
      rhoRequested.property.2]
  have hpaper :
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope height))
          (horizontalSlice data.sourceSet height))
        delta (1 - sigma) (Kakeya.realRpowENN delta (-inputLoss)) := by
    apply (source.globalGrains.global_ad height hheight).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point, ⟨data.sourceSet_subset_source hpoint.1, hpoint.2⟩, rfl⟩
  have hdelta :
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope height))
          (horizontalSlice data.sourceSet height))
        delta (1 - sigma)
        (2 * Kakeya.realRpowENN delta (-inputLoss)) :=
    hpaper.toIsADSet1 (data.slice_projection_bounded height hheight)
  exact hdelta.coarsen_scale (Real.sqrt_pos.mpr hrho)
    (rhoRequested.property.1.trans hrhoRoot)
    (Real.sqrt_le_one.mpr rhoRequested.property.2)

theorem commonBinSlice_occupiedBound
    (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rhoRequested.1) :
    ((pureWZ2OccupiedCommonBins
      (horizontalSlice data.sourceSet height) source.globalGrains.slope
      referenceHeight (Real.sqrt rhoRequested.1)).card : ENNReal) ≤
      264 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN (1 / Real.sqrt rhoRequested.1) (1 - sigma) := by
  have hbound := pureWZ2_fixed_common_bin_occupied_bound
    (horizontalSlice data.sourceSet height) source.globalGrains.slope
    source.globalGrains.slope_lipschitz height referenceHeight hheight
    hreference hclose (data.slice_y_abs_le_one height)
    (data.slice_ad_root height hheight)
    (Real.sqrt_le_one.mpr rhoRequested.property.2)
  calc
    _ ≤ 132 * (2 * Kakeya.realRpowENN delta (-inputLoss)) *
        Kakeya.realRpowENN (1 / Real.sqrt rhoRequested.1) (1 - sigma) :=
      hbound
    _ = _ := by ring

theorem commonBinSliceMass_sum
    (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rhoRequested.1) :
    pureWZ2SourceCommonBinSliceMass data.sourceSet height =
      ∑ bin ∈ pureWZ2OccupiedCommonBins
          (horizontalSlice data.sourceSet height) source.globalGrains.slope
          referenceHeight (Real.sqrt rhoRequested.1),
        pureWZ2FixedCommonBinSliceMass data.sourceSet
          source.globalGrains.slope referenceHeight
          (Real.sqrt rhoRequested.1) height bin := by
  simpa [pureWZ2SourceCommonBinSliceMass] using
    pureWZ2_fixed_common_bin_sliceMass_sum data.sourceSet_measurable
      source.globalGrains.slope referenceHeight
      (Real.sqrt rhoRequested.1) height
      (pureWZ2OccupiedCommonBins (horizontalSlice data.sourceSet height)
        source.globalGrains.slope referenceHeight (Real.sqrt rhoRequested.1))
      (fun point hpoint => by
        exact pureWZ2_fixed_common_bin_mem
          (horizontalSlice data.sourceSet height) source.globalGrains.slope
          source.globalGrains.slope_lipschitz height referenceHeight hheight
          hreference hclose (data.slice_y_abs_le_one height)
          (data.slice_ad_root height hheight)
          (Real.sqrt_le_one.mpr rhoRequested.property.2) hpoint)

private theorem commonBinSliceMass_ne_top (height : ℝ) :
    pureWZ2SourceCommonBinSliceMass data.sourceSet height ≠ ⊤ := by
  have hsliceBall :
      wz1Lemma23PlanarSlice data.sourceSet height ⊆
        Metric.closedBall (0 : Point2) 2 := by
    intro point hpoint
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hbox := shading_union_subset_axisBox
      (data.sourceSet_subset_source hlift)
    have h0 : |point 0| ≤ 1 := by
      simpa [point3, Kakeya.Streamlined.axisBox] using hbox.1
    have h1 : |point 1| ≤ 1 := by
      simpa [point3, Kakeya.Streamlined.axisBox] using hbox.2.1
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖point‖ ^ 2 = point 0 ^ 2 + point 1 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_two]
    have h0sq : point 0 ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (point 0)]
    have h1sq : point 1 ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg (point 1)]
    nlinarith [norm_nonneg point]
  exact ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
    (measure_mono hsliceBall)

theorem measurable_commonBinSliceMass
    (referenceHeight : ℝ) (bin : ℤ) :
    Measurable (fun height : ℝ =>
      pureWZ2FixedCommonBinSliceMass data.sourceSet source.globalGrains.slope
        referenceHeight (Real.sqrt rhoRequested.1) height bin) :=
  measurable_volume_wz1Lemma23PlanarSlice
    (pureWZ2FixedCommonBinRegion data.sourceSet source.globalGrains.slope
      referenceHeight (Real.sqrt rhoRequested.1) bin)
    (measurableSet_pureWZ2FixedCommonBinRegion data.sourceSet_measurable
      source.globalGrains.slope referenceHeight
      (Real.sqrt rhoRequested.1) bin)

theorem distinctRichCommonBin_integratedMass
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ data.popularHeights)
    (B₀ threshold : ENNReal)
    (hB₀ : 264 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN (1 / Real.sqrt rhoRequested.1) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold data.sourceSet
          (Real.sqrt rhoRequested.1)) :
    volume data.sourceSet ≤
      4 * ∑ bin ∈ data.distinctRichCommonBinLabels
          referenceHeight threshold,
        data.integratedBinMass referenceHeight bin := by
  let heights := data.popularHeights
  let richLabels := data.distinctRichCommonBinLabels referenceHeight threshold
  let sliceMass : ℝ → ENNReal :=
    pureWZ2SourceCommonBinSliceMass data.sourceSet
  let binMass : ℝ → ℤ → ENNReal := fun height bin =>
    pureWZ2FixedCommonBinSliceMass data.sourceSet source.globalGrains.slope
      referenceHeight (Real.sqrt rhoRequested.1) height bin
  have hreferenceRange := data.popularHeight_mem_paperRange hreference
  have hpointwise : ∀ height ∈ heights,
      sliceMass height ≤ 2 * ∑ bin ∈ richLabels, binMass height bin := by
    intro height hheight
    have hheightOriginal : height ∈ data.popularHeights := by
      simpa [heights] using hheight
    have hheightRange := data.popularHeight_mem_paperRange hheightOriginal
    have hclose := data.popularHeights_close hheightOriginal hreference
    let bins := pureWZ2OccupiedCommonBins
      (horizontalSlice data.sourceSet height) source.globalGrains.slope
      referenceHeight (Real.sqrt rhoRequested.1)
    have htotalEq :
        sliceMass height = ∑ bin ∈ bins, binMass height bin := by
      simpa [bins, sliceMass, binMass] using data.commonBinSliceMass_sum
        referenceHeight height hreferenceRange hheightRange hclose
    have hcard : (bins.card : ENNReal) ≤ B₀ := by
      simpa [bins] using (data.commonBinSlice_occupiedBound referenceHeight
        height hreferenceRange hheightRange hclose).trans hB₀
    have hpoor :
        2 * ((bins.card : ENNReal) * threshold) ≤ sliceMass height := by
      calc
        _ ≤ 2 * (B₀ * threshold) := by gcongr
        _ = 2 * B₀ * threshold := by ring
        _ ≤ pureWZ2SourceCommonBinPopularThreshold data.sourceSet
            (Real.sqrt rhoRequested.1) := hthresholdBudget
        _ ≤ pureWZ2SourceCommonBinSliceMass data.sourceSet height :=
          hheightOriginal.2
        _ = sliceMass height := rfl
    have hretained := CommonBinRichSelection.total_le_two_mul_rich_sum
      bins (binMass height) threshold (sliceMass height) htotalEq
      (by simpa [sliceMass] using data.commonBinSliceMass_ne_top height) hpoor
    have hsubset : CommonBinRichSelection.richBins
        bins (binMass height) threshold ⊆ richLabels := by
      intro bin hbin
      have hbinData := Finset.mem_filter.mp hbin
      have hambient : bin ∈ pureWZ2OccupiedCommonBins data.sourceSet
          source.globalGrains.slope referenceHeight
          (Real.sqrt rhoRequested.1) := by
        have hbinOccupied := hbinData.1
        dsimp only [bins] at hbinOccupied
        rw [pureWZ2OccupiedCommonBins, Finset.mem_filter] at hbinOccupied ⊢
        refine ⟨hbinOccupied.1, ?_⟩
        rcases hbinOccupied.2 with ⟨point, hpoint, hlabel⟩
        exact ⟨point, hpoint.1, hlabel⟩
      change bin ∈ data.distinctRichCommonBinLabels
        referenceHeight threshold
      rw [distinctRichCommonBinLabels, Finset.mem_filter]
      exact ⟨hambient, height, hheight, hheightRange, hbinData.2⟩
    exact hretained.trans <| mul_le_mul_right
      (Finset.sum_le_sum_of_subset hsubset) 2
  have hheightsMeas : MeasurableSet heights :=
    measurableSet_pureWZ2SourceCommonBinPopularHeights data.sourceSet
      data.sourceSet_measurable data.slabLeft (Real.sqrt rhoRequested.1)
  have hbinMassMeas : ∀ bin : ℤ,
      Measurable (fun height => binMass height bin) := by
    intro bin
    simpa [binMass] using data.measurable_commonBinSliceMass
      referenceHeight bin
  have hintegratedPointwise :
      (∫⁻ height in heights, sliceMass height) ≤
        2 * ∫⁻ height in heights,
          ∑ bin ∈ richLabels, binMass height bin := by
    calc
      _ ≤ ∫⁻ height in heights,
          2 * ∑ bin ∈ richLabels, binMass height bin :=
        setLIntegral_mono' hheightsMeas hpointwise
      _ = _ := MeasureTheory.lintegral_const_mul 2
        (Finset.measurable_sum richLabels fun bin _ => hbinMassMeas bin)
  have hsumIntegral :
      (∫⁻ height in heights, ∑ bin ∈ richLabels, binMass height bin) =
        ∑ bin ∈ richLabels, data.integratedBinMass referenceHeight bin := by
    rw [MeasureTheory.lintegral_finsetSum richLabels]
    · rfl
    · intro bin _
      exact hbinMassMeas bin
  calc
    volume data.sourceSet =
        volume data.sourceSet / 2 + volume data.sourceSet / 2 :=
      (ENNReal.add_halves _).symm
    _ ≤ (∫⁻ height in heights, sliceMass height) +
        ∫⁻ height in heights, sliceMass height := by
      gcongr <;> simpa [heights, sliceMass] using data.popularHalfMass
    _ = 2 * ∫⁻ height in heights, sliceMass height := by ring
    _ ≤ 2 * (2 * ∫⁻ height in heights,
        ∑ bin ∈ richLabels, binMass height bin) := by gcongr
    _ = 4 * ∑ bin ∈ richLabels,
        data.integratedBinMass referenceHeight bin := by
      rw [hsumIntegral]
      ring
    _ = _ := rfl

theorem distinctRichCommonBinWitnessHeight_spec
    (referenceHeight : ℝ) (threshold : ENNReal) {bin : ℤ}
    (hbin : bin ∈ data.distinctRichCommonBinLabels referenceHeight threshold) :
    data.distinctRichCommonBinWitnessHeight referenceHeight threshold bin ∈
        data.popularHeights ∧
      data.distinctRichCommonBinWitnessHeight referenceHeight threshold bin ∈
        Set.Icc (-1 : ℝ) 1 ∧
      threshold ≤ pureWZ2FixedCommonBinSliceMass data.sourceSet
        source.globalGrains.slope referenceHeight
        (Real.sqrt rhoRequested.1)
        (data.distinctRichCommonBinWitnessHeight
          referenceHeight threshold bin) bin := by
  rw [distinctRichCommonBinWitnessHeight, dif_pos hbin]
  exact Classical.choose_spec (Finset.mem_filter.mp hbin).2

private theorem fixedCommonBinSpatialCellSliceMass_le
    (referenceHeight height : ℝ)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (bin : ℤ) (cell : ℤ × ℤ × ℤ) :
    pureWZ2FixedCommonBinSpatialCellSliceMass data.sourceSet
        source.globalGrains.slope referenceHeight
        (Real.sqrt rhoRequested.1) height bin cell ≤
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
        sigma inputLoss delta rhoRequested.1 := by
  have hrho : 0 < rhoRequested.1 :=
    source.extremal.delta_pos.trans_le rhoRequested.property.1
  have hrhoRoot : rhoRequested.1 ≤ Real.sqrt rhoRequested.1 := by
    nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rhoRequested.1,
      rhoRequested.property.2]
  have hsubset :
      wz1Lemma23PlanarSlice
          (pureWZ2FixedCommonBinRegion data.sourceSet
              source.globalGrains.slope referenceHeight
              (Real.sqrt rhoRequested.1) bin ∩
            wz1PaperGridCube (Real.sqrt rhoRequested.1) cell) height ⊆
        wz1Lemma23PlanarSlice
          (source.shading.union ∩
            wz1PaperGridCube (Real.sqrt rhoRequested.1) cell) height := by
    intro point hpoint
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    apply wz1Lemma23_mem_planarSlice_iff.mpr
    exact ⟨data.sourceSet_subset_source hlift.1.1, hlift.2⟩
  calc
    _ ≤ volume (wz1Lemma23PlanarSlice
        (source.shading.union ∩
          wz1PaperGridCube (Real.sqrt rhoRequested.1) cell)
        height) := measure_mono hsubset
    _ ≤ _ := by
      simpa [PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap]
        using source.sourceCommonBinSpatialCellSliceBound hrho
          (rhoRequested.property.1.trans hrhoRoot) cell height hheight

theorem distinctRichCommonBin_activeSpatialCells_card_lower
    (referenceHeight : ℝ) (threshold : ENNReal) (K : ℕ)
    (hK : (K : ENNReal) *
        PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
          sigma inputLoss delta rhoRequested.1 ≤ threshold)
    {bin : ℤ}
    (hbin : bin ∈ data.distinctRichCommonBinLabels
      referenceHeight threshold) :
    K ≤ (data.distinctRichCommonBinActiveSpatialCells
      referenceHeight threshold bin).card := by
  let height := data.distinctRichCommonBinWitnessHeight
    referenceHeight threshold bin
  have hwitness := data.distinctRichCommonBinWitnessHeight_spec
    referenceHeight threshold hbin
  have hrho : 0 < rhoRequested.1 :=
    source.extremal.delta_pos.trans_le rhoRequested.property.1
  apply CommonBinRichSelection.cell_card_lower_of_rich
    (data.distinctRichCommonBinActiveSpatialCells
      referenceHeight threshold bin)
    (pureWZ2FixedCommonBinSpatialCellSliceMass data.sourceSet
      source.globalGrains.slope referenceHeight
      (Real.sqrt rhoRequested.1) height bin)
    (pureWZ2FixedCommonBinSliceMass data.sourceSet source.globalGrains.slope
      referenceHeight (Real.sqrt rhoRequested.1) height bin) threshold
    (PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      sigma inputLoss delta rhoRequested.1) K
  · exact hwitness.2.2
  · exact le_of_eq <| by
      simpa [distinctRichCommonBinActiveSpatialCells, height] using
        pureWZ2_fixed_common_bin_sliceMass_eq_sum_activeSpatialCells
          data.sourceSet_measurable source.globalGrains.slope referenceHeight
          (Real.sqrt_pos.mpr hrho) height bin
          (fun point hpoint => norm_le_two_of_mem_paperShading
            (data.sourceSet_subset_source hpoint))
  · intro cell _
    exact data.fixedCommonBinSpatialCellSliceMass_le
      referenceHeight height hwitness.2.1 bin cell
  · exact hK
  · unfold PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos (by norm_num)
          (ENNReal.ofReal_pos.mpr
            (Real.rpow_pos_of_pos source.extremal.delta_pos _)).ne').ne'
        (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos source.extremal.delta_pos _)).ne').ne'
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hrho _)).ne'
  · unfold PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      Kakeya.realRpowENN
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top

theorem distinctRichCommonBin_cellDegree_le_five
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (threshold : ENNReal) (cell : ℤ × ℤ × ℤ) :
    ((data.distinctRichCommonBinLabels referenceHeight threshold).filter
      fun bin => cell ∈ data.distinctRichCommonBinActiveSpatialCells
        referenceHeight threshold bin).card ≤ 5 := by
  let bins := data.distinctRichCommonBinLabels referenceHeight threshold
  have hsubset :
      bins.filter (fun bin => cell ∈
          data.distinctRichCommonBinActiveSpatialCells
            referenceHeight threshold bin) ⊆
        pureWZ2CommonBinsMeetingSpatialCell bins source.globalGrains.slope
          referenceHeight (Real.sqrt rhoRequested.1) cell := by
    intro bin hbin
    have hdata := Finset.mem_filter.mp hbin
    rw [distinctRichCommonBinActiveSpatialCells,
      pureWZ2FixedCommonBinActiveSpatialCells, Finset.mem_filter] at hdata
    rcases hdata.2.2 with ⟨point, hpoint⟩
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    rw [pureWZ2CommonBinsMeetingSpatialCell, Finset.mem_filter]
    exact ⟨hdata.1, point3 (point 0) (point 1)
      (data.distinctRichCommonBinWitnessHeight referenceHeight threshold bin),
      hlift.2, hlift.1.2⟩
  calc
    _ ≤ (pureWZ2CommonBinsMeetingSpatialCell bins source.globalGrains.slope
          referenceHeight (Real.sqrt rhoRequested.1) cell).card :=
      Finset.card_le_card hsubset
    _ ≤ 5 := commonBinsMeetingSpatialCell_card_le_five
      (Real.sqrt_pos.mpr <|
        source.extremal.delta_pos.trans_le rhoRequested.property.1)
      bins source.globalGrains.slope referenceHeight
      (source.globalGrains.slope_bound referenceHeight hreference) cell

theorem distinctRichCommonBin_activeSpatialCells_subset_standardParents
    (referenceHeight : ℝ) (threshold : ENNReal) (bin : ℤ) :
    data.distinctRichCommonBinActiveSpatialCells referenceHeight threshold bin ⊆
      data.standardParents := by
  intro cell hcell
  rw [distinctRichCommonBinActiveSpatialCells,
    pureWZ2FixedCommonBinActiveSpatialCells, Finset.mem_filter] at hcell
  rcases hcell.2 with ⟨point, hpoint⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
  let sourcePoint := point3 (point 0) (point 1)
    (data.distinctRichCommonBinWitnessHeight referenceHeight threshold bin)
  have hsourcePoint : sourcePoint ∈ data.sourceSet := hlift.1.1
  change sourcePoint ∈ data.sourcePullback.shading.union at hsourcePoint
  rw [data.sourcePullback.union_eq, data.sourcePullback.region_eq] at hsourcePoint
  rcases Set.mem_iUnion₂.mp hsourcePoint.2 with
    ⟨rhoCell, hrhoCell, hpointRho⟩
  have hselected := data.cells_subset_selected hrhoCell
  have hpointParent :=
    selected.standardSecondParent_cell_subset hselected hpointRho
  have hpointCell :
      sourcePoint ∈ wz1PaperGridCube sqrtRequested.1 cell := by
    rw [data.sqrtRequested_eq]
    exact hlift.2
  have hparentEq : selected.standardSecondParent rhoCell = cell :=
    ((mem_wz1PaperGridCube sqrtRequested.1
      (selected.standardSecondParent rhoCell) _).mp hpointParent).symm.trans
      ((mem_wz1PaperGridCube sqrtRequested.1 cell _).mp hpointCell)
  exact Finset.mem_image.mpr
    ⟨rhoCell, data.cells_subset_standard hrhoCell, hparentEq⟩

theorem distinctRichCommonBin_incidence
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (threshold : ENNReal) (K : ℕ)
    (hK : (K : ENNReal) *
        PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
          sigma inputLoss delta rhoRequested.1 ≤ threshold) :
    ((data.distinctRichCommonBinLabels referenceHeight threshold).card :
        ENNReal) * K * fine.balanced.cellMass ≤
      5 * ((data.standardParents.card : ENNReal) *
        fine.balanced.cellMass) := by
  let bins := data.distinctRichCommonBinLabels referenceHeight threshold
  let cells : ℤ → Finset (ℤ × ℤ × ℤ) := fun bin =>
    data.distinctRichCommonBinActiveSpatialCells referenceHeight threshold bin
  apply CommonBinDistinctIncidence.card_mul_cellMass_le_degree_mul_totalMass
    bins cells K 5 fine.balanced.cellMass
      ((data.standardParents.card : ENNReal) * fine.balanced.cellMass)
  · intro bin hbin
    exact data.distinctRichCommonBin_activeSpatialCells_card_lower
      referenceHeight threshold K hK hbin
  · intro cell _
    simpa [bins, cells] using data.distinctRichCommonBin_cellDegree_le_five
      referenceHeight hreference threshold cell
  · have hsubset :
        (@Finset.biUnion ℤ (ℤ × ℤ × ℤ)
          (fun first second => Classical.propDecidable (first = second))
          bins cells) ⊆ data.standardParents := by
      intro cell hcell
      rcases
          (@Finset.mem_biUnion ℤ (ℤ × ℤ × ℤ)
            bins cells
            (fun first second =>
              Classical.propDecidable (first = second))
            cell).mp hcell with ⟨bin, _hbin, hcell⟩
      exact data.distinctRichCommonBin_activeSpatialCells_subset_standardParents
        referenceHeight threshold bin hcell
    have hcard :
        ((@Finset.biUnion ℤ (ℤ × ℤ × ℤ)
          (fun first second => Classical.propDecidable (first = second))
          bins cells).card : ENNReal) ≤ data.standardParents.card := by
      exact_mod_cast Finset.card_le_card hsubset
    gcongr

theorem fixedBinRhoCells_subset
    (referenceHeight : ℝ) (bin : ℤ) :
    data.fixedBinRhoCells referenceHeight bin ⊆ data.cells :=
  Finset.filter_subset _ _

theorem fixedBinHeightRegion_subset_envelope
    (referenceHeight : ℝ) (bin : ℤ) :
    data.fixedBinHeightRegion referenceHeight bin ⊆
      data.fixedBinWholeCellEnvelope referenceHeight bin := by
  intro point hpoint
  have hsource : point ∈ data.sourceSet := hpoint.1.1
  change point ∈ data.sourcePullback.shading.union at hsource
  rw [data.sourcePullback.union_eq] at hsource
  have hregion := hsource.2
  rw [data.sourcePullback.region_eq] at hregion
  rcases Set.mem_iUnion₂.mp hregion with ⟨cell, hcell, hpointCell⟩
  rw [fixedBinWholeCellEnvelope, wz2RetainedCellsUnion]
  exact Set.mem_iUnion₂.mpr
    ⟨cell, Finset.mem_filter.mpr
      ⟨hcell, ⟨point, hpoint, hpointCell⟩⟩, hpointCell⟩

theorem fixedBinHeightRegion_volume
    (referenceHeight : ℝ) (bin : ℤ) :
    volume (data.fixedBinHeightRegion referenceHeight bin) =
      data.integratedBinMass referenceHeight bin := by
  let heights := data.popularHeights
  let fixedRegion := pureWZ2FixedCommonBinRegion data.sourceSet
    source.globalGrains.slope referenceHeight
      (Real.sqrt rhoRequested.1) bin
  have hslice : ∀ height : ℝ,
      wz1Lemma23PlanarSlice
          (data.fixedBinHeightRegion referenceHeight bin) height =
        if height ∈ heights then
          wz1Lemma23PlanarSlice fixedRegion height else ∅ := by
    intro height
    by_cases hheight : height ∈ heights
    · rw [if_pos hheight]
      ext point
      simp only [wz1Lemma23_mem_planarSlice_iff]
      constructor
      · exact fun hpoint => hpoint.1
      · exact fun hpoint => ⟨hpoint, by simpa [point3] using hheight⟩
    · rw [if_neg hheight]
      ext point
      simp only [Set.notMem_empty, iff_false]
      rw [wz1Lemma23_mem_planarSlice_iff]
      exact fun hpoint => hheight (by simpa [point3] using hpoint.2)
  have hmeas : MeasurableSet
      (data.fixedBinHeightRegion referenceHeight bin) :=
    (measurableSet_pureWZ2FixedCommonBinRegion data.sourceSet_measurable
      source.globalGrains.slope referenceHeight
        (Real.sqrt rhoRequested.1) bin).inter
      ((measurableSet_pureWZ2SourceCommonBinPopularHeights data.sourceSet
        data.sourceSet_measurable data.slabLeft
          (Real.sqrt rhoRequested.1)).preimage (by fun_prop))
  rw [wz1_lemma23_volume_eq_lintegral_planarSlice _ hmeas]
  change (∫⁻ height : ℝ,
      volume (wz1Lemma23PlanarSlice
        (data.fixedBinHeightRegion referenceHeight bin) height)) =
    ∫⁻ height in heights,
      volume (wz1Lemma23PlanarSlice fixedRegion height)
  have hheightsMeas : MeasurableSet heights :=
    measurableSet_pureWZ2SourceCommonBinPopularHeights data.sourceSet
      data.sourceSet_measurable data.slabLeft
        (Real.sqrt rhoRequested.1)
  rw [show (∫⁻ height : ℝ,
      volume (wz1Lemma23PlanarSlice
        (data.fixedBinHeightRegion referenceHeight bin) height)) =
      ∫⁻ height : ℝ, if height ∈ heights then
        volume (wz1Lemma23PlanarSlice fixedRegion height) else 0 by
      congr 1
      funext height
      rw [hslice height]
      split_ifs <;> simp]
  rw [← lintegral_indicator hheightsMeas]
  apply lintegral_congr
  intro height
  by_cases hheight : height ∈ heights <;> simp [hheight]

end PureWZ2AnchoredPreBinRhoHeightRegularizedData

namespace CommonBinIntegratedAveraging

/-- Finite averaging chooses one label from the very same retained label set.
This lemma is independent of the construction of slices and cells. -/
theorem exists_label_of_total_le_sum
    {ι : Type*} [DecidableEq ι]
    (labels : Finset ι) (weight : ι → ENNReal)
    (total factor : ENNReal) (htotal : 0 < total)
    (hretained : total ≤ factor * ∑ label ∈ labels, weight label) :
    ∃ label ∈ labels,
      total ≤ factor * (labels.card : ENNReal) * weight label := by
  have hnonempty : labels.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hretained
    simp only [Finset.sum_empty, mul_zero] at hretained
    exact (not_le_of_gt htotal) hretained
  rcases CommonBinDistinctIncidence.exists_weight_ge_average labels hnonempty
      (fun label : {label // label ∈ labels} => weight label.1) with
    ⟨selected, haverage⟩
  refine ⟨selected.1, selected.2, hretained.trans ?_⟩
  calc
    factor * ∑ label ∈ labels, weight label =
        factor * ∑ label : {label // label ∈ labels}, weight label.1 := by
      rw [Finset.sum_subtype labels (fun _ => Iff.rfl)]
    _ ≤ factor * ((labels.card : ENNReal) * weight selected.1) := by
      gcongr
    _ = factor * (labels.card : ENNReal) * weight selected.1 := by ring

/-- Algebraic cancellation behind the integrated graph lower bound. All
geometric work is exposed as named receipts, so anchored and legacy carriers
can share the same final argument. -/
theorem graph_lower_of_cross
    (fullSource sourceMass fullCoarse binMass coarseCellMass fineCellMass
      cubeVolume heightCost labelCount cellCount envelopeVolume : ENNReal)
    (K : ℕ)
    (hfullSource : fullSource ≤ heightCost * sourceMass)
    (hcross : fullSource * cubeVolume = fullCoarse * coarseCellMass)
    (hsourceAverage :
      sourceMass ≤ 4 * labelCount * binMass)
    (hincidence :
      labelCount * K * fineCellMass ≤ 5 * fullCoarse)
    (hbinUpper : binMass ≤ cellCount * coarseCellMass)
    (henvelope : envelopeVolume = cellCount * cubeVolume)
    (hfullCoarsePos : 0 < fullCoarse)
    (hfullCoarseTop : fullCoarse ≠ ⊤)
    (hcoarseCellMassPos : 0 < coarseCellMass)
    (hcoarseCellMassTop : coarseCellMass ≠ ⊤) :
    (K : ENNReal) * fineCellMass ≤
      20 * heightCost * envelopeVolume := by
  have hwithCellMass :
      coarseCellMass * ((K : ENNReal) * fineCellMass) ≤
        20 * heightCost * binMass * cubeVolume := by
    apply (ENNReal.mul_le_mul_iff_right
      hfullCoarsePos.ne' hfullCoarseTop).mp
    calc
      fullCoarse *
          (coarseCellMass * ((K : ENNReal) * fineCellMass)) =
        (fullSource * cubeVolume) *
          ((K : ENNReal) * fineCellMass) := by rw [hcross]; ring
      _ ≤ (heightCost * sourceMass * cubeVolume) *
          ((K : ENNReal) * fineCellMass) := by gcongr
      _ ≤ (heightCost * (4 * labelCount * binMass) * cubeVolume) *
          ((K : ENNReal) * fineCellMass) := by gcongr
      _ = 4 * heightCost * binMass * cubeVolume *
          (labelCount * K * fineCellMass) := by ring
      _ ≤ 4 * heightCost * binMass * cubeVolume *
          (5 * fullCoarse) := by gcongr
      _ = fullCoarse *
          (20 * heightCost * binMass * cubeVolume) := by ring
  apply (ENNReal.mul_le_mul_iff_right
    hcoarseCellMassPos.ne' hcoarseCellMassTop).mp
  calc
    coarseCellMass * ((K : ENNReal) * fineCellMass) ≤
        20 * heightCost * binMass * cubeVolume := hwithCellMass
    _ ≤ 20 * heightCost *
        (cellCount * coarseCellMass) * cubeVolume := by gcongr
    _ = coarseCellMass *
        (20 * heightCost * (cellCount * cubeVolume)) := by ring
    _ = coarseCellMass * (20 * heightCost * envelopeVolume) := by
      rw [henvelope]

end CommonBinIntegratedAveraging

namespace PureWZ2AnchoredPreBinRhoHeightRegularizedData

variable
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈
      selected.standardSqrtSlabIndices}}
    (data : PureWZ2AnchoredPreBinRhoHeightRegularizedData
      selected heightIndex)

/-- The finite `j_*` selector, factored away from the cross-height retention
proof. In particular it cannot silently change the pre-bin block. -/
theorem exists_integratedRichCommonBin_of_retention
    (referenceHeight : ℝ) (threshold : ENNReal)
    (hretained :
      volume data.sourceSet ≤
        4 * ∑ bin ∈ data.distinctRichCommonBinLabels
          referenceHeight threshold,
          data.integratedBinMass referenceHeight bin) :
    ∃ bin ∈ data.distinctRichCommonBinLabels referenceHeight threshold,
      volume data.sourceSet ≤
        4 * ((data.distinctRichCommonBinLabels
          referenceHeight threshold).card : ENNReal) *
          data.integratedBinMass referenceHeight bin := by
  exact CommonBinIntegratedAveraging.exists_label_of_total_le_sum
    (data.distinctRichCommonBinLabels referenceHeight threshold)
    (data.integratedBinMass referenceHeight) (volume data.sourceSet) 4
    data.sourceSet_volume_pos hretained

end PureWZ2AnchoredPreBinRhoHeightRegularizedData

structure PureWZ2AnchoredIntegratedEnvelopeReceipt
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈
      selected.standardSqrtSlabIndices}}
    (data : PureWZ2AnchoredPreBinRhoHeightRegularizedData
      selected heightIndex)
    (referenceHeight : ℝ) (bin : ℤ) where
  cells : Finset (ℤ × ℤ × ℤ) :=
    data.fixedBinRhoCells referenceHeight bin
  cells_eq : cells = data.fixedBinRhoCells referenceHeight bin
  cells_subset : cells ⊆ data.cells
  sourcePullback :
    PureWZ2AnchoredSelectedCellSourcePullback selected cells
  envelope_eq :
    data.fixedBinWholeCellEnvelope referenceHeight bin =
      wz2RetainedCellsUnion rhoRequested.1 cells
  envelope_volume :
    volume (data.fixedBinWholeCellEnvelope referenceHeight bin) =
      (cells.card : ENNReal) *
        volume (wz1PaperGridCube rhoRequested.1 (0, 0, 0))
  source_volume :
    volume sourcePullback.shading.union =
      (cells.card : ENNReal) * coarse.balanced.cellMass
  source_mass :
    sourcePullback.shading.mass =
      (cells.card : ENNReal) * coarse.balanced.incidenceMass
  source_mass_cross :
    sourcePullback.shading.mass *
        volume (wz1PaperGridCube rhoRequested.1 (0, 0, 0)) =
      volume (data.fixedBinWholeCellEnvelope referenceHeight bin) *
        coarse.balanced.incidenceMass

theorem PureWZ2AnchoredPreBinRhoHeightRegularizedData.integratedEnvelope
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈
      selected.standardSqrtSlabIndices}}
    (data : PureWZ2AnchoredPreBinRhoHeightRegularizedData
      selected heightIndex)
    (referenceHeight : ℝ) (bin : ℤ) :
    Nonempty
      (PureWZ2AnchoredIntegratedEnvelopeReceipt data referenceHeight bin) := by
  let cells := data.fixedBinRhoCells referenceHeight bin
  have hcells : cells ⊆ selected.selectedCells :=
    (data.fixedBinRhoCells_subset referenceHeight bin).trans
      data.cells_subset_selected
  rcases selected.restrictCells cells hcells with ⟨sourcePullback⟩
  have henvelope :
      data.fixedBinWholeCellEnvelope referenceHeight bin =
        wz2RetainedCellsUnion rhoRequested.1 cells := rfl
  have hvolume :
      volume (data.fixedBinWholeCellEnvelope referenceHeight bin) =
        (cells.card : ENNReal) *
          volume (wz1PaperGridCube rhoRequested.1 (0, 0, 0)) := by
    rw [henvelope]
    exact wz1PaperGridCube_volume_biUnion
      (source.extremal.delta_pos.trans_le rhoRequested.property.1) cells
  exact ⟨{
    cells := cells
    cells_eq := rfl
    cells_subset := data.fixedBinRhoCells_subset referenceHeight bin
    sourcePullback := sourcePullback
    envelope_eq := henvelope
    envelope_volume := hvolume
    source_volume := sourcePullback.volume_eq
    source_mass := sourcePullback.mass_eq
    source_mass_cross := by
      rw [sourcePullback.mass_eq, hvolume]
      ring
  }⟩

theorem PureWZ2AnchoredPreBinRhoHeightRegularizedData.fixedBinHeightRegion_volume_le
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈
      selected.standardSqrtSlabIndices}}
    (data : PureWZ2AnchoredPreBinRhoHeightRegularizedData
      selected heightIndex)
    (referenceHeight : ℝ) (bin : ℤ) :
    volume (data.fixedBinHeightRegion referenceHeight bin) ≤
      ((data.fixedBinRhoCells referenceHeight bin).card : ENNReal) *
        coarse.balanced.cellMass := by
  rcases data.integratedEnvelope referenceHeight bin with ⟨envelope⟩
  rw [← envelope.cells_eq, ← envelope.source_volume]
  apply measure_mono
  intro point hpoint
  have hsource : point ∈ data.sourcePullback.shading.union := hpoint.1.1
  rw [data.sourcePullback.union_eq] at hsource
  rw [envelope.sourcePullback.union_eq]
  refine ⟨hsource.1, ?_⟩
  rw [envelope.sourcePullback.region_eq, envelope.cells_eq]
  have henvelope :=
    data.fixedBinHeightRegion_subset_envelope referenceHeight bin hpoint
  rw [fixedBinWholeCellEnvelope, wz2RetainedCellsUnion] at henvelope
  exact henvelope

/-- Analytic selection layered on the independently constructed envelope.
No family identification is hidden in this interface. -/
structure PureWZ2AnchoredIntegratedCommonBinReceipt
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈
      selected.standardSqrtSlabIndices}}
    (data : PureWZ2AnchoredPreBinRhoHeightRegularizedData
      selected heightIndex)
    (B₀ threshold : ENNReal) (K : ℕ) where
  referenceHeight : ℝ
  referenceHeight_mem :
    referenceHeight ∈ data.popularHeights
  bin : ℤ
  bin_mem :
    bin ∈ data.distinctRichCommonBinLabels referenceHeight threshold
  envelope :
    PureWZ2AnchoredIntegratedEnvelopeReceipt data referenceHeight bin
  graph_lower :
    (K : ENNReal) * fine.balanced.cellMass ≤
      20 * (data.logarithmicCost : ENNReal) *
        volume (data.fixedBinWholeCellEnvelope referenceHeight bin)
  source_average :
    volume data.sourceSet ≤
      4 * ((data.distinctRichCommonBinLabels
        referenceHeight threshold).card : ENNReal) *
        data.integratedBinMass referenceHeight bin

theorem PureWZ2AnchoredPreBinRhoHeightRegularizedData.integratedCommonBin
    {sigma inputLoss delta coarseLoss fineLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {heightIndex : {heightIndex // heightIndex ∈
      selected.standardSqrtSlabIndices}}
    (data : PureWZ2AnchoredPreBinRhoHeightRegularizedData
      selected heightIndex)
    (B₀ threshold : ENNReal) (K : ℕ)
    (hB₀ : 264 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN (1 / Real.sqrt rhoRequested.1) (1 - sigma) ≤ B₀)
    (hthresholdBudget : 2 * B₀ * threshold ≤
      pureWZ2SourceCommonBinPopularThreshold data.sourceSet
        (Real.sqrt rhoRequested.1))
    (hK : (K : ENNReal) *
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
        sigma inputLoss delta rhoRequested.1 ≤ threshold) :
    Nonempty (PureWZ2AnchoredIntegratedCommonBinReceipt
      data B₀ threshold K) := by
  rcases data.exists_referenceHeight with
    ⟨referenceHeight, hreference, hreferenceRange⟩
  have hretained := data.distinctRichCommonBin_integratedMass
    referenceHeight hreference B₀ threshold hB₀ hthresholdBudget
  rcases data.exists_integratedRichCommonBin_of_retention
      referenceHeight threshold hretained with
    ⟨bin, hbin, hsourceAverage⟩
  rcases data.integratedEnvelope referenceHeight bin with ⟨envelope⟩
  let slabCells := selected.standardSqrtSlabRhoCells heightIndex.1
  let cubeVolume := volume
    (wz1PaperGridCube rhoRequested.1 (0, 0, 0))
  let fullSource : ENNReal :=
    (slabCells.card : ENNReal) * coarse.balanced.cellMass
  let fullCoarse := volume data.standardCoarseRegion
  have hfullSource :
      fullSource ≤ (data.logarithmicCost : ENNReal) *
        volume data.sourceSet := by
    rw [show volume data.sourceSet =
      (data.cells.card : ENNReal) * coarse.balanced.cellMass by
        exact data.source_volume]
    have hcard :
        (slabCells.card : ENNReal) ≤
          (data.logarithmicCost : ENNReal) *
            (data.cells.card : ENNReal) := by
      exact_mod_cast data.card_retention
    calc
      fullSource =
          (slabCells.card : ENNReal) * coarse.balanced.cellMass := rfl
      _ ≤ ((data.logarithmicCost : ENNReal) *
          (data.cells.card : ENNReal)) * coarse.balanced.cellMass := by
        gcongr
      _ = (data.logarithmicCost : ENNReal) *
          ((data.cells.card : ENNReal) * coarse.balanced.cellMass) := by ring
  have hcross :
      fullSource * cubeVolume =
        fullCoarse * coarse.balanced.cellMass := by
    rw [show fullCoarse =
      (slabCells.card : ENNReal) * cubeVolume by
        simpa [fullCoarse, slabCells, cubeVolume] using
          data.standardCoarseRegion_volume]
    simp only [fullSource]
    ring
  have hincidence :
      ((data.distinctRichCommonBinLabels
          referenceHeight threshold).card : ENNReal) *
          K * fine.balanced.cellMass ≤ 5 * fullCoarse := by
    have h := data.distinctRichCommonBin_incidence
      referenceHeight hreferenceRange threshold K hK
    rw [data.standardParentMass_eq_coarseVolume] at h
    exact h
  have hbinUpper :
      data.integratedBinMass referenceHeight bin ≤
        (envelope.cells.card : ENNReal) * coarse.balanced.cellMass := by
    rw [← data.fixedBinHeightRegion_volume referenceHeight bin,
      envelope.cells_eq]
    exact data.fixedBinHeightRegion_volume_le referenceHeight bin
  have hslabNonempty : slabCells.Nonempty :=
    selected.standardSqrtSlabRhoCells_nonempty heightIndex.2
  have hfullCoarsePos : 0 < fullCoarse := by
    rw [show fullCoarse =
      (slabCells.card : ENNReal) * cubeVolume by
        simpa [fullCoarse, slabCells, cubeVolume] using
          data.standardCoarseRegion_volume]
    exact ENNReal.mul_pos
      (by exact_mod_cast hslabNonempty.card_pos.ne')
      (wz1PaperGridCube_volume_pos coarse.coarse_extremal.delta_pos _).ne'
  have hfullCoarseTop : fullCoarse ≠ ⊤ := by
    rw [show fullCoarse =
      (slabCells.card : ENNReal) * cubeVolume by
        simpa [fullCoarse, slabCells, cubeVolume] using
          data.standardCoarseRegion_volume]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (wz1PaperGridCube_volume_ne_top coarse.coarse_extremal.delta_pos _)
  have hgraph := CommonBinIntegratedAveraging.graph_lower_of_cross
    fullSource (volume data.sourceSet) fullCoarse
    (data.integratedBinMass referenceHeight bin)
    coarse.balanced.cellMass fine.balanced.cellMass cubeVolume
    data.logarithmicCost
    (data.distinctRichCommonBinLabels referenceHeight threshold).card
    envelope.cells.card
    (volume (data.fixedBinWholeCellEnvelope referenceHeight bin)) K
    hfullSource hcross hsourceAverage hincidence hbinUpper
    (by simpa [cubeVolume] using envelope.envelope_volume)
    hfullCoarsePos hfullCoarseTop
    coarse.balanced.cellMass_pos coarse.balanced.cellMass_ne_top
  exact ⟨{
    referenceHeight := referenceHeight
    referenceHeight_mem := hreference
    bin := bin
    bin_mem := hbin
    envelope := envelope
    graph_lower := hgraph
    source_average := hsourceAverage
  }⟩

/-- One anchored standard-slab graph block. -/
abbrev PureWZ2AnchoredStandardSlabCommonBinGraphBlockData :=
  @PureWZ2AnchoredIntegratedCommonBinReceipt

/-- The graph family is indexed by the exact pre-bin family stored by the
scalar datum; no second pre-bin selection is possible. -/
structure PureWZ2AnchoredStandardSlabCommonBinGraphFamilyData
    {sigma inputLoss delta coarseLoss fineLoss volumeLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {preBin : PureWZ2AnchoredPreBinRhoHeightFamilyData selected}
    {B₀ : ENNReal}
    (scalar : PureWZ2AnchoredCommonBinScalarData
      (volumeLoss := volumeLoss) preBin B₀) where
  threshold :
    {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices} → ENNReal
  threshold_eq : ∀ heightIndex,
    threshold heightIndex =
      (scalar.K : ENNReal) *
        PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
          sigma inputLoss delta rhoRequested.1
  blockData : ∀ heightIndex,
    PureWZ2AnchoredIntegratedCommonBinReceipt
      (preBin.blockData heightIndex) B₀ (threshold heightIndex) scalar.K

namespace PureWZ2AnchoredStandardSlabCommonBinGraphFamilyData

def graphEnvelope
    {sigma inputLoss delta coarseLoss fineLoss volumeLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {coarseLogExponent : ℕ}
    {coarse : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := coarseLoss)
      source.shading rhoRequested coarseLogExponent}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {fineLogExponent : ℕ}
    {fine : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := fineLoss)
      coarse.croppedCoarseShading sqrtRequested fineLogExponent}
    {selected : PureWZ2AnchoredSourceRelativeFineSelection coarse fine}
    {preBin : PureWZ2AnchoredPreBinRhoHeightFamilyData selected}
    {B₀ : ENNReal}
    {scalar : PureWZ2AnchoredCommonBinScalarData
      (volumeLoss := volumeLoss) preBin B₀}
    (family : PureWZ2AnchoredStandardSlabCommonBinGraphFamilyData scalar)
    (heightIndex :
      {heightIndex // heightIndex ∈ selected.standardSqrtSlabIndices}) :
    Set Point3 :=
  let block := family.blockData heightIndex
  (preBin.blockData heightIndex).fixedBinWholeCellEnvelope
    block.referenceHeight block.bin

end PureWZ2AnchoredStandardSlabCommonBinGraphFamilyData

end Kakeya.Assouad

end
