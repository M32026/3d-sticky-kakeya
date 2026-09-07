import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinPreBinRhoHeightRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabIntegrated
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinWholeCellEnvelope

/-!
# Common-bin selection on a pre-bin height-regularized source slab

This is the paper-order version of the standard-slab common-bin argument.
The complete source side-`rho` height fibres are regularized first.  The
popular set, reference height, fixed common-bin label, and whole-cell graph
envelope are then all selected from that literal retained carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2StandardSlabPreBinRhoHeightRegularizedData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {heightIndex : {heightIndex // heightIndex ∈
      pullback.standardSqrtSlabIndices}}
    (data : PureWZ2StandardSlabPreBinRhoHeightRegularizedData
      pullback heightIndex)

/-- The literal original-source carrier after pre-bin height
regularization. -/
def sourceSet : Set Point3 := data.sourcePullback.shading.union

def slabLeft
    (_data : PureWZ2StandardSlabPreBinRhoHeightRegularizedData
      pullback heightIndex) : ℝ :=
  PureWZ2TwoScaleCellPullbackData.standardSqrtSlabLeft
    (rho := rho) heightIndex.1

def popularHeights : Set ℝ :=
  pureWZ2SourceCommonBinPopularHeights data.sourceSet data.slabLeft
    (Real.sqrt rho)

def distinctRichCommonBinLabels
    (referenceHeight : ℝ) (threshold : ENNReal) : Finset ℤ :=
  (pureWZ2OccupiedCommonBins data.sourceSet source.globalGrains.slope
      referenceHeight (Real.sqrt rho)).filter fun bin =>
    ∃ height,
      height ∈ data.popularHeights ∧
      height ∈ Set.Icc (-1 : ℝ) 1 ∧
      threshold ≤ pureWZ2FixedCommonBinSliceMass
        data.sourceSet source.globalGrains.slope referenceHeight
        (Real.sqrt rho) height bin

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
    (Real.sqrt rho)
    (Real.sqrt_pos.mpr <| by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.coarseGrains.extremal.delta_pos)
    (data.distinctRichCommonBinWitnessHeight referenceHeight threshold bin)
    bin

def integratedBinMass
    (referenceHeight : ℝ) (bin : ℤ) : ENNReal :=
  ∫⁻ height in data.popularHeights,
    pureWZ2FixedCommonBinSliceMass data.sourceSet
      source.globalGrains.slope referenceHeight (Real.sqrt rho) height bin

def fixedBinHeightRegion
    (referenceHeight : ℝ) (bin : ℤ) : Set Point3 :=
  pureWZ2FixedCommonBinRegion data.sourceSet source.globalGrains.slope
      referenceHeight (Real.sqrt rho) bin ∩
    {point | point (2 : Fin 3) ∈ data.popularHeights}

def fixedBinRhoCells
    (referenceHeight : ℝ) (bin : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  data.cells.filter fun cell =>
    (data.fixedBinHeightRegion referenceHeight bin ∩
      wz1PaperGridCube rho cell).Nonempty

def fixedBinWholeCellEnvelope
    (referenceHeight : ℝ) (bin : ℤ) : Set Point3 :=
  wz2RetainedCellsUnion rho (data.fixedBinRhoCells referenceHeight bin)

theorem fixedBinRhoCells_subset
    (referenceHeight : ℝ) (bin : ℤ) :
    data.fixedBinRhoCells referenceHeight bin ⊆ data.cells :=
  Finset.filter_subset _ _

theorem distinctRichCommonBinLabels_card_le
    (referenceHeight : ℝ) (threshold : ENNReal) :
    ((data.distinctRichCommonBinLabels referenceHeight threshold).card :
        ENNReal) ≤ ENNReal.ofReal (12 / Real.sqrt rho) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  let ambient : Finset ℤ := Finset.Icc
    (Int.floor ((-5 : ℝ) / Real.sqrt rho))
    (Int.floor ((5 : ℝ) / Real.sqrt rho))
  have hsubset : data.distinctRichCommonBinLabels
      referenceHeight threshold ⊆ ambient := by
    intro bin hbin
    have hoccupied := (Finset.mem_filter.mp hbin).1
    simpa [ambient, pureWZ2OccupiedCommonBins] using
      (Finset.mem_filter.mp hoccupied).1
  have hlowerUpper :
      Int.floor ((-5 : ℝ) / Real.sqrt rho) ≤
        Int.floor ((5 : ℝ) / Real.sqrt rho) + 1 := by
    have hreal : (-5 : ℝ) / Real.sqrt rho ≤ 5 / Real.sqrt rho :=
      div_le_div_of_nonneg_right (by norm_num) hroot.le
    have := Int.floor_mono hreal
    omega
  have hambientCard :
      (ambient.card : ℤ) = Int.floor ((5 : ℝ) / Real.sqrt rho) + 1 -
        Int.floor ((-5 : ℝ) / Real.sqrt rho) :=
    Int.card_Icc_of_le _ _ hlowerUpper
  have hcardReal :
      ((data.distinctRichCommonBinLabels referenceHeight threshold).card :
        ℝ) ≤ 12 / Real.sqrt rho := by
    have hcardAmbient :
        ((data.distinctRichCommonBinLabels referenceHeight threshold).card :
          ℝ) ≤ (ambient.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset
    have hupper := Int.floor_le ((5 : ℝ) / Real.sqrt rho)
    have hlower := Int.lt_floor_add_one ((-5 : ℝ) / Real.sqrt rho)
    have hambientReal :
        (ambient.card : ℝ) =
          (Int.floor ((5 : ℝ) / Real.sqrt rho) : ℝ) + 1 -
            (Int.floor ((-5 : ℝ) / Real.sqrt rho) : ℝ) := by
      exact_mod_cast hambientCard
    rw [hambientReal] at hcardAmbient
    have hrootOne : Real.sqrt rho ≤ 1 :=
      Real.sqrt_le_one.mpr <| by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.rhoRequested.property.2
    have htwo : 2 ≤ 2 / Real.sqrt rho :=
      (le_div_iff₀ hroot).2 (by nlinarith)
    calc
      _ ≤ (Int.floor ((5 : ℝ) / Real.sqrt rho) : ℝ) + 1 -
          (Int.floor ((-5 : ℝ) / Real.sqrt rho) : ℝ) := hcardAmbient
      _ ≤ 5 / Real.sqrt rho + 2 - ((-5 : ℝ) / Real.sqrt rho) := by
        linarith
      _ = 10 / Real.sqrt rho + 2 := by ring
      _ ≤ 12 / Real.sqrt rho := by
        rw [show 12 / Real.sqrt rho =
          10 / Real.sqrt rho + 2 / Real.sqrt rho by ring]
        gcongr
  have henn := ENNReal.ofReal_mono hcardReal
  simpa using henn

theorem sourceSet_measurable : MeasurableSet data.sourceSet :=
  measurableSet_shading_union data.sourcePullback.shading

theorem sourceSet_subset_standardSlab :
    data.sourceSet ⊆
      pullback.standardSqrtSlabSourceRegion heightIndex.1 := by
  intro point hpoint
  have hregion : point ∈ wz2RetainedCellsUnion rho data.cells := by
    have hpoint' := hpoint
    change point ∈ data.sourcePullback.shading.union at hpoint'
    rw [data.sourcePullback.union_eq] at hpoint'
    have hselected : point ∈ data.sourcePullback.selectedRegion := hpoint'.2
    rw [data.sourcePullback.selectedRegion_eq,
      data.sourcePullback_selectedCells] at hselected
    exact hselected
  have hsource : point ∈ pullback.shading.union := by
    rcases hpoint with ⟨sourceIndex, hsourceIndex⟩
    change point ∈ data.sourcePullback.shading.carrier sourceIndex at hsourceIndex
    rw [data.sourcePullback.carrier_eq] at hsourceIndex
    rcases data.sourcePullback.zeroExtension.carrier_support
        sourceIndex point hsourceIndex.1 with
      ⟨selectedIndex, heq, hselected⟩
    subst sourceIndex
    refine ⟨twoScale.coarse.selected.embedding selectedIndex, ?_⟩
    rw [pullback.carrier_eq, pullback.zeroExtension.carrier_embedding]
    refine ⟨hselected, ?_⟩
    rw [pullback.selectedRegion_eq]
    rcases Set.mem_iUnion₂.mp hregion with ⟨cell, hcell, hpointCell⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, data.cells_subset_selected hcell, hpointCell⟩
  refine ⟨hsource, ?_⟩
  rw [wz2RetainedCellsUnion] at hregion ⊢
  rcases Set.mem_iUnion₂.mp hregion with ⟨cell, hcell, hpointCell⟩
  exact Set.mem_iUnion₂.mpr
    ⟨cell, data.cells_subset_standard hcell, hpointCell⟩

theorem sourceSet_subset_source : data.sourceSet ⊆ source.shading.union := by
  intro point hpoint
  exact data.sourcePullback.subshading.union_subset hpoint

theorem sourceSet_height :
    ∀ point ∈ data.sourceSet,
      point (2 : Fin 3) ∈
        Set.Ico data.slabLeft (data.slabLeft + Real.sqrt rho) := by
  intro point hpoint
  simpa [slabLeft] using
    pullback.standardSqrtSlabSourceRegion_height heightIndex.1 point
      (data.sourceSet_subset_standardSlab hpoint)

theorem sourceSet_volume_pos : 0 < volume data.sourceSet := by
  change 0 < volume data.sourcePullback.shading.union
  rw [data.source_volume]
  exact ENNReal.mul_pos
    (by exact_mod_cast data.cells_nonempty.card_pos.ne')
    twoScale.coarse.balanced.cellMass_pos.ne'

theorem sourceSet_volume_ne_top : volume data.sourceSet ≠ ⊤ := by
  change volume data.sourcePullback.shading.union ≠ ⊤
  rw [data.source_volume]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    twoScale.coarse.balanced.cellMass_ne_top

theorem popularHalfMass :
    volume data.sourceSet / 2 ≤
      ∫⁻ z in data.popularHeights,
        pureWZ2SourceCommonBinSliceMass data.sourceSet z := by
  simpa [popularHeights] using
    pureWZ2SourceCommonBinPopularHalfMass data.sourceSet
      data.sourceSet_measurable data.sourceSet_volume_ne_top
      (Real.sqrt_pos.mpr <| by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.coarseGrains.extremal.delta_pos)
      data.sourceSet_height

theorem exists_referenceHeight :
    ∃ referenceHeight,
      referenceHeight ∈ data.popularHeights ∧
      referenceHeight ∈ Set.Icc (-1 : ℝ) 1 := by
  have hmassPos :
      0 < ∫⁻ z in data.popularHeights,
        pureWZ2SourceCommonBinSliceMass data.sourceSet z := by
    exact (ENNReal.div_pos data.sourceSet_volume_pos.ne' (by norm_num)).trans_le
      data.popularHalfMass
  have hpopular : data.popularHeights.Nonempty := by
    by_contra hempty
    have hempty' : data.popularHeights = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hempty
    rw [hempty'] at hmassPos
    simp at hmassPos
  let referenceHeight := Classical.choose hpopular
  have hreference : referenceHeight ∈ data.popularHeights :=
    Classical.choose_spec hpopular
  refine ⟨referenceHeight, hreference, ?_⟩
  have hthresholdPos :
      0 < pureWZ2SourceCommonBinPopularThreshold
        data.sourceSet (Real.sqrt rho) := by
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
    |first - second| ≤ Real.sqrt rho := by
  rw [abs_le]
  constructor <;>
    linarith [hfirst.1.1, hfirst.1.2, hsecond.1.1, hsecond.1.2]

theorem popularHeight_mem_paperRange
    {height : ℝ} (hheight : height ∈ data.popularHeights) :
    height ∈ Set.Icc (-1 : ℝ) 1 := by
  have hthresholdPos :
      0 < pureWZ2SourceCommonBinPopularThreshold
        data.sourceSet (Real.sqrt rho) := by
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
      (Real.sqrt rho) (1 - sigma)
      (2 * Kakeya.realRpowENN delta (-inputLoss)) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarse.coarse_extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrhoRoot : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho]
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
    (hdeltaRho.trans hrhoRoot) (Real.sqrt_le_one.mpr hrhoOne)

theorem commonBinSlice_occupiedBound
    (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rho) :
    ((pureWZ2OccupiedCommonBins
      (horizontalSlice data.sourceSet height) source.globalGrains.slope
      referenceHeight (Real.sqrt rho)).card : ENNReal) ≤
      264 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) := by
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hbound := pureWZ2_fixed_common_bin_occupied_bound
    (horizontalSlice data.sourceSet height) source.globalGrains.slope
    source.globalGrains.slope_lipschitz height referenceHeight hheight
    hreference hclose (data.slice_y_abs_le_one height)
    (data.slice_ad_root height hheight) (Real.sqrt_le_one.mpr hrhoOne)
  calc
    _ ≤ 132 * (2 * Kakeya.realRpowENN delta (-inputLoss)) *
        Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) := hbound
    _ = _ := by ring

private theorem fixedCommonBinLabel_mem_sliceOccupied
    (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rho)
    {point : Point3} (hpoint : point ∈ horizontalSlice data.sourceSet height) :
    pureWZ2FixedCommonBinLabel source.globalGrains.slope referenceHeight
        (Real.sqrt rho) point ∈
      pureWZ2OccupiedCommonBins (horizontalSlice data.sourceSet height)
        source.globalGrains.slope referenceHeight (Real.sqrt rho) := by
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  exact pureWZ2_fixed_common_bin_mem
    (horizontalSlice data.sourceSet height) source.globalGrains.slope
    source.globalGrains.slope_lipschitz height referenceHeight hheight
    hreference hclose (data.slice_y_abs_le_one height)
    (data.slice_ad_root height hheight) (Real.sqrt_le_one.mpr hrhoOne) hpoint

theorem commonBinSliceMass_sum
    (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rho) :
    pureWZ2SourceCommonBinSliceMass data.sourceSet height =
      ∑ bin ∈ pureWZ2OccupiedCommonBins
          (horizontalSlice data.sourceSet height) source.globalGrains.slope
          referenceHeight (Real.sqrt rho),
        pureWZ2FixedCommonBinSliceMass data.sourceSet
          source.globalGrains.slope referenceHeight
          (Real.sqrt rho) height bin := by
  simpa [pureWZ2SourceCommonBinSliceMass] using
    pureWZ2_fixed_common_bin_sliceMass_sum data.sourceSet_measurable
      source.globalGrains.slope referenceHeight (Real.sqrt rho) height
      (pureWZ2OccupiedCommonBins (horizontalSlice data.sourceSet height)
        source.globalGrains.slope referenceHeight (Real.sqrt rho))
      (fun point hpoint => data.fixedCommonBinLabel_mem_sliceOccupied
        referenceHeight height hreference hheight hclose hpoint)

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
    have h0sq : point 0 ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (point 0)]
    have h1sq : point 1 ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (point 1)]
    nlinarith [norm_nonneg point]
  exact ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
    (measure_mono hsliceBall)

theorem measurable_commonBinSliceMass
    (referenceHeight : ℝ) (bin : ℤ) :
    Measurable (fun height : ℝ =>
      pureWZ2FixedCommonBinSliceMass data.sourceSet source.globalGrains.slope
        referenceHeight (Real.sqrt rho) height bin) :=
  measurable_volume_wz1Lemma23PlanarSlice
    (pureWZ2FixedCommonBinRegion data.sourceSet source.globalGrains.slope
      referenceHeight (Real.sqrt rho) bin)
    (measurableSet_pureWZ2FixedCommonBinRegion data.sourceSet_measurable
      source.globalGrains.slope referenceHeight (Real.sqrt rho) bin)

theorem distinctRichCommonBinWitnessHeight_spec
    (referenceHeight : ℝ) (threshold : ENNReal) {bin : ℤ}
    (hbin : bin ∈ data.distinctRichCommonBinLabels referenceHeight threshold) :
    data.distinctRichCommonBinWitnessHeight referenceHeight threshold bin ∈
        data.popularHeights ∧
      data.distinctRichCommonBinWitnessHeight referenceHeight threshold bin ∈
        Set.Icc (-1 : ℝ) 1 ∧
      threshold ≤ pureWZ2FixedCommonBinSliceMass data.sourceSet
        source.globalGrains.slope referenceHeight (Real.sqrt rho)
        (data.distinctRichCommonBinWitnessHeight
          referenceHeight threshold bin) bin := by
  rw [distinctRichCommonBinWitnessHeight, dif_pos hbin]
  exact Classical.choose_spec (Finset.mem_filter.mp hbin).2

private theorem fixedCommonBinSpatialCellSliceMass_le
    (referenceHeight height : ℝ)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (bin : ℤ) (cell : ℤ × ℤ × ℤ) :
    pureWZ2FixedCommonBinSpatialCellSliceMass data.sourceSet
        source.globalGrains.slope referenceHeight (Real.sqrt rho) height
        bin cell ≤
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
        sigma inputLoss delta rho := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarse.coarse_extremal.delta_pos
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hrhoRoot : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho, hrhoOne]
  have hsubset :
      wz1Lemma23PlanarSlice
          (pureWZ2FixedCommonBinRegion data.sourceSet
              source.globalGrains.slope referenceHeight
              (Real.sqrt rho) bin ∩
            wz1PaperGridCube (Real.sqrt rho) cell) height ⊆
        wz1Lemma23PlanarSlice
          (source.shading.union ∩
            wz1PaperGridCube (Real.sqrt rho) cell) height := by
    intro point hpoint
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    apply wz1Lemma23_mem_planarSlice_iff.mpr
    exact ⟨data.sourceSet_subset_source hlift.1.1, hlift.2⟩
  calc
    _ ≤ volume (wz1Lemma23PlanarSlice
        (source.shading.union ∩ wz1PaperGridCube (Real.sqrt rho) cell)
        height) := measure_mono hsubset
    _ ≤ _ := by
      simpa [PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap]
        using source.sourceCommonBinSpatialCellSliceBound hrho
          (hdeltaRho.trans hrhoRoot) cell height hheight

theorem distinctRichCommonBin_activeSpatialCells_card_lower
    (referenceHeight : ℝ) (threshold : ENNReal) (K : ℕ)
    (hK : (K : ENNReal) *
        PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
          sigma inputLoss delta rho ≤ threshold)
    {bin : ℤ}
    (hbin : bin ∈ data.distinctRichCommonBinLabels
      referenceHeight threshold) :
    K ≤ (data.distinctRichCommonBinActiveSpatialCells
      referenceHeight threshold bin).card := by
  let height := data.distinctRichCommonBinWitnessHeight
    referenceHeight threshold bin
  have hwitness := data.distinctRichCommonBinWitnessHeight_spec
    referenceHeight threshold hbin
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarse.coarse_extremal.delta_pos
  apply CommonBinRichSelection.cell_card_lower_of_rich
    (data.distinctRichCommonBinActiveSpatialCells
      referenceHeight threshold bin)
    (pureWZ2FixedCommonBinSpatialCellSliceMass data.sourceSet
      source.globalGrains.slope referenceHeight (Real.sqrt rho) height bin)
    (pureWZ2FixedCommonBinSliceMass data.sourceSet source.globalGrains.slope
      referenceHeight (Real.sqrt rho) height bin) threshold
    (PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      sigma inputLoss delta rho) K
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
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hrho _)).ne'
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
          referenceHeight (Real.sqrt rho) cell := by
    intro bin hbin
    have hdata := Finset.mem_filter.mp hbin
    rw [distinctRichCommonBinActiveSpatialCells,
      pureWZ2FixedCommonBinActiveSpatialCells, Finset.mem_filter]
      at hdata
    rcases hdata.2.2 with ⟨point, hpoint⟩
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    rw [pureWZ2CommonBinsMeetingSpatialCell, Finset.mem_filter]
    exact ⟨hdata.1, point3 (point 0) (point 1)
      (data.distinctRichCommonBinWitnessHeight referenceHeight threshold bin),
      hlift.2, hlift.1.2⟩
  calc
    _ ≤ (pureWZ2CommonBinsMeetingSpatialCell bins source.globalGrains.slope
          referenceHeight (Real.sqrt rho) cell).card :=
      Finset.card_le_card hsubset
    _ ≤ 5 := commonBinsMeetingSpatialCell_card_le_five
      (Real.sqrt_pos.mpr <| by
        rw [← twoScale.rhoRequested_eq]
        exact twoScale.coarseGrains.extremal.delta_pos) bins
      source.globalGrains.slope referenceHeight
      (source.globalGrains.slope_bound referenceHeight hreference) cell

theorem distinctRichCommonBin_activeSpatialCells_subset_standardParents
    (referenceHeight : ℝ) (threshold : ENNReal) (bin : ℤ) :
    data.distinctRichCommonBinActiveSpatialCells referenceHeight threshold bin ⊆
      pullback.standardSqrtSlabParents heightIndex.1 := by
  intro cell hcell
  rw [distinctRichCommonBinActiveSpatialCells,
    pureWZ2FixedCommonBinActiveSpatialCells, Finset.mem_filter] at hcell
  rcases hcell.2 with ⟨point, hpoint⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
  have hsourcePoint : point3 (point 0) (point 1)
      (data.distinctRichCommonBinWitnessHeight referenceHeight threshold bin) ∈
        data.sourceSet := hlift.1.1
  have hstandard := data.sourceSet_subset_standardSlab hsourcePoint
  change _ ∈ pullback.shading.union ∩
    wz2RetainedCellsUnion rho
      (pullback.standardSqrtSlabRhoCells heightIndex.1) at hstandard
  rw [wz2RetainedCellsUnion] at hstandard
  rcases Set.mem_iUnion₂.mp hstandard.2 with
    ⟨rhoCell, hrhoCell, hpointRho⟩
  have hpointParent := pullback.standardSqrtSlabRhoCell_subset_parent
    hrhoCell hpointRho
  have hpointCell :
      point3 (point 0) (point 1)
        (data.distinctRichCommonBinWitnessHeight
          referenceHeight threshold bin) ∈
        wz1PaperGridCube twoScale.sqrtRequested.1 cell := by
    simpa only [twoScale.sqrtRequested_eq] using hlift.2
  have hparentEq : pullback.standardSecondParent rhoCell = cell :=
    ((mem_wz1PaperGridCube twoScale.sqrtRequested.1
      (pullback.standardSecondParent rhoCell) _).mp hpointParent).symm.trans
      ((mem_wz1PaperGridCube twoScale.sqrtRequested.1 cell _).mp hpointCell)
  exact Finset.mem_image.mpr ⟨rhoCell, hrhoCell, hparentEq⟩

theorem distinctRichCommonBin_incidence
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (threshold : ENNReal) (K : ℕ)
    (hK : (K : ENNReal) *
        PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
          sigma inputLoss delta rho ≤ threshold) :
    ((data.distinctRichCommonBinLabels referenceHeight threshold).card :
        ENNReal) * K * twoScale.fine.balanced.cellMass ≤
      5 * volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1) := by
  let bins := data.distinctRichCommonBinLabels referenceHeight threshold
  let cells : ℤ → Finset (ℤ × ℤ × ℤ) := fun bin =>
    data.distinctRichCommonBinActiveSpatialCells referenceHeight threshold bin
  apply CommonBinDistinctIncidence.card_mul_cellMass_le_degree_mul_totalMass
    bins cells K 5 twoScale.fine.balanced.cellMass
      (volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1))
  · intro bin hbin
    exact data.distinctRichCommonBin_activeSpatialCells_card_lower
      referenceHeight threshold K hK hbin
  · intro cell _
    simpa [bins, cells] using data.distinctRichCommonBin_cellDegree_le_five
      referenceHeight hreference threshold cell
  · have hsubset :
        (@Finset.biUnion ℤ (ℤ × ℤ × ℤ)
          (fun first second => Classical.propDecidable (first = second))
          bins cells) ⊆ pullback.standardSqrtSlabParents heightIndex.1 := by
      intro cell hcell
      rcases
          (@Finset.mem_biUnion ℤ (ℤ × ℤ × ℤ)
            bins cells
            (fun first second =>
              Classical.propDecidable (first = second))
            cell).mp hcell
        with ⟨bin, _hbin, hcell⟩
      exact data.distinctRichCommonBin_activeSpatialCells_subset_standardParents
        referenceHeight threshold bin hcell
    have hcard :
        ((@Finset.biUnion ℤ (ℤ × ℤ × ℤ)
          (fun first second => Classical.propDecidable (first = second))
          bins cells).card : ENNReal) ≤
        (pullback.standardSqrtSlabParents heightIndex.1).card := by
      exact_mod_cast Finset.card_le_card hsubset
    calc
      _ ≤ ((pullback.standardSqrtSlabParents heightIndex.1).card : ENNReal) *
          twoScale.fine.balanced.cellMass := by gcongr
      _ = volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1) :=
        pullback.standardSqrtSlab_parentMass_eq_coarseVolume heightIndex.1

theorem distinctRichCommonBin_integratedMass
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ data.popularHeights)
    (B₀ threshold : ENNReal)
    (hB₀ : 264 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold data.sourceSet
          (Real.sqrt rho)) :
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
      referenceHeight (Real.sqrt rho) height bin
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
      referenceHeight (Real.sqrt rho)
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
            (Real.sqrt rho) := hthresholdBudget
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
          source.globalGrains.slope referenceHeight (Real.sqrt rho) := by
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
      data.sourceSet_measurable data.slabLeft (Real.sqrt rho)
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
    volume data.sourceSet = volume data.sourceSet / 2 +
        volume data.sourceSet / 2 := (ENNReal.add_halves _).symm
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

theorem distinctRichCommonBinLabels_nonempty
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ data.popularHeights)
    (B₀ threshold : ENNReal)
    (hB₀ : 264 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget : 2 * B₀ * threshold ≤
      pureWZ2SourceCommonBinPopularThreshold data.sourceSet
        (Real.sqrt rho)) :
    (data.distinctRichCommonBinLabels referenceHeight threshold).Nonempty := by
  by_contra hempty
  have hempty' : data.distinctRichCommonBinLabels
      referenceHeight threshold = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  have hmass := data.distinctRichCommonBin_integratedMass referenceHeight
    hreference B₀ threshold hB₀ hthresholdBudget
  rw [hempty'] at hmass
  simp only [Finset.sum_empty, mul_zero] at hmass
  exact (not_le_of_gt data.sourceSet_volume_pos) hmass

theorem exists_integratedRichCommonBin
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ data.popularHeights)
    (B₀ threshold : ENNReal)
    (hB₀ : 264 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget : 2 * B₀ * threshold ≤
      pureWZ2SourceCommonBinPopularThreshold data.sourceSet
        (Real.sqrt rho)) :
    ∃ bin ∈ data.distinctRichCommonBinLabels referenceHeight threshold,
      volume data.sourceSet ≤
        4 * ((data.distinctRichCommonBinLabels
          referenceHeight threshold).card : ENNReal) *
          data.integratedBinMass referenceHeight bin := by
  let bins := data.distinctRichCommonBinLabels referenceHeight threshold
  have hnonempty := data.distinctRichCommonBinLabels_nonempty
    referenceHeight hreference B₀ threshold hB₀ hthresholdBudget
  have hrich := data.distinctRichCommonBin_integratedMass referenceHeight
    hreference B₀ threshold hB₀ hthresholdBudget
  rcases CommonBinDistinctIncidence.exists_weight_ge_average bins hnonempty
      (fun bin : {bin // bin ∈ bins} =>
        data.integratedBinMass referenceHeight bin.1) with
    ⟨selected, haverage⟩
  refine ⟨selected.1, selected.2, ?_⟩
  calc
    volume data.sourceSet ≤ 4 * ∑ bin ∈ bins,
        data.integratedBinMass referenceHeight bin := by
      simpa [bins] using hrich
    _ = 4 * ∑ bin : {bin // bin ∈ bins},
        data.integratedBinMass referenceHeight bin.1 := by
      rw [Finset.sum_subtype bins (fun _ => Iff.rfl)]
    _ ≤ 4 * ((bins.card : ENNReal) *
        data.integratedBinMass referenceHeight selected.1) := by gcongr
    _ = _ := by simp only [bins]; ring

theorem fixedBinHeightRegion_volume
    (referenceHeight : ℝ) (bin : ℤ) :
    volume (data.fixedBinHeightRegion referenceHeight bin) =
      data.integratedBinMass referenceHeight bin := by
  let E := data.sourceSet
  let heights := data.popularHeights
  let fixedRegion := pureWZ2FixedCommonBinRegion E
    source.globalGrains.slope referenceHeight (Real.sqrt rho) bin
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
      source.globalGrains.slope referenceHeight (Real.sqrt rho) bin).inter
      ((measurableSet_pureWZ2SourceCommonBinPopularHeights data.sourceSet
        data.sourceSet_measurable data.slabLeft (Real.sqrt rho)).preimage
        (by fun_prop))
  rw [wz1_lemma23_volume_eq_lintegral_planarSlice _ hmeas]
  change (∫⁻ height : ℝ,
      volume (wz1Lemma23PlanarSlice
        (data.fixedBinHeightRegion referenceHeight bin) height)) =
    ∫⁻ height in heights,
      volume (wz1Lemma23PlanarSlice fixedRegion height)
  have hheightsMeas : MeasurableSet heights :=
    measurableSet_pureWZ2SourceCommonBinPopularHeights data.sourceSet
      data.sourceSet_measurable data.slabLeft (Real.sqrt rho)
  calc
    (∫⁻ height : ℝ, volume (wz1Lemma23PlanarSlice
        (data.fixedBinHeightRegion referenceHeight bin) height)) =
        ∫⁻ height : ℝ, Set.indicator heights
          (fun z => volume (wz1Lemma23PlanarSlice fixedRegion z)) height := by
      apply lintegral_congr
      intro height
      rw [hslice height]
      by_cases hheight : height ∈ heights <;> simp [hheight]
    _ = ∫⁻ height in heights,
        volume (wz1Lemma23PlanarSlice fixedRegion height) :=
      lintegral_indicator hheightsMeas _

theorem fixedBinHeightRegion_volume_le
    (referenceHeight : ℝ) (bin : ℤ) :
    volume (data.fixedBinHeightRegion referenceHeight bin) ≤
      ((data.fixedBinRhoCells referenceHeight bin).card : ENNReal) *
        twoScale.coarse.balanced.cellMass := by
  let region := data.fixedBinHeightRegion referenceHeight bin
  let cells := data.fixedBinRhoCells referenceHeight bin
  have hpartition : region = ⋃ cell ∈ cells,
      region ∩ wz1PaperGridCube rho cell := by
    ext point
    constructor
    · intro hpoint
      have hsource : point ∈ data.sourceSet := hpoint.1.1
      have hsource' := hsource
      change point ∈ data.sourcePullback.shading.union at hsource'
      rw [data.sourcePullback.union_eq] at hsource'
      have hselected : point ∈ data.sourcePullback.selectedRegion :=
        hsource'.2
      rw [data.sourcePullback.selectedRegion_eq,
        data.sourcePullback_selectedCells] at hselected
      rcases Set.mem_iUnion₂.mp hselected with
        ⟨cell, hcell, hpointCell⟩
      exact Set.mem_iUnion₂.mpr ⟨cell, Finset.mem_filter.mpr
        ⟨hcell, ⟨point, hpoint, hpointCell⟩⟩, hpoint, hpointCell⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with ⟨_cell, _hcell, hregion, _⟩
      exact hregion
  change volume region ≤
    (cells.card : ENNReal) * twoScale.coarse.balanced.cellMass
  rw [hpartition]
  have hdisjoint : (cells : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint
      (fun cell => region ∩ wz1PaperGridCube rho cell) := by
    intro first _ second _ hne
    exact (wz1PaperGridCube_disjoint hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeas : ∀ cell ∈ cells,
      MeasurableSet (region ∩ wz1PaperGridCube rho cell) := by
    intro cell _
    exact (measurableSet_pureWZ2FixedCommonBinRegion
      data.sourceSet_measurable source.globalGrains.slope referenceHeight
      (Real.sqrt rho) bin |>.inter
        ((measurableSet_pureWZ2SourceCommonBinPopularHeights data.sourceSet
          data.sourceSet_measurable data.slabLeft (Real.sqrt rho)).preimage
          (by fun_prop))).inter (wz1PaperGridCube_measurable cell)
  rw [MeasureTheory.measure_biUnion_finset hdisjoint hmeas]
  calc
    _ ≤ ∑ _cell ∈ cells, twoScale.coarse.balanced.cellMass := by
      apply Finset.sum_le_sum
      intro cell hcell
      have hcellData := Finset.mem_filter.mp hcell
      calc
        volume (region ∩ wz1PaperGridCube rho cell) ≤
            volume (pullback.shading.union ∩
              wz1PaperGridCube rho cell) := by
          apply measure_mono
          rintro point ⟨hpointRegion, hpointCell⟩
          exact ⟨(data.sourceSet_subset_standardSlab hpointRegion.1.1).1,
            hpointCell⟩
        _ = twoScale.coarse.balanced.cellMass :=
          pullback.cell_mass cell
            (data.cells_subset_selected hcellData.1)
    _ = _ := by simp [Finset.sum_const]

theorem fixedBinHeightRegion_subset_envelope
    (referenceHeight : ℝ) (bin : ℤ) :
    data.fixedBinHeightRegion referenceHeight bin ⊆
      data.fixedBinWholeCellEnvelope referenceHeight bin := by
  intro point hpoint
  have hsource : point ∈ data.sourceSet := hpoint.1.1
  have hsource' := hsource
  change point ∈ data.sourcePullback.shading.union at hsource'
  rw [data.sourcePullback.union_eq, data.sourcePullback.selectedRegion_eq,
    data.sourcePullback_selectedCells] at hsource'
  rcases Set.mem_iUnion₂.mp hsource'.2 with
    ⟨cell, hcell, hpointCell⟩
  unfold fixedBinWholeCellEnvelope wz2RetainedCellsUnion
  exact Set.mem_iUnion₂.mpr ⟨cell, Finset.mem_filter.mpr
    ⟨hcell, ⟨point, hpoint, hpointCell⟩⟩, hpointCell⟩

/-- Complete cells meeting the pre-bin fixed-label region remain in the
enlarged fixed strip and in the rho-thickening of the same popular-height
set. -/
theorem fixedBinWholeCellEnvelope_subset_strip_height
    (referenceHeight : ℝ) (bin : ℤ) :
    data.fixedBinWholeCellEnvelope referenceHeight bin ⊆
      pureWZ2FixedCommonBinWholeCellStrip source.globalGrains.slope
          referenceHeight (Real.sqrt rho) (4 * rho) bin ∩
        pureWZ2WholeCellHeightThickening rho data.popularHeights := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarse.coarse_extremal.delta_pos
  have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  intro point hpoint
  unfold fixedBinWholeCellEnvelope wz2RetainedCellsUnion at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with
    ⟨cell, hcell, hpointCell⟩
  have hcellMeet := (Finset.mem_filter.mp hcell).2
  rcases hcellMeet with
    ⟨sourcePoint, hsourcePoint, hsourcePointCell⟩
  have hpointBox := hpointCell
  have hsourcePointBox := hsourcePointCell
  rw [wz1PaperGridCube_eq_Ico hrho cell] at hpointBox hsourcePointBox
  have hcoord0 : |point 0 - sourcePoint 0| ≤ rho := by
    rw [abs_le]
    constructor <;>
      linarith [hpointBox.1, hpointBox.2.1,
        hsourcePointBox.1, hsourcePointBox.2.1]
  have hcoord1 : |point 1 - sourcePoint 1| ≤ rho := by
    rw [abs_le]
    constructor <;>
      linarith [hpointBox.2.2.1, hpointBox.2.2.2.1,
        hsourcePointBox.2.2.1, hsourcePointBox.2.2.2.1]
  have hcoord2 : |point 2 - sourcePoint 2| ≤ rho := by
    rw [abs_le]
    constructor <;>
      linarith [hpointBox.2.2.2.2.1, hpointBox.2.2.2.2.2,
        hsourcePointBox.2.2.2.2.1, hsourcePointBox.2.2.2.2.2]
  let direction :=
    globalGrainDirection (source.globalGrains.slope referenceHeight)
  have hslope : |source.globalGrains.slope referenceHeight| ≤ 3 :=
    source.globalGrains.slope_global_bound referenceHeight
  have hinner :
      |inner ℝ point direction - inner ℝ sourcePoint direction| ≤
        4 * rho := by
    have hformula :
        inner ℝ point direction - inner ℝ sourcePoint direction =
          (point 0 - sourcePoint 0) +
            source.globalGrains.slope referenceHeight *
              (point 1 - sourcePoint 1) := by
      simp [direction, globalGrainDirection, PiLp.inner_apply,
        Fin.sum_univ_succ]
      ring
    rw [hformula]
    calc
      |(point 0 - sourcePoint 0) +
          source.globalGrains.slope referenceHeight *
            (point 1 - sourcePoint 1)| ≤
        |point 0 - sourcePoint 0| +
          |source.globalGrains.slope referenceHeight| *
            |point 1 - sourcePoint 1| := by
        simpa [abs_mul] using abs_add_le (point 0 - sourcePoint 0)
          (source.globalGrains.slope referenceHeight *
            (point 1 - sourcePoint 1))
      _ ≤ rho + 3 * rho := by gcongr
      _ = 4 * rho := by ring
  have hlabel : pureWZ2FixedCommonBinLabel source.globalGrains.slope
      referenceHeight (Real.sqrt rho) sourcePoint = bin :=
    hsourcePoint.1.2
  have hlabelBounds :
      (bin : ℝ) * Real.sqrt rho ≤ inner ℝ sourcePoint direction ∧
        inner ℝ sourcePoint direction <
          ((bin : ℝ) + 1) * Real.sqrt rho := by
    unfold pureWZ2FixedCommonBinLabel at hlabel
    rw [Int.floor_eq_iff] at hlabel
    constructor
    · exact (le_div_iff₀ hroot).mp hlabel.1
    · exact (div_lt_iff₀ hroot).mp hlabel.2
  constructor
  · change
      (bin : ℝ) * Real.sqrt rho - 4 * rho ≤ inner ℝ point direction ∧
        inner ℝ point direction <
          ((bin : ℝ) + 1) * Real.sqrt rho + 4 * rho
    rw [abs_le] at hinner
    constructor <;> linarith [hlabelBounds.1, hlabelBounds.2]
  · exact ⟨sourcePoint 2, hsourcePoint.2, hcoord2⟩

theorem fixedBinWholeCellEnvelope_volume
    (referenceHeight : ℝ) (bin : ℤ) :
    volume (data.fixedBinWholeCellEnvelope referenceHeight bin) =
      ((data.fixedBinRhoCells referenceHeight bin).card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  exact wz1PaperGridCube_volume_biUnion
    (by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.coarseGrains.extremal.delta_pos) _

/-- The integrated selector on the pre-bin carrier.  The only extra factor
compared with the old full-slab formula is the already-recorded logarithmic
height regularization cost. -/
theorem exists_integratedRichCommonBin_graphEnvelope
    (B₀ threshold : ENNReal) (K : ℕ)
    (hB₀ : 264 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget : 2 * B₀ * threshold ≤
      pureWZ2SourceCommonBinPopularThreshold data.sourceSet
        (Real.sqrt rho))
    (hK : (K : ENNReal) *
        PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
          sigma inputLoss delta rho ≤ threshold) :
    ∃ referenceHeight, referenceHeight ∈ data.popularHeights ∧
      ∃ bin ∈ data.distinctRichCommonBinLabels referenceHeight threshold,
        (K : ENNReal) * twoScale.fine.balanced.cellMass ≤
          20 * (data.logarithmicCost : ENNReal) *
            volume (data.fixedBinWholeCellEnvelope referenceHeight bin) ∧
        volume data.sourceSet ≤
          4 * ((data.distinctRichCommonBinLabels
            referenceHeight threshold).card : ENNReal) *
            data.integratedBinMass referenceHeight bin := by
  rcases data.exists_referenceHeight with
    ⟨referenceHeight, hreference, hreferenceRange⟩
  rcases data.exists_integratedRichCommonBin referenceHeight hreference
      B₀ threshold hB₀ hthresholdBudget with
    ⟨bin, hbin, hsourceAverage⟩
  have hincidence := data.distinctRichCommonBin_incidence referenceHeight
    hreferenceRange threshold K hK
  let fullSource := volume
    (pullback.standardSqrtSlabSourceRegion heightIndex.1)
  let sourceMass := volume data.sourceSet
  let fullCoarse := volume
    (pullback.standardSqrtSlabCoarseRegion heightIndex.1)
  let binMass := data.integratedBinMass referenceHeight bin
  let cellMass := twoScale.coarse.balanced.cellMass
  let cubeVolume := volume (wz1PaperGridCube rho (0, 0, 0))
  let heightCost : ENNReal := data.logarithmicCost
  have hfullSource : fullSource ≤ heightCost * sourceMass := by
    simpa [fullSource, sourceMass, heightCost, sourceSet] using
      data.sourceVolume_retention
  have hcross : fullSource * cubeVolume = fullCoarse * cellMass := by
    simpa [fullSource, fullCoarse, cellMass, cubeVolume] using
      pullback.standardSqrtSlab_source_coarse_cross heightIndex.1
  have hfullCoarsePos : 0 < fullCoarse := by
    rw [show fullCoarse = volume
      (pullback.standardSqrtSlabCoarseRegion heightIndex.1) by rfl,
      pullback.standardSqrtSlabCoarseRegion_volume]
    exact ENNReal.mul_pos
      (by exact_mod_cast
        (pullback.standardSqrtSlabRhoCells_nonempty heightIndex.2).card_pos.ne')
      (wz1PaperGridCube_volume_pos
        (by
          rw [← twoScale.rhoRequested_eq]
          exact twoScale.coarseGrains.extremal.delta_pos)
        (0, 0, 0)).ne'
  have hfullCoarseTop : fullCoarse ≠ ⊤ := by
    rw [show fullCoarse = volume
      (pullback.standardSqrtSlabCoarseRegion heightIndex.1) by rfl,
      pullback.standardSqrtSlabCoarseRegion_volume]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (wz1PaperGridCube_volume_ne_top
        (by
          rw [← twoScale.rhoRequested_eq]
          exact twoScale.coarseGrains.extremal.delta_pos)
        (0, 0, 0))
  have hwithCellMass :
      cellMass * ((K : ENNReal) * twoScale.fine.balanced.cellMass) ≤
        20 * heightCost * binMass * cubeVolume := by
    apply (ENNReal.mul_le_mul_iff_right
      hfullCoarsePos.ne' hfullCoarseTop).mp
    calc
      fullCoarse * (cellMass *
          ((K : ENNReal) * twoScale.fine.balanced.cellMass)) =
        (fullSource * cubeVolume) *
          ((K : ENNReal) * twoScale.fine.balanced.cellMass) := by
        rw [hcross]
        ring
      _ ≤ (heightCost * sourceMass * cubeVolume) *
          ((K : ENNReal) * twoScale.fine.balanced.cellMass) := by gcongr
      _ ≤ (heightCost *
          (4 * ((data.distinctRichCommonBinLabels
            referenceHeight threshold).card : ENNReal) * binMass) *
          cubeVolume) *
          ((K : ENNReal) * twoScale.fine.balanced.cellMass) := by gcongr
      _ = 4 * heightCost * binMass * cubeVolume *
          (((data.distinctRichCommonBinLabels
            referenceHeight threshold).card : ENNReal) * K *
              twoScale.fine.balanced.cellMass) := by ring
      _ ≤ 4 * heightCost * binMass * cubeVolume *
          (5 * fullCoarse) := by gcongr
      _ = fullCoarse * (20 * heightCost * binMass * cubeVolume) := by ring
  have hbinUpper :
      binMass ≤ ((data.fixedBinRhoCells referenceHeight bin).card : ENNReal) *
        cellMass := by
    change data.integratedBinMass referenceHeight bin ≤ _
    rw [← data.fixedBinHeightRegion_volume referenceHeight bin]
    exact data.fixedBinHeightRegion_volume_le referenceHeight bin
  have hcellMassPos : 0 < cellMass :=
    twoScale.coarse.balanced.cellMass_pos
  have hcellMassTop : cellMass ≠ ⊤ :=
    twoScale.coarse.balanced.cellMass_ne_top
  refine ⟨referenceHeight, hreference, bin, hbin, ?_, hsourceAverage⟩
  apply (ENNReal.mul_le_mul_iff_right
    hcellMassPos.ne' hcellMassTop).mp
  calc
    cellMass * ((K : ENNReal) * twoScale.fine.balanced.cellMass) ≤
        20 * heightCost * binMass * cubeVolume := hwithCellMass
    _ ≤ 20 * heightCost *
        (((data.fixedBinRhoCells referenceHeight bin).card : ENNReal) *
          cellMass) * cubeVolume := by gcongr
    _ = cellMass * (20 * heightCost *
        (((data.fixedBinRhoCells referenceHeight bin).card : ENNReal) *
          cubeVolume)) := by ring
    _ = cellMass * (20 * heightCost *
        volume (data.fixedBinWholeCellEnvelope referenceHeight bin)) := by
      rw [data.fixedBinWholeCellEnvelope_volume]

end PureWZ2StandardSlabPreBinRhoHeightRegularizedData

end Kakeya.Assouad

end
