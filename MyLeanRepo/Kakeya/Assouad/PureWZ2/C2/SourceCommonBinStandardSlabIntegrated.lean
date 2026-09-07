import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabPopular
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinRichSpatialCells
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinSpatialCellIncidence
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CommonBinDistinctIncidence

/-!
# Integrated rich common bins on an unshifted standard slab

The common-bin averaging in this module is performed directly on
`standardSqrtSlabSourceRegion heightIndex`.  The reference height, fixed
labels, rich-label witnesses, spatial cells, and integrated masses therefore
all belong to the same literal unshifted standard slab.

The participating side-`sqrt rho` cells are proved to be members of
`standardSqrtSlabParents heightIndex`.  Thus their distinct-label incidence
is bounded by the full standard-slab parent mass `G_S`, and the final
fixed-bin estimate uses the exact standard-slab source/coarse cross identity.
No source-carrier window, shifted safe window, graph budget, or joint-density
hypothesis is used.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2TwoScaleCellPullbackData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)

/-- Distinct fixed common-bin labels which are rich at some popular height
of one literal standard source slab. -/
def standardSqrtSlabDistinctRichCommonBinLabels
    (heightIndex : ℤ) (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) : Finset ℤ :=
  (pureWZ2OccupiedCommonBins
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      source.globalGrains.slope referenceHeight (Real.sqrt rho)).filter
    fun bin =>
      ∃ height,
        height ∈ heights ∧
        height ∈ Set.Icc (-1 : ℝ) 1 ∧
        threshold ≤
          pureWZ2FixedCommonBinSliceMass
            (pullback.standardSqrtSlabSourceRegion heightIndex)
            source.globalGrains.slope referenceHeight
            (Real.sqrt rho) height bin

/-- The cross-height rich labels lie in the fixed ambient `u_*` grid.  This
is the geometric `O(rho⁻¹/²)` count; unlike the slice-wise `B₀` estimate it
does not invoke AD regularity. -/
theorem standardSqrtSlabDistinctRichCommonBinLabels_card_le
    (heightIndex : ℤ) (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) :
    ((pullback.standardSqrtSlabDistinctRichCommonBinLabels
      heightIndex referenceHeight heights threshold).card : ENNReal) ≤
      ENNReal.ofReal (12 / Real.sqrt rho) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  let ambient : Finset ℤ :=
    Finset.Icc
      (Int.floor ((-5 : ℝ) / Real.sqrt rho))
      (Int.floor ((5 : ℝ) / Real.sqrt rho))
  have hsubset :
      pullback.standardSqrtSlabDistinctRichCommonBinLabels
          heightIndex referenceHeight heights threshold ⊆ ambient := by
    intro bin hbin
    have hoccupied :
        bin ∈ pureWZ2OccupiedCommonBins
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          source.globalGrains.slope referenceHeight (Real.sqrt rho) :=
      (Finset.mem_filter.mp hbin).1
    simpa [ambient, pureWZ2OccupiedCommonBins] using
      (Finset.mem_filter.mp hoccupied).1
  have hlowerUpper :
      Int.floor ((-5 : ℝ) / Real.sqrt rho) ≤
        Int.floor ((5 : ℝ) / Real.sqrt rho) + 1 := by
    have hreal : (-5 : ℝ) / Real.sqrt rho ≤ 5 / Real.sqrt rho := by
      exact div_le_div_of_nonneg_right (by norm_num) hroot.le
    have := Int.floor_mono hreal
    omega
  have hambientCard :
      (ambient.card : ℤ) =
        Int.floor ((5 : ℝ) / Real.sqrt rho) + 1 -
          Int.floor ((-5 : ℝ) / Real.sqrt rho) := by
    exact Int.card_Icc_of_le _ _ hlowerUpper
  have hcardReal :
      ((pullback.standardSqrtSlabDistinctRichCommonBinLabels
          heightIndex referenceHeight heights threshold).card : ℝ) ≤
        12 / Real.sqrt rho := by
    have hcardNat := Finset.card_le_card hsubset
    have hcardAmbient :
        ((pullback.standardSqrtSlabDistinctRichCommonBinLabels
            heightIndex referenceHeight heights threshold).card : ℝ) ≤
          (ambient.card : ℝ) := by
      exact_mod_cast hcardNat
    have hupper :
        (Int.floor ((5 : ℝ) / Real.sqrt rho) : ℝ) ≤
          5 / Real.sqrt rho := Int.floor_le _
    have hlower :
        (-5 : ℝ) / Real.sqrt rho <
          (Int.floor ((-5 : ℝ) / Real.sqrt rho) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hambientReal :
        (ambient.card : ℝ) =
          (Int.floor ((5 : ℝ) / Real.sqrt rho) : ℝ) + 1 -
            (Int.floor ((-5 : ℝ) / Real.sqrt rho) : ℝ) := by
      exact_mod_cast hambientCard
    rw [hambientReal] at hcardAmbient
    have hten :
        5 / Real.sqrt rho - ((-5 : ℝ) / Real.sqrt rho) =
          10 / Real.sqrt rho := by ring
    have htwo : 2 ≤ 2 / Real.sqrt rho := by
      have hrootOne : Real.sqrt rho ≤ 1 :=
        Real.sqrt_le_one.mpr <| by
          rw [← twoScale.rhoRequested_eq]
          exact twoScale.rhoRequested.property.2
      exact (le_div_iff₀ hroot).2 (by nlinarith)
    calc
      _ ≤ (Int.floor ((5 : ℝ) / Real.sqrt rho) : ℝ) + 1 -
          (Int.floor ((-5 : ℝ) / Real.sqrt rho) : ℝ) := hcardAmbient
      _ ≤ 5 / Real.sqrt rho + 2 - ((-5 : ℝ) / Real.sqrt rho) := by
        linarith
      _ = 10 / Real.sqrt rho + 2 := by rw [← hten]; ring
      _ ≤ 12 / Real.sqrt rho := by
        rw [show 12 / Real.sqrt rho =
          10 / Real.sqrt rho + 2 / Real.sqrt rho by ring]
        gcongr
  have henn := ENNReal.ofReal_mono hcardReal
  simpa using henn

/-- A witnessing rich height for one distinct standard-slab label. -/
def standardSqrtSlabDistinctRichCommonBinWitnessHeight
    (heightIndex : ℤ) (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) (bin : ℤ) : ℝ :=
  if hbin :
      bin ∈ pullback.standardSqrtSlabDistinctRichCommonBinLabels
        heightIndex referenceHeight heights threshold then
    Classical.choose (Finset.mem_filter.mp hbin).2
  else
    0

/-- Active side-`sqrt rho` spatial cells at the witnessing height of one
distinct rich label. -/
def standardSqrtSlabDistinctRichCommonBinActiveSpatialCells
    (heightIndex : ℤ) (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) (bin : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  pureWZ2FixedCommonBinActiveSpatialCells
    (pullback.standardSqrtSlabSourceRegion heightIndex)
    source.globalGrains.slope referenceHeight (Real.sqrt rho)
    (Real.sqrt_pos.mpr <| by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.coarse.coarse_extremal.delta_pos)
    (pullback.standardSqrtSlabDistinctRichCommonBinWitnessHeight
      heightIndex referenceHeight heights threshold bin)
    bin

/-- The union of the witnessing spatial-cell families over all distinct rich
labels in one standard slab. -/
def standardSqrtSlabDistinctRichCommonBinParticipatingSpatialCells
    (heightIndex : ℤ) (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) : Finset (ℤ × ℤ × ℤ) :=
  (pullback.standardSqrtSlabDistinctRichCommonBinLabels
      heightIndex referenceHeight heights threshold).biUnion
    (pullback.standardSqrtSlabDistinctRichCommonBinActiveSpatialCells
      heightIndex referenceHeight heights threshold)

/-- The mass of one fixed standard-slab common-bin label, integrated over a
supplied height set. -/
def standardSqrtSlabIntegratedBinMass
    (heightIndex : ℤ) (referenceHeight : ℝ) (heights : Set ℝ)
    (bin : ℤ) : ENNReal :=
  ∫⁻ height in heights,
    pureWZ2FixedCommonBinSliceMass
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      source.globalGrains.slope referenceHeight
      (Real.sqrt rho) height bin

theorem standardSqrtSlabDistinctRichCommonBinWitnessHeight_spec
    (heightIndex : ℤ) (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) {bin : ℤ}
    (hbin :
      bin ∈ pullback.standardSqrtSlabDistinctRichCommonBinLabels
        heightIndex referenceHeight heights threshold) :
    pullback.standardSqrtSlabDistinctRichCommonBinWitnessHeight
          heightIndex referenceHeight heights threshold bin ∈ heights ∧
      pullback.standardSqrtSlabDistinctRichCommonBinWitnessHeight
          heightIndex referenceHeight heights threshold bin ∈
        Set.Icc (-1 : ℝ) 1 ∧
      threshold ≤
        pureWZ2FixedCommonBinSliceMass
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          source.globalGrains.slope referenceHeight (Real.sqrt rho)
          (pullback.standardSqrtSlabDistinctRichCommonBinWitnessHeight
            heightIndex referenceHeight heights threshold bin)
          bin := by
  rw [standardSqrtSlabDistinctRichCommonBinWitnessHeight, dif_pos hbin]
  exact Classical.choose_spec (Finset.mem_filter.mp hbin).2

private theorem standardSqrtSlabSourceRegion_norm_le_two
    (heightIndex : ℤ) {point : Point3}
    (hpoint :
      point ∈ pullback.standardSqrtSlabSourceRegion heightIndex) :
    ‖point‖ ≤ 2 :=
  norm_le_two_of_mem_paperShading
    (pullback.standardSqrtSlabSourceRegion_subset_source heightIndex hpoint)

/-- Every popular height of an occupied standard slab is a paper height. -/
theorem standardSqrtSlab_commonBinPopularHeight_mem_paperRange
    {heightIndex : ℤ}
    (hheightIndex : heightIndex ∈ pullback.standardSqrtSlabIndices)
    {height : ℝ}
    (hheight :
      height ∈ pureWZ2SourceCommonBinPopularHeights
        (pullback.standardSqrtSlabSourceRegion heightIndex)
        (standardSqrtSlabLeft (rho := rho) heightIndex)
        (Real.sqrt rho)) :
    height ∈ Set.Icc (-1 : ℝ) 1 := by
  have hthresholdPos :
      0 <
        pureWZ2SourceCommonBinPopularThreshold
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          (Real.sqrt rho) := by
    unfold pureWZ2SourceCommonBinPopularThreshold
      pureWZ2CommonBinPopularThreshold
    exact ENNReal.div_pos
      (ENNReal.div_pos
        (pullback.standardSqrtSlabSourceRegion_volume_pos
          hheightIndex).ne'
        (by norm_num)).ne'
      ENNReal.ofReal_ne_top
  have hslicePos :
      0 <
        pureWZ2SourceCommonBinSliceMass
          (pullback.standardSqrtSlabSourceRegion heightIndex) height :=
    hthresholdPos.trans_le hheight.2
  rcases nonempty_of_measure_ne_zero hslicePos.ne' with
    ⟨planarPoint, hplanarPoint⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hplanarPoint
  have hsource :
      point3 (planarPoint 0) (planarPoint 1) height ∈
        source.shading.union :=
    pullback.standardSqrtSlabSourceRegion_subset_source
      heightIndex hlift
  have hbox := shading_union_subset_axisBox hsource
  simpa [point3, Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2

/-- Any two popular heights of the same literal standard slab differ by at
most `sqrt rho`. -/
theorem standardSqrtSlab_commonBinPopularHeights_close
    (heightIndex : ℤ) {first second : ℝ}
    (hfirst :
      first ∈ pureWZ2SourceCommonBinPopularHeights
        (pullback.standardSqrtSlabSourceRegion heightIndex)
        (standardSqrtSlabLeft (rho := rho) heightIndex)
        (Real.sqrt rho))
    (hsecond :
      second ∈ pureWZ2SourceCommonBinPopularHeights
        (pullback.standardSqrtSlabSourceRegion heightIndex)
        (standardSqrtSlabLeft (rho := rho) heightIndex)
        (Real.sqrt rho)) :
    |first - second| ≤ Real.sqrt rho := by
  rw [abs_le]
  constructor <;>
    linarith [hfirst.1.1, hfirst.1.2, hsecond.1.1, hsecond.1.2]

private theorem standardSqrtSlab_slice_y_abs_le_one
    (heightIndex : ℤ) (height : ℝ) :
    ∀ point ∈ horizontalSlice
        (pullback.standardSqrtSlabSourceRegion heightIndex) height,
      |point (1 : Fin 3)| ≤ 1 := by
  intro point hpoint
  have hsource :
      point ∈ source.shading.union :=
    pullback.standardSqrtSlabSourceRegion_subset_source
      heightIndex hpoint.1
  have hbox := shading_union_subset_axisBox hsource
  simpa [Kakeya.Streamlined.axisBox] using hbox.2.1

private theorem standardSqrtSlab_slice_projection_bounded
    (heightIndex : ℤ) (height : ℝ)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1) :
    scalarProjection
        (globalGrainDirection (source.globalGrains.slope height))
        (horizontalSlice
          (pullback.standardSqrtSlabSourceRegion heightIndex) height) ⊆
      Set.Icc (-4 : ℝ) 4 := by
  rintro value ⟨point, hpoint, rfl⟩
  have hsource :
      point ∈ source.shading.union :=
    pullback.standardSqrtSlabSourceRegion_subset_source
      heightIndex hpoint.1
  have hbox := shading_union_subset_axisBox hsource
  have hslope :
      |source.globalGrains.slope height| ≤ 3 :=
    source.globalGrains.slope_bound height hheight
  have hformula :
      inner ℝ point
          (globalGrainDirection (source.globalGrains.slope height)) =
        point 0 + source.globalGrains.slope height * point 1 := by
    simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
  have habs :
      |inner ℝ point
          (globalGrainDirection (source.globalGrains.slope height))| ≤ 4 := by
    rw [hformula]
    calc
      |point 0 + source.globalGrains.slope height * point 1| ≤
          |point 0| +
            |source.globalGrains.slope height| * |point 1| := by
        simpa [abs_mul] using
          abs_add_le (point 0)
            (source.globalGrains.slope height * point 1)
      _ ≤ 1 + 3 * 1 := by
        gcongr
        · simpa [Kakeya.Streamlined.axisBox] using hbox.1
        · simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
      _ = 4 := by norm_num
  exact abs_le.mp habs

private theorem standardSqrtSlab_slice_ad_root
    (heightIndex : ℤ) (height : ℝ)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1) :
    IsADSet1
      (scalarProjection
        (globalGrainDirection (source.globalGrains.slope height))
        (horizontalSlice
          (pullback.standardSqrtSlabSourceRegion heightIndex) height))
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
          (horizontalSlice
            (pullback.standardSqrtSlabSourceRegion heightIndex) height))
        delta (1 - sigma)
        (Kakeya.realRpowENN delta (-inputLoss)) := by
    apply (source.globalGrains.global_ad height hheight).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact
      ⟨point,
        ⟨pullback.standardSqrtSlabSourceRegion_subset_source
            heightIndex hpoint.1,
          hpoint.2⟩,
        rfl⟩
  have hdelta :
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope height))
          (horizontalSlice
            (pullback.standardSqrtSlabSourceRegion heightIndex) height))
        delta (1 - sigma)
        (2 * Kakeya.realRpowENN delta (-inputLoss)) :=
    hpaper.toIsADSet1
      (pullback.standardSqrtSlab_slice_projection_bounded
        heightIndex height hheight)
  exact hdelta.coarsen_scale
    (Real.sqrt_pos.mpr hrho)
    (hdeltaRho.trans hrhoRoot)
    (Real.sqrt_le_one.mpr hrhoOne)

/-- Direct `B₀` estimate on every admissible slice of a standard source slab.
The factor `264` is `132` times the interval-to-ball AD conversion factor
`2`. -/
theorem standardSqrtSlab_commonBinSlice_occupiedBound
    (heightIndex : ℤ) (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rho) :
    ((pureWZ2OccupiedCommonBins
      (horizontalSlice
        (pullback.standardSqrtSlabSourceRegion heightIndex) height)
      source.globalGrains.slope referenceHeight
      (Real.sqrt rho)).card : ENNReal) ≤
        264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) := by
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hbound :=
    pureWZ2_fixed_common_bin_occupied_bound
      (horizontalSlice
        (pullback.standardSqrtSlabSourceRegion heightIndex) height)
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      height referenceHeight hheight hreference hclose
      (pullback.standardSqrtSlab_slice_y_abs_le_one heightIndex height)
      (pullback.standardSqrtSlab_slice_ad_root
        heightIndex height hheight)
      (Real.sqrt_le_one.mpr hrhoOne)
  calc
    ((pureWZ2OccupiedCommonBins
        (horizontalSlice
          (pullback.standardSqrtSlabSourceRegion heightIndex) height)
        source.globalGrains.slope referenceHeight
        (Real.sqrt rho)).card : ENNReal) ≤
      132 * (2 * Kakeya.realRpowENN delta (-inputLoss)) *
        Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) :=
      hbound
    _ =
      264 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) := by
      ring

private theorem standardSqrtSlab_fixedCommonBinLabel_mem_sliceOccupied
    (heightIndex : ℤ) (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rho)
    {point : Point3}
    (hpoint :
      point ∈ horizontalSlice
        (pullback.standardSqrtSlabSourceRegion heightIndex) height) :
    pureWZ2FixedCommonBinLabel source.globalGrains.slope
        referenceHeight (Real.sqrt rho) point ∈
      pureWZ2OccupiedCommonBins
        (horizontalSlice
          (pullback.standardSqrtSlabSourceRegion heightIndex) height)
        source.globalGrains.slope referenceHeight (Real.sqrt rho) := by
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  exact pureWZ2_fixed_common_bin_mem
    (horizontalSlice
      (pullback.standardSqrtSlabSourceRegion heightIndex) height)
    source.globalGrains.slope source.globalGrains.slope_lipschitz
    height referenceHeight hheight hreference hclose
    (pullback.standardSqrtSlab_slice_y_abs_le_one heightIndex height)
    (pullback.standardSqrtSlab_slice_ad_root
      heightIndex height hheight)
    (Real.sqrt_le_one.mpr hrhoOne) hpoint

/-- The pointwise occupied common bins exactly partition a standard-slab
planar slice. -/
theorem standardSqrtSlab_commonBinSliceMass_sum
    (heightIndex : ℤ) (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rho) :
    pureWZ2SourceCommonBinSliceMass
        (pullback.standardSqrtSlabSourceRegion heightIndex) height =
      ∑ bin ∈
        pureWZ2OccupiedCommonBins
          (horizontalSlice
            (pullback.standardSqrtSlabSourceRegion heightIndex) height)
          source.globalGrains.slope referenceHeight (Real.sqrt rho),
        pureWZ2FixedCommonBinSliceMass
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          source.globalGrains.slope referenceHeight
          (Real.sqrt rho) height bin := by
  simpa [pureWZ2SourceCommonBinSliceMass] using
    pureWZ2_fixed_common_bin_sliceMass_sum
      (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
      source.globalGrains.slope referenceHeight (Real.sqrt rho) height
      (pureWZ2OccupiedCommonBins
        (horizontalSlice
          (pullback.standardSqrtSlabSourceRegion heightIndex) height)
        source.globalGrains.slope referenceHeight (Real.sqrt rho))
      (fun point hpoint =>
        pullback.standardSqrtSlab_fixedCommonBinLabel_mem_sliceOccupied
          heightIndex referenceHeight height
          hreference hheight hclose hpoint)

private theorem standardSqrtSlab_commonBinSliceMass_ne_top
    (heightIndex : ℤ) (height : ℝ) :
    pureWZ2SourceCommonBinSliceMass
        (pullback.standardSqrtSlabSourceRegion heightIndex) height ≠ ⊤ := by
  have hsliceBall :
      wz1Lemma23PlanarSlice
          (pullback.standardSqrtSlabSourceRegion heightIndex) height ⊆
        Metric.closedBall (0 : Point2) 2 := by
    intro point hpoint
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hsource :=
      pullback.standardSqrtSlabSourceRegion_subset_source
        heightIndex hlift
    have hbox := shading_union_subset_axisBox hsource
    have h0 : |point 0| ≤ 1 := by
      simpa [point3, Kakeya.Streamlined.axisBox] using hbox.1
    have h1 : |point 1| ≤ 1 := by
      simpa [point3, Kakeya.Streamlined.axisBox] using hbox.2.1
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq :
        ‖point‖ ^ 2 = point 0 ^ 2 + point 1 ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_two]
    have h0sq : point 0 ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (point 0)]
    have h1sq : point 1 ^ 2 ≤ 1 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg (point 1)]
    nlinarith [norm_nonneg point]
  exact ne_top_of_le_ne_top
    Metric.isBounded_closedBall.measure_lt_top.ne
    (measure_mono hsliceBall)

theorem measurable_standardSqrtSlab_commonBinSliceMass
    (heightIndex : ℤ) (referenceHeight : ℝ) (bin : ℤ) :
    Measurable (fun height : ℝ =>
      pureWZ2FixedCommonBinSliceMass
        (pullback.standardSqrtSlabSourceRegion heightIndex)
        source.globalGrains.slope referenceHeight
        (Real.sqrt rho) height bin) := by
  exact measurable_volume_wz1Lemma23PlanarSlice
    (pureWZ2FixedCommonBinRegion
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      source.globalGrains.slope referenceHeight (Real.sqrt rho) bin)
    (measurableSet_pureWZ2FixedCommonBinRegion
      (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
      source.globalGrains.slope referenceHeight (Real.sqrt rho) bin)

private theorem standardSqrtSlab_commonBinSpatialCellCap_pos
    (hdelta : 0 < delta) (hrho : 0 < rho) :
    0 <
      PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
        sigma inputLoss delta rho := by
  have hdeltaLoss :
      0 < Kakeya.realRpowENN delta (-inputLoss) :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta _)
  have hdeltaSigma :
      0 < Kakeya.realRpowENN delta sigma :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta _)
  have hrhoPower :
      0 < Kakeya.realRpowENN rho (1 - sigma / 2) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hrho _)
  exact ENNReal.mul_pos
    (ENNReal.mul_pos
      (ENNReal.mul_pos
        (by norm_num : (32 : ENNReal) ≠ 0)
        hdeltaLoss.ne').ne'
      hdeltaSigma.ne').ne'
    hrhoPower.ne'

private theorem standardSqrtSlab_commonBinSpatialCellCap_ne_top :
    PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      sigma inputLoss delta rho ≠ ⊤ := by
  simp only
    [PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap,
      Kakeya.realRpowENN]
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top)
    ENNReal.ofReal_ne_top

private theorem standardSqrtSlab_fixedCommonBinSpatialCellSliceMass_le
    (heightIndex : ℤ) (referenceHeight height : ℝ)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (bin : ℤ) (cell : ℤ × ℤ × ℤ) :
    pureWZ2FixedCommonBinSpatialCellSliceMass
        (pullback.standardSqrtSlabSourceRegion heightIndex)
        source.globalGrains.slope referenceHeight
        (Real.sqrt rho) height bin cell ≤
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
          (pureWZ2FixedCommonBinRegion
              (pullback.standardSqrtSlabSourceRegion heightIndex)
              source.globalGrains.slope referenceHeight
              (Real.sqrt rho) bin ∩
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
    exact
      ⟨pullback.standardSqrtSlabSourceRegion_subset_source
          heightIndex hregion.1,
        hlift.2⟩
  calc
    pureWZ2FixedCommonBinSpatialCellSliceMass
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          source.globalGrains.slope referenceHeight
          (Real.sqrt rho) height bin cell =
        volume
          (wz1Lemma23PlanarSlice
            (pureWZ2FixedCommonBinRegion
                (pullback.standardSqrtSlabSourceRegion heightIndex)
                source.globalGrains.slope referenceHeight
                (Real.sqrt rho) bin ∩
              wz1PaperGridCube (Real.sqrt rho) cell)
            height) := rfl
    _ ≤
        volume
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
          hrho (hdeltaRho.trans hrhoRoot) cell height hheight

/-- Under `K * a₀ ≤ threshold`, every distinct rich standard-slab label has
at least `K` witnessing side-`sqrt rho` spatial cells. -/
theorem standardSqrtSlabDistinctRichCommonBin_activeSpatialCells_card_lower
    (heightIndex : ℤ) (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) (K : ℕ)
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold)
    {bin : ℤ}
    (hbin :
      bin ∈ pullback.standardSqrtSlabDistinctRichCommonBinLabels
        heightIndex referenceHeight heights threshold) :
    K ≤
      (pullback.standardSqrtSlabDistinctRichCommonBinActiveSpatialCells
        heightIndex referenceHeight heights threshold bin).card := by
  let height :=
    pullback.standardSqrtSlabDistinctRichCommonBinWitnessHeight
      heightIndex referenceHeight heights threshold bin
  have hwitness :=
    pullback.standardSqrtSlabDistinctRichCommonBinWitnessHeight_spec
      heightIndex referenceHeight heights threshold hbin
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarse.coarse_extremal.delta_pos
  apply CommonBinRichSelection.cell_card_lower_of_rich
    (pullback.standardSqrtSlabDistinctRichCommonBinActiveSpatialCells
      heightIndex referenceHeight heights threshold bin)
    (pureWZ2FixedCommonBinSpatialCellSliceMass
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      source.globalGrains.slope referenceHeight
      (Real.sqrt rho) height bin)
    (pureWZ2FixedCommonBinSliceMass
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      source.globalGrains.slope referenceHeight
      (Real.sqrt rho) height bin)
    threshold
    (PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
      sigma inputLoss delta rho)
    K
  · exact hwitness.2.2
  · exact le_of_eq <| by
      simpa
        [standardSqrtSlabDistinctRichCommonBinActiveSpatialCells,
          height] using
        pureWZ2_fixed_common_bin_sliceMass_eq_sum_activeSpatialCells
          (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
          source.globalGrains.slope referenceHeight
          (Real.sqrt_pos.mpr hrho) height bin
          (fun point hpoint =>
            pullback.standardSqrtSlabSourceRegion_norm_le_two
              heightIndex hpoint)
  · intro cell _hcell
    exact
      pullback.standardSqrtSlab_fixedCommonBinSpatialCellSliceMass_le
        heightIndex referenceHeight height hwitness.2.1 bin cell
  · exact hK
  · exact standardSqrtSlab_commonBinSpatialCellCap_pos
      source.extremal.delta_pos hrho
  · exact standardSqrtSlab_commonBinSpatialCellCap_ne_top

/-- Every witnessing spatial cell of a distinct rich label is one of the
genuine second-cover parents belonging to the same standard slab. -/
theorem standardSqrtSlabDistinctRichCommonBin_activeSpatialCells_subset_parents
    (heightIndex : ℤ) (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) (bin : ℤ) :
    pullback.standardSqrtSlabDistinctRichCommonBinActiveSpatialCells
        heightIndex referenceHeight heights threshold bin ⊆
      pullback.standardSqrtSlabParents heightIndex := by
  intro cell hcell
  rw [standardSqrtSlabDistinctRichCommonBinActiveSpatialCells,
    pureWZ2FixedCommonBinActiveSpatialCells,
    Finset.mem_filter] at hcell
  rcases hcell.2 with ⟨planarPoint, hplanarPoint⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hplanarPoint
  have hregion := hlift.1
  rw [pureWZ2FixedCommonBinRegion] at hregion
  have hpointSlab := hregion.1
  change
    point3 (planarPoint 0) (planarPoint 1)
        (pullback.standardSqrtSlabDistinctRichCommonBinWitnessHeight
          heightIndex referenceHeight heights threshold bin) ∈
      pullback.shading.union ∩
        wz2RetainedCellsUnion rho
          (pullback.standardSqrtSlabRhoCells heightIndex) at hpointSlab
  rw [wz2RetainedCellsUnion] at hpointSlab
  rcases Set.mem_iUnion₂.mp hpointSlab.2 with
    ⟨rhoCell, hrhoCell, hpointRhoCell⟩
  let point : Point3 :=
    point3 (planarPoint 0) (planarPoint 1)
      (pullback.standardSqrtSlabDistinctRichCommonBinWitnessHeight
        heightIndex referenceHeight heights threshold bin)
  have hpointCell :
      point ∈ wz1PaperGridCube twoScale.sqrtRequested.1 cell := by
    simpa only [twoScale.sqrtRequested_eq] using hlift.2
  have hpointParent :
      point ∈ wz1PaperGridCube twoScale.sqrtRequested.1
        (pullback.standardSecondParent rhoCell) :=
    pullback.standardSqrtSlabRhoCell_subset_parent
      hrhoCell hpointRhoCell
  have hcellIndex :
      wz1PaperGridIndex twoScale.sqrtRequested.1 point = cell :=
    (mem_wz1PaperGridCube
      twoScale.sqrtRequested.1 cell point).mp hpointCell
  have hparentIndex :
      wz1PaperGridIndex twoScale.sqrtRequested.1 point =
        pullback.standardSecondParent rhoCell :=
    (mem_wz1PaperGridCube twoScale.sqrtRequested.1
      (pullback.standardSecondParent rhoCell) point).mp hpointParent
  have hcellParent :
      cell = pullback.standardSecondParent rhoCell :=
    hcellIndex.symm.trans hparentIndex
  rw [hcellParent]
  exact Finset.mem_image.mpr ⟨rhoCell, hrhoCell, rfl⟩

theorem standardSqrtSlabDistinctRichCommonBin_participatingCells_subset_parents
    (heightIndex : ℤ) (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold : ENNReal) :
    pullback.standardSqrtSlabDistinctRichCommonBinParticipatingSpatialCells
        heightIndex referenceHeight heights threshold ⊆
      pullback.standardSqrtSlabParents heightIndex := by
  intro cell hcell
  rw [standardSqrtSlabDistinctRichCommonBinParticipatingSpatialCells,
    Finset.mem_biUnion] at hcell
  rcases hcell with ⟨bin, _hbin, hcell⟩
  exact
    pullback.standardSqrtSlabDistinctRichCommonBin_activeSpatialCells_subset_parents
      heightIndex referenceHeight heights threshold bin hcell

/-- A spatial cell is used by at most five selected distinct fixed labels. -/
theorem standardSqrtSlabDistinctRichCommonBin_cellDegree_le_five
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (heights : Set ℝ) (threshold : ENNReal)
    (cell : ℤ × ℤ × ℤ) :
    ((pullback.standardSqrtSlabDistinctRichCommonBinLabels
        heightIndex referenceHeight heights threshold).filter fun bin =>
      cell ∈
        pullback.standardSqrtSlabDistinctRichCommonBinActiveSpatialCells
          heightIndex referenceHeight heights threshold bin).card ≤ 5 := by
  let bins :=
    pullback.standardSqrtSlabDistinctRichCommonBinLabels
      heightIndex referenceHeight heights threshold
  have hsubset :
      (bins.filter fun bin =>
          cell ∈
            pullback.standardSqrtSlabDistinctRichCommonBinActiveSpatialCells
              heightIndex referenceHeight heights threshold bin) ⊆
        pureWZ2CommonBinsMeetingSpatialCell bins
          source.globalGrains.slope referenceHeight
          (Real.sqrt rho) cell := by
    intro bin hbin
    rw [Finset.mem_filter] at hbin
    rw [pureWZ2CommonBinsMeetingSpatialCell, Finset.mem_filter]
    refine ⟨hbin.1, ?_⟩
    have hactive := hbin.2
    rw [standardSqrtSlabDistinctRichCommonBinActiveSpatialCells,
      pureWZ2FixedCommonBinActiveSpatialCells,
      Finset.mem_filter] at hactive
    rcases hactive.2 with ⟨point, hpoint⟩
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hregion := hlift.1
    rw [pureWZ2FixedCommonBinRegion] at hregion
    exact
      ⟨point3 (point 0) (point 1)
          (pullback.standardSqrtSlabDistinctRichCommonBinWitnessHeight
            heightIndex referenceHeight heights threshold bin),
        hlift.2, hregion.2⟩
  calc
    ((pullback.standardSqrtSlabDistinctRichCommonBinLabels
          heightIndex referenceHeight heights threshold).filter fun bin =>
        cell ∈
          pullback.standardSqrtSlabDistinctRichCommonBinActiveSpatialCells
            heightIndex referenceHeight heights threshold bin).card =
        (bins.filter fun bin =>
          cell ∈
            pullback.standardSqrtSlabDistinctRichCommonBinActiveSpatialCells
              heightIndex referenceHeight heights threshold bin).card := by
      rfl
    _ ≤
        (pureWZ2CommonBinsMeetingSpatialCell bins
          source.globalGrains.slope referenceHeight
          (Real.sqrt rho) cell).card :=
      Finset.card_le_card hsubset
    _ ≤ 5 :=
      commonBinsMeetingSpatialCell_card_le_five
        (Real.sqrt_pos.mpr <| by
          rw [← twoScale.rhoRequested_eq]
          exact twoScale.coarse.coarse_extremal.delta_pos)
        bins source.globalGrains.slope referenceHeight
        (source.globalGrains.slope_bound referenceHeight hreference)
        cell

/-- Standard-slab distinct-label incidence:

`|R| * K * w_s ≤ 5 * G_S`.

Here `G_S` is the full standard-slab coarse volume, and the participating
cells enter it only through the proved subset of standard slab parents. -/
theorem standardSqrtSlabDistinctRichCommonBin_incidence
    (heightIndex : ℤ) (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (heights : Set ℝ) (threshold : ENNReal) (K : ℕ)
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold) :
    ((pullback.standardSqrtSlabDistinctRichCommonBinLabels
        heightIndex referenceHeight heights threshold).card : ENNReal) *
        K * twoScale.fine.balanced.cellMass ≤
      5 * volume (pullback.standardSqrtSlabCoarseRegion heightIndex) := by
  let bins :=
    pullback.standardSqrtSlabDistinctRichCommonBinLabels
      heightIndex referenceHeight heights threshold
  let cells : ℤ → Finset (ℤ × ℤ × ℤ) :=
    pullback.standardSqrtSlabDistinctRichCommonBinActiveSpatialCells
      heightIndex referenceHeight heights threshold
  apply CommonBinDistinctIncidence.card_mul_cellMass_le_degree_mul_totalMass
    bins cells K 5 twoScale.fine.balanced.cellMass
    (volume (pullback.standardSqrtSlabCoarseRegion heightIndex))
  · intro bin hbin
    exact
      pullback.standardSqrtSlabDistinctRichCommonBin_activeSpatialCells_card_lower
        heightIndex referenceHeight heights threshold K hK hbin
  · intro cell _hcell
    simpa [bins, cells] using
      pullback.standardSqrtSlabDistinctRichCommonBin_cellDegree_le_five
        heightIndex referenceHeight hreference heights threshold cell
  · have hsubset :
        (@Finset.biUnion ℤ (ℤ × ℤ × ℤ)
          (fun first second =>
            Classical.propDecidable (first = second))
          bins cells) ⊆
            pullback.standardSqrtSlabParents heightIndex := by
      intro cell hcell
      rcases
          (@Finset.mem_biUnion ℤ (ℤ × ℤ × ℤ)
            bins cells
            (fun first second =>
              Classical.propDecidable (first = second))
            cell).mp hcell
        with ⟨bin, _hbin, hcell⟩
      exact
        pullback.standardSqrtSlabDistinctRichCommonBin_activeSpatialCells_subset_parents
          heightIndex referenceHeight heights threshold bin hcell
    have hcard :
        ((@Finset.biUnion ℤ (ℤ × ℤ × ℤ)
          (fun first second =>
            Classical.propDecidable (first = second))
          bins cells).card : ENNReal) ≤
            (pullback.standardSqrtSlabParents heightIndex).card := by
      exact_mod_cast Finset.card_le_card hsubset
    calc
      ((@Finset.biUnion ℤ (ℤ × ℤ × ℤ)
          (fun first second =>
            Classical.propDecidable (first = second))
          bins cells).card : ENNReal) *
          twoScale.fine.balanced.cellMass ≤
          ((pullback.standardSqrtSlabParents heightIndex).card : ENNReal) *
            twoScale.fine.balanced.cellMass := by
        gcongr
      _ =
          volume (pullback.standardSqrtSlabCoarseRegion heightIndex) :=
        pullback.standardSqrtSlab_parentMass_eq_coarseVolume heightIndex

/-- Distinct rich labels retain one quarter of the exact standard source
slab after integration over its popular height set. -/
theorem standardSqrtSlabDistinctRichCommonBin_integratedMass
    {heightIndex : ℤ}
    (hheightIndex : heightIndex ∈ pullback.standardSqrtSlabIndices)
    (referenceHeight : ℝ)
    (hreference :
      referenceHeight ∈
        pureWZ2SourceCommonBinPopularHeights
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          (standardSqrtSlabLeft (rho := rho) heightIndex)
          (Real.sqrt rho))
    (B₀ threshold : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          (Real.sqrt rho)) :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex) ≤
      4 * ∑ bin ∈
        pullback.standardSqrtSlabDistinctRichCommonBinLabels
          heightIndex referenceHeight
          (pureWZ2SourceCommonBinPopularHeights
            (pullback.standardSqrtSlabSourceRegion heightIndex)
            (standardSqrtSlabLeft (rho := rho) heightIndex)
            (Real.sqrt rho))
          threshold,
        pullback.standardSqrtSlabIntegratedBinMass
          heightIndex referenceHeight
          (pureWZ2SourceCommonBinPopularHeights
            (pullback.standardSqrtSlabSourceRegion heightIndex)
            (standardSqrtSlabLeft (rho := rho) heightIndex)
            (Real.sqrt rho))
          bin := by
  let E := pullback.standardSqrtSlabSourceRegion heightIndex
  let left := standardSqrtSlabLeft (rho := rho) heightIndex
  let heights :=
    pureWZ2SourceCommonBinPopularHeights E left (Real.sqrt rho)
  let richLabels :=
    pullback.standardSqrtSlabDistinctRichCommonBinLabels
      heightIndex referenceHeight heights threshold
  let sliceMass : ℝ → ENNReal :=
    pureWZ2SourceCommonBinSliceMass E
  let binMass : ℝ → ℤ → ENNReal := fun height bin =>
    pureWZ2FixedCommonBinSliceMass E source.globalGrains.slope
      referenceHeight (Real.sqrt rho) height bin
  have hreferenceRange :
      referenceHeight ∈ Set.Icc (-1 : ℝ) 1 :=
    pullback.standardSqrtSlab_commonBinPopularHeight_mem_paperRange
      hheightIndex hreference
  have hpointwise :
      ∀ height ∈ heights,
        sliceMass height ≤
          2 * ∑ bin ∈ richLabels, binMass height bin := by
    intro height hheight
    have hheightOriginal :
        height ∈ pureWZ2SourceCommonBinPopularHeights
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          (standardSqrtSlabLeft (rho := rho) heightIndex)
          (Real.sqrt rho) := by
      simpa [E, left, heights] using hheight
    have hheightRange :
        height ∈ Set.Icc (-1 : ℝ) 1 :=
      pullback.standardSqrtSlab_commonBinPopularHeight_mem_paperRange
        hheightIndex hheightOriginal
    have hclose : |height - referenceHeight| ≤ Real.sqrt rho :=
      pullback.standardSqrtSlab_commonBinPopularHeights_close
        heightIndex hheightOriginal hreference
    let bins :=
      pureWZ2OccupiedCommonBins
        (horizontalSlice E height)
        source.globalGrains.slope referenceHeight (Real.sqrt rho)
    have htotalEq :
        sliceMass height = ∑ bin ∈ bins, binMass height bin := by
      have hsum :=
        pullback.standardSqrtSlab_commonBinSliceMass_sum
          heightIndex referenceHeight height
          hreferenceRange hheightRange hclose
      simpa [E, bins, sliceMass, binMass] using hsum
    have hcard : (bins.card : ENNReal) ≤ B₀ := by
      exact (by
        simpa [E, bins] using
          (pullback.standardSqrtSlab_commonBinSlice_occupiedBound
            heightIndex referenceHeight height
            hreferenceRange hheightRange hclose).trans hB₀)
    have hpoor :
        2 * ((bins.card : ENNReal) * threshold) ≤ sliceMass height := by
      calc
        2 * ((bins.card : ENNReal) * threshold) ≤
            2 * (B₀ * threshold) := by gcongr
        _ = 2 * B₀ * threshold := by ring
        _ ≤
            pureWZ2SourceCommonBinPopularThreshold
              (pullback.standardSqrtSlabSourceRegion heightIndex)
              (Real.sqrt rho) :=
          hthresholdBudget
        _ ≤
            pureWZ2SourceCommonBinSliceMass
              (pullback.standardSqrtSlabSourceRegion heightIndex) height :=
          hheightOriginal.2
        _ = sliceMass height := by rfl
    have hsliceTop : sliceMass height ≠ ⊤ := by
      simpa [E, sliceMass] using
        pullback.standardSqrtSlab_commonBinSliceMass_ne_top
          heightIndex height
    have hretained :=
      CommonBinRichSelection.total_le_two_mul_rich_sum
        bins (binMass height) threshold (sliceMass height)
        htotalEq hsliceTop hpoor
    have hsubset :
        CommonBinRichSelection.richBins
            bins (binMass height) threshold ⊆ richLabels := by
      intro bin hbin
      have hbinData := Finset.mem_filter.mp hbin
      have hambient :
          bin ∈ pureWZ2OccupiedCommonBins
            E source.globalGrains.slope referenceHeight
            (Real.sqrt rho) := by
        have hbinOccupied := hbinData.1
        dsimp only [bins] at hbinOccupied
        rw [pureWZ2OccupiedCommonBins, Finset.mem_filter] at hbinOccupied
        rw [pureWZ2OccupiedCommonBins, Finset.mem_filter]
        refine ⟨hbinOccupied.1, ?_⟩
        rcases hbinOccupied.2 with ⟨point, hpoint, hlabel⟩
        exact ⟨point, hpoint.1, hlabel⟩
      change
        bin ∈ pullback.standardSqrtSlabDistinctRichCommonBinLabels
          heightIndex referenceHeight heights threshold
      rw [standardSqrtSlabDistinctRichCommonBinLabels,
        Finset.mem_filter]
      exact ⟨hambient, height, hheight, hheightRange, hbinData.2⟩
    calc
      sliceMass height ≤
          2 * ∑ bin ∈
            CommonBinRichSelection.richBins
              bins (binMass height) threshold,
            binMass height bin :=
        hretained
      _ ≤ 2 * ∑ bin ∈ richLabels, binMass height bin :=
        mul_le_mul_right
          (Finset.sum_le_sum_of_subset hsubset) 2
  have hheightsMeas : MeasurableSet heights := by
    exact measurableSet_pureWZ2SourceCommonBinPopularHeights
      E (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
      left (Real.sqrt rho)
  have hbinMassMeas :
      ∀ bin : ℤ, Measurable (fun height => binMass height bin) := by
    intro bin
    simpa [E, binMass] using
      pullback.measurable_standardSqrtSlab_commonBinSliceMass
        heightIndex referenceHeight bin
  have hrichSumMeas :
      Measurable (fun height =>
        ∑ bin ∈ richLabels, binMass height bin) :=
    Finset.measurable_sum richLabels fun bin _ => hbinMassMeas bin
  have hintegratedPointwise :
      (∫⁻ height in heights, sliceMass height) ≤
        2 * ∫⁻ height in heights,
          ∑ bin ∈ richLabels, binMass height bin := by
    calc
      (∫⁻ height in heights, sliceMass height) ≤
          ∫⁻ height in heights,
            2 * ∑ bin ∈ richLabels, binMass height bin :=
        setLIntegral_mono' hheightsMeas hpointwise
      _ = 2 * ∫⁻ height in heights,
            ∑ bin ∈ richLabels, binMass height bin :=
        MeasureTheory.lintegral_const_mul 2 hrichSumMeas
  have hsumIntegral :
      (∫⁻ height in heights,
        ∑ bin ∈ richLabels, binMass height bin) =
      ∑ bin ∈ richLabels,
        pullback.standardSqrtSlabIntegratedBinMass
          heightIndex referenceHeight heights bin := by
    rw [MeasureTheory.lintegral_finsetSum richLabels]
    · rfl
    · intro bin _
      exact hbinMassMeas bin
  have hhalf :
      volume E / 2 ≤
        ∫⁻ height in heights, sliceMass height := by
    simpa [E, left, heights, sliceMass] using
      pullback.standardSqrtSlab_commonBinPopularHalfMass heightIndex
  calc
    volume (pullback.standardSqrtSlabSourceRegion heightIndex) =
        volume E := rfl
    _ = volume E / 2 + volume E / 2 :=
      (ENNReal.add_halves _).symm
    _ ≤ (∫⁻ height in heights, sliceMass height) +
          ∫⁻ height in heights, sliceMass height := by
      gcongr
    _ = 2 * ∫⁻ height in heights, sliceMass height := by ring
    _ ≤ 2 * (2 * ∫⁻ height in heights,
          ∑ bin ∈ richLabels, binMass height bin) := by
      gcongr
    _ = 4 * ∑ bin ∈ richLabels,
          pullback.standardSqrtSlabIntegratedBinMass
            heightIndex referenceHeight heights bin := by
      rw [hsumIntegral]
      ring
    _ = 4 * ∑ bin ∈
          pullback.standardSqrtSlabDistinctRichCommonBinLabels
            heightIndex referenceHeight
            (pureWZ2SourceCommonBinPopularHeights
              (pullback.standardSqrtSlabSourceRegion heightIndex)
              (standardSqrtSlabLeft (rho := rho) heightIndex)
              (Real.sqrt rho))
            threshold,
          pullback.standardSqrtSlabIntegratedBinMass
            heightIndex referenceHeight
            (pureWZ2SourceCommonBinPopularHeights
              (pullback.standardSqrtSlabSourceRegion heightIndex)
              (standardSqrtSlabLeft (rho := rho) heightIndex)
              (Real.sqrt rho))
            bin := by
      rfl

/-- The standard-slab distinct rich-label set is nonempty. -/
theorem standardSqrtSlabDistinctRichCommonBinLabels_nonempty
    {heightIndex : ℤ}
    (hheightIndex : heightIndex ∈ pullback.standardSqrtSlabIndices)
    (referenceHeight : ℝ)
    (hreference :
      referenceHeight ∈
        pureWZ2SourceCommonBinPopularHeights
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          (standardSqrtSlabLeft (rho := rho) heightIndex)
          (Real.sqrt rho))
    (B₀ threshold : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          (Real.sqrt rho)) :
    (pullback.standardSqrtSlabDistinctRichCommonBinLabels
      heightIndex referenceHeight
      (pureWZ2SourceCommonBinPopularHeights
        (pullback.standardSqrtSlabSourceRegion heightIndex)
        (standardSqrtSlabLeft (rho := rho) heightIndex)
        (Real.sqrt rho))
      threshold).Nonempty := by
  let heights :=
    pureWZ2SourceCommonBinPopularHeights
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      (standardSqrtSlabLeft (rho := rho) heightIndex)
      (Real.sqrt rho)
  let richLabels :=
    pullback.standardSqrtSlabDistinctRichCommonBinLabels
      heightIndex referenceHeight heights threshold
  by_contra hempty
  have hempty' : richLabels = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hempty
  have hrichMass :=
    pullback.standardSqrtSlabDistinctRichCommonBin_integratedMass
      hheightIndex referenceHeight hreference
      B₀ threshold hB₀ hthresholdBudget
  have hzero :
      (∑ bin ∈ richLabels,
        pullback.standardSqrtSlabIntegratedBinMass
          heightIndex referenceHeight heights bin) = 0 := by
    simp [hempty']
  have hsourceZero :
      volume (pullback.standardSqrtSlabSourceRegion heightIndex) ≤ 0 := by
    simpa [heights, richLabels, hzero] using hrichMass
  exact
    (not_le_of_gt
      (pullback.standardSqrtSlabSourceRegion_volume_pos hheightIndex))
      hsourceZero

/-- Choose one fixed rich label whose integrated mass controls the distinct
label average on the exact standard slab. -/
theorem exists_standardSqrtSlab_integratedRichCommonBin
    {heightIndex : ℤ}
    (hheightIndex : heightIndex ∈ pullback.standardSqrtSlabIndices)
    (referenceHeight : ℝ)
    (hreference :
      referenceHeight ∈
        pureWZ2SourceCommonBinPopularHeights
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          (standardSqrtSlabLeft (rho := rho) heightIndex)
          (Real.sqrt rho))
    (B₀ threshold : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          (Real.sqrt rho)) :
    ∃ bin ∈
        pullback.standardSqrtSlabDistinctRichCommonBinLabels
          heightIndex referenceHeight
          (pureWZ2SourceCommonBinPopularHeights
            (pullback.standardSqrtSlabSourceRegion heightIndex)
            (standardSqrtSlabLeft (rho := rho) heightIndex)
            (Real.sqrt rho))
          threshold,
      volume (pullback.standardSqrtSlabSourceRegion heightIndex) ≤
        4 *
          ((pullback.standardSqrtSlabDistinctRichCommonBinLabels
            heightIndex referenceHeight
            (pureWZ2SourceCommonBinPopularHeights
              (pullback.standardSqrtSlabSourceRegion heightIndex)
              (standardSqrtSlabLeft (rho := rho) heightIndex)
              (Real.sqrt rho))
            threshold).card : ENNReal) *
          pullback.standardSqrtSlabIntegratedBinMass
            heightIndex referenceHeight
            (pureWZ2SourceCommonBinPopularHeights
              (pullback.standardSqrtSlabSourceRegion heightIndex)
              (standardSqrtSlabLeft (rho := rho) heightIndex)
              (Real.sqrt rho))
            bin := by
  let heights :=
    pureWZ2SourceCommonBinPopularHeights
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      (standardSqrtSlabLeft (rho := rho) heightIndex)
      (Real.sqrt rho)
  let richLabels :=
    pullback.standardSqrtSlabDistinctRichCommonBinLabels
      heightIndex referenceHeight heights threshold
  have hnonempty : richLabels.Nonempty := by
    simpa [heights, richLabels] using
      pullback.standardSqrtSlabDistinctRichCommonBinLabels_nonempty
        hheightIndex referenceHeight hreference
        B₀ threshold hB₀ hthresholdBudget
  have hrichMass :=
    pullback.standardSqrtSlabDistinctRichCommonBin_integratedMass
      hheightIndex referenceHeight hreference
      B₀ threshold hB₀ hthresholdBudget
  rcases CommonBinDistinctIncidence.exists_weight_ge_average
      richLabels hnonempty
      (fun bin : {bin // bin ∈ richLabels} =>
        pullback.standardSqrtSlabIntegratedBinMass
          heightIndex referenceHeight heights bin.1) with
    ⟨selected, haverage⟩
  refine ⟨selected.1, ?_, ?_⟩
  · change selected.1 ∈ richLabels
    exact selected.2
  calc
    volume (pullback.standardSqrtSlabSourceRegion heightIndex) ≤
        4 * ∑ bin ∈ richLabels,
          pullback.standardSqrtSlabIntegratedBinMass
            heightIndex referenceHeight heights bin := by
      simpa [heights, richLabels] using hrichMass
    _ = 4 * ∑ bin : {bin // bin ∈ richLabels},
        pullback.standardSqrtSlabIntegratedBinMass
          heightIndex referenceHeight heights bin.1 := by
      rw [Finset.sum_subtype richLabels (fun _ => Iff.rfl)]
    _ ≤ 4 * ((richLabels.card : ENNReal) *
        pullback.standardSqrtSlabIntegratedBinMass
          heightIndex referenceHeight heights selected.1) := by
      gcongr
    _ = 4 * (richLabels.card : ENNReal) *
        pullback.standardSqrtSlabIntegratedBinMass
          heightIndex referenceHeight heights selected.1 := by
      ring
    _ =
        4 *
          ((pullback.standardSqrtSlabDistinctRichCommonBinLabels
            heightIndex referenceHeight
            (pureWZ2SourceCommonBinPopularHeights
              (pullback.standardSqrtSlabSourceRegion heightIndex)
              (standardSqrtSlabLeft (rho := rho) heightIndex)
              (Real.sqrt rho))
            threshold).card : ENNReal) *
          pullback.standardSqrtSlabIntegratedBinMass
            heightIndex referenceHeight
            (pureWZ2SourceCommonBinPopularHeights
              (pullback.standardSqrtSlabSourceRegion heightIndex)
              (standardSqrtSlabLeft (rho := rho) heightIndex)
              (Real.sqrt rho))
            selected.1 := by
      rfl

/-- Division-free fixed-bin endpoint obtained from the integrated rich-label
average, full standard-slab incidence, and
`standardSqrtSlab_source_coarse_cross`.

This is the form needed before the final per-rho-cell whole-envelope
cancellation: `w_rho * K * w_s` is controlled by the selected integrated
fixed-bin mass times the geometric rho-cube volume. -/
theorem exists_standardSqrtSlab_integratedRichCommonBin_exactCross
    {heightIndex : ℤ}
    (hheightIndex : heightIndex ∈ pullback.standardSqrtSlabIndices)
    (referenceHeight : ℝ)
    (hreference :
      referenceHeight ∈
        pureWZ2SourceCommonBinPopularHeights
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          (standardSqrtSlabLeft (rho := rho) heightIndex)
          (Real.sqrt rho))
    (B₀ threshold : ENNReal) (K : ℕ)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          (Real.sqrt rho))
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold) :
    ∃ bin ∈
        pullback.standardSqrtSlabDistinctRichCommonBinLabels
          heightIndex referenceHeight
          (pureWZ2SourceCommonBinPopularHeights
            (pullback.standardSqrtSlabSourceRegion heightIndex)
            (standardSqrtSlabLeft (rho := rho) heightIndex)
            (Real.sqrt rho))
          threshold,
      (twoScale.coarse.balanced.cellMass *
            (K * twoScale.fine.balanced.cellMass) ≤
          20 *
            pullback.standardSqrtSlabIntegratedBinMass
              heightIndex referenceHeight
              (pureWZ2SourceCommonBinPopularHeights
                (pullback.standardSqrtSlabSourceRegion heightIndex)
                (standardSqrtSlabLeft (rho := rho) heightIndex)
                (Real.sqrt rho))
              bin *
            volume (wz1PaperGridCube rho (0, 0, 0))) ∧
        volume (pullback.standardSqrtSlabSourceRegion heightIndex) ≤
          4 *
            ((pullback.standardSqrtSlabDistinctRichCommonBinLabels
              heightIndex referenceHeight
              (pureWZ2SourceCommonBinPopularHeights
                (pullback.standardSqrtSlabSourceRegion heightIndex)
                (standardSqrtSlabLeft (rho := rho) heightIndex)
                (Real.sqrt rho))
              threshold).card : ENNReal) *
            pullback.standardSqrtSlabIntegratedBinMass
              heightIndex referenceHeight
              (pureWZ2SourceCommonBinPopularHeights
                (pullback.standardSqrtSlabSourceRegion heightIndex)
                (standardSqrtSlabLeft (rho := rho) heightIndex)
                (Real.sqrt rho))
              bin := by
  let heights :=
    pureWZ2SourceCommonBinPopularHeights
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      (standardSqrtSlabLeft (rho := rho) heightIndex)
      (Real.sqrt rho)
  let bins :=
    pullback.standardSqrtSlabDistinctRichCommonBinLabels
      heightIndex referenceHeight heights threshold
  rcases pullback.exists_standardSqrtSlab_integratedRichCommonBin
      hheightIndex referenceHeight hreference
      B₀ threshold hB₀ hthresholdBudget with
    ⟨selected, hselectedMem, hselectedMass⟩
  have hreferenceRange :
      referenceHeight ∈ Set.Icc (-1 : ℝ) 1 :=
    pullback.standardSqrtSlab_commonBinPopularHeight_mem_paperRange
      hheightIndex hreference
  have hincidence :
      (bins.card : ENNReal) * K *
          twoScale.fine.balanced.cellMass ≤
        5 * volume
          (pullback.standardSqrtSlabCoarseRegion heightIndex) := by
    simpa [bins, heights] using
      pullback.standardSqrtSlabDistinctRichCommonBin_incidence
        heightIndex referenceHeight hreferenceRange heights threshold K hK
  have hparentsNonempty :
      (pullback.standardSqrtSlabParents heightIndex).Nonempty := by
    rcases pullback.standardSqrtSlabRhoCells_nonempty hheightIndex with
      ⟨rhoCell, hrhoCell⟩
    exact
      ⟨pullback.standardSecondParent rhoCell,
        Finset.mem_image.mpr ⟨rhoCell, hrhoCell, rfl⟩⟩
  have hcoarsePos :
      0 < volume
        (pullback.standardSqrtSlabCoarseRegion heightIndex) := by
    rw [← pullback.standardSqrtSlab_parentMass_eq_coarseVolume heightIndex]
    exact ENNReal.mul_pos
      (by
        exact_mod_cast
          (Finset.card_pos.mpr hparentsNonempty).ne')
      twoScale.fine.balanced.cellMass_pos.ne'
  have hcoarseTop :
      volume (pullback.standardSqrtSlabCoarseRegion heightIndex) ≠ ⊤ := by
    rw [← pullback.standardSqrtSlab_parentMass_eq_coarseVolume heightIndex]
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top _)
      twoScale.fine.balanced.cellMass_ne_top
  refine ⟨selected, hselectedMem, ?_, ?_⟩
  · apply
      (ENNReal.mul_le_mul_iff_right
        hcoarsePos.ne' hcoarseTop).mp
    calc
      volume (pullback.standardSqrtSlabCoarseRegion heightIndex) *
          (twoScale.coarse.balanced.cellMass *
            (K * twoScale.fine.balanced.cellMass)) =
        (volume (pullback.standardSqrtSlabCoarseRegion heightIndex) *
          twoScale.coarse.balanced.cellMass) *
            (K * twoScale.fine.balanced.cellMass) := by
        ring
      _ =
        (volume (pullback.standardSqrtSlabSourceRegion heightIndex) *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
            (K * twoScale.fine.balanced.cellMass) := by
        rw [pullback.standardSqrtSlab_source_coarse_cross heightIndex]
      _ ≤
        (4 * (bins.card : ENNReal) *
          pullback.standardSqrtSlabIntegratedBinMass
            heightIndex referenceHeight heights selected *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
            (K * twoScale.fine.balanced.cellMass) := by
        gcongr
      _ =
        (4 *
          pullback.standardSqrtSlabIntegratedBinMass
            heightIndex referenceHeight heights selected *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
          ((bins.card : ENNReal) * K *
            twoScale.fine.balanced.cellMass) := by
        ring
      _ ≤
        (4 *
          pullback.standardSqrtSlabIntegratedBinMass
            heightIndex referenceHeight heights selected *
          volume (wz1PaperGridCube rho (0, 0, 0))) *
          (5 * volume
            (pullback.standardSqrtSlabCoarseRegion heightIndex)) := by
        gcongr
      _ =
        volume (pullback.standardSqrtSlabCoarseRegion heightIndex) *
          (20 *
            pullback.standardSqrtSlabIntegratedBinMass
              heightIndex referenceHeight heights selected *
            volume (wz1PaperGridCube rho (0, 0, 0))) := by
        ring
  · exact hselectedMass

end PureWZ2TwoScaleCellPullbackData

end Kakeya.Assouad

end
