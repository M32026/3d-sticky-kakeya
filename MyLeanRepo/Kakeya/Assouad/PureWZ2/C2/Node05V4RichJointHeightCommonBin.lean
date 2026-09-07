import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSourceVolumePopularEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSourcePopularIntegratedBin

/-!
# Common-bin selection after joint source-height regularization

The source set is first restricted to the paper's continuous slice-popular
set `Z_S`, then to a dyadically comparable graph-height band.  Common-bin
selection is run only after both restrictions.  Thus its whole source mass is
the mass needed by the later bounded-fibre height return.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

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
    (volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex)

/-- Exact joint source set: continuous paper `Z_S` and the auxiliary
comparable-volume graph-height band. -/
def jointSourceSet : Set Point3 :=
  volumePopular.popular.shading.union

def jointSlabLeft
    (_volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex) :
    ℝ :=
  pullback.sourcePopularSlabLeft heightIndex.1.1

/-- A second literal slice-mass popularity, now on the joint source set.
This is the set over which the fixed-bin masses are integrated. -/
def jointPopularHeights : Set ℝ :=
  pureWZ2SourceCommonBinPopularHeights
    volumePopular.jointSourceSet volumePopular.jointSlabLeft (Real.sqrt rho)

def jointRichCommonBinLabels
    (referenceHeight : ℝ) (threshold : ENNReal) : Finset ℤ :=
  (pureWZ2OccupiedCommonBins volumePopular.jointSourceSet
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho)).filter fun bin =>
    ∃ height,
      height ∈ volumePopular.jointPopularHeights ∧
      height ∈ Set.Icc (-1 : ℝ) 1 ∧
      threshold ≤ pureWZ2FixedCommonBinSliceMass
        volumePopular.jointSourceSet current.grain.globalGrains.slope
        referenceHeight (Real.sqrt rho) height bin

def jointIntegratedBinMass
    (referenceHeight : ℝ) (bin : ℤ) : ENNReal :=
  ∫⁻ height in volumePopular.jointPopularHeights,
    pureWZ2FixedCommonBinSliceMass volumePopular.jointSourceSet
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho) height bin

/-- Family-free bound for the number of joint integrated labels. -/
theorem jointRichCommonBinLabels_card_le
    (referenceHeight : ℝ) (threshold : ENNReal) :
    ((volumePopular.jointRichCommonBinLabels
      referenceHeight threshold).card : ENNReal) ≤
      ENNReal.ofReal (12 / Real.sqrt rho) := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hroot : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  let ambient : Finset ℤ := Finset.Icc
    (Int.floor ((-5 : ℝ) / Real.sqrt rho))
    (Int.floor ((5 : ℝ) / Real.sqrt rho))
  have hsubset :
      volumePopular.jointRichCommonBinLabels
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
      (ambient.card : ℤ) =
        Int.floor ((5 : ℝ) / Real.sqrt rho) + 1 -
          Int.floor ((-5 : ℝ) / Real.sqrt rho) :=
    Int.card_Icc_of_le _ _ hlowerUpper
  have hcardReal :
      ((volumePopular.jointRichCommonBinLabels
        referenceHeight threshold).card : ℝ) ≤
        12 / Real.sqrt rho := by
    have hcardAmbient :
        ((volumePopular.jointRichCommonBinLabels
          referenceHeight threshold).card : ℝ) ≤ (ambient.card : ℝ) := by
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
        rw [← pullback.rhoRequested_eq]
        exact rhoRequested.property.2
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

def jointFixedBinHeightRegion
    (referenceHeight : ℝ) (bin : ℤ) : Set Point3 :=
  pureWZ2FixedCommonBinRegion volumePopular.jointSourceSet
      current.grain.globalGrains.slope referenceHeight (Real.sqrt rho) bin ∩
    {point | point (2 : Fin 3) ∈ volumePopular.jointPopularHeights}

theorem jointSourceSet_measurable :
    MeasurableSet volumePopular.jointSourceSet :=
  measurableSet_shading_union volumePopular.popular.shading

theorem jointSourceSet_subset_sourcePopular :
    volumePopular.jointSourceSet ⊆
      volumePopular.sourcePopularShading.union := by
  rw [jointSourceSet, volumePopular.popular.union_eq]
  exact Set.inter_subset_left

theorem jointSourceSet_subset_standardSlab :
    volumePopular.jointSourceSet ⊆
      pullback.standardSqrtSlabSourceRegion heightIndex.1.1 := by
  intro point hpoint
  have hsource :=
    volumePopular.sourcePopularShading_sub_slab.union_subset
      (volumePopular.jointSourceSet_subset_sourcePopular hpoint)
  rwa [pullback.standardSqrtSlabSourceShading_union] at hsource

theorem jointSourceSet_subset_current :
    volumePopular.jointSourceSet ⊆ current.grain.shading.union := by
  intro point hpoint
  exact (pullback.standardSqrtSlabSourceShading_sub_source
    heightIndex.1.1).union_subset (by
      rw [pullback.standardSqrtSlabSourceShading_union]
      exact volumePopular.jointSourceSet_subset_standardSlab hpoint)

theorem jointSourceSet_height_mem_ZS
    {point : Point3} (hpoint : point ∈ volumePopular.jointSourceSet) :
    point (2 : Fin 3) ∈ volumePopular.continuous.popularHeights := by
  have hsource :=
    volumePopular.jointSourceSet_subset_sourcePopular hpoint
  rw [volumePopular.sourcePopularShading_union,
    volumePopular.continuous.popularRegion_eq,
    PureWZ2Node05V4RichTwoScaleCellPullbackData.sourcePopularRegion,
    ← volumePopular.continuous.popularHeights_eq] at hsource
  exact hsource.2

theorem jointSourceSet_height :
    ∀ point ∈ volumePopular.jointSourceSet,
      point (2 : Fin 3) ∈
        Set.Ico volumePopular.jointSlabLeft
          (volumePopular.jointSlabLeft + Real.sqrt rho) := by
  intro point hpoint
  simpa [jointSlabLeft,
    PureWZ2Node05V4RichTwoScaleCellPullbackData.sourcePopularSlabLeft] using
    pullback.standardSqrtSlabSourceRegion_height
      (heightIndex := heightIndex.1.1) (point := point)
      (volumePopular.jointSourceSet_subset_standardSlab hpoint)

theorem jointSourceSet_volume_pos :
    0 < volume volumePopular.jointSourceSet := by
  rcases volumePopular.popular.heightIndices_nonempty with
    ⟨selectedHeight, hselectedHeight⟩
  apply volumePopular.popular.layerMass_pos.trans_le
  calc
    volumePopular.popular.layerMass ≤
        volume (volumePopular.sourcePopularShading.union ∩
          wz1Lemma23HeightSlab (256 * rho) selectedHeight) :=
      (volumePopular.popular.layer_volume_band
        selectedHeight hselectedHeight).1
    _ ≤ volume volumePopular.jointSourceSet := by
      rw [jointSourceSet, volumePopular.popular.union_eq]
      rw [volumePopular.popular.heightRegion_eq]
      exact measure_mono (by
        intro point hpoint
        exact ⟨hpoint.1, Set.mem_iUnion₂.mpr
          ⟨selectedHeight, hselectedHeight, hpoint.2⟩⟩)

theorem jointSourceSet_volume_ne_top :
    volume volumePopular.jointSourceSet ≠ ⊤ := by
  have hball :
      volumePopular.jointSourceSet ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hnorm :=
      norm_le_two_of_mem_paperShading
        (volumePopular.jointSourceSet_subset_current hpoint)
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  exact ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
    (measure_mono hball)

theorem jointPopularHalfMass :
    volume volumePopular.jointSourceSet / 2 ≤
      ∫⁻ height in volumePopular.jointPopularHeights,
        pureWZ2SourceCommonBinSliceMass
          volumePopular.jointSourceSet height := by
  exact pureWZ2SourceCommonBinPopularHalfMass
    volumePopular.jointSourceSet volumePopular.jointSourceSet_measurable
    volumePopular.jointSourceSet_volume_ne_top
    (Real.sqrt_pos.mpr <| by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos)
    volumePopular.jointSourceSet_height

theorem jointPopularHeights_measurable :
    MeasurableSet volumePopular.jointPopularHeights :=
  measurableSet_pureWZ2SourceCommonBinPopularHeights
    volumePopular.jointSourceSet volumePopular.jointSourceSet_measurable
    volumePopular.jointSlabLeft (Real.sqrt rho)

theorem jointPopularThreshold_pos :
    0 < pureWZ2SourceCommonBinPopularThreshold
      volumePopular.jointSourceSet (Real.sqrt rho) := by
  unfold pureWZ2SourceCommonBinPopularThreshold
    pureWZ2CommonBinPopularThreshold
  apply ENNReal.div_pos
  · exact (ENNReal.div_pos
      volumePopular.jointSourceSet_volume_pos.ne' (by norm_num)).ne'
  · exact ENNReal.ofReal_ne_top

theorem jointPopularHeight_mem_ZS
    {height : ℝ} (hheight : height ∈ volumePopular.jointPopularHeights) :
    height ∈ volumePopular.continuous.popularHeights := by
  have hslicePos :
      0 < pureWZ2SourceCommonBinSliceMass
        volumePopular.jointSourceSet height :=
    volumePopular.jointPopularThreshold_pos.trans_le hheight.2
  rcases nonempty_of_measure_ne_zero hslicePos.ne' with
    ⟨planarPoint, hplanarPoint⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hplanarPoint
  simpa [point3] using volumePopular.jointSourceSet_height_mem_ZS hlift

theorem jointPopularHeight_mem_paperRange
    {height : ℝ} (hheight : height ∈ volumePopular.jointPopularHeights) :
    height ∈ Set.Icc (-1 : ℝ) 1 :=
  pullback.sourcePopularHeight_mem_paperRange
    heightIndex.1.2 (by
      rw [← volumePopular.continuous.popularHeights_eq]
      exact volumePopular.jointPopularHeight_mem_ZS hheight)

theorem jointPopularHeights_close
    {first second : ℝ}
    (hfirst : first ∈ volumePopular.jointPopularHeights)
    (hsecond : second ∈ volumePopular.jointPopularHeights) :
    |first - second| ≤ Real.sqrt rho := by
  have hfirstInterval := hfirst.1
  have hsecondInterval := hsecond.1
  rw [abs_le]
  constructor
  · linarith [hfirstInterval.1, hsecondInterval.2]
  · linarith [hfirstInterval.2, hsecondInterval.1]

theorem jointPopularHeights_nonempty :
    volumePopular.jointPopularHeights.Nonempty := by
  have hmassPos :
      0 < ∫⁻ height in volumePopular.jointPopularHeights,
        pureWZ2SourceCommonBinSliceMass
          volumePopular.jointSourceSet height := by
    have hhalfPos :
        0 < volume volumePopular.jointSourceSet / 2 :=
      ENNReal.div_pos volumePopular.jointSourceSet_volume_pos.ne' (by norm_num)
    exact hhalfPos.trans_le volumePopular.jointPopularHalfMass
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hmassPos
  simp at hmassPos

theorem joint_slice_y_abs_le_one
    (height : ℝ) :
    ∀ point ∈ horizontalSlice volumePopular.jointSourceSet height,
      |point (1 : Fin 3)| ≤ 1 := by
  intro point hpoint
  have hcurrent :=
    volumePopular.jointSourceSet_subset_current hpoint.1
  have hbox := shading_union_subset_axisBox hcurrent
  simpa using hbox.2.1

theorem joint_slice_ad_root
    (height : ℝ) (hheight : height ∈ Set.Icc (-1 : ℝ) 1) :
    IsADSet1
      (scalarProjection
        (globalGrainDirection (current.grain.globalGrains.slope height))
        (horizontalSlice volumePopular.jointSourceSet height))
      (Real.sqrt rho) (1 - sigma)
      (2 * Kakeya.realRpowENN delta (-inputLoss)) := by
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.2
  have hdeltaRho : delta ≤ rho := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.1
  have hrhoRoot : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho]
  have hpaper :
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope height))
          (horizontalSlice volumePopular.jointSourceSet height))
        delta (1 - sigma)
        (Kakeya.realRpowENN delta (-inputLoss)) := by
    apply (current.grain.globalGrains.global_ad height hheight).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point,
      ⟨volumePopular.jointSourceSet_subset_current hpoint.1, hpoint.2⟩,
      rfl⟩
  have hbounded :
      scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope height))
          (horizontalSlice volumePopular.jointSourceSet height) ⊆
        Set.Icc (-4 : ℝ) 4 := by
    rintro value ⟨point, hpoint, rfl⟩
    have hbox := shading_union_subset_axisBox
      (volumePopular.jointSourceSet_subset_current hpoint.1)
    have hx : |point 0| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.1
    have hy : |point 1| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    have hslope := current.grain.globalGrains.slope_bound height hheight
    have hformula :
        inner ℝ point
            (globalGrainDirection
              (current.grain.globalGrains.slope height)) =
          point 0 + current.grain.globalGrains.slope height * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    change inner ℝ point
        (globalGrainDirection
          (current.grain.globalGrains.slope height)) ∈ Set.Icc (-4 : ℝ) 4
    rw [hformula]
    apply abs_le.mp
    calc
      |point 0 + current.grain.globalGrains.slope height * point 1| ≤
          |point 0| +
            |current.grain.globalGrains.slope height| * |point 1| := by
        simpa [abs_mul] using abs_add_le (point 0)
          (current.grain.globalGrains.slope height * point 1)
      _ ≤ 1 + 3 * 1 := by gcongr
      _ = 4 := by norm_num
  have hdelta :
      IsADSet1
        (scalarProjection
          (globalGrainDirection (current.grain.globalGrains.slope height))
          (horizontalSlice volumePopular.jointSourceSet height))
        delta (1 - sigma)
        (2 * Kakeya.realRpowENN delta (-inputLoss)) :=
    hpaper.toIsADSet1 hbounded
  exact hdelta.coarsen_scale
    (Real.sqrt_pos.mpr hrho)
    (hdeltaRho.trans hrhoRoot)
    (Real.sqrt_le_one.mpr hrhoOne)

theorem jointCommonBinSlice_occupiedBound
    (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rho) :
    ((pureWZ2OccupiedCommonBins
      (horizontalSlice volumePopular.jointSourceSet height)
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho)).card : ENNReal) ≤
        264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) := by
  have hrhoOne : rho ≤ 1 := by
    rw [← pullback.rhoRequested_eq]
    exact rhoRequested.property.2
  have hbound :=
    pureWZ2_fixed_common_bin_occupied_bound
      (horizontalSlice volumePopular.jointSourceSet height)
      current.grain.globalGrains.slope
      current.grain.globalGrains.slope_lipschitz
      height referenceHeight hheight hreference hclose
      (volumePopular.joint_slice_y_abs_le_one height)
      (volumePopular.joint_slice_ad_root height hheight)
      (Real.sqrt_le_one.mpr hrhoOne)
  calc
    _ ≤ 132 * (2 * Kakeya.realRpowENN delta (-inputLoss)) *
        Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) := hbound
    _ = 264 * Kakeya.realRpowENN delta (-inputLoss) *
        Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) := by ring

theorem jointCommonBinSliceMass_sum
    (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rho) :
    pureWZ2SourceCommonBinSliceMass volumePopular.jointSourceSet height =
      ∑ bin ∈ pureWZ2OccupiedCommonBins
        (horizontalSlice volumePopular.jointSourceSet height)
        current.grain.globalGrains.slope referenceHeight (Real.sqrt rho),
        pureWZ2FixedCommonBinSliceMass volumePopular.jointSourceSet
          current.grain.globalGrains.slope referenceHeight
          (Real.sqrt rho) height bin := by
  simpa [pureWZ2SourceCommonBinSliceMass] using
    pureWZ2_fixed_common_bin_sliceMass_sum
      volumePopular.jointSourceSet_measurable
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho) height
      (pureWZ2OccupiedCommonBins
        (horizontalSlice volumePopular.jointSourceSet height)
        current.grain.globalGrains.slope referenceHeight (Real.sqrt rho))
      (fun point hpoint =>
        pureWZ2_fixed_common_bin_mem
          (horizontalSlice volumePopular.jointSourceSet height)
          current.grain.globalGrains.slope
          current.grain.globalGrains.slope_lipschitz
          height referenceHeight hheight hreference hclose
          (volumePopular.joint_slice_y_abs_le_one height)
          (volumePopular.joint_slice_ad_root height hheight)
          (Real.sqrt_le_one.mpr <| by
            rw [← pullback.rhoRequested_eq]
            exact rhoRequested.property.2)
          hpoint)

theorem jointFixedCommonBinSliceMass_measurable
    (referenceHeight : ℝ) (bin : ℤ) :
    Measurable (fun height : ℝ =>
      pureWZ2FixedCommonBinSliceMass volumePopular.jointSourceSet
        current.grain.globalGrains.slope referenceHeight
        (Real.sqrt rho) height bin) :=
  measurable_volume_wz1Lemma23PlanarSlice
    (pureWZ2FixedCommonBinRegion volumePopular.jointSourceSet
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho) bin)
    (measurableSet_pureWZ2FixedCommonBinRegion
      volumePopular.jointSourceSet_measurable
      current.grain.globalGrains.slope referenceHeight (Real.sqrt rho) bin)

private theorem jointCommonBinSliceMass_ne_top (height : ℝ) :
    pureWZ2SourceCommonBinSliceMass volumePopular.jointSourceSet height ≠ ⊤ := by
  have hsubset :
      wz1Lemma23PlanarSlice volumePopular.jointSourceSet height ⊆
        Metric.closedBall (0 : Point2) 2 := by
    intro point hpoint
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hbox := shading_union_subset_axisBox
      (volumePopular.jointSourceSet_subset_current hlift)
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
    (measure_mono hsubset)

/-- The joint source mass is controlled by integrated rich fixed-bin labels.
All heights and points still come from the prior continuous paper `Z_S`. -/
theorem jointRichCommonBin_integratedMass
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ volumePopular.jointPopularHeights)
    (B₀ threshold : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          volumePopular.jointSourceSet (Real.sqrt rho)) :
    volume volumePopular.jointSourceSet ≤
      4 * ∑ bin ∈ volumePopular.jointRichCommonBinLabels
          referenceHeight threshold,
        volumePopular.jointIntegratedBinMass referenceHeight bin := by
  let E := volumePopular.jointSourceSet
  let heights := volumePopular.jointPopularHeights
  let richLabels :=
    volumePopular.jointRichCommonBinLabels referenceHeight threshold
  let sliceMass : ℝ → ENNReal :=
    pureWZ2SourceCommonBinSliceMass E
  let binMass : ℝ → ℤ → ENNReal := fun height bin =>
    pureWZ2FixedCommonBinSliceMass E
      current.grain.globalGrains.slope referenceHeight
      (Real.sqrt rho) height bin
  have hreferenceRange :=
    volumePopular.jointPopularHeight_mem_paperRange hreference
  have hpointwise : ∀ height ∈ heights,
      sliceMass height ≤ 2 * ∑ bin ∈ richLabels, binMass height bin := by
    intro height hheight
    have hheightOriginal :
        height ∈ volumePopular.jointPopularHeights := by
      simpa [heights] using hheight
    have hheightRange :=
      volumePopular.jointPopularHeight_mem_paperRange hheightOriginal
    have hclose :=
      volumePopular.jointPopularHeights_close hheightOriginal hreference
    let bins := pureWZ2OccupiedCommonBins
      (horizontalSlice E height) current.grain.globalGrains.slope
      referenceHeight (Real.sqrt rho)
    have htotalEq :
        sliceMass height = ∑ bin ∈ bins, binMass height bin := by
      simpa [bins, sliceMass, binMass, E] using
        volumePopular.jointCommonBinSliceMass_sum
          referenceHeight height hreferenceRange hheightRange hclose
    have hcard : (bins.card : ENNReal) ≤ B₀ := by
      simpa [bins, E] using
        (volumePopular.jointCommonBinSlice_occupiedBound
          referenceHeight height hreferenceRange hheightRange hclose).trans hB₀
    have hpoor :
        2 * ((bins.card : ENNReal) * threshold) ≤ sliceMass height := by
      calc
        _ ≤ 2 * (B₀ * threshold) := by gcongr
        _ = 2 * B₀ * threshold := by ring
        _ ≤ pureWZ2SourceCommonBinPopularThreshold E
            (Real.sqrt rho) := by simpa [E] using hthresholdBudget
        _ ≤ pureWZ2SourceCommonBinSliceMass E height := hheightOriginal.2
        _ = sliceMass height := rfl
    have hretained := CommonBinRichSelection.total_le_two_mul_rich_sum
      bins (binMass height) threshold (sliceMass height) htotalEq
      (by simpa [sliceMass, E] using
        volumePopular.jointCommonBinSliceMass_ne_top height)
      hpoor
    have hsubset :
        CommonBinRichSelection.richBins
          bins (binMass height) threshold ⊆ richLabels := by
      intro bin hbin
      have hbinData := Finset.mem_filter.mp hbin
      have hambient : bin ∈ pureWZ2OccupiedCommonBins E
          current.grain.globalGrains.slope referenceHeight
          (Real.sqrt rho) := by
        have hbinOccupied := hbinData.1
        dsimp only [bins] at hbinOccupied
        rw [pureWZ2OccupiedCommonBins, Finset.mem_filter] at hbinOccupied ⊢
        refine ⟨hbinOccupied.1, ?_⟩
        rcases hbinOccupied.2 with ⟨point, hpoint, hlabel⟩
        exact ⟨point, hpoint.1, hlabel⟩
      change bin ∈ volumePopular.jointRichCommonBinLabels
        referenceHeight threshold
      rw [jointRichCommonBinLabels, Finset.mem_filter]
      exact ⟨hambient, height, hheight, hheightRange, hbinData.2⟩
    exact hretained.trans <| mul_le_mul_right
      (Finset.sum_le_sum_of_subset hsubset) 2
  have hbinMassMeas : ∀ bin : ℤ,
      Measurable (fun height => binMass height bin) := by
    intro bin
    simpa [binMass, E] using
      volumePopular.jointFixedCommonBinSliceMass_measurable
        referenceHeight bin
  have hintegratedPointwise :
      (∫⁻ height in heights, sliceMass height) ≤
        2 * ∫⁻ height in heights,
          ∑ bin ∈ richLabels, binMass height bin := by
    calc
      _ ≤ ∫⁻ height in heights,
          2 * ∑ bin ∈ richLabels, binMass height bin :=
        setLIntegral_mono'
          (by simpa [heights] using
            volumePopular.jointPopularHeights_measurable) hpointwise
      _ = _ := MeasureTheory.lintegral_const_mul 2
        (Finset.measurable_sum richLabels fun bin _ => hbinMassMeas bin)
  have hsumIntegral :
      (∫⁻ height in heights,
        ∑ bin ∈ richLabels, binMass height bin) =
      ∑ bin ∈ richLabels,
        volumePopular.jointIntegratedBinMass referenceHeight bin := by
    rw [MeasureTheory.lintegral_finsetSum richLabels]
    · rfl
    · intro bin _
      exact hbinMassMeas bin
  have hpopularHalf :
      volume E / 2 ≤ ∫⁻ height in heights, sliceMass height := by
    simpa [E, heights, sliceMass] using volumePopular.jointPopularHalfMass
  calc
    volume E = volume E / 2 + volume E / 2 :=
      (ENNReal.add_halves _).symm
    _ ≤ (∫⁻ height in heights, sliceMass height) +
        ∫⁻ height in heights, sliceMass height := by gcongr
    _ = 2 * ∫⁻ height in heights, sliceMass height := by ring
    _ ≤ 2 * (2 * ∫⁻ height in heights,
        ∑ bin ∈ richLabels, binMass height bin) := by gcongr
    _ = 4 * ∑ bin ∈ richLabels,
        volumePopular.jointIntegratedBinMass referenceHeight bin := by
      rw [hsumIntegral]
      ring

/-- Select one runtime reference height and one integrated fixed-bin label
from the same joint source witness. -/
structure JointHeightCommonBinData
    (B₀ threshold : ENNReal) where
  referenceHeight : ℝ
  referenceHeight_mem :
    referenceHeight ∈ volumePopular.jointPopularHeights
  bin : ℤ
  bin_mem :
    bin ∈ volumePopular.jointRichCommonBinLabels referenceHeight threshold
  source_average :
    volume volumePopular.jointSourceSet ≤
      4 * ((volumePopular.jointRichCommonBinLabels
        referenceHeight threshold).card : ENNReal) *
        volumePopular.jointIntegratedBinMass referenceHeight bin

theorem jointHeightCommonBin
    (B₀ threshold : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          volumePopular.jointSourceSet (Real.sqrt rho)) :
    Nonempty (volumePopular.JointHeightCommonBinData B₀ threshold) := by
  let referenceHeight := Classical.choose volumePopular.jointPopularHeights_nonempty
  have hreference : referenceHeight ∈ volumePopular.jointPopularHeights :=
    Classical.choose_spec volumePopular.jointPopularHeights_nonempty
  have hretained := volumePopular.jointRichCommonBin_integratedMass
    referenceHeight hreference B₀ threshold hB₀ hthresholdBudget
  rcases CommonBinIntegratedAveraging.exists_label_of_total_le_sum
      (volumePopular.jointRichCommonBinLabels referenceHeight threshold)
      (volumePopular.jointIntegratedBinMass referenceHeight)
      (volume volumePopular.jointSourceSet) 4
      volumePopular.jointSourceSet_volume_pos hretained with
    ⟨bin, hbin, haverage⟩
  exact ⟨{
    referenceHeight := referenceHeight
    referenceHeight_mem := hreference
    bin := bin
    bin_mem := hbin
    source_average := haverage
  }⟩

/-- Select the integrated common bin at a reference height fixed by an earlier
paper step.  In the Lemma-5.4 application this is the `z₀ ∈ Z_S` already
stored by the genuine coarse-neighborhood witness, so no second reference
height is selected here. -/
theorem jointHeightCommonBinAt
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ volumePopular.jointPopularHeights)
    (B₀ threshold : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          volumePopular.jointSourceSet (Real.sqrt rho)) :
    Nonempty (volumePopular.JointHeightCommonBinData B₀ threshold) := by
  have hretained := volumePopular.jointRichCommonBin_integratedMass
    referenceHeight hreference B₀ threshold hB₀ hthresholdBudget
  rcases CommonBinIntegratedAveraging.exists_label_of_total_le_sum
      (volumePopular.jointRichCommonBinLabels referenceHeight threshold)
      (volumePopular.jointIntegratedBinMass referenceHeight)
      (volume volumePopular.jointSourceSet) 4
      volumePopular.jointSourceSet_volume_pos hretained with
    ⟨bin, hbin, haverage⟩
  exact ⟨{
    referenceHeight := referenceHeight
    referenceHeight_mem := hreference
    bin := bin
    bin_mem := hbin
    source_average := haverage
  }⟩

end PureWZ2Node05V4RichSourceVolumePopularHeightData

end Kakeya.Assouad

end
