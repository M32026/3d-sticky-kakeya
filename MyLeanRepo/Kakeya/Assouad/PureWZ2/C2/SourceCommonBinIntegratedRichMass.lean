import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinDistinctRichLabels

/-!
# Integrated mass of distinct rich common-bin labels

This module performs the averaging in height which is needed before choosing
one fixed common-bin label.  Every slice uses the same `referenceHeight`.
The rich-label family is the finite set of distinct labels from
`SourceCommonBinDistinctRichLabels`; labels are not counted again when they
are rich at several heights.

The only threshold input is the literal multiplicative poor-bin budget

`2 * B₀ * threshold ≤ m_*`.

Together with the pointwise occupied-bin bound by `B₀`, this retains one half
of every popular slice.  Tonelli for a finite measurable sum then retains one
quarter of the source slab.  No graph budget or joint-envelope density is
used.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2SourceCarrierWindow

/-- The mass of one fixed common-bin label, integrated over a supplied set of
heights. -/
def integratedBinMass
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ) (heights : Set ℝ) (bin : ℤ) : ENNReal :=
  ∫⁻ height in heights,
    pureWZ2FixedCommonBinSliceMass
      window.shading.union source.globalGrains.slope
      referenceHeight (Real.sqrt rho) height bin

/-- The slice-mass integrand of a fixed common-bin label is measurable. -/
theorem measurable_commonBinSliceMass
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ) (bin : ℤ) :
    Measurable (fun height : ℝ =>
      pureWZ2FixedCommonBinSliceMass
        window.shading.union source.globalGrains.slope
        referenceHeight (Real.sqrt rho) height bin) := by
  exact measurable_volume_wz1Lemma23PlanarSlice
    (pureWZ2FixedCommonBinRegion
      window.shading.union source.globalGrains.slope
      referenceHeight (Real.sqrt rho) bin)
    (measurableSet_pureWZ2FixedCommonBinRegion
      (measurableSet_shading_union window.shading)
      source.globalGrains.slope referenceHeight (Real.sqrt rho) bin)

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

private theorem slice_y_abs_le_one
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (height : ℝ) :
    ∀ point ∈ horizontalSlice window.shading.union height,
      |point (1 : Fin 3)| ≤ 1 := by
  intro point hpoint
  have hsource : point ∈ source.shading.union :=
    window.union_subset_source hpoint.1
  have hbox := shading_union_subset_axisBox hsource
  simpa [Kakeya.Streamlined.axisBox] using hbox.2.1

private theorem slice_ad_root
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (height : ℝ) (hheight : height ∈ Set.Icc (-1 : ℝ) 1) :
    IsADSet1
      (scalarProjection
        (globalGrainDirection (source.globalGrains.slope height))
        (horizontalSlice window.shading.union height))
      (Real.sqrt rho) (1 - sigma)
      (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hrhoRoot : rho ≤ Real.sqrt rho := by
    nlinarith [Real.sq_sqrt hrho.le, Real.sqrt_nonneg rho]
  have hADrho :
      IsADSet1
        (scalarProjection
          (globalGrainDirection (source.globalGrains.slope height))
          (horizontalSlice window.shading.union height))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    apply (prepared.exactAD height hheight).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact
      ⟨point,
        ⟨window.subshading.union_subset hpoint.1, hpoint.2⟩,
        rfl⟩
  exact hADrho.coarsen_scale
    (Real.sqrt_pos.mpr hrho) hrhoRoot (Real.sqrt_le_one.mpr hrhoOne)

/-- At every admissible height, the number of occupied bins in the common
reference lattice obeys the same `B₀` estimate. -/
theorem commonBinSlice_occupiedBound
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rho) :
    ((pureWZ2OccupiedCommonBins
      (horizontalSlice window.shading.union height)
      source.globalGrains.slope referenceHeight
      (Real.sqrt rho)).card : ENNReal) ≤
        132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) := by
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  exact pureWZ2_fixed_common_bin_occupied_bound
    (horizontalSlice window.shading.union height)
    source.globalGrains.slope
    source.globalGrains.slope_lipschitz
    height referenceHeight hheight hreference hclose
    (window.slice_y_abs_le_one height)
    (window.slice_ad_root height hheight)
    (Real.sqrt_le_one.mpr hrhoOne)

private theorem fixedCommonBinLabel_mem_sliceOccupied
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rho)
    {point : Point3}
    (hpoint : point ∈ horizontalSlice window.shading.union height) :
    pureWZ2FixedCommonBinLabel source.globalGrains.slope
        referenceHeight (Real.sqrt rho) point ∈
      pureWZ2OccupiedCommonBins
        (horizontalSlice window.shading.union height)
        source.globalGrains.slope referenceHeight (Real.sqrt rho) := by
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  exact pureWZ2_fixed_common_bin_mem
    (horizontalSlice window.shading.union height)
    source.globalGrains.slope
    source.globalGrains.slope_lipschitz
    height referenceHeight hheight hreference hclose
    (window.slice_y_abs_le_one height)
    (window.slice_ad_root height hheight)
    (Real.sqrt_le_one.mpr hrhoOne) hpoint

/-- The occupied common bins at one height form an exact finite partition of
that planar slice. -/
theorem commonBinSliceMass_sum
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight height : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (hheight : height ∈ Set.Icc (-1 : ℝ) 1)
    (hclose : |height - referenceHeight| ≤ Real.sqrt rho) :
    pureWZ2SourceCommonBinSliceMass window.shading.union height =
      ∑ bin ∈
        pureWZ2OccupiedCommonBins
          (horizontalSlice window.shading.union height)
          source.globalGrains.slope referenceHeight (Real.sqrt rho),
        pureWZ2FixedCommonBinSliceMass
          window.shading.union source.globalGrains.slope
          referenceHeight (Real.sqrt rho) height bin := by
  simpa [pureWZ2SourceCommonBinSliceMass] using
    pureWZ2_fixed_common_bin_sliceMass_sum
      (measurableSet_shading_union window.shading)
      source.globalGrains.slope referenceHeight (Real.sqrt rho) height
      (pureWZ2OccupiedCommonBins
        (horizontalSlice window.shading.union height)
        source.globalGrains.slope referenceHeight (Real.sqrt rho))
      (fun point hpoint =>
        window.fixedCommonBinLabel_mem_sliceOccupied
          referenceHeight height hreference hheight hclose hpoint)

private theorem commonBinSliceMass_ne_top
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (height : ℝ) :
    pureWZ2SourceCommonBinSliceMass window.shading.union height ≠ ⊤ := by
  have hball :
      window.shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hnorm :=
      norm_le_two_of_mem_paperShading (window.union_subset_source hpoint)
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hupper :=
    wz1_lemma23_exactSlice_area_le_two
      window.shading source.extremal.delta_pos hball height
  apply ne_top_of_le_ne_top
    (show
      ((wz1Lemma23ExactSliceCells window.shading delta
          source.extremal.delta_pos height).card : ENNReal) *
          (ENNReal.ofReal delta ^ 2 * ENNReal.ofReal Real.pi) ≠ ⊤ by
      exact ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top
          (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
          ENNReal.ofReal_ne_top))
  simpa [pureWZ2SourceCommonBinSliceMass] using hupper

end PureWZ2SourceCarrierWindow

namespace PureWZ2BalancedSafeWindowData

private theorem sourceSlabVolume_pos
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {left : ℝ}
    (data : PureWZ2BalancedSafeWindowData prepared left) :
    0 < volume data.shading.union := by
  rw [data.volume_eq]
  apply ENNReal.mul_pos
  · simpa using (Finset.card_pos.mpr data.cells_nonempty).ne'
  · exact twoScale.coarse.balanced.cellMass_pos.ne'

/-- Every popular source-slab height is a genuine paper height. -/
theorem commonBinPopularHeight_mem_paperRange
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {left : ℝ}
    (data : PureWZ2BalancedSafeWindowData prepared left)
    {height : ℝ}
    (hheight : height ∈
      pureWZ2SourceCommonBinPopularHeights
        data.shading.union left (Real.sqrt rho)) :
    height ∈ Set.Icc (-1 : ℝ) 1 := by
  have hthresholdPos :
      0 <
        pureWZ2SourceCommonBinPopularThreshold
          data.shading.union (Real.sqrt rho) := by
    unfold pureWZ2SourceCommonBinPopularThreshold
      pureWZ2CommonBinPopularThreshold
    have htwoTop : (2 : ENNReal) ≠ ⊤ := by norm_num
    have hrootTop :
        ENNReal.ofReal (Real.sqrt rho) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    exact ENNReal.div_pos
      (ENNReal.div_pos data.sourceSlabVolume_pos.ne' htwoTop).ne'
      hrootTop
  have hslicePos :
      0 < pureWZ2SourceCommonBinSliceMass data.shading.union height :=
    hthresholdPos.trans_le hheight.2
  rcases MeasureTheory.nonempty_of_measure_ne_zero hslicePos.ne' with
    ⟨point, hpoint⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
  have hwindowPoint : point3 (point 0) (point 1) height ∈
      data.window.shading.union := by
    rw [data.window_shading]
    exact hlift
  have hsource : point3 (point 0) (point 1) height ∈
      source.shading.union :=
    data.window.union_subset_source hwindowPoint
  have hbox := shading_union_subset_axisBox hsource
  simpa [point3, Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2

/-- Two heights in the same popular side-`sqrt rho` slab differ by at most
`sqrt rho`. -/
theorem commonBinPopularHeights_close
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {left : ℝ}
    (data : PureWZ2BalancedSafeWindowData prepared left)
    {first second : ℝ}
    (hfirst : first ∈
      pureWZ2SourceCommonBinPopularHeights
        data.shading.union left (Real.sqrt rho))
    (hsecond : second ∈
      pureWZ2SourceCommonBinPopularHeights
        data.shading.union left (Real.sqrt rho)) :
    |first - second| ≤ Real.sqrt rho := by
  rw [abs_le]
  constructor <;> linarith [hfirst.1.1, hfirst.1.2,
    hsecond.1.1, hsecond.1.2]

/-- Integrated rich-label retention on the literal popular-height set.

The premise `hthresholdBudget` is the exact multiplicative version of
`threshold = m_* / (2 * B₀)`. -/
theorem distinctRichCommonBin_integratedMass
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {left : ℝ}
    (data : PureWZ2BalancedSafeWindowData prepared left)
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈
      pureWZ2SourceCommonBinPopularHeights
        data.shading.union left (Real.sqrt rho))
    (B₀ threshold : ENNReal)
    (hB₀ :
      132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          data.shading.union (Real.sqrt rho)) :
    volume data.shading.union ≤
      4 * ∑ bin ∈
        data.window.distinctRichCommonBinLabels
          referenceHeight
          (pureWZ2SourceCommonBinPopularHeights
            data.shading.union left (Real.sqrt rho))
          threshold,
        data.window.integratedBinMass
          referenceHeight
          (pureWZ2SourceCommonBinPopularHeights
            data.shading.union left (Real.sqrt rho))
          bin := by
  let heights :=
    pureWZ2SourceCommonBinPopularHeights
      data.shading.union left (Real.sqrt rho)
  let richLabels :=
    data.window.distinctRichCommonBinLabels
      referenceHeight heights threshold
  let sliceMass : ℝ → ENNReal :=
    pureWZ2SourceCommonBinSliceMass data.shading.union
  let binMass : ℝ → ℤ → ENNReal := fun height bin =>
    pureWZ2FixedCommonBinSliceMass
      data.window.shading.union source.globalGrains.slope
      referenceHeight (Real.sqrt rho) height bin
  have hreferenceRange :
      referenceHeight ∈ Set.Icc (-1 : ℝ) 1 :=
    data.commonBinPopularHeight_mem_paperRange hreference
  have hpointwise :
      ∀ height ∈ heights,
        sliceMass height ≤
          2 * ∑ bin ∈ richLabels, binMass height bin := by
    intro height hheight
    have hheightOriginal :
        height ∈ pureWZ2SourceCommonBinPopularHeights
          data.shading.union left (Real.sqrt rho) := by
      simpa [heights] using hheight
    have hheightRange :
        height ∈ Set.Icc (-1 : ℝ) 1 :=
      data.commonBinPopularHeight_mem_paperRange hheightOriginal
    have hclose : |height - referenceHeight| ≤ Real.sqrt rho :=
      data.commonBinPopularHeights_close hheightOriginal hreference
    let bins :=
      pureWZ2OccupiedCommonBins
        (horizontalSlice data.window.shading.union height)
        source.globalGrains.slope referenceHeight (Real.sqrt rho)
    have htotalEq :
        sliceMass height = ∑ bin ∈ bins, binMass height bin := by
      have hsum :=
        data.window.commonBinSliceMass_sum
          referenceHeight height hreferenceRange hheightRange hclose
      calc
        sliceMass height =
            pureWZ2SourceCommonBinSliceMass
              data.window.shading.union height := by
          simp only [sliceMass]
          rw [data.window_shading]
        _ = ∑ bin ∈ bins, binMass height bin := by
          simpa [binMass, bins] using hsum
    have hcard :
        (bins.card : ENNReal) ≤ B₀ := by
      exact (by
        simpa [bins] using
          (data.window.commonBinSlice_occupiedBound
            referenceHeight height hreferenceRange hheightRange hclose).trans
            hB₀)
    have hpoor :
        2 * ((bins.card : ENNReal) * threshold) ≤ sliceMass height := by
      calc
        2 * ((bins.card : ENNReal) * threshold) ≤
            2 * (B₀ * threshold) := by gcongr
        _ = 2 * B₀ * threshold := by ring
        _ ≤
            pureWZ2SourceCommonBinPopularThreshold
              data.shading.union (Real.sqrt rho) :=
          hthresholdBudget
        _ ≤ pureWZ2SourceCommonBinSliceMass
              data.shading.union height :=
          hheightOriginal.2
        _ = sliceMass height := by rfl
    have hsliceTop : sliceMass height ≠ ⊤ := by
      have htop := data.window.commonBinSliceMass_ne_top height
      rw [data.window_shading] at htop
      exact htop
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
            data.window.shading.union source.globalGrains.slope
            referenceHeight (Real.sqrt rho) := by
        have hbinOccupied := hbinData.1
        dsimp only [bins] at hbinOccupied
        rw [pureWZ2OccupiedCommonBins, Finset.mem_filter] at hbinOccupied
        rw [pureWZ2OccupiedCommonBins, Finset.mem_filter]
        refine ⟨hbinOccupied.1, ?_⟩
        rcases hbinOccupied.2 with ⟨point, hpoint, hlabel⟩
        exact ⟨point, hpoint.1, hlabel⟩
      change bin ∈ data.window.distinctRichCommonBinLabels
        referenceHeight heights threshold
      rw [PureWZ2SourceCarrierWindow.distinctRichCommonBinLabels,
        Finset.mem_filter]
      refine ⟨hambient, height, hheight, hheightRange, ?_⟩
      exact hbinData.2
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
      data.shading.union (measurableSet_shading_union data.shading)
      left (Real.sqrt rho)
  have hbinMassMeas :
      ∀ bin : ℤ, Measurable (fun height => binMass height bin) := by
    intro bin
    exact data.window.measurable_commonBinSliceMass referenceHeight bin
  have hrichSumMeas :
      Measurable (fun height =>
        ∑ bin ∈ richLabels, binMass height bin) := by
    exact Finset.measurable_sum richLabels fun bin _ => hbinMassMeas bin
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
            ∑ bin ∈ richLabels, binMass height bin := by
        exact MeasureTheory.lintegral_const_mul 2 hrichSumMeas
  have hsumIntegral :
      (∫⁻ height in heights,
        ∑ bin ∈ richLabels, binMass height bin) =
      ∑ bin ∈ richLabels,
        data.window.integratedBinMass referenceHeight heights bin := by
    rw [MeasureTheory.lintegral_finsetSum richLabels]
    · rfl
    · intro bin _
      exact hbinMassMeas bin
  have hhalf :
      volume data.shading.union / 2 ≤
        ∫⁻ height in heights, sliceMass height := by
    have hpopular := data.commonBinPopularHalfMass
    simpa [heights, sliceMass] using hpopular
  calc
    volume data.shading.union =
        volume data.shading.union / 2 +
          volume data.shading.union / 2 :=
      (ENNReal.add_halves _).symm
    _ ≤ (∫⁻ height in heights, sliceMass height) +
          ∫⁻ height in heights, sliceMass height := by
      gcongr
    _ = 2 * ∫⁻ height in heights, sliceMass height := by ring
    _ ≤ 2 * (2 * ∫⁻ height in heights,
          ∑ bin ∈ richLabels, binMass height bin) := by
      gcongr
    _ = 4 * ∑ bin ∈ richLabels,
          data.window.integratedBinMass referenceHeight heights bin := by
      rw [hsumIntegral]
      ring
    _ = 4 * ∑ bin ∈
          data.window.distinctRichCommonBinLabels
            referenceHeight
            (pureWZ2SourceCommonBinPopularHeights
              data.shading.union left (Real.sqrt rho))
            threshold,
          data.window.integratedBinMass
            referenceHeight
            (pureWZ2SourceCommonBinPopularHeights
              data.shading.union left (Real.sqrt rho))
            bin := by
      rfl

end PureWZ2BalancedSafeWindowData

namespace PureWZ2SourceCarrierWindow

/-- If the integrated masses of the distinct rich labels retain one quarter
of `slabMass`, one fixed rich label controls their average. -/
theorem exists_integratedBinMass_lower
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold slabMass : ENNReal)
    (hslabMass : 0 < slabMass)
    (hrichMass :
      slabMass ≤
        4 * ∑ bin ∈
          window.distinctRichCommonBinLabels
            referenceHeight heights threshold,
          window.integratedBinMass referenceHeight heights bin) :
    ∃ bin ∈ window.distinctRichCommonBinLabels
          referenceHeight heights threshold,
      slabMass ≤
        4 *
          ((window.distinctRichCommonBinLabels
            referenceHeight heights threshold).card : ENNReal) *
          window.integratedBinMass referenceHeight heights bin := by
  let richLabels :=
    window.distinctRichCommonBinLabels referenceHeight heights threshold
  have hnonempty : richLabels.Nonempty := by
    by_contra hempty
    have hempty' : richLabels = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero :
        (∑ bin ∈ richLabels,
          window.integratedBinMass referenceHeight heights bin) = 0 := by
      simp [hempty']
    rw [hzero] at hrichMass
    exact (not_le_of_gt hslabMass) (by simpa using hrichMass)
  rcases CommonBinDistinctIncidence.exists_weight_ge_average
      richLabels hnonempty
      (fun bin : {bin // bin ∈ richLabels} =>
        window.integratedBinMass referenceHeight heights bin.1) with
    ⟨selected, haverage⟩
  refine ⟨selected.1, ?_, ?_⟩
  · change selected.1 ∈ richLabels
    exact selected.2
  calc
    slabMass ≤ 4 * ∑ bin ∈ richLabels,
        window.integratedBinMass referenceHeight heights bin := by
      simpa [richLabels] using hrichMass
    _ = 4 * ∑ bin : {bin // bin ∈ richLabels},
        window.integratedBinMass referenceHeight heights bin.1 := by
      rw [Finset.sum_subtype richLabels (fun _ => Iff.rfl)]
    _ ≤ 4 * ((richLabels.card : ENNReal) *
        window.integratedBinMass
          referenceHeight heights selected.1) := by
      gcongr
    _ = 4 * ((richLabels.card : ENNReal)) *
        window.integratedBinMass
          referenceHeight heights selected.1 := by ring
    _ = 4 *
          ((window.distinctRichCommonBinLabels
            referenceHeight heights threshold).card : ENNReal) *
          window.integratedBinMass
            referenceHeight heights selected.1 := by
      rfl

/-- Combine the fixed-label average with an explicit standard-slab incidence
bound and exact source/coarse cross identity.  This is the interface for a
standard coarse slab mass `coarseMass`; it does not identify that mass with
the smaller participating-cell restriction. -/
theorem exists_integratedBinMass_of_incidence_cross
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (referenceHeight : ℝ) (heights : Set ℝ)
    (threshold slabMass coarseMass theta : ENNReal)
    (K : ℕ)
    (hslabMass : 0 < slabMass)
    (hrichMass :
      slabMass ≤
        4 * ∑ bin ∈
          window.distinctRichCommonBinLabels
            referenceHeight heights threshold,
          window.integratedBinMass referenceHeight heights bin)
    (incidence :
      ((window.distinctRichCommonBinLabels
        referenceHeight heights threshold).card : ENNReal) *
          K * twoScale.fine.balanced.cellMass ≤
        5 * coarseMass)
    (cross : slabMass = theta * coarseMass)
    (hcoarseMass : 0 < coarseMass)
    (hcoarseMassTop : coarseMass ≠ ⊤) :
    ∃ bin ∈ window.distinctRichCommonBinLabels
          referenceHeight heights threshold,
      theta * K * twoScale.fine.balanced.cellMass ≤
        20 * window.integratedBinMass referenceHeight heights bin := by
  rcases window.exists_integratedBinMass_lower
      referenceHeight heights threshold slabMass hslabMass hrichMass with
    ⟨selected, hselectedMem, hselectedMass⟩
  refine ⟨selected, hselectedMem, ?_⟩
  apply
    (ENNReal.mul_le_mul_iff_right
      hcoarseMass.ne' hcoarseMassTop).mp
  calc
    coarseMass *
          (theta * K * twoScale.fine.balanced.cellMass) =
        (theta * coarseMass) *
          (K * twoScale.fine.balanced.cellMass) := by ring
    _ = slabMass *
          (K * twoScale.fine.balanced.cellMass) := by rw [cross]
    _ ≤
        (4 *
          ((window.distinctRichCommonBinLabels
            referenceHeight heights threshold).card : ENNReal) *
          window.integratedBinMass
            referenceHeight heights selected) *
          (K * twoScale.fine.balanced.cellMass) := by
      gcongr
    _ =
        4 * window.integratedBinMass
          referenceHeight heights selected *
          (((window.distinctRichCommonBinLabels
            referenceHeight heights threshold).card : ENNReal) *
            K * twoScale.fine.balanced.cellMass) := by ring
    _ ≤
        4 * window.integratedBinMass
          referenceHeight heights selected * (5 * coarseMass) := by
      gcongr
    _ =
        coarseMass *
          (20 * window.integratedBinMass
            referenceHeight heights selected) := by ring

/-- Exact-cross endpoint.  The only cross input is the displayed identity
between the source slab and the literal participating-cell restriction
volume.  The factor `5` comes from distinct-label cell incidence. -/
theorem exists_integratedBinMass_cross
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
    (heights : Set ℝ) (threshold slabMass theta : ENNReal)
    (K : ℕ)
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold)
    (hslabMass : 0 < slabMass)
    (hrichMass :
      slabMass ≤
        4 * ∑ bin ∈
          window.distinctRichCommonBinLabels
            referenceHeight heights threshold,
          window.integratedBinMass referenceHeight heights bin)
    (cross :
      slabMass =
        theta * window.distinctRichCommonBinRestrictionVolume
          referenceHeight heights threshold) :
    ∃ bin ∈ window.distinctRichCommonBinLabels
          referenceHeight heights threshold,
      theta * K * twoScale.fine.balanced.cellMass ≤
        20 * window.integratedBinMass referenceHeight heights bin := by
  let bins :=
    window.distinctRichCommonBinLabels referenceHeight heights threshold
  let cells : ℤ → Finset (ℤ × ℤ × ℤ) :=
    window.distinctRichCommonBinActiveSpatialCells
      referenceHeight heights threshold
  have hselected :=
    window.exists_integratedBinMass_lower
      referenceHeight heights threshold slabMass hslabMass hrichMass
  rcases hselected with ⟨_selected, hselectedMem, _hselectedMass⟩
  have hnonempty : bins.Nonempty :=
    ⟨_selected, by simpa [bins] using hselectedMem⟩
  have hcoarsePos :
      0 < window.distinctRichCommonBinRestrictionVolume
        referenceHeight heights threshold := by
    apply pos_of_mul_pos_right
    · rw [← cross]
      exact hslabMass
    · exact bot_le
  have hcoarseTop :
      window.distinctRichCommonBinRestrictionVolume
        referenceHeight heights threshold ≠ ⊤ := by
    rw [window.distinctRichCommonBinRestrictionVolume_eq
      referenceHeight heights threshold]
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top _)
      twoScale.fine.balanced.cellMass_ne_top
  have hrichMassSubtype :
      slabMass ≤
        4 * ∑ bin : {bin // bin ∈ bins},
          window.integratedBinMass referenceHeight heights bin.1 := by
    rw [← Finset.sum_subtype bins (fun _ => Iff.rfl)]
    simpa [bins] using hrichMass
  rcases CommonBinDistinctIncidence.exists_fixed_bin_mass_lower
      bins hnonempty cells
      K 5 twoScale.fine.balanced.cellMass slabMass
      (window.distinctRichCommonBinRestrictionVolume
        referenceHeight heights threshold)
      theta
      (fun bin : {bin // bin ∈ bins} =>
        window.integratedBinMass referenceHeight heights bin.1)
      (fun bin hbin =>
        by
          simpa [bins, cells] using
            window.distinctRichCommonBin_activeSpatialCells_card_lower
              referenceHeight heights threshold K hK hbin)
      (fun cell _hcell => by
        simpa [bins, cells] using
          window.distinctRichCommonBin_cellDegree_le_five
            referenceHeight hreference heights threshold cell)
      (by
        rw [window.distinctRichCommonBinRestrictionVolume_eq
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
        rw [hcells])
      hrichMassSubtype cross hcoarsePos hcoarseTop with
    ⟨selected, hselected⟩
  refine ⟨selected.1, ?_, ?_⟩
  · change selected.1 ∈ bins
    exact selected.2
  calc
    theta * K * twoScale.fine.balanced.cellMass ≤
        4 * (5 : ENNReal) *
          window.integratedBinMass referenceHeight heights selected.1 := by
      simpa only [Nat.cast_ofNat] using hselected
    _ = 20 *
          window.integratedBinMass referenceHeight heights selected.1 := by
      ring

end PureWZ2SourceCarrierWindow

/-- Select one distinct rich label whose integrated mass controls the source
slab average. -/
theorem PureWZ2BalancedSafeWindowData.exists_integratedRichCommonBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {left : ℝ}
    (data : PureWZ2BalancedSafeWindowData prepared left)
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈
      pureWZ2SourceCommonBinPopularHeights
        data.shading.union left (Real.sqrt rho))
    (B₀ threshold : ENNReal)
    (hB₀ :
      132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          data.shading.union (Real.sqrt rho)) :
    ∃ bin ∈ data.window.distinctRichCommonBinLabels
          referenceHeight
          (pureWZ2SourceCommonBinPopularHeights
            data.shading.union left (Real.sqrt rho))
          threshold,
      volume data.shading.union ≤
        4 *
          ((data.window.distinctRichCommonBinLabels
            referenceHeight
            (pureWZ2SourceCommonBinPopularHeights
              data.shading.union left (Real.sqrt rho))
            threshold).card : ENNReal) *
          data.window.integratedBinMass
            referenceHeight
            (pureWZ2SourceCommonBinPopularHeights
              data.shading.union left (Real.sqrt rho))
            bin := by
  apply data.window.exists_integratedBinMass_lower
    referenceHeight
    (pureWZ2SourceCommonBinPopularHeights
      data.shading.union left (Real.sqrt rho))
    threshold (volume data.shading.union) data.sourceSlabVolume_pos
  exact data.distinctRichCommonBin_integratedMass
    referenceHeight hreference B₀ threshold hB₀ hthresholdBudget

/-- Source-specialized convenience endpoint when the exact cross is already
known for the participating-cell restriction `G_R`. -/
theorem PureWZ2BalancedSafeWindowData.exists_integratedRichCommonBin_restriction_cross
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {left : ℝ}
    (data : PureWZ2BalancedSafeWindowData prepared left)
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈
      pureWZ2SourceCommonBinPopularHeights
        data.shading.union left (Real.sqrt rho))
    (B₀ threshold theta : ENNReal)
    (K : ℕ)
    (hB₀ :
      132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          data.shading.union (Real.sqrt rho))
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold)
    (cross :
      volume data.shading.union =
        theta * data.window.distinctRichCommonBinRestrictionVolume
          referenceHeight
          (pureWZ2SourceCommonBinPopularHeights
            data.shading.union left (Real.sqrt rho))
          threshold) :
    ∃ bin ∈ data.window.distinctRichCommonBinLabels
          referenceHeight
          (pureWZ2SourceCommonBinPopularHeights
            data.shading.union left (Real.sqrt rho))
          threshold,
      theta * K * twoScale.fine.balanced.cellMass ≤
        20 * data.window.integratedBinMass
          referenceHeight
          (pureWZ2SourceCommonBinPopularHeights
            data.shading.union left (Real.sqrt rho))
          bin := by
  apply data.window.exists_integratedBinMass_cross
    referenceHeight
    (data.commonBinPopularHeight_mem_paperRange hreference)
    (pureWZ2SourceCommonBinPopularHeights
      data.shading.union left (Real.sqrt rho))
    threshold (volume data.shading.union) theta K hK
    data.sourceSlabVolume_pos
  · exact data.distinctRichCommonBin_integratedMass
      referenceHeight hreference B₀ threshold hB₀ hthresholdBudget
  · exact cross

/-- Standard-slab exact-cross endpoint.  Here `coarseMass` is an explicit
mathematical input `G_S`; the theorem assumes exactly the incidence
`|R| * K * w_s ≤ 5 * G_S` and cross
`volume sourceSlab = theta * G_S`. -/
theorem PureWZ2BalancedSafeWindowData.exists_integratedRichCommonBin_cross
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {left : ℝ}
    (data : PureWZ2BalancedSafeWindowData prepared left)
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈
      pureWZ2SourceCommonBinPopularHeights
        data.shading.union left (Real.sqrt rho))
    (B₀ threshold coarseMass theta : ENNReal)
    (K : ℕ)
    (hB₀ :
      132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          data.shading.union (Real.sqrt rho))
    (incidence :
      ((data.window.distinctRichCommonBinLabels
        referenceHeight
        (pureWZ2SourceCommonBinPopularHeights
          data.shading.union left (Real.sqrt rho))
        threshold).card : ENNReal) *
          K * twoScale.fine.balanced.cellMass ≤
        5 * coarseMass)
    (cross :
      volume data.shading.union = theta * coarseMass)
    (hcoarseMass : 0 < coarseMass)
    (hcoarseMassTop : coarseMass ≠ ⊤) :
    ∃ bin ∈ data.window.distinctRichCommonBinLabels
          referenceHeight
          (pureWZ2SourceCommonBinPopularHeights
            data.shading.union left (Real.sqrt rho))
          threshold,
      theta * K * twoScale.fine.balanced.cellMass ≤
        20 * data.window.integratedBinMass
          referenceHeight
          (pureWZ2SourceCommonBinPopularHeights
            data.shading.union left (Real.sqrt rho))
          bin := by
  apply data.window.exists_integratedBinMass_of_incidence_cross
    referenceHeight
    (pureWZ2SourceCommonBinPopularHeights
      data.shading.union left (Real.sqrt rho))
    threshold (volume data.shading.union) coarseMass theta K
    data.sourceSlabVolume_pos
  · exact data.distinctRichCommonBin_integratedMass
      referenceHeight hreference B₀ threshold hB₀ hthresholdBudget
  · exact incidence
  · exact cross
  · exact hcoarseMass
  · exact hcoarseMassTop

end Kakeya.Assouad

end
