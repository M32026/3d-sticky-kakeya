import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichTwoScaleCellPullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinPopularHalfMass

/-!
# Source-popular heights on a prescribed V4 standard slab

This is the literal `Z_S` step in WZ Lemma 5.4.  For one occupied
side-`sqrt rho` slab of the post-two-call source, it records the heights at
which the genuine source slice has at least half its average area.  These
heights retain at least half of the slab volume, and the reference height
used for the fixed global line is selected from this same set.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

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

/-- Left endpoint of the literal unshifted standard side-`sqrt rho` slab. -/
def sourcePopularSlabLeft
    (_pullback : PureWZ2Node05V4RichTwoScaleCellPullbackData
      (rho := rho) twoScale)
    (heightIndex : ℤ) : ℝ :=
  (heightIndex : ℝ) * Real.sqrt rho

/-- The paper's source-popular height set `Z_S` for one prescribed V4 slab. -/
def sourcePopularHeights (heightIndex : ℤ) : Set ℝ :=
  pureWZ2SourceCommonBinPopularHeights
    (pullback.standardSqrtSlabSourceRegion heightIndex)
    (pullback.sourcePopularSlabLeft heightIndex)
    (Real.sqrt rho)

/-- Restrict a point set to the paper's source-popular heights in one V4
standard slab. -/
def sourcePopularRegion (heightIndex : ℤ) : Set Point3 :=
  pullback.standardSqrtSlabSourceRegion heightIndex ∩
    {point | point (2 : Fin 3) ∈ pullback.sourcePopularHeights heightIndex}

theorem measurableSet_sourcePopularRegion (heightIndex : ℤ) :
    MeasurableSet (pullback.sourcePopularRegion heightIndex) := by
  apply
    (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex).inter
  exact
    (measurableSet_pureWZ2SourceCommonBinPopularHeights
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
      (pullback.sourcePopularSlabLeft heightIndex)
      (Real.sqrt rho)).preimage (by fun_prop)

/-- Fubini identifies the volume of the popular region with the integrated
source slice mass over `Z_S`. -/
theorem sourcePopularRegion_volume (heightIndex : ℤ) :
    volume (pullback.sourcePopularRegion heightIndex) =
      ∫⁻ z in pullback.sourcePopularHeights heightIndex,
        pureWZ2SourceCommonBinSliceMass
          (pullback.standardSqrtSlabSourceRegion heightIndex) z := by
  let E := pullback.standardSqrtSlabSourceRegion heightIndex
  let popular := pullback.sourcePopularHeights heightIndex
  have hpopularMeasurable : MeasurableSet popular := by
    exact measurableSet_pureWZ2SourceCommonBinPopularHeights
      E (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
      (pullback.sourcePopularSlabLeft heightIndex) (Real.sqrt rho)
  have hslice : ∀ z : ℝ,
      wz1Lemma23PlanarSlice (pullback.sourcePopularRegion heightIndex) z =
        if z ∈ popular then wz1Lemma23PlanarSlice E z else ∅ := by
    intro z
    by_cases hz : z ∈ popular
    · rw [if_pos hz]
      ext point
      simp only [wz1Lemma23_mem_planarSlice_iff]
      constructor
      · exact fun hpoint => hpoint.1
      · exact fun hpoint => ⟨hpoint, by simpa [popular, point3] using hz⟩
    · rw [if_neg hz]
      ext point
      simp only [Set.notMem_empty, iff_false]
      rw [wz1Lemma23_mem_planarSlice_iff]
      exact fun hpoint => hz (by simpa [popular, point3] using hpoint.2)
  rw [wz1_lemma23_volume_eq_lintegral_planarSlice
    (pullback.sourcePopularRegion heightIndex)
    (pullback.measurableSet_sourcePopularRegion heightIndex)]
  change
    (∫⁻ z : ℝ,
        volume (wz1Lemma23PlanarSlice
          (pullback.sourcePopularRegion heightIndex) z)) =
      ∫⁻ z in popular, volume (wz1Lemma23PlanarSlice E z)
  rw [← lintegral_indicator hpopularMeasurable]
  apply lintegral_congr
  intro z
  rw [hslice z]
  by_cases hz : z ∈ popular
  · simp [hz, E]
  · simp [hz]

/-- The literal V4 `Z_S` region retains at least half of its source slab. -/
theorem sourcePopularRegion_half_volume (heightIndex : ℤ) :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex) / 2 ≤
      volume (pullback.sourcePopularRegion heightIndex) := by
  rw [pullback.sourcePopularRegion_volume heightIndex]
  apply pureWZ2SourceCommonBinPopularHalfMass
    (pullback.standardSqrtSlabSourceRegion heightIndex)
    (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
    (pullback.standardSqrtSlabSourceRegion_volume_ne_top heightIndex)
  · exact Real.sqrt_pos.mpr <| by
      rw [← pullback.rhoRequested_eq]
      exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  · intro point hpoint
    simpa [sourcePopularSlabLeft] using
      pullback.standardSqrtSlabSourceRegion_height
        (heightIndex := heightIndex) (point := point) hpoint

/-- Same-witness data for the source-popularity step preceding `z₀` and the
fixed global line in WZ Lemma 5.4. -/
structure SourcePopularHeightData
    (heightIndex : {heightIndex //
      heightIndex ∈ pullback.standardSqrtSlabIndices}) where
  popularHeights : Set ℝ := pullback.sourcePopularHeights heightIndex.1
  popularHeights_eq :
    popularHeights = pullback.sourcePopularHeights heightIndex.1
  popularHeights_measurable : MeasurableSet popularHeights
  popularHalfMass :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) / 2 ≤
      ∫⁻ z in popularHeights,
        pureWZ2SourceCommonBinSliceMass
          (pullback.standardSqrtSlabSourceRegion heightIndex.1) z
  popularRegion : Set Point3 := pullback.sourcePopularRegion heightIndex.1
  popularRegion_eq :
    popularRegion = pullback.sourcePopularRegion heightIndex.1
  popularRegion_measurable : MeasurableSet popularRegion
  popularRegion_half_volume :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1) / 2 ≤
      volume popularRegion
  referenceHeight : ℝ
  referenceHeight_mem : referenceHeight ∈ popularHeights
  referenceHeight_mem_paperRange : referenceHeight ∈ Set.Icc (-1 : ℝ) 1

/-- Construct `Z_S` and choose the later fixed-line reference height from it. -/
theorem sourcePopularHeightData
    (heightIndex : {heightIndex //
      heightIndex ∈ pullback.standardSqrtSlabIndices}) :
    Nonempty (pullback.SourcePopularHeightData heightIndex) := by
  let E := pullback.standardSqrtSlabSourceRegion heightIndex.1
  let left := pullback.sourcePopularSlabLeft heightIndex.1
  let popular := pullback.sourcePopularHeights heightIndex.1
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hpopularMeasurable : MeasurableSet popular := by
    exact measurableSet_pureWZ2SourceCommonBinPopularHeights
      E (by simpa [E] using
        pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex.1)
      left (Real.sqrt rho)
  have hhalf :
      volume E / 2 ≤
        ∫⁻ z in popular, pureWZ2SourceCommonBinSliceMass E z := by
    apply pureWZ2SourceCommonBinPopularHalfMass E
      (by simpa [E] using
        pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex.1)
      (by simpa [E] using
        pullback.standardSqrtSlabSourceRegion_volume_ne_top heightIndex.1)
      (Real.sqrt_pos.mpr hrho)
    intro point hpoint
    simpa [E, left, sourcePopularSlabLeft] using
      pullback.standardSqrtSlabSourceRegion_height
        (heightIndex := heightIndex.1) (point := point) hpoint
  have hpopularMassPos :
      0 < ∫⁻ z in popular, pureWZ2SourceCommonBinSliceMass E z := by
    have hhalfPos : 0 < volume E / 2 :=
      ENNReal.div_pos
        (by simpa [E] using
          (pullback.standardSqrtSlabSourceRegion_volume_pos
            heightIndex.property).ne')
        (by norm_num)
    exact hhalfPos.trans_le hhalf
  have hpopularNonempty : popular.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hpopularMassPos
    simp at hpopularMassPos
  let referenceHeight := Classical.choose hpopularNonempty
  have hreference : referenceHeight ∈ popular :=
    Classical.choose_spec hpopularNonempty
  have hthresholdPos :
      0 < pureWZ2SourceCommonBinPopularThreshold E (Real.sqrt rho) := by
    unfold pureWZ2SourceCommonBinPopularThreshold
      pureWZ2CommonBinPopularThreshold
    apply ENNReal.div_pos
    · exact
        (ENNReal.div_pos
          (by simpa [E] using
            (pullback.standardSqrtSlabSourceRegion_volume_pos
              heightIndex.property).ne')
          (by norm_num)).ne'
    · exact ENNReal.ofReal_ne_top
  have hslicePos :
      0 < pureWZ2SourceCommonBinSliceMass E referenceHeight :=
    hthresholdPos.trans_le hreference.2
  rcases nonempty_of_measure_ne_zero hslicePos.ne' with
    ⟨planarPoint, hplanarPoint⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hplanarPoint
  have hsource :
      point3 (planarPoint 0) (planarPoint 1) referenceHeight ∈
        current.grain.shading.union :=
    pullback.subshading.union_subset
      (pullback.standardSqrtSlabSourceRegion_subset_source
        heightIndex.1 (by simpa [E] using hlift))
  have hbox := shading_union_subset_axisBox hsource
  have hreferenceRange : referenceHeight ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [point3, Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2
  exact ⟨{
    popularHeights := popular
    popularHeights_eq := by rfl
    popularHeights_measurable := hpopularMeasurable
    popularHalfMass := by simpa [E, popular] using hhalf
    popularRegion := pullback.sourcePopularRegion heightIndex.1
    popularRegion_eq := rfl
    popularRegion_measurable :=
      pullback.measurableSet_sourcePopularRegion heightIndex.1
    popularRegion_half_volume :=
      pullback.sourcePopularRegion_half_volume heightIndex.1
    referenceHeight := referenceHeight
    referenceHeight_mem := hreference
    referenceHeight_mem_paperRange := hreferenceRange
  }⟩

end PureWZ2Node05V4RichTwoScaleCellPullbackData

end Kakeya.Assouad

end
