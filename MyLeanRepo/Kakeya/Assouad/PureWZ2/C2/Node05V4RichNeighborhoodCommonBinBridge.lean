import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichNeighborhoodFullGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightScalarSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSourcePopularIntegratedEnvelope

/-!
# Same-witness source-popular common bin for the V4 coarse neighborhood

The prescribed heavy-slab neighborhood has already selected the paper set
`Z_S`, an outer reference height in `Z_S`, and the fixed global line.  This
module runs the integrated common-bin selection on exactly those stored
objects.  It does not select another `Z_S` or outer reference height, and it
does not assert the still-open graph-volume comparison.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2PreCommonBinGlobalGrainNeighborhoodAtData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss : ℝ}
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
    (block : PureWZ2PreCommonBinGlobalGrainNeighborhoodAtData
      pullback heightIndex.1 neighborhoodLoss)

/-- Recover the exact continuous `Z_S` witness stored by the neighborhood, at
the caller's heavy-slab index.  Every field is a projection of `block`; no
choice is performed. -/
def sourcePopularData : pullback.SourcePopularHeightData heightIndex.1 where
  popularHeights := block.neighborhood.sourcePopularHeights
  popularHeights_eq := by
    rw [block.neighborhood.sourcePopularHeights_eq, block.heightIndex_eq]
  popularHeights_measurable :=
    block.neighborhood.sourcePopularHeights_measurable
  popularHalfMass := by
    simpa only [block.heightIndex_eq] using
      block.neighborhood.sourcePopularHalfMass
  popularRegion := block.neighborhood.sourcePopularRegion
  popularRegion_eq := by
    rw [block.neighborhood.sourcePopularRegion_eq, block.heightIndex_eq]
  popularRegion_measurable :=
    block.neighborhood.sourcePopularRegion_measurable
  popularRegion_half_volume := by
    simpa only [block.heightIndex_eq] using
      block.neighborhood.sourcePopularRegion_half_volume
  referenceHeight := block.neighborhood.lineHeight
  referenceHeight_mem := block.neighborhood.lineHeight_mem_popular
  referenceHeight_mem_paperRange := block.neighborhood.lineHeight_mem

/-- The integrated common-bin envelope selected from the exact `Z_S` and
outer reference height already stored in the genuine coarse neighborhood. -/
theorem sourcePopularIntegratedEnvelope
    (B₀ threshold : ENNReal)
    (hB₀ :
      264 * Kakeya.realRpowENN delta (-inputLoss) *
          Kakeya.realRpowENN (1 / Real.sqrt rho) (1 - sigma) ≤ B₀)
    (hthresholdBudget :
      2 * B₀ * threshold ≤
        pureWZ2SourceCommonBinPopularThreshold
          (pullback.standardSqrtSlabSourceRegion heightIndex.1.1)
          (Real.sqrt rho)) :
    Nonempty { envelope :
      PureWZ2Node05V4RichSourcePopularIntegratedEnvelopeData
        pullback heightIndex.1 B₀ threshold //
      envelope.popular.referenceHeight = block.neighborhood.lineHeight ∧
        envelope.popular.popularHeights =
          block.neighborhood.sourcePopularHeights } := by
  rcases pullback.sourcePopularIntegratedEnvelopeOfPopular
      heightIndex.1 block.sourcePopularData B₀ threshold hB₀ hthresholdBudget with
    ⟨envelope⟩
  refine ⟨envelope.1, ?_, ?_⟩
  · rw [envelope.2]
    rfl
  · rw [envelope.2]
    rfl

/-- Instantiate the common P0 threshold on the exact `Z_S`, reference height,
and fixed line stored by this neighborhood.  The auxiliary volume-popular band
is used only to prove the uniform scalar budget; it is not retained or used to
select any output witness. -/
theorem sourcePopularIntegratedEnvelopeOfScheduledThreshold
    (hgraphOne : 256 * rho ≤ 1) :
    Nonempty { envelope :
      PureWZ2Node05V4RichSourcePopularIntegratedEnvelopeData
        pullback heightIndex.1
          (pureWZ2Node05V4RichJointOccupiedBinBound
            sigma inputLoss delta rho)
          (pureWZ2Node05V4RichJointCommonBinThreshold pullback) //
      envelope.popular.referenceHeight = block.neighborhood.lineHeight ∧
        envelope.popular.popularHeights =
          block.neighborhood.sourcePopularHeights } := by
  rcases pullback.sourceVolumePopularHeightDataOfContinuous
      heightIndex block.sourcePopularData with ⟨volumePopular⟩
  have hjoint := pullback.jointCommonBinThreshold_budget
    hgraphOne heightIndex volumePopular
  have hvolume :
      volume volumePopular.jointSourceSet ≤
        volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1) :=
    measure_mono volumePopular.jointSourceSet_subset_standardSlab
  have hthreshold :
      pureWZ2SourceCommonBinPopularThreshold
          volumePopular.jointSourceSet (Real.sqrt rho) ≤
        pureWZ2SourceCommonBinPopularThreshold
          (pullback.standardSqrtSlabSourceRegion heightIndex.1.1)
          (Real.sqrt rho) := by
    rw [pureWZ2SourceCommonBinPopularThreshold_eq,
      pureWZ2SourceCommonBinPopularThreshold_eq]
    exact ENNReal.div_le_div_right hvolume _
  exact block.sourcePopularIntegratedEnvelope
    (pureWZ2Node05V4RichJointOccupiedBinBound sigma inputLoss delta rho)
    (pureWZ2Node05V4RichJointCommonBinThreshold pullback) le_rfl
    (hjoint.trans hthreshold)

end PureWZ2PreCommonBinGlobalGrainNeighborhoodAtData

/-- Common-bin envelopes on every retained source-heavy slab.  Each dependent
field is indexed by the exact neighborhood block that supplied its `Z_S`,
outer reference height, and fixed line. -/
structure PureWZ2Node05V4RichNeighborhoodCommonBinFamilyData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss : ℝ}
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
    (family : PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss) where
  envelope : ∀ heightIndex,
    { envelope : PureWZ2Node05V4RichSourcePopularIntegratedEnvelopeData
        pullback heightIndex.1
          (pureWZ2Node05V4RichJointOccupiedBinBound
            sigma inputLoss delta rho)
          (pureWZ2Node05V4RichJointCommonBinThreshold pullback) //
      envelope.popular.referenceHeight =
          (family.block heightIndex).neighborhood.lineHeight ∧
        envelope.popular.popularHeights =
          (family.block heightIndex).neighborhood.sourcePopularHeights }

namespace PureWZ2Node05V4RichHeavySlabNeighborhoodFamily

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss neighborhoodLoss : ℝ}
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
    (family : PureWZ2Node05V4RichHeavySlabNeighborhoodFamily
      pullback neighborhoodLoss)

/-- Run the same preselected positive common-bin threshold on every exact
heavy-slab neighborhood. -/
theorem commonBinEnvelopes
    (hgraphOne : 256 * rho ≤ 1) :
    Nonempty
      (PureWZ2Node05V4RichNeighborhoodCommonBinFamilyData family) := by
  let envelope : ∀ heightIndex,
      { envelope : PureWZ2Node05V4RichSourcePopularIntegratedEnvelopeData
          pullback heightIndex.1
            (pureWZ2Node05V4RichJointOccupiedBinBound
              sigma inputLoss delta rho)
            (pureWZ2Node05V4RichJointCommonBinThreshold pullback) //
        envelope.popular.referenceHeight =
            (family.block heightIndex).neighborhood.lineHeight ∧
          envelope.popular.popularHeights =
            (family.block heightIndex).neighborhood.sourcePopularHeights } :=
    fun heightIndex => Classical.choice
      ((family.block heightIndex
        ).sourcePopularIntegratedEnvelopeOfScheduledThreshold hgraphOne)
  exact ⟨{ envelope := envelope }⟩

end PureWZ2Node05V4RichHeavySlabNeighborhoodFamily

end Kakeya.Assouad

end
