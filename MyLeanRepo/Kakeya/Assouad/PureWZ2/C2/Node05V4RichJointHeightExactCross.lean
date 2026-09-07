import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightSeparatedGraph
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSourcePopularCapacityScalar

/-!
# Exact-cross volume closure for the joint-height graph

The joint-height route first regularizes the continuous paper set `Z_S` by
three-dimensional source volume.  This costs one dyadic height-bin factor.
The distinct-label incidence and the two exact balanced-cover cross identities
then cancel both balanced cell masses before the same-height saturation is
used.  Thus the graph-volume input to Theorem 5.2 loses only the scheduled
polylogarithmic height-bin factor, and no fixed power of `rho`.
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

/-- Every rich label selected on the volume-popular joint source is also rich
on the original continuous `Z_S` source slab, at the same reference height
and threshold. -/
theorem jointRichCommonBinLabels_subset_sourcePopular
    (referenceHeight : ℝ) (threshold : ENNReal) :
    volumePopular.jointRichCommonBinLabels referenceHeight threshold ⊆
      pullback.sourcePopularRichCommonBinLabels
        heightIndex.1.1 referenceHeight threshold := by
  intro bin hbin
  rw [jointRichCommonBinLabels, Finset.mem_filter] at hbin
  rw [PureWZ2Node05V4RichTwoScaleCellPullbackData.sourcePopularRichCommonBinLabels,
    Finset.mem_filter]
  constructor
  · rw [pureWZ2OccupiedCommonBins, Finset.mem_filter] at hbin ⊢
    refine ⟨hbin.1.1, ?_⟩
    rcases hbin.1.2 with ⟨point, hpoint, hlabel⟩
    exact ⟨point, volumePopular.jointSourceSet_subset_standardSlab hpoint, hlabel⟩
  · rcases hbin.2 with ⟨height, hheight, hheightRange, hmass⟩
    refine ⟨height, ?_, hheightRange, hmass.trans ?_⟩
    · rw [← volumePopular.continuous.popularHeights_eq]
      exact volumePopular.jointPopularHeight_mem_ZS hheight
    · apply measure_mono
      intro point hpoint
      have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
      apply wz1Lemma23_mem_planarSlice_iff.mpr
      exact ⟨volumePopular.jointSourceSet_subset_standardSlab hlift.1,
        hlift.2⟩

/-- The joint rich labels inherit the full-slab distinct-label incidence
bound.  Only the label family is restricted; every witnessing spatial parent
still belongs to the same genuine second-cover slab. -/
theorem jointRichCommonBin_incidence
    (referenceHeight : ℝ)
    (hreference : referenceHeight ∈ Set.Icc (-1 : ℝ) 1)
    (threshold : ENNReal) (K : ℕ)
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold) :
    ((volumePopular.jointRichCommonBinLabels
        referenceHeight threshold).card : ENNReal) * K *
        twoScale.secondBalancedCover.cellMass ≤
      5 * volume
        (pullback.standardSqrtSlabCoarseRegion heightIndex.1.1) := by
  have hcard :
      ((volumePopular.jointRichCommonBinLabels
          referenceHeight threshold).card : ENNReal) ≤
        (pullback.sourcePopularRichCommonBinLabels
          heightIndex.1.1 referenceHeight threshold).card := by
    exact_mod_cast Finset.card_le_card
      (volumePopular.jointRichCommonBinLabels_subset_sourcePopular
        referenceHeight threshold)
  calc
    ((volumePopular.jointRichCommonBinLabels
          referenceHeight threshold).card : ENNReal) * K *
        twoScale.secondBalancedCover.cellMass ≤
      ((pullback.sourcePopularRichCommonBinLabels
          heightIndex.1.1 referenceHeight threshold).card : ENNReal) * K *
        twoScale.secondBalancedCover.cellMass := by gcongr
    _ ≤ 5 * volume
        (pullback.standardSqrtSlabCoarseRegion heightIndex.1.1) :=
      pullback.sourcePopularRichCommonBin_incidence heightIndex.1.1
        referenceHeight hreference threshold K hK

end PureWZ2Node05V4RichSourceVolumePopularHeightData

namespace PureWZ2Node05V4RichSourceVolumePopularHeightData.JointHeightCommonBinData

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

/-- Exact-cross estimate for the joint volume-popular common bin.  The sole
extra factor compared with the continuous-`Z_S` version is the dyadic
height-volume bin count. -/
theorem firstCellMass_mul_K_mul_secondCellMass_le_jointFixedBinMass_mul_cube
    (K : ℕ)
    (hK :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold) :
    pullback.firstPostBalanced.cellMass *
          ((K : ENNReal) * twoScale.secondBalancedCover.cellMass) ≤
      80 * (volumePopular.popular.bins : ENNReal) *
        volumePopular.jointIntegratedBinMass
          block.referenceHeight block.bin *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  let slabMass :=
    volume (pullback.standardSqrtSlabSourceRegion heightIndex.1.1)
  let coarseMass :=
    volume (pullback.standardSqrtSlabCoarseRegion heightIndex.1.1)
  let bins : ENNReal := volumePopular.popular.bins
  let labels : ENNReal :=
    (volumePopular.jointRichCommonBinLabels
      block.referenceHeight threshold).card
  let fixedMass :=
    volumePopular.jointIntegratedBinMass block.referenceHeight block.bin
  let cubeVolume := volume (wz1PaperGridCube rho (0, 0, 0))
  have hslabToContinuous :
      slabMass ≤ 2 * volume volumePopular.continuous.popularRegion := by
    calc
      slabMass = slabMass / 2 + slabMass / 2 :=
        (ENNReal.add_halves _).symm
      _ ≤ volume volumePopular.continuous.popularRegion +
          volume volumePopular.continuous.popularRegion := by
        gcongr
        · exact volumePopular.continuous.popularRegion_half_volume
        · exact volumePopular.continuous.popularRegion_half_volume
      _ = 2 * volume volumePopular.continuous.popularRegion := by ring
  have hcontinuousToJoint :
      volume volumePopular.continuous.popularRegion ≤
        2 * bins * volume volumePopular.jointSourceSet := by
    rw [← volumePopular.sourcePopularShading_union]
    calc
      volume volumePopular.sourcePopularShading.union =
          volume volumePopular.sourcePopularShading.union / 2 +
            volume volumePopular.sourcePopularShading.union / 2 :=
        (ENNReal.add_halves _).symm
      _ ≤ (volumePopular.popular.bins : ENNReal) *
            volume volumePopular.jointSourceSet +
          (volumePopular.popular.bins : ENNReal) *
            volume volumePopular.jointSourceSet := by
        gcongr
        · simpa only [
            PureWZ2Node05V4RichSourceVolumePopularHeightData.jointSourceSet]
            using volumePopular.popular.retained_volume
        · simpa only [
            PureWZ2Node05V4RichSourceVolumePopularHeightData.jointSourceSet]
            using volumePopular.popular.retained_volume
      _ = 2 * bins * volume volumePopular.jointSourceSet := by ring
  have hsourceAverage :
      slabMass ≤ 16 * bins * labels * fixedMass := by
    calc
      slabMass ≤ 2 * volume volumePopular.continuous.popularRegion :=
        hslabToContinuous
      _ ≤ 2 * (2 * bins * volume volumePopular.jointSourceSet) := by gcongr
      _ ≤ 2 * (2 * bins * (4 * labels * fixedMass)) := by
        gcongr
        simpa only [labels, fixedMass] using block.source_average
      _ = 16 * bins * labels * fixedMass := by ring
  have hreference :=
    volumePopular.jointPopularHeight_mem_paperRange block.referenceHeight_mem
  have hincidence :
      labels * K * twoScale.secondBalancedCover.cellMass ≤
        5 * coarseMass := by
    simpa only [labels, coarseMass] using
      volumePopular.jointRichCommonBin_incidence
        block.referenceHeight hreference threshold K hK
  have hcross : slabMass * cubeVolume =
      coarseMass * pullback.firstPostBalanced.cellMass := by
    exact pullback.selectedRhoCells_source_coarse_cross
      (pullback.standardSqrtSlabRhoCells heightIndex.1.1)
      (pullback.standardSqrtSlabRhoCells_subset heightIndex.1.1)
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hcoarsePos : 0 < coarseMass := by
    dsimp only [coarseMass]
    rw [pullback.standardSqrtSlabCoarseRegion_volume]
    exact ENNReal.mul_pos
      (by exact_mod_cast
        (pullback.standardSqrtSlabRhoCells_nonempty heightIndex.1.2).card_pos.ne')
      (wz1PaperGridCube_volume_pos hrho (0, 0, 0)).ne'
  have hcoarseTop : coarseMass ≠ ⊤ := by
    dsimp only [coarseMass]
    rw [pullback.standardSqrtSlabCoarseRegion_volume]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (wz1PaperGridCube_volume_ne_top hrho (0, 0, 0))
  apply (ENNReal.mul_le_mul_iff_right hcoarsePos.ne' hcoarseTop).mp
  calc
    coarseMass *
          (pullback.firstPostBalanced.cellMass *
            ((K : ENNReal) * twoScale.secondBalancedCover.cellMass)) =
        (slabMass * cubeVolume) *
          ((K : ENNReal) * twoScale.secondBalancedCover.cellMass) := by
      simpa only [mul_assoc] using congrArg
        (fun value : ENNReal =>
          value * ((K : ENNReal) * twoScale.secondBalancedCover.cellMass))
        hcross.symm
    _ ≤ (16 * bins * labels * fixedMass * cubeVolume) *
          ((K : ENNReal) * twoScale.secondBalancedCover.cellMass) := by gcongr
    _ = (16 * bins * fixedMass * cubeVolume) *
          (labels * K * twoScale.secondBalancedCover.cellMass) := by ring
    _ ≤ (16 * bins * fixedMass * cubeVolume) * (5 * coarseMass) := by gcongr
    _ = coarseMass * (80 * bins * fixedMass * cubeVolume) := by ring

end PureWZ2Node05V4RichSourceVolumePopularHeightData.JointHeightCommonBinData

namespace PureWZ2Node05V4RichJointSeparatedParentData

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
    {block : volumePopular.JointHeightCommonBinData B₀ threshold}
    {oneParent : block.JointOneParentPerYData}
    (separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent)

/-- Close the absolute graph-volume hypothesis from the joint exact cross.
The common-bin label count and both balanced cell masses cancel; only the
dyadic height-volume bin count remains for the P0 schedule. -/
theorem graph_volume_lower_of_jointExactCross
    (K : ℕ)
    (hKcapacity :
      (K : ENNReal) *
          PureWZ2SourceHorizontalFixedLineData.commonBinSpatialCellCap
            sigma inputLoss delta rho ≤ threshold)
    (eta volumeLoss : ℝ)
    (hgraphK :
      (80 * (volumePopular.popular.bins : ENNReal) * 512 * 45) *
          Kakeya.realRpowENN separated.graphScale
            (1 + sigma / 2 + volumeLoss) ≤
        (K : ENNReal) *
          Kakeya.realRpowENN (4 * rho)
            (3 / 2 + sigma / 2 + eta))
    (hsaturationPower :
      ((32 * Kakeya.realRpowENN delta (-inputLoss) *
              Kakeya.realRpowENN delta sigma *
              Kakeya.realRpowENN rho (2 - sigma)) *
            ENNReal.ofReal rho) *
          Kakeya.realRpowENN (4 * rho)
            (3 / 2 + sigma / 2 + eta) ≤
        pullback.firstPostBalanced.cellMass *
          twoScale.secondBalancedCover.cellMass) :
    Kakeya.realRpowENN separated.graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume separated.graphShading.union := by
  let bins : ENNReal := volumePopular.popular.bins
  let cap : ENNReal :=
    32 * Kakeya.realRpowENN delta (-inputLoss) *
      Kakeya.realRpowENN delta sigma *
      Kakeya.realRpowENN rho (2 - sigma)
  let cost : ENNReal := 80 * bins * 512 * 45 * cap * ENNReal.ofReal rho
  have hrho : 0 < rho := by
    rw [← pullback.rhoRequested_eq]
    exact twoScale.first.publicSticky.coarse_extremal.delta_pos
  have hdeltaLossPos :
      0 < Kakeya.realRpowENN delta (-inputLoss) :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos current.grain.extremal.delta_pos _)
  have hdeltaSigmaPos :
      0 < Kakeya.realRpowENN delta sigma :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos current.grain.extremal.delta_pos _)
  have hrhoPowerPos :
      0 < Kakeya.realRpowENN rho (2 - sigma) :=
    ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hrho _)
  have hcapPos : 0 < cap := by
    dsimp only [cap]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos (by norm_num) hdeltaLossPos.ne').ne'
        hdeltaSigmaPos.ne').ne' hrhoPowerPos.ne'
  have hcapTop : cap ≠ ⊤ := by
    dsimp only [cap]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN]))
        (by simp [Kakeya.realRpowENN]))
      (by simp [Kakeya.realRpowENN])
  have hbinsPos : 0 < bins := by
    dsimp only [bins]
    exact_mod_cast (show 0 < volumePopular.popular.bins by
      rw [volumePopular.popular.bins_eq]
      omega)
  have hbinsTop : bins ≠ ⊤ := by
    dsimp only [bins]
    exact ENNReal.natCast_ne_top _
  have hcostPos : 0 < cost := by
    dsimp only [cost]
    have hconstantPos : 0 < (80 * bins * 512 * 45 : ENNReal) :=
      ENNReal.mul_pos
        (ENNReal.mul_pos
          (ENNReal.mul_pos (by norm_num) hbinsPos.ne').ne'
          (by norm_num)).ne' (by norm_num)
    exact ENNReal.mul_pos
      (ENNReal.mul_pos hconstantPos.ne' hcapPos.ne').ne'
      (ENNReal.ofReal_pos.mpr hrho).ne'
  have hcostTop : cost ≠ ⊤ := by
    dsimp only [cost]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hbinsTop)
            (by norm_num)) (by norm_num)) hcapTop) ENNReal.ofReal_ne_top
  have hexact :=
    block.firstCellMass_mul_K_mul_secondCellMass_le_jointFixedBinMass_mul_cube
      K hKcapacity
  have hsaturation := block.jointFixedBin_volume_mul_square_le_saturation
  have honeParent := oneParent.volume_retention
  have hseparated := separated.volume_retention
  have hcube :
      volume (wz1PaperGridCube rho (0, 0, 0)) =
        ENNReal.ofReal (rho ^ 2) * ENNReal.ofReal rho := by
    rw [wz1PaperGridCube_volume_exact hrho]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ rho ^ 2)]
    congr 1
  apply (ENNReal.mul_le_mul_iff_right hcostPos.ne' hcostTop).mp
  calc
    cost * Kakeya.realRpowENN separated.graphScale
          (1 + sigma / 2 + volumeLoss) =
        (cap * ENNReal.ofReal rho) *
          ((80 * bins * 512 * 45) *
            Kakeya.realRpowENN separated.graphScale
              (1 + sigma / 2 + volumeLoss)) := by ring
    _ ≤ (cap * ENNReal.ofReal rho) *
          ((K : ENNReal) * Kakeya.realRpowENN (4 * rho)
            (3 / 2 + sigma / 2 + eta)) :=
      mul_le_mul_left' hgraphK _
    _ = (K : ENNReal) *
          ((cap * ENNReal.ofReal rho) *
            Kakeya.realRpowENN (4 * rho)
              (3 / 2 + sigma / 2 + eta)) := by ring
    _ ≤ (K : ENNReal) *
          (pullback.firstPostBalanced.cellMass *
            twoScale.secondBalancedCover.cellMass) :=
      mul_le_mul_left' hsaturationPower _
    _ = pullback.firstPostBalanced.cellMass *
          ((K : ENNReal) * twoScale.secondBalancedCover.cellMass) := by ring
    _ ≤ 80 * bins *
          volumePopular.jointIntegratedBinMass
            block.referenceHeight block.bin *
          volume (wz1PaperGridCube rho (0, 0, 0)) := by
      simpa only [bins] using hexact
    _ = 80 * bins *
          (volume (volumePopular.jointFixedBinHeightRegion
              block.referenceHeight block.bin) * ENNReal.ofReal (rho ^ 2)) *
          ENNReal.ofReal rho := by
      rw [volumePopular.jointFixedBinHeightRegion_volume block, hcube]
      ring
    _ ≤ 80 * bins *
          (cap * volume block.jointSaturatedUnion) * ENNReal.ofReal rho := by
      gcongr
    _ ≤ 80 * bins *
          (cap * (45 * volume oneParent.saturatedUnion)) *
          ENNReal.ofReal rho := by gcongr
    _ ≤ 80 * bins *
          (cap * (45 * (512 * volume separated.saturatedUnion))) *
          ENNReal.ofReal rho := by gcongr
    _ = cost * volume separated.graphShading.union := by
      rw [separated.graphShading_union]
      dsimp only [cost, cap, bins]
      ring

end PureWZ2Node05V4RichJointSeparatedParentData

end Kakeya.Assouad

end
