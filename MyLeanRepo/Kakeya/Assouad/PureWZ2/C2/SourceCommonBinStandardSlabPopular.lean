import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabSecondCoverMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinPopularHalfMass

/-!
# Popular heights on an unshifted standard sqrt-rho slab

The common-bin construction starts directly from the exact standard-slab
source region.  No Lemma-23 snapped-height window is introduced at this stage.
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

def standardSqrtSlabLeft
    (heightIndex : ℤ) : ℝ :=
  (heightIndex : ℝ) * Real.sqrt rho

theorem measurableSet_standardSqrtSlabSourceRegion
    (heightIndex : ℤ) :
    MeasurableSet
      (pullback.standardSqrtSlabSourceRegion heightIndex) := by
  unfold standardSqrtSlabSourceRegion selectedRhoCellsSourceRegion
  exact (measurableSet_shading_union pullback.shading).inter <|
    MeasurableSet.biUnion
      (pullback.standardSqrtSlabRhoCells heightIndex).finite_toSet.countable
      fun cell _ => wz1PaperGridCube_measurable cell

/-- Every source point in a standard slab lies in its literal unshifted
side-`sqrt rho` height interval. -/
theorem standardSqrtSlabSourceRegion_height
    (heightIndex : ℤ) :
    ∀ point ∈ pullback.standardSqrtSlabSourceRegion heightIndex,
      point (2 : Fin 3) ∈
        Set.Ico
          (standardSqrtSlabLeft (rho := rho) heightIndex)
          (standardSqrtSlabLeft (rho := rho) heightIndex + Real.sqrt rho) := by
  intro point hpoint
  have hpoint' := hpoint
  change point ∈ pullback.shading.union ∩
    wz2RetainedCellsUnion rho
      (pullback.standardSqrtSlabRhoCells heightIndex) at hpoint'
  rw [wz2RetainedCellsUnion] at hpoint'
  rcases Set.mem_iUnion₂.mp hpoint'.2 with
    ⟨rhoCell, hrhoCell, hpointRhoCell⟩
  have hpointParent :
      point ∈ wz1PaperGridCube twoScale.sqrtRequested.1
        (pullback.standardSecondParent rhoCell) :=
    pullback.standardSqrtSlabRhoCell_subset_parent
      hrhoCell hpointRhoCell
  have hroot :
      0 < twoScale.sqrtRequested.1 :=
    twoScale.fine.coarse_extremal.delta_pos
  have hparentBox := hpointParent
  rw [wz1PaperGridCube_eq_Ico hroot] at hparentBox
  have hparentHeight :=
    pullback.standardSqrtSlabRhoCell_parent_height hrhoCell
  constructor
  · change (heightIndex : ℝ) * Real.sqrt rho ≤ point (2 : Fin 3)
    rw [← hparentHeight, ← twoScale.sqrtRequested_eq]
    exact hparentBox.2.2.2.2.1
  · change point (2 : Fin 3) <
      (heightIndex : ℝ) * Real.sqrt rho + Real.sqrt rho
    have hupper := hparentBox.2.2.2.2.2
    rw [hparentHeight, twoScale.sqrtRequested_eq] at hupper
    calc
      point (2 : Fin 3) <
          ((heightIndex : ℝ) + 1) * Real.sqrt rho := hupper
      _ = (heightIndex : ℝ) * Real.sqrt rho + Real.sqrt rho := by ring

theorem standardSqrtSlabSourceRegion_subset_source
    (heightIndex : ℤ) :
    pullback.standardSqrtSlabSourceRegion heightIndex ⊆
      source.shading.union := by
  intro point hpoint
  apply pullback.subshading.union_subset
  exact hpoint.1

theorem standardSqrtSlabSourceRegion_volume_pos
    {heightIndex : ℤ}
    (hheight : heightIndex ∈ pullback.standardSqrtSlabIndices) :
    0 < volume (pullback.standardSqrtSlabSourceRegion heightIndex) := by
  rw [pullback.standardSqrtSlabSourceRegion_volume]
  apply ENNReal.mul_pos
  · exact_mod_cast
      (pullback.standardSqrtSlabRhoCells_nonempty hheight).card_pos.ne'
  · exact twoScale.coarse.balanced.cellMass_pos.ne'

theorem standardSqrtSlabSourceRegion_volume_ne_top
    (heightIndex : ℤ) :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex) ≠ ⊤ := by
  rw [pullback.standardSqrtSlabSourceRegion_volume]
  exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    twoScale.coarse.balanced.cellMass_ne_top

/-- Half of the exact standard-slab source mass lies over its common-bin
popular height set. -/
theorem standardSqrtSlab_commonBinPopularHalfMass
    (heightIndex : ℤ) :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex) / 2 ≤
      ∫⁻ z in pureWZ2SourceCommonBinPopularHeights
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          (standardSqrtSlabLeft (rho := rho) heightIndex)
          (Real.sqrt rho),
        pureWZ2SourceCommonBinSliceMass
          (pullback.standardSqrtSlabSourceRegion heightIndex) z := by
  apply pureWZ2SourceCommonBinPopularHalfMass
    (pullback.standardSqrtSlabSourceRegion heightIndex)
    (pullback.measurableSet_standardSqrtSlabSourceRegion heightIndex)
    (pullback.standardSqrtSlabSourceRegion_volume_ne_top heightIndex)
  · exact Real.sqrt_pos.mpr <| by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.coarse.coarse_extremal.delta_pos
  · exact pullback.standardSqrtSlabSourceRegion_height heightIndex

/-- An occupied standard slab has a popular reference height in the paper
height range. -/
theorem exists_standardSqrtSlab_commonBinReferenceHeight
    {heightIndex : ℤ}
    (hheight : heightIndex ∈ pullback.standardSqrtSlabIndices) :
    ∃ referenceHeight,
      referenceHeight ∈
        pureWZ2SourceCommonBinPopularHeights
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          (standardSqrtSlabLeft (rho := rho) heightIndex)
          (Real.sqrt rho) ∧
      referenceHeight ∈ Set.Icc (-1 : ℝ) 1 := by
  let heights :=
    pureWZ2SourceCommonBinPopularHeights
      (pullback.standardSqrtSlabSourceRegion heightIndex)
      (standardSqrtSlabLeft (rho := rho) heightIndex)
      (Real.sqrt rho)
  have hmassPos :
      0 <
        ∫⁻ z in heights,
          pureWZ2SourceCommonBinSliceMass
            (pullback.standardSqrtSlabSourceRegion heightIndex) z := by
    have hhalfPos :
        0 <
          volume (pullback.standardSqrtSlabSourceRegion heightIndex) / 2 :=
      ENNReal.div_pos
        (pullback.standardSqrtSlabSourceRegion_volume_pos hheight).ne'
        (by norm_num)
    exact hhalfPos.trans_le <| by
      simpa [heights] using
        pullback.standardSqrtSlab_commonBinPopularHalfMass heightIndex
  have hheightSet : heights.Nonempty := by
    by_contra hempty
    have hempty' : heights = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    rw [hempty'] at hmassPos
    simp at hmassPos
  let referenceHeight := Classical.choose hheightSet
  have hreference : referenceHeight ∈ heights :=
    Classical.choose_spec hheightSet
  refine ⟨referenceHeight, hreference, ?_⟩
  have hsliceThreshold :=
    hreference.2
  have hthresholdPos :
      0 <
        pureWZ2SourceCommonBinPopularThreshold
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          (Real.sqrt rho) := by
    unfold pureWZ2SourceCommonBinPopularThreshold
      pureWZ2CommonBinPopularThreshold
    apply ENNReal.div_pos
    · exact
        (ENNReal.div_pos
          (pullback.standardSqrtSlabSourceRegion_volume_pos hheight).ne'
          (by norm_num)).ne'
    · exact ENNReal.ofReal_ne_top
  have hslicePos :
      0 <
        pureWZ2SourceCommonBinSliceMass
          (pullback.standardSqrtSlabSourceRegion heightIndex)
          referenceHeight :=
    hthresholdPos.trans_le hsliceThreshold
  rcases nonempty_of_measure_ne_zero hslicePos.ne' with
    ⟨planarPoint, hplanarPoint⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hplanarPoint
  have hsource :
      point3 (planarPoint 0) (planarPoint 1) referenceHeight ∈
        source.shading.union :=
    pullback.standardSqrtSlabSourceRegion_subset_source
      heightIndex hlift
  have hbox := shading_union_subset_axisBox hsource
  simpa [point3, Kakeya.Streamlined.axisBox, abs_le] using hbox.2.2

end PureWZ2TwoScaleCellPullbackData

end Kakeya.Assouad

end
