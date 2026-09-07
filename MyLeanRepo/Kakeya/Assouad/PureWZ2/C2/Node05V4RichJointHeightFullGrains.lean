import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightGraphParents
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichSaturatedFullLocalGrain

/-!
# Full local grains on the final joint-height parents

Each selected second-cover parent receives a canonical anchor from the same
joint fixed-bin source and the direct-rich saturated full-grain witness at
that exact anchor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichJointFullGrainData
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta : ℝ}
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
    (separated : PureWZ2Node05V4RichJointSeparatedParentData oneParent) where
  sourceCellFor : WZ2PaperCellIndex → WZ2PaperCellIndex
  sourceCellFor_mem :
    ∀ parent ∈ separated.selectedParents,
      sourceCellFor parent ∈ separated.selectedCells
  sourceCellFor_parent :
    ∀ parent ∈ separated.selectedParents,
      pullback.standardSecondParent (sourceCellFor parent) = parent
  anchorFor : WZ2PaperCellIndex → Point3
  anchorFor_mem_fixed :
    ∀ parent ∈ separated.selectedParents,
      anchorFor parent ∈
        volumePopular.jointFixedBinHeightRegion
          block.referenceHeight block.bin
  anchorFor_mem_sourceCell :
    ∀ parent ∈ separated.selectedParents,
      anchorFor parent ∈ wz1PaperGridCube rho (sourceCellFor parent)
  anchorFor_mem_current :
    ∀ parent ∈ separated.selectedParents,
      anchorFor parent ∈ current.grain.shading.union
  anchorFor_mem_parent :
    ∀ parent ∈ separated.selectedParents,
      anchorFor parent ∈ wz1PaperGridCube sqrtRequested.1 parent
  fullGrainFor : ∀ parent (_hparent : parent ∈ separated.selectedParents),
    PureWZ2Node05V4RichSaturatedFullLocalGrainData
      (eta := eta) pullback parent
  fullGrain_anchor_eq :
    ∀ parent (hparent : parent ∈ separated.selectedParents),
      (fullGrainFor parent hparent).anchor = anchorFor parent
  normalFor : WZ2PaperCellIndex → Point3
  normalFor_eq :
    ∀ parent (hparent : parent ∈ separated.selectedParents),
      normalFor parent = (fullGrainFor parent hparent).normal

namespace PureWZ2Node05V4RichJointSeparatedParentData

variable
    {capability : PureWZ2PropStickyCapability}
    {sigma inputLoss delta rho stickyLoss eta : ℝ}
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

theorem fullGrains
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hcertificateOne : 4 * rhoRequested.1 ≤ 1)
    (hsourcePower :
      ((32 * Kakeya.realRpowENN delta (-inputLoss) *
            Kakeya.realRpowENN delta sigma *
            Kakeya.realRpowENN rho (2 - sigma)) *
          ENNReal.ofReal rho) *
          Kakeya.realRpowENN (4 * rhoRequested.1)
            (3 / 2 + sigma / 2 + eta) ≤
        (Kakeya.realRpowENN rhoRequested.1 3 *
            Kakeya.realRpowENN (delta / rhoRequested.1)
              (sigma + 2 * twoScale.first.rich.terminalLoss)) *
          Kakeya.realRpowENN rhoRequested.1
            (3 / 2 + sigma / 2 + twoScale.second.terminalLoss))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rhoRequested.1) (-eta)) :
    Nonempty (PureWZ2Node05V4RichJointFullGrainData
      (eta := eta) separated) := by
  have hsourceCellExists :
      ∀ parent (hparent : parent ∈ separated.selectedParents),
        ∃ cell ∈ separated.selectedCells,
          pullback.standardSecondParent cell = parent := by
    intro parent hparent
    rw [separated.selectedParents_eq] at hparent
    exact Finset.mem_image.mp hparent
  let defaultCell := Classical.choose separated.selectedCells_nonempty
  let sourceCellFor : WZ2PaperCellIndex → WZ2PaperCellIndex := fun parent =>
    if hparent : parent ∈ separated.selectedParents then
      Classical.choose (hsourceCellExists parent hparent)
    else defaultCell
  have hsourceCellForMem :
      ∀ parent (hparent : parent ∈ separated.selectedParents),
        sourceCellFor parent ∈ separated.selectedCells := by
    intro parent hparent
    simp only [sourceCellFor, dif_pos hparent]
    exact (Classical.choose_spec (hsourceCellExists parent hparent)).1
  have hsourceCellForParent :
      ∀ parent (hparent : parent ∈ separated.selectedParents),
        pullback.standardSecondParent (sourceCellFor parent) = parent := by
    intro parent hparent
    simp only [sourceCellFor, dif_pos hparent]
    exact (Classical.choose_spec (hsourceCellExists parent hparent)).2
  have hanchorExists :
      ∀ parent (hparent : parent ∈ separated.selectedParents),
        ∃ point ∈ block.jointCellSource (sourceCellFor parent),
          point ∈ wz1PaperGridCube rho (sourceCellFor parent) := by
    intro parent hparent
    rcases block.jointCellSource_nonempty
      (oneParent.selectedCells_subset
        (separated.selectedCells_subset
          (hsourceCellForMem parent hparent))) with
      ⟨point, hpoint⟩
    exact ⟨point, hpoint, hpoint.2⟩
  let anchorFor : WZ2PaperCellIndex → Point3 := fun parent =>
    if hparent : parent ∈ separated.selectedParents then
      Classical.choose (hanchorExists parent hparent)
    else 0
  have hanchorSpec :
      ∀ parent (hparent : parent ∈ separated.selectedParents),
        anchorFor parent ∈ block.jointCellSource (sourceCellFor parent) ∧
          anchorFor parent ∈ wz1PaperGridCube rho (sourceCellFor parent) := by
    intro parent hparent
    simp only [anchorFor, dif_pos hparent]
    exact Classical.choose_spec (hanchorExists parent hparent)
  have hanchorCurrent :
      ∀ parent (hparent : parent ∈ separated.selectedParents),
        anchorFor parent ∈ current.grain.shading.union := by
    intro parent hparent
    exact volumePopular.jointSourceSet_subset_current
      (hanchorSpec parent hparent).1.1.1.1
  have hsourceSelected :
      ∀ parent (hparent : parent ∈ separated.selectedParents),
        sourceCellFor parent ∈ pullback.selectedCells := by
    intro parent hparent
    exact block.jointFixedBinRhoCells_subset_selected
      (oneParent.selectedCells_subset
        (separated.selectedCells_subset
          (hsourceCellForMem parent hparent)))
  have hanchorParent :
      ∀ parent (hparent : parent ∈ separated.selectedParents),
        anchorFor parent ∈ wz1PaperGridCube sqrtRequested.1 parent := by
    intro parent hparent
    have hraw := pullback.standardSecondParent_cell_subset
      (hsourceSelected parent hparent)
      (hanchorSpec parent hparent).2
    rwa [hsourceCellForParent parent hparent] at hraw
  have hparentActive :
      ∀ parent (hparent : parent ∈ separated.selectedParents),
        parent ∈ twoScale.secondBalancedCover.activeCells := by
    intro parent hparent
    have hactive := pullback.standardSecondParent_active
      (hsourceSelected parent hparent)
    rwa [hsourceCellForParent parent hparent] at hactive
  have hsourceFloor :
      ∀ parent (hparent : parent ∈ separated.selectedParents),
        Kakeya.realRpowENN (4 * rhoRequested.1)
            (3 / 2 + sigma / 2 + eta) ≤
          volume (pullback.sameHeightParentSaturation parent) := by
    intro parent hparent
    exact pullback.sameHeightParentSaturation_volume_lower
      (hparentActive parent hparent) _ hsourcePower
  have hgrain :
      ∀ parent (hparent : parent ∈ separated.selectedParents),
        ∃ grain : PureWZ2Node05V4RichSaturatedFullLocalGrainData
            (eta := eta) pullback parent,
          grain.anchor = anchorFor parent := by
    intro parent hparent
    exact pullback.saturatedFullLocalGrainAt
      parent (hparentActive parent hparent)
      (anchorFor parent) (hanchorCurrent parent hparent)
      (hanchorParent parent hparent) hbridge hcertificateOne
      (hsourceFloor parent hparent) hlocalPower
  let fullGrainFor :
      ∀ parent (hparent : parent ∈ separated.selectedParents),
        PureWZ2Node05V4RichSaturatedFullLocalGrainData
          (eta := eta) pullback parent :=
    fun parent hparent => Classical.choose (hgrain parent hparent)
  let normalFor : WZ2PaperCellIndex → Point3 := fun parent =>
    if hparent : parent ∈ separated.selectedParents then
      (fullGrainFor parent hparent).normal
    else 0
  exact ⟨{
    sourceCellFor := sourceCellFor
    sourceCellFor_mem := hsourceCellForMem
    sourceCellFor_parent := hsourceCellForParent
    anchorFor := anchorFor
    anchorFor_mem_fixed := fun parent hparent =>
      (hanchorSpec parent hparent).1.1
    anchorFor_mem_sourceCell := fun parent hparent =>
      (hanchorSpec parent hparent).2
    anchorFor_mem_current := hanchorCurrent
    anchorFor_mem_parent := hanchorParent
    fullGrainFor := fullGrainFor
    fullGrain_anchor_eq := fun parent hparent =>
      Classical.choose_spec (hgrain parent hparent)
    normalFor := normalFor
    normalFor_eq := by
      intro parent hparent
      simp [normalFor, hparent]
  }⟩

end PureWZ2Node05V4RichJointSeparatedParentData

end Kakeya.Assouad

end
