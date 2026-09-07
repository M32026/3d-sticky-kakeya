import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightParents
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalBlockResidue

/-!
# Mod-512 separation after one-parent-per-y

The selected source cells are colored by the y-index of their unique
second-cover parent.  Weighted pigeonholing retains a fixed fraction of the
actual saturated volume and makes nearby graph cells use the same parent
y-layer.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2Node05V4RichJointSeparatedParentData
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
    (oneParent : block.JointOneParentPerYData) where
  residue : Fin 512
  selectedCells : Finset WZ2PaperCellIndex :=
    oneParent.selectedCells.filter fun cell =>
      ((pullback.standardSecondParent cell).2.1 % (512 : ℤ)).toNat = residue
  selectedCells_eq :
    selectedCells = oneParent.selectedCells.filter fun cell =>
      ((pullback.standardSecondParent cell).2.1 % (512 : ℤ)).toNat = residue
  selectedCells_subset : selectedCells ⊆ oneParent.selectedCells
  selectedCells_nonempty : selectedCells.Nonempty
  parent_y_residue :
    ∀ cell ∈ selectedCells,
      (pullback.standardSecondParent cell).2.1 % (512 : ℤ) = (residue : ℤ)
  selectedParents : Finset WZ2PaperCellIndex :=
    selectedCells.image pullback.standardSecondParent
  selectedParents_eq :
    selectedParents = selectedCells.image pullback.standardSecondParent
  selectedParents_subset : selectedParents ⊆ oneParent.selectedParents
  selectedParents_nonempty : selectedParents.Nonempty
  selectedParents_y_injective :
    Set.InjOn (fun parent : WZ2PaperCellIndex => parent.2.1) selectedParents
  saturatedUnion : Set Point3 :=
    ⋃ cell ∈ selectedCells, block.jointCellSaturation cell
  saturatedUnion_eq :
    saturatedUnion =
      ⋃ cell ∈ selectedCells, block.jointCellSaturation cell
  saturatedUnion_measurable : MeasurableSet saturatedUnion
  saturatedUnion_volume :
    volume saturatedUnion =
      ∑ cell ∈ selectedCells, volume (block.jointCellSaturation cell)
  volume_retention :
    volume oneParent.saturatedUnion ≤ 512 * volume saturatedUnion

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
    {volumePopular :
      PureWZ2Node05V4RichSourceVolumePopularHeightData pullback heightIndex}
    {B₀ threshold : ENNReal}
    {block : volumePopular.JointHeightCommonBinData B₀ threshold}
    (oneParent : block.JointOneParentPerYData)

theorem jointSeparatedParents :
    Nonempty
      (PureWZ2Node05V4RichJointSeparatedParentData oneParent) := by
  let weight : WZ2PaperCellIndex → ENNReal := fun cell =>
    volume (block.jointCellSaturation cell)
  let color : WZ2PaperCellIndex → Fin 512 := fun cell =>
    ⟨((pullback.standardSecondParent cell).2.1 % (512 : ℤ)).toNat, by
      have hnonneg :
          0 ≤ (pullback.standardSecondParent cell).2.1 % (512 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hlt :
          (pullback.standardSecondParent cell).2.1 % (512 : ℤ) <
            (512 : ℤ) :=
        Int.emod_lt_of_pos _ (by norm_num)
      omega⟩
  rcases finset_ennreal_weighted_pigeonhole
      (n := 512) (by norm_num) oneParent.selectedCells weight color with
    ⟨residue, hretained⟩
  let selectedCells := oneParent.selectedCells.filter fun cell =>
    color cell = residue
  have hallVolume :
      (∑ cell ∈ oneParent.selectedCells, weight cell) =
        volume oneParent.saturatedUnion := by
    simpa [weight] using oneParent.saturatedUnion_volume.symm
  have hsaturatedPos : 0 < volume oneParent.saturatedUnion := by
    have hintegratedPos :
        0 < volumePopular.jointIntegratedBinMass
          block.referenceHeight block.bin := by
      have hproductPos :
          0 < 4 * ((volumePopular.jointRichCommonBinLabels
            block.referenceHeight threshold).card : ENNReal) *
              volumePopular.jointIntegratedBinMass
                block.referenceHeight block.bin :=
        volumePopular.jointSourceSet_volume_pos.trans_le block.source_average
      by_contra hnot
      have hzero :
          volumePopular.jointIntegratedBinMass
            block.referenceHeight block.bin = 0 :=
        bot_unique (not_lt.mp hnot)
      rw [hzero, mul_zero] at hproductPos
      exact (lt_irrefl 0 hproductPos)
    have hallPos : 0 < volume block.jointSaturatedUnion :=
      hintegratedPos.trans_le block.jointFixedBin_volume_le_saturation
    have hselectedScaled :
        0 < 45 * volume oneParent.saturatedUnion :=
      hallPos.trans_le oneParent.volume_retention
    by_contra hnot
    have hzero : volume oneParent.saturatedUnion = 0 :=
      bot_unique (not_lt.mp hnot)
    rw [hzero, mul_zero] at hselectedScaled
    exact (lt_irrefl 0 hselectedScaled)
  have hselectedNonempty : selectedCells.Nonempty := by
    by_contra hempty
    have hempty' : selectedCells = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hempty
    have hzero : ∑ cell ∈ selectedCells, weight cell = 0 := by
      simp [hempty']
    have htotalZero :
        ∑ cell ∈ oneParent.selectedCells, weight cell = 0 := by
      have hle : (∑ cell ∈ oneParent.selectedCells, weight cell) ≤ 0 := by
        simpa [selectedCells, hzero] using hretained
      exact le_zero_iff.mp hle
    rw [hallVolume] at htotalZero
    exact (ne_of_gt hsaturatedPos) htotalZero
  let selectedParents :=
    selectedCells.image pullback.standardSecondParent
  have hselectedParentsSubset :
      selectedParents ⊆ oneParent.selectedParents := by
    intro parent hparent
    rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
    exact oneParent.selected_parent cell
      (Finset.mem_filter.mp hcell).1
  let saturatedUnion :=
    ⋃ cell ∈ selectedCells, block.jointCellSaturation cell
  have hsaturatedMeas : MeasurableSet saturatedUnion :=
    MeasurableSet.biUnion selectedCells.finite_toSet.countable
      (fun cell _ =>
        measurableSet_wz1PaperGridCubeSameHeightSaturation
          rho cell (block.jointCellSource cell)
          (block.jointCellSource_measurable cell))
  have hsaturatedVolume :
      volume saturatedUnion =
        ∑ cell ∈ selectedCells,
          volume (block.jointCellSaturation cell) := by
    unfold saturatedUnion
    exact MeasureTheory.measure_biUnion_finset
      (fun first _ second _ hne =>
        (wz1PaperGridCube_disjoint hne).mono
          (wz1PaperGridCubeSameHeightSaturation_subset_cube
            rho first (block.jointCellSource first))
          (wz1PaperGridCubeSameHeightSaturation_subset_cube
            rho second (block.jointCellSource second)))
      (fun cell _ =>
        measurableSet_wz1PaperGridCubeSameHeightSaturation
          rho cell (block.jointCellSource cell)
          (block.jointCellSource_measurable cell))
  have hvolumeRetention :
      volume oneParent.saturatedUnion ≤ 512 * volume saturatedUnion := by
    calc
      volume oneParent.saturatedUnion =
          ∑ cell ∈ oneParent.selectedCells, weight cell := hallVolume.symm
      _ ≤ 512 * ∑ cell ∈ selectedCells, weight cell := by
        simpa [selectedCells] using hretained
      _ = 512 * volume saturatedUnion := by rw [hsaturatedVolume]
  exact ⟨{
    residue := residue
    selectedCells := selectedCells
    selectedCells_eq := by
      apply Finset.ext
      intro cell
      simp only [selectedCells, Finset.mem_filter]
      constructor
      · rintro ⟨hcell, hcolor⟩
        exact ⟨hcell, congrArg Fin.val hcolor⟩
      · rintro ⟨hcell, hvalue⟩
        exact ⟨hcell, Fin.ext hvalue⟩
    selectedCells_subset := Finset.filter_subset _ _
    selectedCells_nonempty := hselectedNonempty
    parent_y_residue := by
      intro cell hcell
      have hlabel := (Finset.mem_filter.mp hcell).2
      have hnonneg :
          0 ≤ (pullback.standardSecondParent cell).2.1 % (512 : ℤ) :=
        Int.emod_nonneg _ (by norm_num)
      have hcast : ((color cell : ℕ) : ℤ) =
          (pullback.standardSecondParent cell).2.1 % (512 : ℤ) := by
        simp [color, Int.toNat_of_nonneg hnonneg]
      have hcastEq :=
        congrArg (fun value : Fin 512 => (value : ℤ)) hlabel
      rwa [hcast] at hcastEq
    selectedParents := selectedParents
    selectedParents_eq := rfl
    selectedParents_subset := hselectedParentsSubset
    selectedParents_nonempty :=
      hselectedNonempty.image pullback.standardSecondParent
    selectedParents_y_injective :=
      oneParent.selectedParents_y_injective.mono hselectedParentsSubset
    saturatedUnion := saturatedUnion
    saturatedUnion_eq := rfl
    saturatedUnion_measurable := hsaturatedMeas
    saturatedUnion_volume := hsaturatedVolume
    volume_retention := hvolumeRetention
  }⟩

end PureWZ2Node05V4RichSourceVolumePopularHeightData

end Kakeya.Assouad

end
