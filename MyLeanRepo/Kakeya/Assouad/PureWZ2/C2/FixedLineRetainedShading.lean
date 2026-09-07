import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineParentCount
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperCubeSliceArea
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyZeroExtension
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Whole-cell shading retained by the fixed horizontal line
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2FixedLineRetainedShadingData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    (parents : PureWZ2HorizontalFixedLineParentData line) where
  zeroExtension :
    WZ2PaperSubfamilyZeroExtensionData
      twoScale.fine.selected twoScale.fine.refined
  selectedRegion : Set Point3 :=
    ⋃ parent ∈ parents.parents,
      wz1PaperGridCube twoScale.sqrtRequested.1 parent
  selectedRegion_eq :
    selectedRegion =
      ⋃ parent ∈ parents.parents,
        wz1PaperGridCube twoScale.sqrtRequested.1 parent
  selectedRegion_measurable : MeasurableSet selectedRegion
  shading : WZ1PaperTubeShading twoScale.coarse.coarse
  carrier_eq :
    ∀ index, shading.carrier index =
      zeroExtension.ambientShading.carrier index ∩ selectedRegion
  subshading :
    PureWZ2PaperIsSubshading shading twoScale.coarseGrains.shading
  whole_cells : WZ1PaperIsCubicalShading shading
  union_eq :
    shading.union = twoScale.fine.refined.union ∩ selectedRegion
  volume_eq :
    MeasureTheory.volume shading.union =
      (parents.parents.card : ENNReal) * twoScale.fine.balanced.cellMass
  commonParentHeight : ℤ
  parent_height_eq :
    ∀ parent ∈ parents.parents, parent.2.2 = commonParentHeight
  union_height :
    ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈
        Set.Ico
          ((commonParentHeight : ℝ) * twoScale.sqrtRequested.1)
          (((commonParentHeight : ℝ) + 1) * twoScale.sqrtRequested.1)

theorem PureWZ2HorizontalFixedLineParentData.retainShading
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    (parents : PureWZ2HorizontalFixedLineParentData line) :
    Nonempty (PureWZ2FixedLineRetainedShadingData parents) := by
  let rhoScale := twoScale.rhoRequested.1
  let sqrtScale := twoScale.sqrtRequested.1
  have hrho : 0 < rhoScale := twoScale.coarseGrains.extremal.delta_pos
  have hsqrt : 0 < sqrtScale := twoScale.fine.coarse_extremal.delta_pos
  rcases wz2_paper_subfamily_zero_extension
      twoScale.fine.selected twoScale.fine.refined with
    ⟨zeroExtension⟩
  let selectedRegion : Set Point3 :=
    ⋃ parent ∈ parents.parents, wz1PaperGridCube sqrtScale parent
  have hregionMeas : MeasurableSet selectedRegion :=
    MeasurableSet.biUnion parents.parents.finite_toSet.countable
      (fun parent _ => wz1PaperGridCube_measurable parent)
  let shading : WZ1PaperTubeShading twoScale.coarse.coarse :=
    { carrier := fun index =>
        zeroExtension.ambientShading.carrier index ∩ selectedRegion
      measurable_carrier := fun index =>
        (zeroExtension.ambientShading.measurable_carrier index).inter hregionMeas
      subset_body := fun index =>
        Set.inter_subset_left.trans
          (zeroExtension.ambientShading.subset_body index) }
  have hsub : PureWZ2PaperIsSubshading shading
      twoScale.coarseGrains.shading := by
    intro index point hpoint
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, heq, hselected⟩
    subst index
    exact twoScale.fine.subshading selectedIndex hselected
  have hunion :
      shading.union = twoScale.fine.refined.union ∩ selectedRegion := by
    ext point
    constructor
    · rintro ⟨index, hzero, hregion⟩
      have hzeroUnion : point ∈ zeroExtension.ambientShading.union :=
        ⟨index, hzero⟩
      rw [zeroExtension.union_eq] at hzeroUnion
      exact ⟨hzeroUnion, hregion⟩
    · rintro ⟨hfine, hregion⟩
      rw [← zeroExtension.union_eq] at hfine
      rcases hfine with ⟨index, hindex⟩
      exact ⟨index, hindex, hregion⟩
  have hwhole : WZ1PaperIsCubicalShading shading := by
    have hzeroCubical := zeroExtension.cubical twoScale.fine.refined_cubical
    intro index point hpoint other hother
    have hzeroOther := hzeroCubical index point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨selectedParent, hselectedParent, hpointParent⟩
    rcases zeroExtension.carrier_support index point hpoint.1 with
      ⟨selectedIndex, _heq, hselectedFine⟩
    rcases twoScale.fine.balanced.fine_cell_nested
        selectedIndex point hselectedFine with
      ⟨nestedParent, hnestedActive, hnested⟩
    have hpointNested : point ∈ wz1PaperGridCube sqrtScale nestedParent := by
      apply hnested
      exact (mem_wz1PaperGridCube rhoScale _ point).mpr rfl
    have hparentEq : nestedParent = selectedParent :=
      ((mem_wz1PaperGridCube sqrtScale nestedParent point).mp hpointNested).symm.trans
        ((mem_wz1PaperGridCube sqrtScale selectedParent point).mp hpointParent)
    exact ⟨hzeroOther, Set.mem_iUnion₂.mpr
      ⟨selectedParent, hselectedParent, by
        rw [← hparentEq]
        exact hnested hother⟩⟩
  have hvolume :
      MeasureTheory.volume shading.union =
        (parents.parents.card : ENNReal) * twoScale.fine.balanced.cellMass := by
    rw [hunion]
    exact twoScale.fine.balanced.selected_cells_volume
      parents.parents parents.parents_subset
  let firstParent := Classical.choose parents.parents_nonempty
  have hfirstParent : firstParent ∈ parents.parents :=
    Classical.choose_spec parents.parents_nonempty
  let commonParentHeight := firstParent.2.2
  have hparentHeight :
      ∀ parent ∈ parents.parents, parent.2.2 = commonParentHeight := by
    intro parent hparent
    rcases parents.parent_hit parent hparent with ⟨cell, hcell, hcellParent⟩
    rcases parents.parent_hit firstParent hfirstParent with
      ⟨firstCell, hfirstCell, hfirstCellParent⟩
    have hheight := line.representative_height cell hcell
    have hfirstHeight := line.representative_height firstCell hfirstCell
    have hmem := parents.representative_mem_parent cell hcell
    have hfirstMem := parents.representative_mem_parent firstCell hfirstCell
    rw [hcellParent] at hmem
    rw [hfirstCellParent] at hfirstMem
    have hindex :
        wz1PaperGridIndex sqrtScale (line.representative cell) = parent :=
      (mem_wz1PaperGridCube sqrtScale parent _).mp hmem
    have hfirstIndex :
        wz1PaperGridIndex sqrtScale (line.representative firstCell) = firstParent :=
      (mem_wz1PaperGridCube sqrtScale firstParent _).mp hfirstMem
    have hz := congrArg (fun idx : ℤ × ℤ × ℤ => idx.2.2) hindex
    have hzFirst := congrArg (fun idx : ℤ × ℤ × ℤ => idx.2.2) hfirstIndex
    simp [wz1PaperGridIndex, gridIndex, hheight, hfirstHeight] at hz hzFirst
    exact hz.symm.trans (hzFirst.trans rfl)
  have hunionHeight :
      ∀ point ∈ shading.union,
        point (2 : Fin 3) ∈
          Set.Ico ((commonParentHeight : ℝ) * sqrtScale)
            (((commonParentHeight : ℝ) + 1) * sqrtScale) := by
    intro point hpoint
    have hregion := (by rw [hunion] at hpoint; exact hpoint.2)
    rcases Set.mem_iUnion₂.mp hregion with ⟨parent, hparent, hpointParent⟩
    rw [wz1PaperGridCube_eq_Ico hsqrt parent] at hpointParent
    rw [← hparentHeight parent hparent]
    exact ⟨hpointParent.2.2.2.2.1, hpointParent.2.2.2.2.2⟩
  exact
    ⟨{ zeroExtension := zeroExtension
       selectedRegion := selectedRegion
       selectedRegion_eq := rfl
       selectedRegion_measurable := hregionMeas
       shading := shading
       carrier_eq := fun _ => rfl
       subshading := hsub
       whole_cells := hwhole
       union_eq := hunion
       volume_eq := hvolume
       commonParentHeight := commonParentHeight
       parent_height_eq := hparentHeight
       union_height := hunionHeight }⟩

end Kakeya.Assouad
