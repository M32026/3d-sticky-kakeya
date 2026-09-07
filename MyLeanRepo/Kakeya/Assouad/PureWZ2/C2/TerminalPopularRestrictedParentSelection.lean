import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularRestrictedParents
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularWeightedParents

/-!
# Weighted separated parents after the pre-line terminal restriction

The fixed line sees only parents from the already selected positive dyadic
weight class.  We choose a maximum-weight parent over each occupied y-index
and then a maximum-weight residue modulo 512.  All retained weights remain
literal outer-popular intersection volumes.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

theorem PureWZ2TerminalPopularRestrictedFixedBinParentData.parent_y_fiber_card
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    (parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line)
    (y : ℤ) :
    (parents.parents.filter fun parent => parent.2.1 = y).card ≤ 45 := by
  have hdeltaRoot : delta ≤ terminal.sqrtRequested.1 := by
    rw [terminal.sqrtRequested_eq]
    nlinarith [Real.sqrt_nonneg delta,
      Real.sq_sqrt source.extremal.delta_pos.le,
      source.extremal.delta_le_one]
  exact pureWZ2_fixedLine_parent_y_fiber_card
    line terminal.sqrtRequested.1
    terminal.sticky.coarse_extremal.delta_pos hdeltaRoot
    (source.globalGrains.slope_bound line.lineHeight line.lineHeight_mem)
    parents.parents parents.parentCell parents.parent_hit
    parents.representative_mem_parent y

structure PureWZ2TerminalPopularRestrictedParentSelectionData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    (parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line)
    extends PureWZ2FiniteWeightedParentYResidueData parents.parents
      (pureWZ2TerminalPopularParentWeight carrier) where
  selected_subset_weightClass : selected ⊆ weightClass.selectedParents
  selected_weight_pos : 0 <
    ∑ parent ∈ selected, pureWZ2TerminalPopularParentWeight carrier parent
  visible_to_selected_weight :
    (∑ parent ∈ parents.parents,
        pureWZ2TerminalPopularParentWeight carrier parent) ≤
      (45 * 512 : ENNReal) *
        ∑ parent ∈ selected,
          pureWZ2TerminalPopularParentWeight carrier parent
  selectedRegion : Set Point3 :=
    ⋃ parent ∈ selected,
      wz1PaperGridCube terminal.sqrtRequested.1 parent
  selectedRegion_eq : selectedRegion =
    ⋃ parent ∈ selected,
      wz1PaperGridCube terminal.sqrtRequested.1 parent
  selectedRegion_measurable : MeasurableSet selectedRegion
  selected_weight_eq :
    (∑ parent ∈ selected,
        pureWZ2TerminalPopularParentWeight carrier parent) =
      volume (carrier.shading.union ∩ selectedRegion)
  commonParentHeight : ℤ
  parent_height_eq :
    ∀ parent ∈ selected, parent.2.2 = commonParentHeight

theorem PureWZ2TerminalPopularRestrictedFixedBinParentData.selectWeightedParents
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    (parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line) :
    Nonempty (PureWZ2TerminalPopularRestrictedParentSelectionData parents) := by
  let weight := pureWZ2TerminalPopularParentWeight carrier
  rcases pureWZ2_selectFiniteWeightedParentYResidue parents.parents weight
      parents.parents_nonempty parents.parent_y_fiber_card with ⟨selection⟩
  have hselectedSubsetClass :
      selection.selected ⊆ weightClass.selectedParents :=
    selection.selected_subset.trans
      (selection.onePerY_subset.trans parents.parents_subset_selected)
  have hselectedWeightPos : 0 <
      ∑ parent ∈ selection.selected, weight parent := by
    rcases selection.selected_nonempty with ⟨parent, hparent⟩
    have hpositive : 0 < weight parent :=
      weightClass.weightFloor_pos.trans_le
        (weightClass.weight_band parent
          (hselectedSubsetClass hparent)).1
    exact hpositive.trans_le
      (Finset.single_le_sum (fun _ _ => bot_le) hparent)
  have hvisibleSelected :
      (∑ parent ∈ parents.parents, weight parent) ≤
        (45 * 512 : ENNReal) *
          ∑ parent ∈ selection.selected, weight parent := by
    calc
      (∑ parent ∈ parents.parents, weight parent) ≤
          45 * ∑ parent ∈ selection.onePerY, weight parent :=
        selection.onePerY_weight_retention
      _ ≤ 45 * (512 * ∑ parent ∈ selection.selected, weight parent) := by
        gcongr
        exact selection.residue_weight_retention
      _ = (45 * 512 : ENNReal) *
          ∑ parent ∈ selection.selected, weight parent := by ring
  let selectedRegion : Set Point3 :=
    ⋃ parent ∈ selection.selected,
      wz1PaperGridCube terminal.sqrtRequested.1 parent
  have hregionMeas : MeasurableSet selectedRegion :=
    MeasurableSet.biUnion selection.selected.finite_toSet.countable
      (fun parent _ => wz1PaperGridCube_measurable parent)
  let firstParent := Classical.choose selection.selected_nonempty
  have hfirstParent : firstParent ∈ selection.selected :=
    Classical.choose_spec selection.selected_nonempty
  let commonParentHeight := firstParent.2.2
  have hparentHeight : ∀ parent ∈ selection.selected,
      parent.2.2 = commonParentHeight := by
    intro parent hparent
    rcases parents.parent_hit parent
        (selection.onePerY_subset (selection.selected_subset hparent)) with
      ⟨cell, hcell, hcellParent⟩
    rcases parents.parent_hit firstParent
        (selection.onePerY_subset
          (selection.selected_subset hfirstParent)) with
      ⟨firstCell, hfirstCell, hfirstCellParent⟩
    have hmem := parents.representative_mem_parent cell hcell
    have hfirstMem := parents.representative_mem_parent firstCell hfirstCell
    rw [hcellParent] at hmem
    rw [hfirstCellParent] at hfirstMem
    have hindex : wz1PaperGridIndex terminal.sqrtRequested.1
        (line.representative cell) = parent :=
      (mem_wz1PaperGridCube terminal.sqrtRequested.1 parent _).mp hmem
    have hfirstIndex : wz1PaperGridIndex terminal.sqrtRequested.1
        (line.representative firstCell) = firstParent :=
      (mem_wz1PaperGridCube terminal.sqrtRequested.1 firstParent _).mp
        hfirstMem
    have hheight := line.representative_height cell hcell
    have hfirstHeight := line.representative_height firstCell hfirstCell
    have hz := congrArg (fun idx : ℤ × ℤ × ℤ => idx.2.2) hindex
    have hzFirst := congrArg (fun idx : ℤ × ℤ × ℤ => idx.2.2) hfirstIndex
    simp [wz1PaperGridIndex, gridIndex, hheight, hfirstHeight]
      at hz hzFirst
    exact hz.symm.trans hzFirst
  exact ⟨{
    toPureWZ2FiniteWeightedParentYResidueData := selection
    selected_subset_weightClass := hselectedSubsetClass
    selected_weight_pos := hselectedWeightPos
    visible_to_selected_weight := hvisibleSelected
    selectedRegion := selectedRegion
    selectedRegion_eq := rfl
    selectedRegion_measurable := hregionMeas
    selected_weight_eq := by
      simpa [selectedRegion, weight] using
        pureWZ2TerminalPopularParentWeight_sum_eq
          carrier selection.selected
    commonParentHeight := commonParentHeight
    parent_height_eq := hparentHeight
  }⟩

end Kakeya.Assouad

end
