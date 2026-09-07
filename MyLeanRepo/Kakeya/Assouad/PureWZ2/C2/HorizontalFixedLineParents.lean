import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLine
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SecondStageSources

/-!
# Actual second-stage parents hit by the horizontal fixed line

The Lemma-23 diameter grid and the paper `rho` grid are different.  Parent
selection is therefore routed through the genuine exact-slice representative
point and `fine_cell_nested`; no equality of the two grid indices is asserted.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2HorizontalFixedLineParentData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    (line : PureWZ2HorizontalFixedLineData windowed) where
  fineIndex : (ℤ × ℤ × ℤ) → Fin twoScale.fine.selected.family.card
  representative_mem_fine :
    ∀ cell ∈ line.heavyCells,
      line.representative cell ∈ twoScale.fine.refined.carrier (fineIndex cell)
  parentCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  parent_active :
    ∀ cell ∈ line.heavyCells,
      parentCell cell ∈ twoScale.fine.balanced.activeCells
  fine_paper_cell_nested :
    ∀ cell (hcell : cell ∈ line.heavyCells),
      wz1PaperGridCube twoScale.rhoRequested.1
          (wz1PaperGridIndex twoScale.rhoRequested.1
            (line.representative cell)) ⊆
        wz1PaperGridCube twoScale.sqrtRequested.1 (parentCell cell)
  representative_mem_parent :
    ∀ cell ∈ line.heavyCells,
      line.representative cell ∈
        wz1PaperGridCube twoScale.sqrtRequested.1 (parentCell cell)
  parents : Finset (ℤ × ℤ × ℤ)
  parents_eq : parents = line.heavyCells.image parentCell
  parents_nonempty : parents.Nonempty
  parents_subset : parents ⊆ twoScale.fine.balanced.activeCells
  parent_hit :
    ∀ parent ∈ parents,
      ∃ cell ∈ line.heavyCells, parentCell cell = parent

theorem PureWZ2HorizontalFixedLineData.toParents
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    (line : PureWZ2HorizontalFixedLineData windowed) :
    Nonempty (PureWZ2HorizontalFixedLineParentData line) := by
  have hrho : 0 < twoScale.rhoRequested.1 :=
    twoScale.coarseGrains.extremal.delta_pos
  have hpointFine :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈ twoScale.fine.refined.union := by
    intro cell hcell
    have hwindow := line.representative_mem cell hcell
    have hshadow : line.representative cell ∈ prepared.shadow.union := by
      rcases hwindow with ⟨index, hindex⟩
      exact ⟨index, windowed.subshading index hindex⟩
    rw [prepared.shadow_union] at hshadow
    exact hshadow
  let fineIndex : (ℤ × ℤ × ℤ) →
      Fin twoScale.fine.selected.family.card := fun cell =>
    if hcell : cell ∈ line.heavyCells then
      Classical.choose (hpointFine cell hcell)
    else ⟨0, twoScale.fine.selected_nonempty⟩
  have hpointCarrier :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈
          twoScale.fine.refined.carrier (fineIndex cell) := by
    intro cell hcell
    simp only [fineIndex, dif_pos hcell]
    exact Classical.choose_spec (hpointFine cell hcell)
  have hnestedExists :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        ∃ parent ∈ twoScale.fine.balanced.activeCells,
          wz1PaperGridCube twoScale.rhoRequested.1
              (wz1PaperGridIndex twoScale.rhoRequested.1
                (line.representative cell)) ⊆
            wz1PaperGridCube twoScale.sqrtRequested.1 parent := by
    intro cell hcell
    exact twoScale.fine.balanced.fine_cell_nested
      (fineIndex cell) (line.representative cell) (hpointCarrier cell hcell)
  let parentCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    if hcell : cell ∈ line.heavyCells then
      Classical.choose (hnestedExists cell hcell)
    else (0, 0, 0)
  have hparentActive :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        parentCell cell ∈ twoScale.fine.balanced.activeCells := by
    intro cell hcell
    simp only [parentCell, dif_pos hcell]
    exact (Classical.choose_spec (hnestedExists cell hcell)).1
  have hnested :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        wz1PaperGridCube twoScale.rhoRequested.1
            (wz1PaperGridIndex twoScale.rhoRequested.1
              (line.representative cell)) ⊆
          wz1PaperGridCube twoScale.sqrtRequested.1 (parentCell cell) := by
    intro cell hcell
    simp only [parentCell, dif_pos hcell]
    exact (Classical.choose_spec (hnestedExists cell hcell)).2
  have hrepresentativeParent :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈
          wz1PaperGridCube twoScale.sqrtRequested.1 (parentCell cell) := by
    intro cell hcell
    apply hnested cell hcell
    exact (mem_wz1PaperGridCube _ _ _).mpr rfl
  let parents := line.heavyCells.image parentCell
  have hparentsNonempty : parents.Nonempty :=
    line.heavyCells_nonempty.image parentCell
  exact
    ⟨{ fineIndex := fineIndex
       representative_mem_fine := hpointCarrier
       parentCell := parentCell
       parent_active := hparentActive
       fine_paper_cell_nested := hnested
       representative_mem_parent := hrepresentativeParent
       parents := parents
       parents_eq := rfl
       parents_nonempty := hparentsNonempty
       parents_subset := by
         intro parent hparent
         rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
         exact hparentActive cell hcell
       parent_hit := by
         intro parent hparent
         rcases Finset.mem_image.mp hparent with ⟨cell, hcell, heq⟩
         exact ⟨cell, hcell, heq⟩ }⟩

end Kakeya.Assouad
