import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalGlobalBinFamily

/-!
# Actual second-sticky parents met by the source-slope horizontal line

The source representative need not lie in the second fine shading.  We first
recover its selected `rho` cell from the pullback carrier, choose a genuine
second-fine witness in that same cell, and only then use `fine_cell_nested`.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceHorizontalFixedBinParentData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedBinData window) where
  rhoCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  rhoCell_selected :
    ∀ cell ∈ line.heavyCells, rhoCell cell ∈ pullback.selectedCells
  representative_mem_rhoCell :
    ∀ cell ∈ line.heavyCells, line.representative cell ∈
      wz1PaperGridCube rho (rhoCell cell)
  fineIndex : (ℤ × ℤ × ℤ) → Fin twoScale.fine.selected.family.card
  finePoint : (ℤ × ℤ × ℤ) → Point3
  fine_point_mem :
    ∀ cell ∈ line.heavyCells,
      finePoint cell ∈ twoScale.fine.refined.carrier (fineIndex cell)
  fine_point_mem_rhoCell :
    ∀ cell ∈ line.heavyCells, finePoint cell ∈
      wz1PaperGridCube rho (rhoCell cell)
  parentCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  parent_active :
    ∀ cell ∈ line.heavyCells,
      parentCell cell ∈ twoScale.fine.balanced.activeCells
  rho_cell_nested :
    ∀ cell (hcell : cell ∈ line.heavyCells),
      wz1PaperGridCube rho (rhoCell cell) ⊆
        wz1PaperGridCube twoScale.sqrtRequested.1 (parentCell cell)
  representative_mem_parent :
    ∀ cell ∈ line.heavyCells, line.representative cell ∈
      wz1PaperGridCube twoScale.sqrtRequested.1 (parentCell cell)
  parents : Finset (ℤ × ℤ × ℤ)
  parents_eq : parents = line.heavyCells.image parentCell
  parents_nonempty : parents.Nonempty
  parents_subset : parents ⊆ twoScale.fine.balanced.activeCells
  parent_hit :
    ∀ parent ∈ parents, ∃ cell ∈ line.heavyCells, parentCell cell = parent

theorem PureWZ2SourceHorizontalFixedBinData.toParents
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedBinData window) :
    Nonempty (PureWZ2SourceHorizontalFixedBinParentData line) := by
  have hrepPullback :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈ pullback.shading.union := by
    intro cell hcell
    have hwindow := line.representative_mem cell hcell
    have hshadow : line.representative cell ∈ prepared.shadow.union := by
      rcases hwindow with ⟨index, hindex⟩
      exact ⟨index, window.subshading index hindex⟩
    rwa [prepared.shadow_union] at hshadow
  have hselectedExists :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        ∃ selected ∈ pullback.selectedCells,
          line.representative cell ∈ wz1PaperGridCube rho selected := by
    intro cell hcell
    have hpoint := hrepPullback cell hcell
    rw [pullback.union_eq] at hpoint
    have hregion := hpoint.2
    rw [pullback.selectedRegion_eq] at hregion
    rcases Set.mem_iUnion₂.mp hregion with ⟨selected, hselected, hmem⟩
    exact ⟨selected, hselected, hmem⟩
  let rhoCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    if hcell : cell ∈ line.heavyCells then
      Classical.choose (hselectedExists cell hcell) else (0, 0, 0)
  have hrhoSelected :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        rhoCell cell ∈ pullback.selectedCells := by
    intro cell hcell
    simp only [rhoCell, dif_pos hcell]
    exact (Classical.choose_spec (hselectedExists cell hcell)).1
  have hrepRho :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈ wz1PaperGridCube rho (rhoCell cell) := by
    intro cell hcell
    simp only [rhoCell, dif_pos hcell]
    exact (Classical.choose_spec (hselectedExists cell hcell)).2
  have hfineExists :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        ∃ point, point ∈ twoScale.fine.refined.union ∧
          point ∈ wz1PaperGridCube rho (rhoCell cell) := by
    intro cell hcell
    have hactive : rhoCell cell ∈ wz1PaperActiveCells
        twoScale.fine.refined
          twoScale.coarseGrains.extremal.delta_pos := by
      simpa [pullback.selectedCells_eq, twoScale.rhoRequested_eq] using
        hrhoSelected cell hcell
    rcases ((mem_wz1PaperActiveCells twoScale.fine.refined
      twoScale.coarseGrains.extremal.delta_pos (rhoCell cell)).mp hactive).2 with
      ⟨point, hpointUnion, hpointCell⟩
    exact ⟨point, hpointUnion, by
      simpa only [twoScale.rhoRequested_eq] using hpointCell⟩
  let finePoint : (ℤ × ℤ × ℤ) → Point3 := fun cell =>
    if hcell : cell ∈ line.heavyCells then
      Classical.choose (hfineExists cell hcell) else 0
  have hfinePoint :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        finePoint cell ∈ twoScale.fine.refined.union ∧
          finePoint cell ∈ wz1PaperGridCube rho (rhoCell cell) := by
    intro cell hcell
    simp only [finePoint, dif_pos hcell]
    exact Classical.choose_spec (hfineExists cell hcell)
  let fineIndex : (ℤ × ℤ × ℤ) →
      Fin twoScale.fine.selected.family.card := fun cell =>
    if hcell : cell ∈ line.heavyCells then
      Classical.choose (hfinePoint cell hcell).1
    else ⟨0, twoScale.fine.selected_nonempty⟩
  have hfineCarrier :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        finePoint cell ∈ twoScale.fine.refined.carrier (fineIndex cell) := by
    intro cell hcell
    simp only [fineIndex, dif_pos hcell]
    exact Classical.choose_spec (hfinePoint cell hcell).1
  have hnestedExists :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        ∃ parent ∈ twoScale.fine.balanced.activeCells,
          wz1PaperGridCube twoScale.rhoRequested.1
              (wz1PaperGridIndex twoScale.rhoRequested.1 (finePoint cell)) ⊆
            wz1PaperGridCube twoScale.sqrtRequested.1 parent := by
    intro cell hcell
    exact twoScale.fine.balanced.fine_cell_nested
      (fineIndex cell) (finePoint cell) (hfineCarrier cell hcell)
  let parentCell : (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ) := fun cell =>
    if hcell : cell ∈ line.heavyCells then
      Classical.choose (hnestedExists cell hcell) else (0, 0, 0)
  have hparentActive :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        parentCell cell ∈ twoScale.fine.balanced.activeCells := by
    intro cell hcell
    simp only [parentCell, dif_pos hcell]
    exact (Classical.choose_spec (hnestedExists cell hcell)).1
  have hindexEq :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        wz1PaperGridIndex twoScale.rhoRequested.1 (finePoint cell) = rhoCell cell := by
    intro cell hcell
    rw [twoScale.rhoRequested_eq]
    exact (mem_wz1PaperGridCube rho (rhoCell cell) (finePoint cell)).mp
      (hfinePoint cell hcell).2
  have hnested :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        wz1PaperGridCube rho (rhoCell cell) ⊆
          wz1PaperGridCube twoScale.sqrtRequested.1 (parentCell cell) := by
    intro cell hcell
    have hraw := (Classical.choose_spec (hnestedExists cell hcell)).2
    simp only [parentCell, dif_pos hcell]
    have hsource :
        wz1PaperGridCube rho (rhoCell cell) =
          wz1PaperGridCube twoScale.rhoRequested.1
            (wz1PaperGridIndex twoScale.rhoRequested.1 (finePoint cell)) := by
      rw [hindexEq cell hcell]
      congr 1
      exact twoScale.rhoRequested_eq.symm
    rw [hsource]
    exact hraw
  have hrepParent :
      ∀ cell (hcell : cell ∈ line.heavyCells),
        line.representative cell ∈
          wz1PaperGridCube twoScale.sqrtRequested.1 (parentCell cell) := by
    intro cell hcell
    exact hnested cell hcell (hrepRho cell hcell)
  let parents := line.heavyCells.image parentCell
  exact ⟨{
    rhoCell := rhoCell
    rhoCell_selected := hrhoSelected
    representative_mem_rhoCell := hrepRho
    fineIndex := fineIndex
    finePoint := finePoint
    fine_point_mem := hfineCarrier
    fine_point_mem_rhoCell := fun cell hcell => (hfinePoint cell hcell).2
    parentCell := parentCell
    parent_active := hparentActive
    rho_cell_nested := hnested
    representative_mem_parent := hrepParent
    parents := parents
    parents_eq := rfl
    parents_nonempty := line.heavyCells_nonempty.image parentCell
    parents_subset := by
      intro parent hparent
      rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
      exact hparentActive cell hcell
    parent_hit := by
      intro parent hparent
      rcases Finset.mem_image.mp hparent with ⟨cell, hcell, heq⟩
      exact ⟨cell, hcell, heq⟩
  }⟩

/-- Backwards-compatible parent data on the maximal global bin. -/
abbrev PureWZ2SourceHorizontalParentData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window) :=
  PureWZ2SourceHorizontalFixedBinParentData line.toFixedBinData

/-- Compatibility wrapper for the formerly maximal-bin-only parent API. -/
theorem PureWZ2SourceHorizontalFixedLineData.toParents
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window) :
    Nonempty (PureWZ2SourceHorizontalParentData line) :=
  line.toFixedBinData.toParents

end Kakeya.Assouad
