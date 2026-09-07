import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinSecondCoverCells

/-!
# Canonical second-cover parent of a selected rho-cell

Every rho-cell selected by the two-scale pullback is a genuine active cell of
the second refined shading.  The second balanced cover places that complete
rho-cell in a unique active side-`sqrt rho` spatial parent.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

namespace PureWZ2TwoScaleCellPullbackData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)

private theorem exists_standardSecondParent
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ pullback.selectedCells) :
    ∃ parent ∈ twoScale.fine.balanced.activeCells,
      wz1PaperGridCube rho cell ⊆
        wz1PaperGridCube twoScale.sqrtRequested.1 parent := by
  have hrho :
      0 < twoScale.rhoRequested.1 :=
    twoScale.coarse.coarse_extremal.delta_pos
  have hactive :
      cell ∈ wz1PaperActiveCells twoScale.fine.refined hrho := by
    simpa only [pullback.selectedCells_eq] using hcell
  rw [mem_wz1PaperActiveCells] at hactive
  rcases hactive.2 with ⟨point, hpointFine, hpointCell⟩
  rcases hpointFine with ⟨fineIndex, hpointCarrier⟩
  rcases
      twoScale.fine.balanced.fine_cell_nested
        fineIndex point hpointCarrier
    with
    ⟨parent, hparent, hnested⟩
  have hindex :
      wz1PaperGridIndex twoScale.rhoRequested.1 point = cell :=
    (mem_wz1PaperGridCube
      twoScale.rhoRequested.1 cell point).mp hpointCell
  refine ⟨parent, hparent, ?_⟩
  rw [hindex] at hnested
  simpa only [twoScale.rhoRequested_eq] using hnested

/-- Canonical genuine second-cover parent of one selected rho-cell. -/
noncomputable def standardSecondParent
    (cell : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  if hcell : cell ∈ pullback.selectedCells then
    Classical.choose (pullback.exists_standardSecondParent hcell)
  else
    (0, 0, 0)

theorem standardSecondParent_active
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ pullback.selectedCells) :
    pullback.standardSecondParent cell ∈
      twoScale.fine.balanced.activeCells := by
  rw [standardSecondParent, dif_pos hcell]
  exact
    (Classical.choose_spec
      (pullback.exists_standardSecondParent hcell)).1

theorem standardSecondParent_cell_subset
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ pullback.selectedCells) :
    wz1PaperGridCube rho cell ⊆
      wz1PaperGridCube twoScale.sqrtRequested.1
        (pullback.standardSecondParent cell) := by
  rw [standardSecondParent, dif_pos hcell]
  exact
    (Classical.choose_spec
      (pullback.exists_standardSecondParent hcell)).2

/-- Complete-grid containment makes the active second parent unique. -/
theorem standardSecondParent_unique
    {cell parent : ℤ × ℤ × ℤ}
    (hcell : cell ∈ pullback.selectedCells)
    (_hparent : parent ∈ twoScale.fine.balanced.activeCells)
    (hsubset :
      wz1PaperGridCube rho cell ⊆
        wz1PaperGridCube twoScale.sqrtRequested.1 parent) :
    parent = pullback.standardSecondParent cell := by
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarse.coarse_extremal.delta_pos
  let point := cellCorner rho cell
  have hpoint : point ∈ wz1PaperGridCube rho cell :=
    cellCorner_mem_gridCube hrho cell
  have hpointParent :
      point ∈ wz1PaperGridCube twoScale.sqrtRequested.1 parent :=
    hsubset hpoint
  have hpointCanonical :
      point ∈ wz1PaperGridCube twoScale.sqrtRequested.1
        (pullback.standardSecondParent cell) :=
    pullback.standardSecondParent_cell_subset hcell hpoint
  have hparentIndex :
      wz1PaperGridIndex twoScale.sqrtRequested.1 point = parent :=
    (mem_wz1PaperGridCube
      twoScale.sqrtRequested.1 parent point).mp hpointParent
  have hcanonicalIndex :
      wz1PaperGridIndex twoScale.sqrtRequested.1 point =
        pullback.standardSecondParent cell :=
    (mem_wz1PaperGridCube twoScale.sqrtRequested.1
      (pullback.standardSecondParent cell) point).mp hpointCanonical
  exact hparentIndex.symm.trans hcanonicalIndex

end PureWZ2TwoScaleCellPullbackData

end Kakeya.Assouad

end
