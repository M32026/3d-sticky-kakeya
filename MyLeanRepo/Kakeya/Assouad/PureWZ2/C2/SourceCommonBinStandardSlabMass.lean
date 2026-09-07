import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabCells
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers

/-!
# Exact mass on standard side-sqrt-rho slabs

The source and second-refined regions use the same selected rho-cell family.
Their exact cellwise formulas give the source/coarse cross identity without
division.
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

/-- Source pullback restricted to a selected family of rho-cells. -/
def selectedRhoCellsSourceRegion
    (cells : Finset (ℤ × ℤ × ℤ)) : Set Point3 :=
  pullback.shading.union ∩ wz2RetainedCellsUnion rho cells

/-- Second refined shading restricted to the same rho-cell family. -/
def selectedRhoCellsCoarseRegion
    (cells : Finset (ℤ × ℤ × ℤ)) : Set Point3 :=
  twoScale.fine.refined.union ∩ wz2RetainedCellsUnion rho cells

theorem selectedRhoCellsSourceRegion_eq_biUnion
    (cells : Finset (ℤ × ℤ × ℤ)) :
    pullback.selectedRhoCellsSourceRegion cells =
      ⋃ cell ∈ cells,
        pullback.shading.union ∩ wz1PaperGridCube rho cell := by
  ext point
  simp [selectedRhoCellsSourceRegion, wz2RetainedCellsUnion]

/-- Exact source mass on any selected rho-cell subfamily. -/
theorem selectedRhoCellsSourceRegion_volume
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : cells ⊆ pullback.selectedCells) :
    volume (pullback.selectedRhoCellsSourceRegion cells) =
      (cells.card : ENNReal) *
        twoScale.coarse.balanced.cellMass := by
  rw [pullback.selectedRhoCellsSourceRegion_eq_biUnion]
  have hdisjoint :
      (cells : Set (ℤ × ℤ × ℤ)).PairwiseDisjoint
        (fun cell =>
          pullback.shading.union ∩ wz1PaperGridCube rho cell) := by
    intro first _ second _ hne
    exact (wz1PaperGridCube_disjoint hne).mono
      Set.inter_subset_right Set.inter_subset_right
  have hmeasurable :
      ∀ cell ∈ cells,
        MeasurableSet
          (pullback.shading.union ∩ wz1PaperGridCube rho cell) := by
    intro cell _
    exact (measurableSet_shading_union pullback.shading).inter
      (wz1PaperGridCube_measurable cell)
  rw [MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable]
  calc
    (∑ cell ∈ cells,
        volume
          (pullback.shading.union ∩
            wz1PaperGridCube rho cell)) =
        ∑ _cell ∈ cells, twoScale.coarse.balanced.cellMass := by
      apply Finset.sum_congr rfl
      intro cell hcell
      exact pullback.cell_mass cell (hcells hcell)
    _ = (cells.card : ENNReal) *
        twoScale.coarse.balanced.cellMass := by
      simp [Finset.sum_const]

/-- A selected rho-cell is wholly contained in the second refined union. -/
theorem selectedRhoCell_subset_fine_refined
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ pullback.selectedCells) :
    wz1PaperGridCube rho cell ⊆ twoScale.fine.refined.union := by
  have hrho :
      0 < twoScale.rhoRequested.1 :=
    twoScale.coarse.coarse_extremal.delta_pos
  have hactive :
      cell ∈ wz1PaperActiveCells twoScale.fine.refined hrho := by
    simpa only [pullback.selectedCells_eq] using hcell
  rw [mem_wz1PaperActiveCells] at hactive
  rcases hactive.2 with ⟨witness, hwitness, hwitnessCell⟩
  rcases hwitness with ⟨index, hwitnessCarrier⟩
  intro point hpointCell
  have hwitnessIndex :
      wz1PaperGridIndex twoScale.rhoRequested.1 witness = cell :=
    (mem_wz1PaperGridCube
      twoScale.rhoRequested.1 cell witness).mp hwitnessCell
  have hpointSameCell :
      point ∈
        wz1PaperGridCube twoScale.rhoRequested.1
          (wz1PaperGridIndex twoScale.rhoRequested.1 witness) := by
    rw [hwitnessIndex, twoScale.rhoRequested_eq]
    exact hpointCell
  exact
    ⟨index, twoScale.fine.refined_cubical
      index witness hwitnessCarrier hpointSameCell⟩

theorem selectedRhoCellsCoarseRegion_eq_retained
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : cells ⊆ pullback.selectedCells) :
    selectedRhoCellsCoarseRegion (twoScale := twoScale) cells =
      wz2RetainedCellsUnion rho cells := by
  apply Set.inter_eq_right.mpr
  rw [wz2RetainedCellsUnion]
  intro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
  exact pullback.selectedRhoCell_subset_fine_refined
    (hcells hcell) hpointCell

/-- Exact geometric coarse volume on the same rho-cell subfamily. -/
theorem selectedRhoCellsCoarseRegion_volume
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : cells ⊆ pullback.selectedCells) :
    volume (selectedRhoCellsCoarseRegion
      (twoScale := twoScale) cells) =
      (cells.card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) := by
  rw [pullback.selectedRhoCellsCoarseRegion_eq_retained cells hcells]
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarse.coarse_extremal.delta_pos
  exact wz1PaperGridCube_volume_biUnion hrho cells

/-- Exact source/coarse cross identity on any selected rho-cell subfamily. -/
theorem selectedRhoCells_source_coarse_cross
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : cells ⊆ pullback.selectedCells) :
    volume (pullback.selectedRhoCellsSourceRegion cells) *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
      volume (selectedRhoCellsCoarseRegion
        (twoScale := twoScale) cells) *
          twoScale.coarse.balanced.cellMass := by
  rw [pullback.selectedRhoCellsSourceRegion_volume cells hcells,
    pullback.selectedRhoCellsCoarseRegion_volume cells hcells]
  ring

/-- Standard-slab source region. -/
def standardSqrtSlabSourceRegion
    (heightIndex : ℤ) : Set Point3 :=
  pullback.selectedRhoCellsSourceRegion
    (pullback.standardSqrtSlabRhoCells heightIndex)

/-- Standard-slab second-refined rho-cell region. -/
def standardSqrtSlabCoarseRegion
    (heightIndex : ℤ) : Set Point3 :=
  selectedRhoCellsCoarseRegion (twoScale := twoScale)
    (pullback.standardSqrtSlabRhoCells heightIndex)

theorem standardSqrtSlabSourceRegion_volume
    (heightIndex : ℤ) :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex) =
      ((pullback.standardSqrtSlabRhoCells heightIndex).card : ENNReal) *
        twoScale.coarse.balanced.cellMass :=
  pullback.selectedRhoCellsSourceRegion_volume _
    (pullback.standardSqrtSlabRhoCells_subset heightIndex)

theorem standardSqrtSlabCoarseRegion_volume
    (heightIndex : ℤ) :
    volume (pullback.standardSqrtSlabCoarseRegion heightIndex) =
      ((pullback.standardSqrtSlabRhoCells heightIndex).card : ENNReal) *
        volume (wz1PaperGridCube rho (0, 0, 0)) :=
  pullback.selectedRhoCellsCoarseRegion_volume _
    (pullback.standardSqrtSlabRhoCells_subset heightIndex)

/-- The exact `A_S`/`G_S` cross identity on one unshifted standard slab. -/
theorem standardSqrtSlab_source_coarse_cross
    (heightIndex : ℤ) :
    volume (pullback.standardSqrtSlabSourceRegion heightIndex) *
          volume (wz1PaperGridCube rho (0, 0, 0)) =
      volume (pullback.standardSqrtSlabCoarseRegion heightIndex) *
          twoScale.coarse.balanced.cellMass :=
  pullback.selectedRhoCells_source_coarse_cross _
    (pullback.standardSqrtSlabRhoCells_subset heightIndex)

end PureWZ2TwoScaleCellPullbackData

end Kakeya.Assouad

end
