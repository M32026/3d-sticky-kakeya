import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSecondParents

/-!
# Standard side-sqrt-rho slab cells

Selected rho-cells are grouped by the vertical index of their canonical
second-cover spatial parent.  These are standard, unshifted sqrt-rho slabs.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2TwoScaleCellPullbackData

variable
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)

/-- Standard sqrt-rho slab index of one selected rho-cell. -/
def standardSqrtSlabIndex
    (cell : ℤ × ℤ × ℤ) : ℤ :=
  (pullback.standardSecondParent cell).2.2

/-- Standard slab indices actually occupied by selected rho-cells. -/
def standardSqrtSlabIndices : Finset ℤ :=
  pullback.selectedCells.image pullback.standardSqrtSlabIndex

/-- Selected rho-cells whose canonical second parent lies in one standard
horizontal sqrt-rho slab. -/
def standardSqrtSlabRhoCells
    (heightIndex : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  pullback.selectedCells.filter fun cell =>
    pullback.standardSqrtSlabIndex cell = heightIndex

/-- Genuine second-cover spatial parents occurring over one standard slab. -/
def standardSqrtSlabParents
    (heightIndex : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  (pullback.standardSqrtSlabRhoCells heightIndex).image
    pullback.standardSecondParent

theorem standardSqrtSlabRhoCells_subset
    (heightIndex : ℤ) :
    pullback.standardSqrtSlabRhoCells heightIndex ⊆
      pullback.selectedCells :=
  Finset.filter_subset _ _

theorem mem_standardSqrtSlabRhoCells
    {heightIndex : ℤ}
    {cell : ℤ × ℤ × ℤ} :
    cell ∈ pullback.standardSqrtSlabRhoCells heightIndex ↔
      cell ∈ pullback.selectedCells ∧
        pullback.standardSqrtSlabIndex cell = heightIndex := by
  simp [standardSqrtSlabRhoCells]

theorem standardSqrtSlabRhoCell_parent_active
    {heightIndex : ℤ}
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ pullback.standardSqrtSlabRhoCells heightIndex) :
    pullback.standardSecondParent cell ∈
      twoScale.fine.balanced.activeCells :=
  pullback.standardSecondParent_active
    (pullback.standardSqrtSlabRhoCells_subset heightIndex hcell)

theorem standardSqrtSlabRhoCell_subset_parent
    {heightIndex : ℤ}
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ pullback.standardSqrtSlabRhoCells heightIndex) :
    wz1PaperGridCube rho cell ⊆
      wz1PaperGridCube twoScale.sqrtRequested.1
        (pullback.standardSecondParent cell) :=
  pullback.standardSecondParent_cell_subset
    (pullback.standardSqrtSlabRhoCells_subset heightIndex hcell)

theorem standardSqrtSlabRhoCell_parent_height
    {heightIndex : ℤ}
    {cell : ℤ × ℤ × ℤ}
    (hcell : cell ∈ pullback.standardSqrtSlabRhoCells heightIndex) :
    (pullback.standardSecondParent cell).2.2 = heightIndex :=
  (pullback.mem_standardSqrtSlabRhoCells.mp hcell).2

theorem standardSqrtSlabParents_subset_active
    (heightIndex : ℤ) :
    pullback.standardSqrtSlabParents heightIndex ⊆
      twoScale.fine.balanced.activeCells := by
  intro parent hparent
  rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
  exact pullback.standardSqrtSlabRhoCell_parent_active hcell

theorem standardSqrtSlabParent_height
    {heightIndex : ℤ}
    {parent : ℤ × ℤ × ℤ}
    (hparent :
      parent ∈ pullback.standardSqrtSlabParents heightIndex) :
    parent.2.2 = heightIndex := by
  rcases Finset.mem_image.mp hparent with ⟨cell, hcell, rfl⟩
  exact pullback.standardSqrtSlabRhoCell_parent_height hcell

theorem standardSqrtSlabRhoCells_nonempty
    {heightIndex : ℤ}
    (hheight : heightIndex ∈ pullback.standardSqrtSlabIndices) :
    (pullback.standardSqrtSlabRhoCells heightIndex).Nonempty := by
  rcases Finset.mem_image.mp hheight with ⟨cell, hcell, hindex⟩
  exact
    ⟨cell, pullback.mem_standardSqrtSlabRhoCells.mpr
      ⟨hcell, hindex⟩⟩

/-- The standard slab rho-cell families partition all selected rho-cells. -/
theorem selectedCells_eq_biUnion_standardSqrtSlabRhoCells :
    pullback.selectedCells =
      pullback.standardSqrtSlabIndices.biUnion
        pullback.standardSqrtSlabRhoCells := by
  ext cell
  constructor
  · intro hcell
    let heightIndex := pullback.standardSqrtSlabIndex cell
    apply Finset.mem_biUnion.mpr
    refine ⟨heightIndex, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
    · exact pullback.mem_standardSqrtSlabRhoCells.mpr ⟨hcell, rfl⟩
  · intro hcell
    rcases Finset.mem_biUnion.mp hcell with ⟨heightIndex, _, hcell⟩
    exact pullback.standardSqrtSlabRhoCells_subset heightIndex hcell

end PureWZ2TwoScaleCellPullbackData

end Kakeya.Assouad

end
