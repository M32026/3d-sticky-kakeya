import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinStandardSlabMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperCubeSliceArea

/-!
# Second-cover mass on a standard side-sqrt-rho slab

The union of complete second-cover parents in one standard slab is exactly
the second refined region formed by the selected rho-cells assigned to that
slab.
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

/-- Second refined shading restricted to all genuine second parents in one
standard horizontal slab. -/
def standardSqrtSlabSecondRegion
    (heightIndex : ℤ) : Set Point3 :=
  twoScale.fine.refined.union ∩
    ⋃ parent ∈ pullback.standardSqrtSlabParents heightIndex,
      wz1PaperGridCube twoScale.sqrtRequested.1 parent

/-- The full-parent and selected-rho-cell descriptions of one standard slab
are equal. -/
theorem standardSqrtSlabSecondRegion_eq_coarseRegion
    (heightIndex : ℤ) :
    pullback.standardSqrtSlabSecondRegion heightIndex =
      pullback.standardSqrtSlabCoarseRegion heightIndex := by
  have hrho :
      0 < twoScale.rhoRequested.1 :=
    twoScale.coarse.coarse_extremal.delta_pos
  have hfull :=
    twoScale.fine.refined_cubical.union_eq_activeCells hrho
  ext point
  constructor
  · rintro ⟨hpointFine, hpointParentUnion⟩
    rcases Set.mem_iUnion₂.mp hpointParentUnion with
      ⟨parent, hparent, hpointParent⟩
    have hpointFine' := hpointFine
    rw [hfull] at hpointFine'
    rcases Set.mem_iUnion₂.mp hpointFine' with
      ⟨rhoCell, hrhoCellActive, hpointRhoCell⟩
    have hrhoCellSelected : rhoCell ∈ pullback.selectedCells := by
      rw [pullback.selectedCells_eq]
      exact hrhoCellActive
    have hpointRhoCellAtRho :
        point ∈ wz1PaperGridCube rho rhoCell := by
      simpa only [twoScale.rhoRequested_eq] using hpointRhoCell
    have hpointCanonical :
        point ∈ wz1PaperGridCube twoScale.sqrtRequested.1
          (pullback.standardSecondParent rhoCell) :=
      pullback.standardSecondParent_cell_subset
        hrhoCellSelected hpointRhoCellAtRho
    have hparentIndex :
        wz1PaperGridIndex twoScale.sqrtRequested.1 point = parent :=
      (mem_wz1PaperGridCube
        twoScale.sqrtRequested.1 parent point).mp hpointParent
    have hcanonicalIndex :
        wz1PaperGridIndex twoScale.sqrtRequested.1 point =
          pullback.standardSecondParent rhoCell :=
      (mem_wz1PaperGridCube twoScale.sqrtRequested.1
        (pullback.standardSecondParent rhoCell) point).mp hpointCanonical
    have hparentCanonical :
        parent = pullback.standardSecondParent rhoCell :=
      hparentIndex.symm.trans hcanonicalIndex
    have hparentHeight :
        parent.2.2 = heightIndex :=
      pullback.standardSqrtSlabParent_height hparent
    have hrhoCellSlab :
        rhoCell ∈ pullback.standardSqrtSlabRhoCells heightIndex := by
      apply pullback.mem_standardSqrtSlabRhoCells.mpr
      refine ⟨hrhoCellSelected, ?_⟩
      unfold standardSqrtSlabIndex
      rw [← hparentCanonical]
      exact hparentHeight
    change point ∈ twoScale.fine.refined.union ∩
      wz2RetainedCellsUnion rho
        (pullback.standardSqrtSlabRhoCells heightIndex)
    refine ⟨hpointFine, ?_⟩
    rw [wz2RetainedCellsUnion]
    exact Set.mem_iUnion₂.mpr
      ⟨rhoCell, hrhoCellSlab, hpointRhoCellAtRho⟩
  · intro hpoint
    have hpoint' := hpoint
    change point ∈ twoScale.fine.refined.union ∩
      wz2RetainedCellsUnion rho
        (pullback.standardSqrtSlabRhoCells heightIndex) at hpoint'
    rw [wz2RetainedCellsUnion] at hpoint'
    rcases Set.mem_iUnion₂.mp hpoint'.2 with
      ⟨rhoCell, hrhoCellSlab, hpointRhoCell⟩
    let parent := pullback.standardSecondParent rhoCell
    have hparent :
        parent ∈ pullback.standardSqrtSlabParents heightIndex :=
      Finset.mem_image.mpr ⟨rhoCell, hrhoCellSlab, rfl⟩
    have hpointParent :
        point ∈ wz1PaperGridCube twoScale.sqrtRequested.1 parent :=
      pullback.standardSqrtSlabRhoCell_subset_parent
        hrhoCellSlab hpointRhoCell
    exact
      ⟨hpoint'.1, Set.mem_iUnion₂.mpr
        ⟨parent, hparent, hpointParent⟩⟩

/-- Exact balanced second-cover mass on one standard slab. -/
theorem standardSqrtSlabSecondRegion_volume
    (heightIndex : ℤ) :
    volume (pullback.standardSqrtSlabSecondRegion heightIndex) =
      ((pullback.standardSqrtSlabParents heightIndex).card : ENNReal) *
        twoScale.fine.balanced.cellMass := by
  unfold standardSqrtSlabSecondRegion
  exact
    twoScale.fine.balanced.selected_cells_volume
      (pullback.standardSqrtSlabParents heightIndex)
      (pullback.standardSqrtSlabParents_subset_active heightIndex)

/-- The full second-parent balanced mass is the same `G_S` used by the
standard-slab source/coarse cross identity. -/
theorem standardSqrtSlab_parentMass_eq_coarseVolume
    (heightIndex : ℤ) :
    ((pullback.standardSqrtSlabParents heightIndex).card : ENNReal) *
        twoScale.fine.balanced.cellMass =
      volume (pullback.standardSqrtSlabCoarseRegion heightIndex) := by
  rw [← pullback.standardSqrtSlabSecondRegion_volume heightIndex,
    pullback.standardSqrtSlabSecondRegion_eq_coarseRegion heightIndex]

end PureWZ2TwoScaleCellPullbackData

end Kakeya.Assouad

end
