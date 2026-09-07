import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullbackMass

/-!
# Restrict a frozen balanced cover to common coarse whole cells

A common-spatial cubical restriction of the coarse shading selects a set of
whole balanced cells.  Pull the fine shading back to exactly those cells.
The cover, cell mass, and point compatibility then remain valid without any
new geometric hypothesis.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Restrict a balanced cover to the whole cells selected by a common-spatial
coarse subshading.  The same positive cell mass is retained on every selected
cell. -/
def wholeCellBalancedRestriction
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading selectedCoarse : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hsub : PaperIsSubshading selectedCoarse coarseShading)
    (hcubical : WZ1PaperIsCubicalShading selectedCoarse)
    (hcommon : ∀ parent,
      selectedCoarse.carrier parent =
        coarseShading.carrier parent ∩ selectedCoarse.union) :
    PureWZ2BalancedCoverData cover
      (propertyThreeFinePullbackShading
        cover fineShading selectedCoarse)
      selectedCoarse := by
  let fineSelected :=
    propertyThreeFinePullbackShading cover fineShading selectedCoarse
  let goodCells := propertyThreeGoodCells balanced selectedCoarse
  have hpointCompatibility :
      ∀ source parent,
        WZ1PaperTubeCovers (fine.tube source) (coarse.tube parent) →
          ∀ point, point ∈ fineSelected.carrier source →
            point ∈ selectedCoarse.carrier parent := by
    intro source parent hcovered point hpoint
    rcases propertyThreeFinePullbackShading_support
        cover fineShading selectedCoarse source point hpoint with
      ⟨witness, hwitness, hgrid⟩
    have hpointSelected : point ∈ selectedCoarse.union := by
      rcases hwitness with ⟨witnessParent, hwitnessParent⟩
      refine ⟨witnessParent, hcubical witnessParent witness
        hwitnessParent ?_⟩
      apply (mem_wz1PaperGridCube rho
        (wz1PaperGridIndex rho witness) point).mpr
      exact hgrid.symm
    have hpointCoarse : point ∈ coarseShading.carrier parent :=
      balanced.point_compatibility source parent hcovered point hpoint.1
    rw [hcommon parent]
    exact ⟨hpointCoarse, hpointSelected⟩
  have hfineCellMass : ∀ cell ∈ goodCells,
      volume (fineSelected.union ∩ wz1PaperGridCube rho cell) =
        balanced.cellMass := by
    intro cell hcell
    have hset :
        fineSelected.union ∩ wz1PaperGridCube rho cell =
          fineShading.union ∩ wz1PaperGridCube rho cell := by
      apply Set.Subset.antisymm
      · rintro point ⟨⟨source, hsource⟩, hpointCell⟩
        exact ⟨⟨source, hsource.1⟩, hpointCell⟩
      · rintro point ⟨⟨source, hsource⟩, hpointCell⟩
        rcases (mem_propertyThreeGoodCells
          balanced selectedCoarse cell).mp hcell with
          ⟨_, witness, hwitness, hwitnessCell⟩
        have hwitnessIndex : wz1PaperGridIndex rho witness = cell :=
          (mem_wz1PaperGridCube rho cell witness).mp hwitnessCell
        have hpointIndex : wz1PaperGridIndex rho point = cell :=
          (mem_wz1PaperGridCube rho cell point).mp hpointCell
        refine ⟨⟨source, hsource, ?_⟩, hpointCell⟩
        exact ⟨witness, hwitness, hwitnessIndex.trans hpointIndex.symm⟩
    rw [hset]
    exact balanced.fine_cell_mass cell
      ((mem_propertyThreeGoodCells
        balanced selectedCoarse cell).mp hcell).1
  exact
    { point_compatibility := hpointCompatibility
      coarse_cubical := hcubical
      activeCells := goodCells
      coarse_union_eq :=
        propertyThree_union_eq_goodCells balanced hsub hcubical
      cellMass := balanced.cellMass
      cellMass_pos := balanced.cellMass_pos
      cellMass_ne_top := balanced.cellMass_ne_top
      fine_cell_mass := hfineCellMass }

end Kakeya.Assouad.PureWZ2

end
