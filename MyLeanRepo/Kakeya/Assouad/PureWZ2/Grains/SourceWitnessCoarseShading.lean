import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseParentPairRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-!
# Source-witness coarse shading for a frozen Section 6 cover

Rebuild a coarse whole-cell shading directly from the frozen fine shading.
Every retained parent-cell stores an actual fine source and an actual shaded
point in that cell.  This restores the provenance needed by a coarse-anchor
global-grain construction without strengthening `PureWZ2PropStickyData`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Coarse cells in which one actual source from the given parent fiber has
a shaded point. -/
def sourceWitnessParentCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced :
      PureWZ2BalancedCoverData cover fineShading coarseShading)
    (parent : Fin coarse.card) : Finset (ℤ × ℤ × ℤ) :=
  balanced.activeCells.filter fun cell =>
    ∃ source : Fin fine.card,
      cover.toPaperTubeCover.parent source = parent ∧
        (fineShading.carrier source ∩
          wz1PaperGridCube rho cell).Nonempty

/-- A balanced coarse shading reconstructed from actual fine source cells. -/
structure PureWZ2SourceWitnessCoarseShadingData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original :
      PureWZ2BalancedCoverData cover fineShading coarseShading) where
  parentCells : Fin coarse.card → Finset (ℤ × ℤ × ℤ)
  parentCells_eq :
    ∀ parent, parentCells parent = sourceWitnessParentCells original parent
  source_witness :
    ∀ parent cell, cell ∈ parentCells parent →
      ∃ source point,
        cover.toPaperTubeCover.parent source = parent ∧
          point ∈ fineShading.carrier source ∧
          point ∈ wz1PaperGridCube rho cell
  retained_cell_owned :
    ∀ cell ∈ original.activeCells,
      ∃ parent, cell ∈ parentCells parent
  shading : WZ1PaperTubeShading coarse
  shading_carrier_eq :
    ∀ parent,
      shading.carrier parent =
        ⋃ cell ∈ parentCells parent, wz1PaperGridCube rho cell
  subshading : PaperIsSubshading shading coarseShading
  balanced : PureWZ2BalancedCoverData cover fineShading shading
  balanced_activeCells_eq : balanced.activeCells = original.activeCells

/-- Rebuild the source-witness coarse shading from the public frozen balanced
cover.  No new geometric hypothesis is required: the original point
compatibility and coarse cubicality put each witnessed whole cell in its
parent carrier. -/
theorem source_witness_coarse_shading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (original :
      PureWZ2BalancedCoverData cover fineShading coarseShading) :
    Nonempty (PureWZ2SourceWitnessCoarseShadingData original) := by
  let parentCells : Fin coarse.card → Finset (ℤ × ℤ × ℤ) :=
    sourceWitnessParentCells original
  have hsourceWitness :
      ∀ parent cell, cell ∈ parentCells parent →
        ∃ source point,
          cover.toPaperTubeCover.parent source = parent ∧
            point ∈ fineShading.carrier source ∧
            point ∈ wz1PaperGridCube rho cell := by
    intro parent cell hcell
    have hwitness :=
      (Finset.mem_filter.mp hcell).2
    rcases hwitness with
      ⟨source, hparent, point, hpointFine, hpointCell⟩
    exact ⟨source, point, hparent, hpointFine, hpointCell⟩
  have hparentCellSubset :
      ∀ parent cell, cell ∈ parentCells parent →
        wz1PaperGridCube rho cell ⊆ coarseShading.carrier parent := by
    intro parent cell hcell
    rcases hsourceWitness parent cell hcell with
      ⟨source, point, hparent, hpointFine, hpointCell⟩
    have hpointCoarse : point ∈ coarseShading.carrier parent := by
      have hcompat := original.point_compatibility source parent
        (by
          rw [← hparent]
          exact cover.toPaperTubeCover.parent_covers source)
        point hpointFine
      exact hcompat
    have hwhole := original.coarse_cubical parent point hpointCoarse
    intro other hother
    apply hwhole
    apply (mem_wz1PaperGridCube rho
      (wz1PaperGridIndex rho point) other).mpr
    have hotherIndex : wz1PaperGridIndex rho other = cell :=
      (mem_wz1PaperGridCube rho cell other).mp hother
    have hpointIndex : wz1PaperGridIndex rho point = cell :=
      (mem_wz1PaperGridCube rho cell point).mp hpointCell
    exact hotherIndex.trans hpointIndex.symm
  let shading : WZ1PaperTubeShading coarse :=
    { carrier := fun parent =>
        ⋃ cell ∈ parentCells parent, wz1PaperGridCube rho cell
      measurable_carrier := by
        intro parent
        apply MeasurableSet.iUnion
        intro cell
        apply MeasurableSet.iUnion
        intro _
        exact wz1PaperGridCube_measurable cell
      subset_body := by
        intro parent
        apply Set.iUnion_subset
        intro cell
        apply Set.iUnion_subset
        intro hcell
        exact (hparentCellSubset parent cell hcell).trans
          (coarseShading.subset_body parent) }
  have hsubshading : PaperIsSubshading shading coarseShading := by
    intro parent point hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨cell, hpoint⟩
    rcases Set.mem_iUnion.mp hpoint with ⟨hcell, hpointCell⟩
    exact hparentCellSubset parent cell hcell hpointCell
  have hretainedOwned :
      ∀ cell ∈ original.activeCells,
        ∃ parent, cell ∈ parentCells parent := by
    intro cell hcell
    rcases original.cellIntersection_nonempty cell hcell with
      ⟨point, hpointFine, hpointCell⟩
    rcases hpointFine with ⟨source, hpointSource⟩
    let parent := cover.toPaperTubeCover.parent source
    refine ⟨parent, Finset.mem_filter.mpr ⟨hcell, ?_⟩⟩
    exact ⟨source, rfl, point, hpointSource, hpointCell⟩
  have hcubical : WZ1PaperIsCubicalShading shading := by
    intro parent point hpoint other hother
    rcases Set.mem_iUnion.mp hpoint with ⟨cell, hpoint⟩
    rcases Set.mem_iUnion.mp hpoint with ⟨hcell, hpointCell⟩
    have hpointIndex : wz1PaperGridIndex rho point = cell :=
      (mem_wz1PaperGridCube rho cell point).mp hpointCell
    have hotherCell : other ∈ wz1PaperGridCube rho cell := by
      apply (mem_wz1PaperGridCube rho cell other).mpr
      exact ((mem_wz1PaperGridCube rho
        (wz1PaperGridIndex rho point) other).mp hother).trans hpointIndex
    exact Set.mem_iUnion.mpr
      ⟨cell, Set.mem_iUnion.mpr ⟨hcell, hotherCell⟩⟩
  have hpointCompatibility :
      ∀ source parent,
        WZ1PaperTubeCovers (fine.tube source) (coarse.tube parent) →
          ∀ point, point ∈ fineShading.carrier source →
            point ∈ shading.carrier parent := by
    intro source parent hcovered point hpoint
    have hparent : cover.toPaperTubeCover.parent source = parent :=
      (cover.toPaperTubeCover.parent_unique source parent hcovered).symm
    have hactive := paperBalanced_fine_point_active original point
      ⟨source, hpoint⟩
    let cell := wz1PaperGridIndex rho point
    have hcell : cell ∈ parentCells parent := by
      apply Finset.mem_filter.mpr
      refine ⟨hactive, source, hparent, point, hpoint, ?_⟩
      exact (mem_wz1PaperGridCube rho cell point).mpr rfl
    exact Set.mem_iUnion.mpr
      ⟨cell, Set.mem_iUnion.mpr
        ⟨hcell, (mem_wz1PaperGridCube rho cell point).mpr rfl⟩⟩
  have hunion :
      shading.union =
        ⋃ cell ∈ original.activeCells, wz1PaperGridCube rho cell := by
    apply Set.Subset.antisymm
    · rintro point ⟨parent, hpoint⟩
      rcases Set.mem_iUnion.mp hpoint with ⟨cell, hpoint⟩
      rcases Set.mem_iUnion.mp hpoint with ⟨hcell, hpointCell⟩
      exact Set.mem_iUnion.mpr
        ⟨cell, Set.mem_iUnion.mpr
          ⟨(Finset.mem_filter.mp hcell).1, hpointCell⟩⟩
    · intro point hpoint
      rcases Set.mem_iUnion.mp hpoint with ⟨cell, hpoint⟩
      rcases Set.mem_iUnion.mp hpoint with ⟨hcell, hpointCell⟩
      rcases hretainedOwned cell hcell with ⟨parent, hparent⟩
      exact ⟨parent, Set.mem_iUnion.mpr
        ⟨cell, Set.mem_iUnion.mpr ⟨hparent, hpointCell⟩⟩⟩
  let rebuiltBalanced :
      PureWZ2BalancedCoverData cover fineShading shading :=
    { point_compatibility := hpointCompatibility
      coarse_cubical := hcubical
      activeCells := original.activeCells
      coarse_union_eq := hunion
      cellMass := original.cellMass
      cellMass_pos := original.cellMass_pos
      cellMass_ne_top := original.cellMass_ne_top
      fine_cell_mass := original.fine_cell_mass }
  exact
    ⟨{ parentCells := parentCells
       parentCells_eq := fun _ => rfl
       source_witness := hsourceWitness
       retained_cell_owned := hretainedOwned
       shading := shading
       shading_carrier_eq := fun _ => rfl
       subshading := hsubshading
       balanced := rebuiltBalanced
       balanced_activeCells_eq := rfl }⟩

end Kakeya.Assouad.PureWZ2

end
