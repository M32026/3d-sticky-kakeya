import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalInducedCoarseShadingStatements

/-!
# Adapter from final induced coarse shading to the reusable coarse-data API

The final induced package already contains every field of
`WZ2PaperCoarseShadingData`.  The only nontrivial adapter field is the
parent-cell witness, recovered from the actual nonempty final full-fiber
intersection.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

noncomputable def
    WZ2PaperFinalInducedCoarseShadingData.toCoarseShadingData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {sourceShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) sourceShading coarseCells
        availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells
        availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {active :
      WZ2PaperBalancedActiveParentCellsData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData hdelta hrho}
    {fiberBand :
      WZ2PaperFiberMultiplicityBandData
        cover balancing.refined}
    {pairBand :
      WZ2PaperParentCellMassBandData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand}
    {restriction :
      WZ2PaperParentCellRestrictionData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand pairBand}
    {finalFine :
      WZ2PaperFinalFineExactBalancingData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand pairBand restriction}
    (induced :
      WZ2PaperFinalInducedCoarseShadingData
        cover sourceShading coarseCells availableFineCells
        balancing coarseData active fiberBand pairBand restriction
        finalFine) :
    WZ2PaperCoarseShadingData
      cover finalFine.fineBand finalFine.finalCoarseCells
      finalFine.availableFinalFineCells finalFine.exact where
  parentCells := induced.parentCells
  parentCells_subset := induced.parentCells_subset
  parentCells_witness := by
    intro parent cell hcell
    have hactive :
        parent ∈ induced.activeParents cell := by
      rw [induced.activeParents_eq]
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ parent, hcell⟩
    rcases induced.parent_cell_nonempty cell
        (induced.parentCells_subset parent hcell)
        parent hactive with
      ⟨point, hfiber, hpointCell⟩
    rcases hfiber with ⟨localIndex, hlocal⟩
    let source :=
      (cover.fullFiberSubfamily parent).embedding localIndex
    have hparent : cover.parent source = parent := by
      exact
        (cover.mem_fullFiber_iff_parent parent source).mp
          (cover.fullFiberSubfamily_mem parent localIndex)
    exact ⟨source, point, hparent, hlocal, hpointCell⟩
  retained_cell_owned := induced.retained_cell_owned
  coarseShading := induced.coarseShading
  coarseShading_carrier_eq := induced.coarse_carrier_eq
  balancedCover := induced.balanced

end Kakeya.Assouad

end
