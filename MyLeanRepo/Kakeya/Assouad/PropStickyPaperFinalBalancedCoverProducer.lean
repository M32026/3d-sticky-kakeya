import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverProducerStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedActiveParentCells
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFiberMultiplicityBand
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperParentCellMassBand
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperParentCellRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancing
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalInducedCoarseShading
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalCoarseMultiplicityBand
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverV2

/-! # Produce the ghost-free final balanced cover -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_final_balanced_cover_producer :
    WZ2PaperFinalBalancedCoverProducerStatement := by
  intro coarseCellContainment activeLeaf fiberBandLeaf pairBandLeaf
    restrictionLeaf finalFineLeaf inducedLeaf coarseBandLeaf finalCoverLeaf
    delta rho hdelta hrho hscale fine coarse cover fineLine coarseLine
    sourceShading coarseCells availableFineCells balancing coarseData hCrop
  rcases activeLeaf hdelta hrho cover sourceShading coarseCells
      availableFineCells balancing coarseData with
    ⟨active⟩
  rcases fiberBandLeaf cover balancing.refined
      balancing.refined_cubical with
    ⟨fiberBand⟩
  rcases pairBandLeaf hdelta hrho cover sourceShading coarseCells
      availableFineCells balancing coarseData active fiberBand with
    ⟨pairBand⟩
  rcases restrictionLeaf hdelta hrho cover sourceShading coarseCells
      availableFineCells balancing coarseData active fiberBand pairBand with
    ⟨restriction⟩
  rcases finalFineLeaf hdelta hrho cover sourceShading coarseCells
      availableFineCells balancing coarseData active fiberBand pairBand
      restriction with
    ⟨finalFine⟩
  have hFinalCrop :
      ∀ cell ∈ finalFine.exact.retainedCoarseCells,
        wz1PaperGridCube rho cell ⊆
          Kakeya.Streamlined.axisBox 2 2 2 := by
    intro cell hcell
    apply hCrop cell
    exact restriction.selectedCells_subset
      (finalFine.retained_coarse_subset hcell)
  rcases inducedLeaf coarseCellContainment hdelta hrho hscale cover
      fineLine coarseLine sourceShading coarseCells availableFineCells
      balancing coarseData active fiberBand pairBand restriction finalFine
      hFinalCrop with
    ⟨induced⟩
  rcases coarseBandLeaf hdelta hrho cover sourceShading coarseCells
      availableFineCells balancing coarseData active fiberBand pairBand
      restriction finalFine induced with
    ⟨coarseBand⟩
  rcases finalCoverLeaf hdelta hrho cover sourceShading coarseCells
      availableFineCells balancing coarseData active fiberBand pairBand
      restriction finalFine induced coarseBand with
    ⟨finalCover⟩
  exact ⟨{
    active := active
    fiberBand := fiberBand
    pairBand := pairBand
    restriction := restriction
    finalFine := finalFine
    induced := induced
    coarseBand := coarseBand
    finalCover := finalCover
  }⟩

theorem wz2_paper_final_balanced_cover_producer_closed :
    WZ2PaperFinalBalancedCoverProducerClosedStatement :=
  wz2_paper_final_balanced_cover_producer
    wz2_prop_sticky_coarse_cell_containment
    wz2_paper_balanced_active_parent_cells
    wz2_paper_fiber_multiplicity_band
    wz2_paper_parent_cell_mass_band
    wz2_paper_parent_cell_restriction
    wz2_paper_final_fine_exact_balancing
    wz2_paper_final_induced_coarse_shading
    wz2_paper_final_coarse_multiplicity_band
    wz2_paper_final_balanced_cover_v2

end Kakeya.Assouad

end
