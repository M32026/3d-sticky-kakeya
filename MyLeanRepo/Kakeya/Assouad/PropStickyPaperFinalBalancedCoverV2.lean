import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverV2Statements

/-! # Package the ghost-free final literal balanced cover -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_final_balanced_cover_v2 :
    WZ2PaperFinalBalancedCoverV2Statement := by
  intro delta rho hdelta hrho fine coarse cover sourceShading coarseCells
    availableFineCells balancing coarseData active fiberBand pairBand
    restriction finalFine induced coarseBand
  refine' ⟨_⟩
  exact
    { balanced :=
        { point_compatibility := coarseBand.point_compatibility
          coarse_cubical := coarseBand.selectedCoarse_cubical
          activeCells := coarseBand.selectedCells
          coarse_union_eq := by
            rw [coarseBand.selectedCoarse_union_eq, coarseBand.selectedRegion_eq]
          cellMass := finalFine.exact.cellMass
          cellMass_pos := finalFine.exact.cellMass_pos
          cellMass_ne_top := finalFine.exact.cellMass_ne_top
          fine_cell_mass := coarseBand.selected_cell_mass }
      activeCells_eq := rfl
      cellMass_eq := rfl
      coarse_multiplicity_band := fun point hpoint =>
        coarseBand.coarse_multiplicity_band point
          (by rwa [← coarseBand.selectedCoarse_union_eq])
      fiber_multiplicity_band := coarseBand.fiber_multiplicity_band }

end Kakeya.Assouad

end
