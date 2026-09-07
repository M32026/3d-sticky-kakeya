import MyLeanRepo.Kakeya.Assouad.PropStickyPaperWholeCellRebalancingStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruning
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancing
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoarseShading
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment

/-! # Rebalance a fixed complete-fiber cover by whole cells -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_whole_cell_rebalancing :
    WZ2PaperWholeCellRebalancingStatement := by
  intro delta rho hdelta hrho hdeltaRho hrhoOne hscale
    fine coarse cover fineLine coarseLine shading bandData
    hBoundary hCrop
  let multiplicityCap : ENNReal :=
    (2 ^ (bandData.level + 1) : ENNReal)
  have capBound :
      ∀ point,
        (bandData.band.pointMultiplicity point : ENNReal) ≤
          multiplicityCap := by
    intro point
    by_cases point_mem : point ∈ bandData.band.union
    · exact (bandData.band_multiplicity point point_mem).2.le
    · have point_zero :
          bandData.band.pointMultiplicity point = 0 := by
        classical
        simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
        apply Finset.card_eq_zero.mpr
        rw [Finset.filter_eq_empty_iff]
        intro index _
        exact fun carrier_mem =>
          point_mem ⟨index, carrier_mem⟩
      rw [point_zero]
      simp
  rcases
      wz2_prop_sticky_boundary_cell_pruning
        hdelta hdeltaRho hrho hrhoOne
        bandData.band bandData.band_cubical
        multiplicityCap capBound hBoundary
    with ⟨pruning⟩
  rcases
      wz2_prop_sticky_exact_cell_balancing
        hdelta hrho pruning.pruned pruning.pruned_cubical
        pruning.coarseCells pruning.coarseCells_nonempty
        pruning.availableFineCells
        pruning.availableFineCells_nonempty
        pruning.availableFineCells_ready
    with ⟨balancing⟩
  rcases
      wz2_prop_sticky_paper_coarse_shading
        wz2_prop_sticky_coarse_cell_containment
        hdelta hrho hscale cover fineLine coarseLine
        pruning.pruned pruning.pruned_cubical
        pruning.coarseCells pruning.coarseCells_nonempty
        pruning.availableFineCells
        pruning.availableFineCells_nonempty
        pruning.availableFineCells_ready balancing
        (fun cell _ => hCrop cell)
    with ⟨coarseData⟩
  exact
    ⟨{
      multiplicityCap := multiplicityCap
      multiplicityCap_eq := rfl
      pruning := pruning
      balancing := balancing
      coarseData := coarseData
    }⟩

end Kakeya.Assouad

end
