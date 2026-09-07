import MyLeanRepo.Kakeya.Assouad.PropStickyPaperInitialBalancingStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperWholeCellRebalancing

/-! # Initial whole-cell balancing after parentwise merge -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_global_multiplicity_band
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (cubical : WZ1PaperIsCubicalShading shading) :
    Nonempty (WZ2PaperGlobalMultiplicityBandData shading) := by
  rcases paperDyadicBandPigeonhole cubical with
    ⟨level, bandCubical, massRetention, multiplicity⟩
  exact
    ⟨{
      level := level
      band := wz1PaperDyadicBandSubshading shading level
      band_eq := rfl
      band_cubical := bandCubical
      band_mass_retention := massRetention
      band_multiplicity := multiplicity
    }⟩

theorem wz2_paper_initial_balancing :
    WZ2PaperInitialBalancingStatement := by
  intro delta rho sigma strongLoss outputLoss hdelta hrho
    hdeltaRho hrhoOne hscale fine coarse cover shading heavy
    logExponent ambientFiberData parentwise fineLine coarseLine
    bandData hBoundary hCrop
  rcases
      wz2_paper_whole_cell_rebalancing
        hdelta hrho hdeltaRho hrhoOne hscale
        parentwise.parentwise.restrictedCover fineLine coarseLine
        parentwise.parentwise.merged.refinement.refined bandData
        hBoundary hCrop
    with ⟨rebalanced⟩
  exact
    ⟨{
      multiplicityCap := rebalanced.multiplicityCap
      multiplicityCap_eq := rebalanced.multiplicityCap_eq
      pruning := rebalanced.pruning
      balancing := rebalanced.balancing
      coarseData := rebalanced.coarseData
    }⟩

end Kakeya.Assouad

end
