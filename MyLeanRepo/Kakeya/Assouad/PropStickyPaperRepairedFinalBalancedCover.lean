import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRepairedFinalBalancedCoverStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperWholeCellRebalancingRepaired
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverRefinement

/-! # Produce the final balanced cover from crop-corrected rebalancing -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_repaired_final_balanced_cover :
    WZ2PaperRepairedFinalBalancedCoverStatement := by
  intro delta rho hdelta hrho hdeltaRho hrhoOne hscale
    fine coarse cover fineLine coarseLine shading bandData
    hBoundary hCropAbsorb finalLogExponent hFinalAbsorb
  rcases
      wz2_paper_whole_cell_rebalancing_repaired
        hdelta hrho hdeltaRho hrhoOne hscale cover fineLine coarseLine
        shading bandData hBoundary hCropAbsorb
    with ⟨rebalancing⟩
  rcases
      wz2_paper_final_balanced_cover_producer_closed
        hdelta hrho hscale cover fineLine coarseLine
        rebalancing.cropPruning.refined
        rebalancing.cropPruning.retainedCoarseCells
        rebalancing.cropPruning.selectedFineCells
        rebalancing.cropPruning.croppedBalancing
        rebalancing.coarseData rebalancing.cropPruning.crop
    with ⟨producer⟩
  rcases
      wz2_paper_final_balanced_cover_refinement
        producer finalLogExponent
        (hFinalAbsorb rebalancing producer)
    with ⟨finalRefinement⟩
  exact
    ⟨⟨rebalancing, {
      producer := producer
      finalRefinement := finalRefinement
    }⟩⟩

theorem wz2_paper_repaired_final_balanced_cover_from_rebalancing
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hscale : 18 * delta ≤ rho)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (shading : WZ1PaperTubeShading fine)
    (bandData : WZ2PaperGlobalMultiplicityBandData shading)
    (rebalancing :
      WZ2PaperWholeCellRebalancingRepairedData
        cover shading bandData hdelta hrho)
    (finalLogExponent : ℕ)
    (hFinalAbsorb :
      ∀ producer :
          WZ2PaperFinalBalancedCoverProducerData
            (hdelta := hdelta) (hrho := hrho)
            cover rebalancing.cropPruning.refined
            rebalancing.cropPruning.retainedCoarseCells
            rebalancing.cropPruning.selectedFineCells
            rebalancing.cropPruning.croppedBalancing
            rebalancing.coarseData,
        wz1PaperRefinementFraction delta finalLogExponent *
            wz2PaperFinalBalancedCoverLoss producer ≤ 1) :
    Nonempty
      (WZ2PaperRepairedFinalBalancedCoverData
        cover shading bandData hdelta hrho
        rebalancing finalLogExponent) := by
  rcases
      wz2_paper_final_balanced_cover_producer_closed
        hdelta hrho hscale cover fineLine coarseLine
        rebalancing.cropPruning.refined
        rebalancing.cropPruning.retainedCoarseCells
        rebalancing.cropPruning.selectedFineCells
        rebalancing.cropPruning.croppedBalancing
        rebalancing.coarseData rebalancing.cropPruning.crop
    with ⟨producer⟩
  rcases
      wz2_paper_final_balanced_cover_refinement
        producer finalLogExponent (hFinalAbsorb producer)
    with ⟨finalRefinement⟩
  exact
    ⟨{
      producer := producer
      finalRefinement := finalRefinement
    }⟩

end Kakeya.Assouad

end
