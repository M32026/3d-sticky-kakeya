import MyLeanRepo.Kakeya.Assouad.PropStickyPaperWholeCellRebalancingRepairedStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverProducerStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverRefinementStatements

/-!
# Final balanced cover from repaired whole-cell rebalancing

Package the crop-corrected initial whole-cell balancing together with the
ghost-free final balanced cover and its explicit refinement loss.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperRepairedFinalBalancedCoverData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (shading : WZ1PaperTubeShading fine)
    (bandData : WZ2PaperGlobalMultiplicityBandData shading)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (rebalancing :
      WZ2PaperWholeCellRebalancingRepairedData
        cover shading bandData hdelta hrho)
    (finalLogExponent : ℕ) where
  producer :
    WZ2PaperFinalBalancedCoverProducerData
      (hdelta := hdelta) (hrho := hrho)
      cover rebalancing.cropPruning.refined
      rebalancing.cropPruning.retainedCoarseCells
      rebalancing.cropPruning.selectedFineCells
      rebalancing.cropPruning.croppedBalancing
      rebalancing.coarseData
  finalRefinement :
    WZ2PaperFinalBalancedCoverRefinementData
      producer finalLogExponent

def WZ2PaperRepairedFinalBalancedCoverStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hdelta : 0 < delta),
      ∀ (hrho : 0 < rho),
        delta ≤ rho →
        rho ≤ 1 →
        18 * delta ≤ rho →
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
            ∀ (cover : WZ2PaperPartitioningCover fine coarse),
              WZ1PaperIsLineClass fine →
              WZ1PaperIsLineClass coarse →
              ∀ (shading : WZ1PaperTubeShading fine),
                ∀ (bandData :
                    WZ2PaperGlobalMultiplicityBandData shading),
                  (2 ^ (bandData.level + 1) : ENNReal) *
                        ENNReal.ofReal (1000 * delta / rho) <
                      bandData.band.mass →
                  (∀ boundaryPruning :
                      WZ2PaperBoundaryCellPruningData
                        (rho := rho) bandData.band hdelta
                        (2 ^ (bandData.level + 1) : ENNReal),
                    ∀ initialBalancing :
                        WZ2PaperExactCellBalancingData
                          (rho := rho)
                          boundaryPruning.pruned
                          boundaryPruning.coarseCells
                          boundaryPruning.availableFineCells,
                      (2 ^ (bandData.level + 1) : ENNReal) *
                          ENNReal.ofReal (48 * rho) <
                        initialBalancing.refined.mass) →
                  ∀ (finalLogExponent : ℕ),
                    (∀ rebalancing :
                        WZ2PaperWholeCellRebalancingRepairedData
                          cover shading bandData hdelta hrho,
                      ∀ producer :
                          WZ2PaperFinalBalancedCoverProducerData
                            (hdelta := hdelta) (hrho := hrho)
                            cover rebalancing.cropPruning.refined
                            rebalancing.cropPruning.retainedCoarseCells
                            rebalancing.cropPruning.selectedFineCells
                            rebalancing.cropPruning.croppedBalancing
                            rebalancing.coarseData,
                        wz1PaperRefinementFraction
                              delta finalLogExponent *
                            wz2PaperFinalBalancedCoverLoss producer ≤
                          1) →
                    Nonempty
                      (Σ rebalancing :
                          WZ2PaperWholeCellRebalancingRepairedData
                            cover shading bandData hdelta hrho,
                        WZ2PaperRepairedFinalBalancedCoverData
                          cover shading bandData hdelta hrho
                          rebalancing finalLogExponent)

end Kakeya.Assouad

end
