import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentMultiplicityBandsStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalMultiplicityComparisonStatements

/-!
# Final multiplicity comparison after parent deletion

Apply the global `mu_coarse * mu_fine` product estimate to the exact final
retained cover.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFinalParentMultiplicityComparisonData
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
        (rho := rho) sourceShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover sourceShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData}
    {referenceFiberMass : Fin coarse.card → ENNReal}
    {threshold : ENNReal}
    (finalDeletion :
      WZ2PaperFinalParentDeletionData
        producer referenceFiberMass threshold)
    (bands :
      WZ2PaperFinalParentMultiplicityBandsData finalDeletion)
    (massLower volumeUpper : ENNReal) where
  comparison :
    WZ2PaperFinalMultiplicityComparisonData
      finalDeletion.restriction.restrictedCover
      finalDeletion.restriction.selectedFineShading
      finalDeletion.restriction.selectedCoarseShading
      finalDeletion.restriction.balanced
      producer.coarseBand.level producer.fiberBand.level
      massLower volumeUpper

def WZ2PaperFinalParentMultiplicityComparisonStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
      ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
        ∀ {cover : WZ2PaperPartitioningCover fine coarse},
          ∀ {sourceShading : WZ1PaperTubeShading fine},
            ∀ {coarseCells : Finset WZ2PaperCellIndex},
              ∀ {availableFineCells :
                  WZ2PaperCellIndex → Finset WZ2PaperCellIndex},
                ∀ {balancing :
                    WZ2PaperExactCellBalancingData
                      (rho := rho) sourceShading coarseCells
                      availableFineCells},
                  ∀ {coarseData :
                      WZ2PaperCoarseShadingData
                        cover sourceShading coarseCells
                        availableFineCells balancing},
                    ∀ {hdelta : 0 < delta},
                      ∀ {hrho : 0 < rho},
                        ∀ {producer :
                            WZ2PaperFinalBalancedCoverProducerData
                              (hdelta := hdelta) (hrho := hrho)
                              cover sourceShading coarseCells
                              availableFineCells balancing coarseData},
                          ∀ {referenceFiberMass :
                              Fin coarse.card → ENNReal},
                          ∀ {threshold : ENNReal},
                            ∀ (finalDeletion :
                                WZ2PaperFinalParentDeletionData
                                  producer referenceFiberMass threshold),
                              ∀ (bands :
                                  WZ2PaperFinalParentMultiplicityBandsData
                                    finalDeletion),
                                ∀ (massLower volumeUpper : ENNReal),
                                  massLower ≤
                                      finalDeletion.restriction.selectedFineShading.mass →
                                  MeasureTheory.volume
                                        finalDeletion.restriction.selectedFineShading.union ≤
                                      volumeUpper →
                                  Nonempty
                                    (WZ2PaperFinalParentMultiplicityComparisonData
                                      finalDeletion bands
                                      massLower volumeUpper)

end Kakeya.Assouad

end
