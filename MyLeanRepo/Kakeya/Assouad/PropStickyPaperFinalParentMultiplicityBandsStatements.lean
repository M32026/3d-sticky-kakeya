import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentDeletionStatements

/-!
# Multiplicity bands after final parent deletion

Whole-cell deletion and complete-fiber restriction preserve the two common
dyadic multiplicity bands selected before deletion.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFinalParentMultiplicityBandsData
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
        producer referenceFiberMass threshold) where
  coarse_band :
    ∀ point ∈
        finalDeletion.restriction.selectedCoarseShading.union,
      (2 ^ producer.coarseBand.level : ENNReal) ≤
          (finalDeletion.restriction.selectedCoarseShading.pointMultiplicity
            point : ENNReal) ∧
        (finalDeletion.restriction.selectedCoarseShading.pointMultiplicity
            point : ENNReal) <
          (2 ^ (producer.coarseBand.level + 1) : ENNReal)
  fiber_band :
    ∀ parent point,
      point ∈
          (restrictPaperShading
            (finalDeletion.restriction.restrictedCover.fullFiberSubfamily
              parent)
            finalDeletion.restriction.selectedFineShading).union →
        (2 ^ producer.fiberBand.level : ENNReal) ≤
            ((restrictPaperShading
              (finalDeletion.restriction.restrictedCover.fullFiberSubfamily
                parent)
              finalDeletion.restriction.selectedFineShading).pointMultiplicity
                point : ENNReal) ∧
          ((restrictPaperShading
            (finalDeletion.restriction.restrictedCover.fullFiberSubfamily
              parent)
            finalDeletion.restriction.selectedFineShading).pointMultiplicity
              point : ENNReal) <
            (2 ^ (producer.fiberBand.level + 1) : ENNReal)

def WZ2PaperFinalParentMultiplicityBandsStatement : Prop :=
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
                              Nonempty
                                (WZ2PaperFinalParentMultiplicityBandsData
                                  finalDeletion)

end Kakeya.Assouad

end
