import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalParentDeletionStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementCompositionStatements

/-!
# Shaded-mass retention through final parent deletion

The final deletion removes whole balanced `rho`-cells.  Its cell-volume
charging estimate, multiplied by the final fine multiplicity cap, bounds the
deleted shaded mass.  A one-half error budget therefore gives one fixed
paper-refinement exponent.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFinalParentDeletionMassRetentionData
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
    {threshold : ENNReal}
    {referenceFiberMass : Fin coarse.card → ENNReal}
    (finalDeletion :
      WZ2PaperFinalParentDeletionData
        producer referenceFiberMass threshold)
    (deletionExponent : ℕ) where
  source_mass_le :
    finalDeletion.exactAdapter.exact.refined.mass ≤
      2 * finalDeletion.restriction.selectedFineShading.mass
  refinement :
    WZ1PaperRefinement
      finalDeletion.exactAdapter.exact.refined deletionExponent
  refinement_selected_eq :
    refinement.selected =
      finalDeletion.restriction.selected
  refinement_refined_heq :
    HEq refinement.refined
      finalDeletion.restriction.selectedFineShading
  refinement_refined_mass_eq :
    refinement.refined.mass =
      finalDeletion.restriction.selectedFineShading.mass
  retained_mass_to_selected :
    wz1PaperRefinementFraction delta deletionExponent *
        finalDeletion.exactAdapter.exact.refined.mass ≤
      finalDeletion.restriction.selectedFineShading.mass

def WZ2PaperFinalParentDeletionMassRetentionStatement : Prop :=
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
                          ∀ {threshold : ENNReal},
                            ∀ {referenceFiberMass :
                                Fin coarse.card → ENNReal},
                            ∀ (finalDeletion :
                                WZ2PaperFinalParentDeletionData
                                  producer referenceFiberMass threshold),
                              let fineCap : ENNReal :=
                                (2 ^
                                  (producer.finalFine.fineLevel + 1) :
                                  ENNReal)
                              let degreeCap : ENNReal :=
                                wz2PaperBalancedParentDegreeCap
                                  finalDeletion.exactAdapter.exact
                                  producer.finalFine.fineLevel
                              fineCap *
                                    (2 * degreeCap * threshold *
                                      ∑ parent : Fin coarse.card,
                                        referenceFiberMass parent) ≤
                                  (1 / 2 : ENNReal) *
                                    finalDeletion.exactAdapter.exact.refined.mass →
                                ∀ (deletionExponent : ℕ),
                                  wz1PaperRefinementFraction
                                      delta deletionExponent ≤
                                    (1 / 2 : ENNReal) →
                                  Nonempty
                                    (WZ2PaperFinalParentDeletionMassRetentionData
                                      finalDeletion deletionExponent)

end Kakeya.Assouad

end
