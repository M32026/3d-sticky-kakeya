import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedCoverProducerStatements

/-!
# Total refinement loss for the ghost-free final balanced cover

The final selected fine shading is obtained from the initial exactly balanced
fine shading by five finite pigeonhole/restriction steps.  This module records
their explicit product loss and packages the result as a paper refinement on
the unchanged fine tube family.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperFinalBalancedCoverLoss
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
    (producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData) : ENNReal :=
  ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) *
    (2 *
      ((Nat.log 2
          (2 *
            (wz2PaperPositiveParentCellPairs
              producer.active producer.fiberBand.refined).card) :
        ENNReal) + 1)) *
    ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) *
    (4 *
      ((Nat.log 2
          (∑ cell ∈ producer.finalFine.finalCoarseCells,
            (producer.finalFine.availableFinalFineCells cell).card) + 1 :
        ℕ) : ENNReal)) *
    ((Nat.log 2 coarse.card + 1 : ℕ) : ENNReal)

structure WZ2PaperFinalBalancedCoverRefinementData
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
    (producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData)
    (logExponent : ℕ) where
  source_mass_le :
    balancing.refined.mass ≤
      wz2PaperFinalBalancedCoverLoss producer *
        producer.coarseBand.selectedFineShading.mass
  subshading :
    ∀ index,
      producer.coarseBand.selectedFineShading.carrier index ⊆
        balancing.refined.carrier index
  retained_mass :
    wz1PaperRefinementFraction delta logExponent *
        balancing.refined.mass ≤
      producer.coarseBand.selectedFineShading.mass

namespace WZ2PaperFinalBalancedCoverRefinementData

noncomputable def toRefinement
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
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover sourceShading coarseCells availableFineCells
        balancing coarseData}
    {logExponent : ℕ}
    (data :
      WZ2PaperFinalBalancedCoverRefinementData
        producer logExponent) :
    WZ1PaperRefinement balancing.refined logExponent where
  selected :=
    { family := fine
      embedding := Equiv.toEmbedding (Equiv.refl (Fin fine.card))
      tube_eq := fun _ => rfl }
  refined := producer.coarseBand.selectedFineShading
  subshading := data.subshading
  retained_mass := data.retained_mass

end WZ2PaperFinalBalancedCoverRefinementData

def WZ2PaperFinalBalancedCoverRefinementStatement : Prop :=
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
                        ∀ (producer :
                            WZ2PaperFinalBalancedCoverProducerData
                              (hdelta := hdelta) (hrho := hrho)
                              cover sourceShading coarseCells
                              availableFineCells balancing coarseData),
                          ∀ (logExponent : ℕ),
                            wz1PaperRefinementFraction delta logExponent *
                                  wz2PaperFinalBalancedCoverLoss producer ≤
                                1 →
                              Nonempty
                                (WZ2PaperFinalBalancedCoverRefinementData
                                  producer logExponent)

end Kakeya.Assouad

end
