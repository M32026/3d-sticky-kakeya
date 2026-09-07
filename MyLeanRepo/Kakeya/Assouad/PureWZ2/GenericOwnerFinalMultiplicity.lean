import MyLeanRepo.Kakeya.Assouad.PureWZ2.GenericOwnerCriticalFiberMultiplicity

/-!
# Final multiplicity pair for the generic owner route

This module packages the closed coarse H5 producer and the cropped-critical
H6 producer against the same final selected family and shading.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2GenericOwnerSelectedData

variable
    {delta rho sigma floorLoss strongLoss outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : WZ2PaperPartitioningCover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells :
      WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing :
      WZ2PaperExactCellBalancingData
        (rho := rho) fineShading coarseCells availableFineCells}
    {coarseData :
      WZ2PaperCoarseShadingData
        cover fineShading coarseCells availableFineCells balancing}
    {hdelta : 0 < delta}
    {hrho : 0 < rho}
    {producer :
      WZ2PaperFinalBalancedCoverProducerData
        (hdelta := hdelta) (hrho := hrho)
        cover fineShading coarseCells availableFineCells
        balancing coarseData}
    {owner : WZ2PaperDirectOwnerPreparationData producer}
    {outputConstant : ENNReal}
    (data : PureWZ2GenericOwnerSelectedData owner outputConstant)

structure FinalMultiplicityInputs where
  rho_le_one : rho ≤ 1
  sigma_pos : 0 < sigma
  strongLoss_pos : 0 < strongLoss
  loss_budget : 3 * strongLoss ≤ outputLoss
  coarse_cardinality_absorption :
    (48 : ENNReal) * outputConstant ≤
      Kakeya.realRpowENN rho (-2 * strongLoss)
  ratio_pos : 0 < delta / rho
  ratio_le_one : delta / rho ≤ 1
  ratio_small : delta / rho ≤ 1 / 24
  critical :
    PureWZ2CriticalFloorSelectionData
      sigma floorLoss strongLoss
  ratio_critical : delta / rho ≤ critical.delta₀
  floor_strong : floorLoss < strongLoss
  multiplicity_absorption :
    2 * (55296 * Kakeya.deltaTubeVolume 1) ≤
      Kakeya.realRpowENN (delta / rho)
        (-(strongLoss - floorLoss))
  critical_rescaled :
    ∀ parent : Fin data.selectedPacked.family.card,
      Nonempty
        (PureWZ2CriticalRescaledFiberWitness
          (sigma := sigma) (loss := critical.structuralLoss)
          (restrictPaperShading
            (data.internalCover.fullFiberSubfamily parent)
            data.finalFineShading)
          (data.selectedPacked.family.tube parent) hrho)

theorem FinalMultiplicityInputs.coarse_bound
    (inputs :
      FinalMultiplicityInputs
        (sigma := sigma) (floorLoss := floorLoss)
        (strongLoss := strongLoss) (outputLoss := outputLoss)
        data) :
    ∀ point,
      (data.finalCoarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho (2 - sigma - outputLoss) *
          data.selectedPacked.family.enncard :=
  data.coarse_multiplicity_of_pure_cwa
    inputs.rho_le_one inputs.sigma_pos inputs.strongLoss_pos.le
    inputs.loss_budget inputs.coarse_cardinality_absorption

theorem FinalMultiplicityInputs.fiber
    (inputs :
      FinalMultiplicityInputs
        (sigma := sigma) (floorLoss := floorLoss)
        (strongLoss := strongLoss) (outputLoss := outputLoss)
        data) :
    ∀ parent point,
      (((wz2PaperFullFiberIndices
          data.selectedFine.family data.selectedPacked.family parent).filter
          fun index =>
            point ∈ data.finalFineShading.carrier index).card : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - outputLoss) *
          ((wz2PaperFullFiberIndices
            data.selectedFine.family
            data.selectedPacked.family parent).card : ENNReal) :=
  data.fiber_multiplicity_of_critical_rescaled inputs.critical
    inputs.ratio_pos inputs.ratio_le_one inputs.ratio_small
    inputs.ratio_critical inputs.floor_strong inputs.strongLoss_pos
    inputs.loss_budget inputs.multiplicity_absorption
    inputs.critical_rescaled

theorem FinalMultiplicityInputs.public_rescaled
    (inputs :
      FinalMultiplicityInputs
        (sigma := sigma) (floorLoss := floorLoss)
        (strongLoss := strongLoss) (outputLoss := outputLoss)
        data) :
    ∀ parent : Fin data.selectedPacked.family.card,
      Nonempty
        (WZ2PaperPureRescaledFullFiberOutput
          (sigma := sigma) (loss := outputLoss)
          (restrictPaperShading
            (data.internalCover.fullFiberSubfamily parent)
            data.finalFineShading)
          (data.selectedPacked.family.tube parent) hrho) :=
  data.critical_rescaled_fiber_public_output inputs.critical
    inputs.strongLoss_pos inputs.loss_budget inputs.critical_rescaled

end PureWZ2GenericOwnerSelectedData

end Kakeya.Assouad

end
