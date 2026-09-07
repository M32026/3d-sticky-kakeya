import MyLeanRepo.Kakeya.Assouad.PureWZ2.GenericOwnerStructure
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GenericOwnerFinalMultiplicity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedCoarseDensity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedVolumeIdentities
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Generic owner-parent prop-sticky output

This adapter packages a low-level owner-parent balanced pullback into the
frozen Node 3 output.  It deliberately carries no historical quotient-net
parameters.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace PureWZ2GenericOwnerSelectedData

variable
    {delta rho sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
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

structure PropStickyLeaves
    (logExponent : ℕ) where
  sourceEmbedding :
    Fin data.selectedFine.family.card ↪ Fin source.card
  source_tube_eq :
    ∀ index,
      data.selectedFine.family.tube index =
        source.tube (sourceEmbedding index)
  source_subshading :
    ∀ index,
      data.finalFineShading.carrier index ⊆
        sourceShading.carrier (sourceEmbedding index)
  source_nonempty : data.selectedFine.family.Nonempty
  retained_mass :
    wz2PaperPureRefinementFraction delta logExponent *
        sourceShading.mass ≤
      data.finalFineShading.mass
  final_fine_cubical :
    WZ1PaperIsCubicalShading data.finalFineShading
  fine_line : WZ1PaperIsLineClass fine
  coarse_line : WZ1PaperIsLineClass coarse
  coarse_distinct : WZ1PaperIsEssentiallyDistinct coarse
  delta_le_rho : delta ≤ rho
  rho_le_one : rho ≤ 1
  coarse_pure :
    WZ2PaperPureCWAAtNearbyScales data.selectedPacked.family
      (Kakeya.realRpowENN rho (-outputLoss))
  coarse_density :
    data.finalCoarseShading.IsLambdaDense
      (Kakeya.realRpowENN rho outputLoss)
  coarse_volume :
    volume data.finalCoarseShading.union ≤
      Kakeya.realRpowENN rho (sigma - outputLoss)
  rescaled_fiber :
    ∀ parent : Fin data.selectedPacked.family.card,
      Nonempty
        (WZ2PaperPureRescaledFullFiberOutput
          (sigma := sigma) (loss := outputLoss)
          (restrictPaperShading
            (data.internalCover.fullFiberSubfamily parent)
            data.finalFineShading)
          (data.selectedPacked.family.tube parent) hrho)
  coarse_multiplicity :
    ∀ point,
      (data.finalCoarseShading.pointMultiplicity point : ENNReal) ≤
        Kakeya.realRpowENN rho (2 - sigma - outputLoss) *
          data.selectedPacked.family.enncard
  fiber_multiplicity :
    ∀ parent point,
      (((wz2PaperFullFiberIndices
          data.selectedFine.family data.selectedPacked.family parent).filter
          fun index =>
            point ∈ data.finalFineShading.carrier index).card : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - outputLoss) *
          ((wz2PaperFullFiberIndices
            data.selectedFine.family
            data.selectedPacked.family parent).card : ENNReal)

structure PropStickyGeometricLeaves
    (logExponent : ℕ) where
  sourceEmbedding :
    Fin data.selectedFine.family.card ↪ Fin source.card
  source_tube_eq :
    ∀ index,
      data.selectedFine.family.tube index =
        source.tube (sourceEmbedding index)
  source_subshading :
    ∀ index,
      data.finalFineShading.carrier index ⊆
        sourceShading.carrier (sourceEmbedding index)
  source_nonempty : data.selectedFine.family.Nonempty
  retained_mass :
    wz2PaperPureRefinementFraction delta logExponent *
        sourceShading.mass ≤
      data.finalFineShading.mass
  final_fine_cubical :
    WZ1PaperIsCubicalShading data.finalFineShading
  fine_line : WZ1PaperIsLineClass fine
  coarse_line : WZ1PaperIsLineClass coarse
  coarse_distinct : WZ1PaperIsEssentiallyDistinct coarse
  delta_le_rho : delta ≤ rho
  rho_le_one : rho ≤ 1
  coarse_pure :
    WZ2PaperPureCWAAtNearbyScales data.selectedPacked.family
      (Kakeya.realRpowENN rho (-outputLoss))
  coarse_density :
    data.finalCoarseShading.IsLambdaDense
      (Kakeya.realRpowENN rho outputLoss)
  coarse_volume :
    volume data.finalCoarseShading.union ≤
      Kakeya.realRpowENN rho (sigma - outputLoss)

noncomputable def PropStickyGeometricLeaves.withFinalMultiplicity
    {logExponent : ℕ}
    {floorLoss strongLoss : ℝ}
    (geometric :
      PropStickyGeometricLeaves
        (sigma := sigma) (outputLoss := outputLoss)
        (source := source) (sourceShading := sourceShading)
        data logExponent)
    (multiplicity :
      FinalMultiplicityInputs
        (sigma := sigma) (floorLoss := floorLoss)
        (strongLoss := strongLoss) (outputLoss := outputLoss)
        data) :
    PropStickyLeaves
      (sigma := sigma) (outputLoss := outputLoss)
      (source := source) (sourceShading := sourceShading)
      data logExponent where
  sourceEmbedding := geometric.sourceEmbedding
  source_tube_eq := geometric.source_tube_eq
  source_subshading := geometric.source_subshading
  source_nonempty := geometric.source_nonempty
  retained_mass := geometric.retained_mass
  final_fine_cubical := geometric.final_fine_cubical
  fine_line := geometric.fine_line
  coarse_line := geometric.coarse_line
  coarse_distinct := geometric.coarse_distinct
  delta_le_rho := geometric.delta_le_rho
  rho_le_one := geometric.rho_le_one
  coarse_pure := geometric.coarse_pure
  coarse_density := geometric.coarse_density
  coarse_volume := geometric.coarse_volume
  rescaled_fiber := multiplicity.public_rescaled
  coarse_multiplicity := multiplicity.coarse_bound
  fiber_multiplicity := multiplicity.fiber

noncomputable def PropStickyLeaves.assemble
    {logExponent : ℕ}
    (leaves :
      PropStickyLeaves
        (sigma := sigma) (outputLoss := outputLoss)
        (source := source) (sourceShading := sourceShading)
        data logExponent) :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading
        ⟨rho, leaves.delta_le_rho, leaves.rho_le_one⟩
        logExponent := by
  let selected : Kakeya.Streamlined.TubeSubfamily source :=
    {
      family := data.selectedFine.family
      embedding := leaves.sourceEmbedding
      tube_eq := leaves.source_tube_eq
    }
  let section6 :=
    data.section6Cover
      leaves.fine_line leaves.coarse_line leaves.coarse_distinct
  let balancedPublic :=
    data.publicBalanced
      leaves.fine_line leaves.coarse_line leaves.coarse_distinct
  exact
    {
      selected := selected
      selected_nonempty := leaves.source_nonempty
      refined := data.finalFineShading
      subshading := leaves.source_subshading
      retained_mass := leaves.retained_mass
      refined_cubical := leaves.final_fine_cubical
      coarse := data.selectedPacked.family
      cover := section6
      croppedCoarseShading := data.finalCoarseShading
      balanced := balancedPublic
      coarse_extremal :=
        {
          delta_pos := hrho
          delta_le_one := leaves.rho_le_one
          nonempty := data.selected_nonempty
          cwa_nearby_scales := leaves.coarse_pure
          cubical := balancedPublic.coarse_cubical
          dense := leaves.coarse_density
          volume_upper := leaves.coarse_volume
        }
      rescaledFiber := by
        intro parent
        exact leaves.rescaled_fiber parent
      coarse_multiplicity_upper := leaves.coarse_multiplicity
      fiber_multiplicity_upper := leaves.fiber_multiplicity
    }

end PureWZ2GenericOwnerSelectedData

end Kakeya.Assouad

end
