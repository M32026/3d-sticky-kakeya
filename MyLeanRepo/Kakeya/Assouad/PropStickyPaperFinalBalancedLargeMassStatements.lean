import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPostDeletionLargeMassRegularizedStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFrontRefinementsStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPostBalancingRefinementStatements

/-!
# Final balance on the post-`largeMass` CWA family

Paper source:

> “There is a number `w > 0` so that for each `T̃ ∈ T̃₅` and each
> `rho`-cube `Q ⊂ Ỹ₅(T̃)`, we have
> `|Q ∩ E_{T₅[T̃]}| = w`.”
>
> “To fix this problem, we define `T̃₆ ⊂ T̃₅` to be the set of tubes for
> which [largeMass] holds.”

The upstream `T̃₆` deletion and second complete-fiber-mass regularizer already
produce one nearby-CWA coarse family whose complete fibers satisfy
`largeMass`.  The last whole-cell balancing keeps that coarse tube family
fixed and only refines its shadings.  Thus nearby CWA is unchanged, while the
four fixed finite losses below produce one exact balanced cover and a genuine
global paper refinement.  The final fiber density is reconstructed later
from the common fine/coarse multiplicity comparison; it is not asserted to
equal the pre-balancing density.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperFinalBalancedLargeMassInputData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambient : Kakeya.Streamlined.TubeFamily rho}
    {packed : Kakeya.Streamlined.TubeSubfamily ambient}
    {cover : WZ2PaperPartitioningCover fine packed.family}
    {fineShading : WZ1PaperTubeShading fine}
    {packedCoarseShading : WZ1PaperTubeShading packed.family}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    (regularized :
      WZ2PaperPostDeletionFiberMassRegularizationData
        packed cover fineShading packedCoarseShading
        ambientConstant outputConstant normalizationWeight weightUpper
        packedConstant levelCount)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (bandExponent postExponent cropExponent finalExponent : ℕ) : Type where
  hrho_le_one : rho ≤ 1
  scale_separation : 18 * delta ≤ rho
  fine_line :
    WZ1PaperIsLineClass regularized.pullback.selectedFine.family
  coarse_line :
    WZ1PaperIsLineClass regularized.regularized.selected.family
  boundary_absorption :
    ∀ bandData :
        WZ2PaperGlobalMultiplicityBandData
          regularized.pullback.selectedFineShading,
      (2 ^ (bandData.level + 1) : ENNReal) *
            ENNReal.ofReal (1000 * delta / rho) <
        bandData.band.mass
  boundary_retention :
    ∀ bandData :
        WZ2PaperGlobalMultiplicityBandData
          regularized.pullback.selectedFineShading,
      ∀ rebalancing :
          WZ2PaperWholeCellRebalancingRepairedData
            regularized.pullback.restrictedCover
            regularized.pullback.selectedFineShading
            bandData hdelta hrho,
        bandData.band.mass ≤
          2 * rebalancing.boundaryPruning.pruned.mass
  band_absorption :
    ∀ bandData :
        WZ2PaperGlobalMultiplicityBandData
          regularized.pullback.selectedFineShading,
      wz1PaperRefinementFraction delta bandExponent *
          wz2PaperGlobalMultiplicityBandLoss bandData ≤
        1
  post_absorption :
    ∀ bandData :
        WZ2PaperGlobalMultiplicityBandData
          regularized.pullback.selectedFineShading,
      ∀ rebalancing :
          WZ2PaperWholeCellRebalancingRepairedData
            regularized.pullback.restrictedCover
            regularized.pullback.selectedFineShading
            bandData hdelta hrho,
        wz1PaperRefinementFraction delta postExponent *
            wz2PaperPostBalancingLoss
              rebalancing.boundaryPruning ≤
          1
  crop_absorption :
    ∀ bandData :
        WZ2PaperGlobalMultiplicityBandData
          regularized.pullback.selectedFineShading,
      ∀ multiplicityCap : ENNReal,
        multiplicityCap =
            (2 ^ (bandData.level + 1) : ENNReal) →
      ∀ boundaryPruning :
          WZ2PaperBoundaryCellPruningData
            (rho := rho) bandData.band hdelta multiplicityCap,
        ∀ initialBalancing :
            WZ2PaperExactCellBalancingData
              (rho := rho)
              boundaryPruning.pruned
              boundaryPruning.coarseCells
              boundaryPruning.availableFineCells,
          multiplicityCap * ENNReal.ofReal (48 * rho) ≤
            (1 / 2 : ENNReal) * initialBalancing.refined.mass
  crop_fraction :
    wz1PaperRefinementFraction delta cropExponent ≤
      (1 / 2 : ENNReal)
  final_absorption :
    ∀ bandData :
        WZ2PaperGlobalMultiplicityBandData
          regularized.pullback.selectedFineShading,
      ∀ rebalancing :
          WZ2PaperWholeCellRebalancingRepairedData
            regularized.pullback.restrictedCover
            regularized.pullback.selectedFineShading
            bandData hdelta hrho,
        ∀ producer :
            WZ2PaperFinalBalancedCoverProducerData
              (hdelta := hdelta) (hrho := hrho)
              regularized.pullback.restrictedCover
              rebalancing.cropPruning.refined
              rebalancing.cropPruning.retainedCoarseCells
              rebalancing.cropPruning.selectedFineCells
              rebalancing.cropPruning.croppedBalancing
              rebalancing.coarseData,
          wz1PaperRefinementFraction delta finalExponent *
                wz2PaperFinalBalancedCoverLoss producer ≤
            1

structure WZ2PaperFinalBalancedLargeMassData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambient : Kakeya.Streamlined.TubeFamily rho}
    {packed : Kakeya.Streamlined.TubeSubfamily ambient}
    {cover : WZ2PaperPartitioningCover fine packed.family}
    {fineShading : WZ1PaperTubeShading fine}
    {packedCoarseShading : WZ1PaperTubeShading packed.family}
    {ambientConstant outputConstant normalizationWeight weightUpper
      packedConstant : ENNReal}
    {levelCount : ℕ}
    (regularized :
      WZ2PaperPostDeletionFiberMassRegularizationData
        packed cover fineShading packedCoarseShading
        ambientConstant outputConstant normalizationWeight weightUpper
        packedConstant levelCount)
    (hdelta : 0 < delta)
    (logExponent : ℕ) where
  selectedCoarse :
    Kakeya.Streamlined.TubeSubfamily
      regularized.regularized.selected.family
  selected_coarse_nonempty : selectedCoarse.Nonempty
  selectedFine :
    Kakeya.Streamlined.TubeSubfamily
      regularized.pullback.selectedFine.family
  restrictedCover :
    WZ2PaperPartitioningCover selectedFine.family selectedCoarse.family
  full_fiber_complete :
    ∀ parent : Fin selectedCoarse.family.card,
      Finset.image selectedFine.embedding
          (wz2PaperFullFiberIndices
            selectedFine.family selectedCoarse.family parent) =
        wz2PaperFullFiberIndices
          regularized.pullback.selectedFine.family
          regularized.regularized.selected.family
          (selectedCoarse.embedding parent)
  refined : WZ1PaperTubeShading selectedFine.family
  refined_cubical : WZ1PaperIsCubicalShading refined
  refined_subshading :
    ∀ index,
      refined.carrier index ⊆
        regularized.pullback.selectedFineShading.carrier
          (selectedFine.embedding index)
  coarseShading : WZ1PaperTubeShading selectedCoarse.family
  balanced :
    WZ1PaperBalancedCoverData
      restrictedCover.toWZ1PaperTubeCover refined coarseShading
  coarseMultiplicityLevel : ℕ
  fiberMultiplicityLevel : ℕ
  coarse_multiplicity_band :
    ∀ point ∈ coarseShading.union,
      (2 ^ coarseMultiplicityLevel : ENNReal) ≤
          (coarseShading.pointMultiplicity point : ENNReal) ∧
        (coarseShading.pointMultiplicity point : ENNReal) <
          (2 ^ (coarseMultiplicityLevel + 1) : ENNReal)
  fiber_multiplicity_band :
    ∀ parent point,
      point ∈
          (restrictPaperShading
            (restrictedCover.fullFiberSubfamily parent)
            refined).union →
        (2 ^ fiberMultiplicityLevel : ENNReal) ≤
            ((restrictPaperShading
              (restrictedCover.fullFiberSubfamily parent)
              refined).pointMultiplicity point : ENNReal) ∧
          ((restrictPaperShading
            (restrictedCover.fullFiberSubfamily parent)
            refined).pointMultiplicity point : ENNReal) <
            (2 ^ (fiberMultiplicityLevel + 1) : ENNReal)
  cwa_nearby :
    WZ2PaperCWAAtNearbyScales selectedCoarse.family outputConstant
  retained_mass :
    wz1PaperRefinementFraction delta logExponent *
          regularized.pullback.selectedFineShading.mass ≤
      refined.mass

def WZ2PaperFinalBalancedLargeMassStatement : Prop :=
  ∃ bandExponent postExponent cropExponent finalExponent : ℕ,
    ∀ {delta rho : ℝ}
      {fine : Kakeya.Streamlined.TubeFamily delta}
      {ambient : Kakeya.Streamlined.TubeFamily rho}
      {packed : Kakeya.Streamlined.TubeSubfamily ambient}
      {cover : WZ2PaperPartitioningCover fine packed.family}
      {fineShading : WZ1PaperTubeShading fine}
      {packedCoarseShading : WZ1PaperTubeShading packed.family}
      {ambientConstant outputConstant normalizationWeight weightUpper
        packedConstant : ENNReal}
      {levelCount : ℕ}
      (regularized :
        WZ2PaperPostDeletionFiberMassRegularizationData
          packed cover fineShading packedCoarseShading
          ambientConstant outputConstant normalizationWeight weightUpper
          packedConstant levelCount)
      (hdelta : 0 < delta)
      (hrho : 0 < rho)
      (input :
        WZ2PaperFinalBalancedLargeMassInputData
          regularized hdelta hrho
          bandExponent postExponent cropExponent finalExponent),
      Nonempty
        (WZ2PaperFinalBalancedLargeMassData
          regularized hdelta
          ((bandExponent + (postExponent + cropExponent)) +
            finalExponent))

end Kakeya.Assouad

end
