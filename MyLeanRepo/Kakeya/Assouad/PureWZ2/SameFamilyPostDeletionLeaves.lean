import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPostDeletionPropStickyAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPostDeletionRescaledFiber

/-!
# Remaining mathematical leaves on the same-family post-deletion route

All family selection, complete-fiber provenance, whole-cell balancing,
positive-parent deletion, mass retention, public cover synchronization, and
pointwise multiplicity conversion have already been closed.

This record is the exact remaining mathematical boundary for one normalized
cropped input and one caller scale.  In particular, the pointwise H5/H6
conclusions are not fields: they are derived mechanically from the two scalar
cap bounds and the retained dyadic bands.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2SameFamilyPositiveParentDeletionData

structure PostDeletionPropStickyLeaves
    {delta sigma outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation}
    {deletionExponent : ℕ}
    (data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent)
    (logExponent : ℕ) where
  degreeConstant : ENNReal
  degreeConstant_ne_top : degreeConstant ≠ ⊤
  degree_uniform :
    data.PostDeletionCoarseClassDegreeUniform degreeConstant
  retention_absorption :
    wz2PaperPureRefinementFraction delta logExponent *
          (2 *
            (((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
                pureWZ2CompleteParentRegularizationLoss
                  actualNearby.scaleData.coarse.card coordinateCount *
                sameFamily.retentionConstant) *
              pureWZ2SameFamilyFixedOriginBalancingLoss
                balancing.balanced)) ≤
      1
  coarse_cwa_absorption :
    postDeletionCoarseRestrictionConstant
        coarseConstant degreeConstant
        (pureWZ2SameFamilyFixedOriginBalancingLoss balancing.balanced) ≤
      Kakeya.realRpowENN callerRequested.1 (-outputLoss)
  rho_small : callerRequested.1 ≤ 1 / 24
  fiber_ratio_small : delta / callerRequested.1 ≤ 1 / 24
  coarse_density_absorption :
    Kakeya.realRpowENN callerRequested.1 outputLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN callerRequested.1 2) *
          data.selectedCoarse.family.enncard *
          (2 ^
            (balancing.balanced.finalData.producer.fiberBand.level + 1) :
              ENNReal) ≤
      data.finalFineShading.mass
  coarse_volume_scalar :
    volume data.finalFineShading.union *
          volume
            (wz1PaperGridCube callerRequested.1 (0, 0, 0)) ≤
      Kakeya.realRpowENN callerRequested.1
          (sigma - outputLoss) *
        data.publicBalanced.cellMass
  rescaled_fiber_leaves :
    ∀ parent : Fin data.selectedCoarse.family.card,
      FinalFiberRescalingLeaves
        (sigma := sigma) (outputLoss := outputLoss)
        data parent fiber_ratio_small
  coarse_cap_upper :
    (2 ^
        (balancing.balanced.finalData.producer.coarseBand.level + 1) :
      ENNReal) ≤
      Kakeya.realRpowENN callerRequested.1
          (2 - sigma - outputLoss) *
        data.selectedCoarse.family.enncard
  fiber_cap_upper :
    ∀ parent : Fin data.selectedCoarse.family.card,
      (2 ^
          (balancing.balanced.finalData.producer.fiberBand.level + 1) :
        ENNReal) ≤
        Kakeya.realRpowENN (delta / callerRequested.1)
            (2 - sigma - outputLoss) *
          ((wz2PaperFullFiberIndices
            data.selectedFine.family
            data.selectedCoarse.family parent).card : ENNReal)

noncomputable def PostDeletionPropStickyLeaves.assemble
    {delta sigma outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    {quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading}
    {support : PureWZ2PositiveCallerSupportData quotient}
    {coordinateCount : ℕ}
    {regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount}
    {merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized}
    {scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta}
    {scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant}
    {sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled}
    {scaleSeparation : 18 * delta ≤ callerRequested.1}
    {balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation}
    {deletionExponent logExponent : ℕ}
    {data :
      PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent}
    (leaves :
      PostDeletionPropStickyLeaves
        (sigma := sigma) (outputLoss := outputLoss)
        data logExponent) :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      shading callerRequested logExponent :=
  data.post_deletion_same_family_prop_sticky
    leaves.degreeConstant leaves.degreeConstant_ne_top
    leaves.degree_uniform logExponent
    leaves.retention_absorption leaves.coarse_cwa_absorption
    leaves.rho_small leaves.coarse_density_absorption
    leaves.coarse_volume_scalar
    (fun parent =>
      ⟨(leaves.rescaled_fiber_leaves parent).output⟩)
    leaves.coarse_cap_upper leaves.fiber_cap_upper

end PureWZ2SameFamilyPositiveParentDeletionData

end Kakeya.Assouad

end
