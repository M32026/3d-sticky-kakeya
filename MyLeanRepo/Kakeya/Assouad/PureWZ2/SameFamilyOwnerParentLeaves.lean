import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentPropStickyAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentRescalingGeometry

/-!
# Remaining leaves on the same-family owner-parent route

Owner-parent simultaneous selection already supplies:

* one final coarse family with pure nearby-scale CWA;
* complete final fine fibers;
* an exact whole-cell balanced cover;
* retained shaded mass;
* coarse point multiplicity at most one; and
* inherited pure nearby CWA on every unrescaled final source fiber.

The remaining boundary consists only of scalar absorptions, the genuine
public rescaled-fiber output, and the final fiber-cap scalar.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace WZ2PaperOwnerParentSelectedData

structure OwnerParentPropStickyLeaves
    {delta sigma outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant outputConstant : ENNReal}
    {actualRequested : WZ2PaperRequestedScale delta}
    (actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant)
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient :
      PureWZ2ParentQuotientNetSelectionData
        actualNearby callerRequested shading)
    (support : PureWZ2PositiveCallerSupportData quotient)
    (coordinateCount : ℕ)
    (regularized :
      PureWZ2AllPositiveCallerRegularizationData
        (outputConstant := fiberConstant)
        actualNearby quotient support coordinateCount)
    (merged :
      PureWZ2MergedCallerClassRegularizationData
        actualNearby quotient support coordinateCount regularized)
    (scales :
      Fin coordinateCount → WZ2PaperRequestedScale delta)
    (scheduled :
      ∀ coordinate,
        WZ2PaperPureNearbyScaleCoverData
          fine (scales coordinate) ambientConstant)
    (sameFamily :
      PureWZ2SameFamilyCallerNearbyAssemblyData
        (coarseConstant := coarseConstant)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled)
    (scaleSeparation : 18 * delta ≤ callerRequested.1)
    (balancing :
      PureWZ2SameFamilyFixedOriginBalancingData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation)
    (owner :
      WZ2PaperDirectOwnerPreparationData
        balancing.balanced.finalData.producer)
    (data :
      WZ2PaperOwnerParentSelectedData owner outputConstant)
    (logExponent : ℕ) where
  retention_absorption :
    wz2PaperPureRefinementFraction delta logExponent *
        ((((pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
            pureWZ2CompleteParentRegularizationLoss
              actualNearby.scaleData.coarse.card coordinateCount *
            sameFamily.retentionConstant) *
          pureWZ2SameFamilyOwnerLoss balancing owner) *
          data.regularizationLoss) ≤
      1
  coarse_cwa_absorption :
    outputConstant ≤
      Kakeya.realRpowENN callerRequested.1 (-outputLoss)
  rho_small : callerRequested.1 ≤ 1 / 24
  fiber_ratio_small : delta / callerRequested.1 ≤ 1 / 24
  coarse_density_absorption :
    Kakeya.realRpowENN callerRequested.1 outputLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN callerRequested.1 2) *
          data.selectedPacked.family.enncard *
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
  rescaled_fiber_geometry :
    ∀ parent : Fin data.selectedPacked.family.card,
      FinalFiberRescalingGeometry data parent
  rescaled_fiber_absorptions :
    ∀ parent : Fin data.selectedPacked.family.card,
      FinalFiberRescalingScalarAbsorptions
        (sigma := sigma) (outputLoss := outputLoss)
        data parent fiber_ratio_small
  coarse_multiplicity_scalar :
    (1 : ENNReal) ≤
      Kakeya.realRpowENN callerRequested.1
          (2 - sigma - outputLoss) *
        data.selectedPacked.family.enncard
  fiber_cap_upper :
    ∀ parent : Fin data.selectedPacked.family.card,
      (2 ^
          (balancing.balanced.finalData.producer.fiberBand.level + 1) :
        ENNReal) ≤
        Kakeya.realRpowENN (delta / callerRequested.1)
            (2 - sigma - outputLoss) *
          ((wz2PaperFullFiberIndices
            data.selectedFine.family
            data.selectedPacked.family parent).card : ENNReal)

noncomputable def OwnerParentPropStickyLeaves.assemble
    {delta sigma outputLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant outputConstant : ENNReal}
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
    {owner :
      WZ2PaperDirectOwnerPreparationData
        balancing.balanced.finalData.producer}
    {data :
      WZ2PaperOwnerParentSelectedData owner outputConstant}
    {logExponent : ℕ}
    (leaves :
      OwnerParentPropStickyLeaves
        (sigma := sigma) (outputLoss := outputLoss)
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing owner data
        logExponent) :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      shading callerRequested logExponent :=
  owner_parent_same_family_prop_sticky
    actualNearby quotient support coordinateCount regularized merged
    scales scheduled sameFamily scaleSeparation balancing owner data
    logExponent leaves.retention_absorption
    leaves.coarse_cwa_absorption leaves.rho_small
    leaves.coarse_density_absorption leaves.coarse_volume_scalar
    (fun parent =>
      ⟨((leaves.rescaled_fiber_geometry parent).toLeaves
        (leaves.rescaled_fiber_absorptions parent)).output⟩)
    leaves.coarse_multiplicity_scalar
    leaves.fiber_cap_upper

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
