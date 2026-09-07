import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyOwnerParentStructure
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedCoarseDensity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedVolumeIdentities
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperOwnerParentBalancedMultiplicity

/-!
# Coarse bounds for the same-family owner-parent route

The selected coarse shading is a disjoint owner-cell shading.  Its point
multiplicity is therefore at most one.  Coarse density and volume are then
the standard balanced-cover consequences of one fiber-multiplicity cap and
two scalar absorption inequalities.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

namespace WZ2PaperOwnerParentSelectedData

variable
    {delta : ℝ}
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
    (data : WZ2PaperOwnerParentSelectedData owner outputConstant)

theorem coarse_pointMultiplicity_le_one :
    ∀ point,
      (data.finalCoarseShading.pointMultiplicity point : ENNReal) ≤ 1 := by
  exact data.balancedPullback.coarse_pointMultiplicity_le_one

theorem final_fiber_pointMultiplicity_le_cap :
    ∀ parent point,
      (data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
          data.finalFineShading parent point : ENNReal) ≤
        (2 ^
          (balancing.balanced.finalData.producer.fiberBand.level + 1) :
            ENNReal) := by
  intro parent point
  let ownerFiber :=
    owner.exactified.restrictedCover.fullFiberSubfamily
      (data.selectedPacked.embedding parent)
  have hPointEq :
      (restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.finalFineShading).pointMultiplicity point =
      (restrictPaperShading ownerFiber
        owner.exactified.refined).pointMultiplicity point :=
    data.balancedPullback.pullback.full_fiber_pointMultiplicity_eq
      parent point
  have hOwnerBand :
      ∀ point ∈
          (restrictPaperShading ownerFiber
            owner.exactified.refined).union,
        (2 ^ balancing.balanced.finalData.producer.fiberBand.level :
            ENNReal) ≤
          ((restrictPaperShading ownerFiber
            owner.exactified.refined).pointMultiplicity point :
            ENNReal) ∧
        ((restrictPaperShading ownerFiber
          owner.exactified.refined).pointMultiplicity point :
            ENNReal) <
          (2 ^
            (balancing.balanced.finalData.producer.fiberBand.level + 1) :
              ENNReal) :=
    owner.fiber_multiplicity_band
      (data.selectedPacked.embedding parent)
  rw [← data.internalCover.restrict_fullFiber_pointMultiplicity_eq
    data.finalFineShading parent point]
  rw [hPointEq]
  by_cases hpoint :
      point ∈
        (restrictPaperShading ownerFiber
          owner.exactified.refined).union
  · exact (hOwnerBand point hpoint).2.le
  · have hzero :
        (restrictPaperShading ownerFiber
          owner.exactified.refined).pointMultiplicity point = 0 := by
      simp [Kakeya.Streamlined.Shading.pointMultiplicity,
        show ∀ index,
            point ∉
              (restrictPaperShading ownerFiber
                owner.exactified.refined).carrier index by
          intro index hindex
          exact hpoint ⟨index, hindex⟩]
    rw [hzero]
    simp

theorem final_coarse_density
    (lambda : ENNReal)
    (rhoSmall : callerRequested.1 ≤ 1 / 24)
    (densityAbsorption :
      lambda *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN callerRequested.1 2) *
            data.selectedPacked.family.enncard *
            (2 ^
              (balancing.balanced.finalData.producer.fiberBand.level + 1) :
                ENNReal) ≤
        data.finalFineShading.mass) :
    data.finalCoarseShading.IsLambdaDense lambda := by
  let fiberCap : ENNReal :=
    (2 ^
      (balancing.balanced.finalData.producer.fiberBand.level + 1) :
        ENNReal)
  have fiberCapZero : fiberCap ≠ 0 := by
    dsimp only [fiberCap]
    positivity
  have fiberCapTop : fiberCap ≠ ⊤ := by
    dsimp only [fiberCap]
    simp
  have fiberMultiplicity :
      ∀ parent point,
        (data.internalCover.toWZ1PaperTubeCover.fiberPointMultiplicity
            data.finalFineShading parent point : ENNReal) ≤
          fiberCap := by
    intro parent point
    exact data.final_fiber_pointMultiplicity_le_cap parent point
  exact
    wz2_paper_balanced_coarse_density
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      rhoSmall data.internalCover data.finalFineShading
      data.finalCoarseShading data.balancedPullback.balanced
      data.section6Cover.coarse_line_class
      fiberCap data.finalFineShading.mass lambda
      fiberCapZero fiberCapTop fiberMultiplicity le_rfl
      (by simpa [fiberCap] using densityAbsorption)

theorem final_coarse_volume_upper
    (upper : ENNReal)
    (scalar :
      volume data.finalFineShading.union *
            volume
              (wz1PaperGridCube callerRequested.1 (0, 0, 0)) ≤
        upper * data.publicBalanced.cellMass) :
    volume data.finalCoarseShading.union ≤ upper := by
  apply
    data.balancedPullback.balanced.coarse_union_volume_le
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      upper
  change
    volume data.balancedPullback.pullback.selectedFineShading.union *
          volume
            (wz1PaperGridCube callerRequested.1 (0, 0, 0)) ≤
      upper * data.balancedPullback.balanced.cellMass
  exact scalar

end WZ2PaperOwnerParentSelectedData

end Kakeya.Assouad

end
