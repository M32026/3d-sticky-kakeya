import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPostDeletionStructure
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedCoarseDensity
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalMultiplicityComparison

/-!
# Coarse density after positive parent deletion

The surviving fine and coarse shadings remain an exact balanced cover and
retain the common final dyadic fiber-multiplicity band.  Consequently coarse
density follows from one scalar absorption inequality.  No critical-volume
floor or new selection is used here.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2SameFamilyPositiveParentDeletionData

theorem final_coarse_density
    {delta : ℝ}
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
    (lambda : ENNReal)
    (rhoSmall : callerRequested.1 ≤ 1 / 24)
    (densityAbsorption :
      lambda *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN callerRequested.1 2) *
            data.selectedCoarse.family.enncard *
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
    have hEq :=
      data.internalCover.restrict_fullFiber_pointMultiplicity_eq
        data.finalFineShading parent point
    let fiberShading :=
      restrictPaperShading
        (data.internalCover.fullFiberSubfamily parent)
        data.finalFineShading
    rw [← hEq]
    by_cases hpoint : point ∈ fiberShading.union
    · exact (data.post.bands.fiber_band parent point hpoint).2.le
    · have hzero : fiberShading.pointMultiplicity point = 0 := by
        simp [Kakeya.Streamlined.Shading.pointMultiplicity,
          show ∀ index, point ∉ fiberShading.carrier index by
            intro index hindex
            exact hpoint ⟨index, hindex⟩]
      rw [hzero]
      simp
  exact
    wz2_paper_balanced_coarse_density
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      rhoSmall data.internalCover data.finalFineShading
      data.finalCoarseShading
      data.post.postDeletion.deletion.restriction.balanced
      data.section6Cover.coarse_line_class
      fiberCap data.finalFineShading.mass lambda
      fiberCapZero fiberCapTop fiberMultiplicity le_rfl
      (by simpa [fiberCap] using densityAbsorption)

end PureWZ2SameFamilyPositiveParentDeletionData

end Kakeya.Assouad

end
