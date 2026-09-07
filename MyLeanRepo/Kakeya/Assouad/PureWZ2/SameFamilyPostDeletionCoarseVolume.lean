import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyPostDeletionStructure
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedVolumeIdentities

/-!
# Coarse union-volume bound after positive parent deletion

The final post-deletion cover is still exactly balanced on its active
caller-scale cells.  Hence the coarse union-volume estimate is equivalent to
one scalar comparison between the final fine union, one literal grid cube,
and the common fine mass per active cell.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2SameFamilyPositiveParentDeletionData

theorem final_coarse_volume_upper
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
    (upper : ENNReal)
    (scalar :
      volume data.finalFineShading.union *
            volume
              (wz1PaperGridCube callerRequested.1 (0, 0, 0)) ≤
        upper * data.publicBalanced.cellMass) :
    volume data.finalCoarseShading.union ≤ upper := by
  let historical :=
    data.post.postDeletion.deletion.restriction.balanced
  apply
    historical.coarse_union_volume_le
      (actualNearby.scaleData.delta_pos.trans_le callerRequested.2.1)
      upper
  change
    volume data.finalFineShading.union *
          volume
            (wz1PaperGridCube callerRequested.1 (0, 0, 0)) ≤
      upper * data.publicBalanced.cellMass
  exact scalar

end PureWZ2SameFamilyPositiveParentDeletionData

end Kakeya.Assouad

end
