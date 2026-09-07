import MyLeanRepo.Kakeya.Assouad.PureWZ2.SameFamilyFixedOriginBalancing
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDirectPositiveFinalComparison
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCompleteFiberReindex
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureCWAReindex

/-!
# Positive whole-parent deletion on the same-family route

The final fixed-origin balancing may leave coarse parents with zero shaded
mass.  Delete low-mass parents by whole coarse cells, then retain every tube
in each surviving complete caller fiber.  The resulting fine/coarse families,
balanced shadings, and full-fiber CWA all remain synchronized.

This module does not claim that the surviving coarse subfamily automatically
inherits normalized pure nearby-scale CWA.  That requires its own quantitative
degree/cardinality argument and remains an explicit downstream leaf.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

structure PureWZ2SameFamilyPositiveParentDeletionData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
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
    (deletionExponent : ℕ) where
  post :
    WZ2PaperDirectPositiveFinalComparisonData
      balancing.balanced deletionExponent

/--
Delete low-mass parents after balancing while preserving complete fibers and
the final exact balanced cover.
-/
theorem pureWZ2_same_family_positive_parent_deletion
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant fiberConstant coarseConstant : ENNReal}
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
    (deletionExponent : ℕ)
    (fractionSmall :
      wz1PaperRefinementFraction delta deletionExponent ≤
        (1 / 2 : ENNReal)) :
    Nonempty
      (PureWZ2SameFamilyPositiveParentDeletionData
        actualNearby quotient support coordinateCount regularized merged
        scales scheduled sameFamily scaleSeparation balancing
        deletionExponent) := by
  let post :
      WZ2PaperDirectPositiveFinalComparisonData
        balancing.balanced deletionExponent :=
    Classical.choice <|
      wz2_paper_direct_positive_final_comparison
        balancing.balanced deletionExponent fractionSmall
  exact ⟨{ post := post }⟩

end Kakeya.Assouad

end
