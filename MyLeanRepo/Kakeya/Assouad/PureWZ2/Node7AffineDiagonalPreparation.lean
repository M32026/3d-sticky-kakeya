import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectCommonYSourceAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SubbandPopularBox
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7AffineDiagonalScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PopularSourceExternalRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalSelectedFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalSelectedLocalizedCleanup

/-!
# Node 7 affine-diagonal preparation

This module records the first closed portion of the proof-local WZ-Lemma-8
normalization.  The horizontal rotation is the genuine rotation by the slope
at the selected height, and the subsequent affine-diagonal scale and selected
family are kept in one dependent record.  The final exact
Mobius slope is deliberately not exposed here: it is attached in the next
layer only after its active-interval two-jet has been extended globally.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The first synchronized affine-diagonal package used by Node 7. -/
structure PureWZ2Node7AffineDiagonalPreparationData
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta) where
  popular : PureWZ2SubbandPopularBoxData commonSource.subband
  node7Scale : PureWZ2Node7AffineDiagonalScaleData commonSource.subband
  sourceRegularization :
    PureWZ2AutoPopularSourceRegularizationData popular
  selected : PureWZ2AffineDiagonalSelectedFamilyData
    popular node7Scale.affineScale sourceRegularization.regularized

/-- Assemble the synchronized zero-slope affine-diagonal prefix. -/
theorem pureWZ2_node7_affine_diagonal_preparation
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)
    (hsourceTwo : 2 < commonSource.commonBand.band.sourceConstant) :
    Nonempty (PureWZ2Node7AffineDiagonalPreparationData commonSource) := by
  rcases commonSource.subband.toPopularBox with ⟨popular⟩
  rcases commonSource.subband.toNode7AffineDiagonalScaleData with
    ⟨node7Scale⟩
  rcases pureWZ2_popular_source_external_regularization_auto
      popular hsourceTwo with ⟨sourceRegularization⟩
  rcases popular.toAffineDiagonalSelectedFamily node7Scale.affineScale
      sourceRegularization.regularized with ⟨selected⟩
  exact ⟨{
    popular := popular
    node7Scale := node7Scale
    sourceRegularization := sourceRegularization
    selected := selected
  }⟩

end Kakeya.Assouad

end
