import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectCommonYSourceAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FixedLambdaProjectiveNormal

/-!
# Direct half-offset projective normal field

This is only the exact-image transport for the half-offset source assembled
in the direct common-y route.  It deliberately contains no extension or
saturation argument.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The half-offset projective plane field, pulled back along any controlled
exact-image preimage map, is unit-Lipschitz after the fixed total transport
and normalization. -/
theorem PureWZ2DirectCommonYSourceAssembly.halfOffset_fixedLambdaProjectiveNormal_lipschitz
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)
    {X : Type*} [PseudoMetricSpace X] {b S : ℝ}
    {preimage : X → {point : Point3 //
      point ∈ commonSource.halfOffsetAssembly.horizontalSource.sourceShading.union}}
    (hb : 0 < b) (hb_one : b ≤ 1) (hS : 1 ≤ S)
    (hpreimage : ∀ first second,
      b * dist (preimage first) (preimage second) ≤ 3 * dist first second) :
    LipschitzWith 1
      (fun point => pureWZ2OffsetProjectiveTotalNormalizedNormal b S
        pureWZ2FixedProjectiveNormalLambda
        (pureWZ2OffsetShearProjectiveNormal
          (PureWZ2HalfOffsetHorizontalSourceData.offset
            commonSource.halfOffsetAssembly.horizontalSource)
          (commonSource.halfOffsetAssembly.horizontalSource.sourceLocalGrains.planeMap
            (preimage point)))) := by
  exact pureWZ2FixedProjectiveNormal_exactImage_lipschitz
    (preimage := preimage)
    (field := fun sourcePoint => pureWZ2OffsetShearProjectiveNormal
      (PureWZ2HalfOffsetHorizontalSourceData.offset
        commonSource.halfOffsetAssembly.horizontalSource)
      (commonSource.halfOffsetAssembly.horizontalSource.sourceLocalGrains.planeMap sourcePoint))
    hb hb_one hS hpreimage
    (PureWZ2HalfOffsetHorizontalSourceData.projectiveNormal_lipschitz_restrict
      commonSource.halfOffsetAssembly.horizontalSource
      commonSource.halfOffsetAssembly_compatibility)
    (PureWZ2HalfOffsetHorizontalSourceData.projectiveNormal_coord_one_restrict
      commonSource.halfOffsetAssembly.horizontalSource
      commonSource.halfOffsetAssembly_compatibility)

end Kakeya.Assouad

end
