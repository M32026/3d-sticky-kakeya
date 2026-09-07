import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedLayerLocalVolumeBranchesInputs

/-!
# Geometric cancellation in the selected-layer local coefficient

The parent-neighborhood area contributes
`DeltaRep * sqrt (DeltaRep / (C_R * tRep))`, the ambient cardinality
contributes `tRep / delta`, and the fine-shading area contributes
`delta^2 / sqrt (tRep * DeltaRep)`.  With the paper's `1/4`--`3/4`
interpolation powers, the representative scales cancel and leave one positive
power of `delta`.
-/

namespace Kakeya.Cinematic

def AmbientRestrictedLayerGeometricCancellationStatement : Prop :=
  ∀ (delta tRep DeltaRep C_R C_shading C_KT
      parentConstant parentArea cardUpper : ℝ),
    0 < delta →
    0 < tRep →
    0 < DeltaRep →
    0 < C_R →
    0 < C_shading →
    0 < C_KT →
    0 < parentConstant →
    0 ≤ parentArea →
    0 ≤ cardUpper →
    parentArea ≤
      parentConstant * DeltaRep *
        Real.sqrt (DeltaRep / (C_R * tRep)) →
    cardUpper ≤ C_KT * 3 * tRep / delta →
    Real.sqrt cardUpper *
          Real.rpow parentArea (1 / 4 : ℝ) *
          Real.rpow
            (ambientRestrictedSelectedFineGeometricArea
              C_shading delta C_R tRep DeltaRep)
            (3 / 4 : ℝ) ≤
      (Real.sqrt (3 * C_KT) *
          Real.rpow parentConstant (1 / 4 : ℝ) *
          Real.rpow
            (2 * C_shading * Real.sqrt C_shading)
            (3 / 4 : ℝ) /
          Real.sqrt C_R) *
        delta

end Kakeya.Cinematic
