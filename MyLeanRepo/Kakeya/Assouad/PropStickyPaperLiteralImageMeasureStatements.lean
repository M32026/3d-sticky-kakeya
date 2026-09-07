import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageTransportStatements

/-!
# Measure lower bounds for the literal-paper image shading

WZ Definition 5 uses

> `(x₁, ..., xₙ) ↦ (c x₁ / rho, ..., c xₙ₋₁ / rho, c xₙ)`.

For the fixed Lean choice `c = 1 / 100`, the exact three-dimensional
Jacobian is `(1 / 100)^3 * rho⁻²`. The legal target shading is the cubical
saturation of each affine image, so it contains the exact image. These facts
give per-tube, aggregate-mass, and union-volume lower bounds with the same
Jacobian.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure WZ2PaperLiteralImageMeasureData
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (familyData :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho)
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (shadingData :
      WZ2PaperLiteralUnitRescaledShadingData
        familyData sourceShading) where
  per_tube_volume_lower :
    ∀ target,
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho : ℝ) ^ 2) *
          volume
            (sourceShading.carrier
              (familyData.sourceIndex target)) ≤
        volume (shadingData.targetShading.carrier target)
  mass_lower :
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho : ℝ) ^ 2) *
        sourceShading.mass ≤
      shadingData.targetShading.mass
  union_volume_lower :
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho : ℝ) ^ 2) *
        volume sourceShading.union ≤
      volume shadingData.targetShading.union

def WZ2PaperLiteralImageMeasureStatement : Prop :=
  WZ2PaperLiteralUnitRescalingVolumeStatement →
    ∀ {delta rho : ℝ},
      ∀ {sourceFamily :
          Kakeya.Streamlined.TubeFamily delta},
        ∀ {anchor : Kakeya.DeltaTube rho},
          ∀ {hrho : 0 < rho},
            ∀ (familyData :
                WZ2PaperLiteralUnitRescaledFamilyData
                  sourceFamily anchor hrho),
              ∀ (sourceShading :
                  WZ1PaperTubeShading sourceFamily),
                ∀ (shadingData :
                    WZ2PaperLiteralUnitRescaledShadingData
                      familyData sourceShading),
                  Nonempty
                    (WZ2PaperLiteralImageMeasureData
                      familyData sourceShading shadingData)

end Kakeya.Assouad

end
