import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageAssemblyStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.PullbackMultiplicity
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds

/-!
# Measure and multiplicity transport for the literal paper image

The literal map is the ordinary unit rescaling at transverse scale `rho`,
followed by isotropic multiplication by `1 / 100`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Exact three-dimensional Jacobian of the literal paper affine map. -/
def WZ2PaperLiteralUnitRescalingVolumeStatement : Prop :=
  ∀ {rho : ℝ},
    ∀ (anchor : Kakeya.DeltaTube rho),
      ∀ (hrho : 0 < rho),
        ∀ source : Set Point3,
          MeasurableSet source →
          volume
              (wz2PaperLiteralUnitRescalingMap
                anchor hrho '' source) =
            ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
              ENNReal.ofReal ((1 / rho : ℝ) ^ 2) *
                volume source

/--
The one-to-one literal image preserves indexed cardinality and dominates
source point multiplicity at the affine image point.
-/
def WZ2PaperLiteralImageMultiplicityStatement : Prop :=
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
                familyData.targetFamily.enncard =
                    sourceFamily.enncard ∧
                  ∀ point,
                    (sourceShading.pointMultiplicity point : ENNReal) ≤
                      (shadingData.targetShading.pointMultiplicity
                        (wz2PaperLiteralUnitRescalingMap
                          anchor hrho point) : ENNReal)

end Kakeya.Assouad

end
