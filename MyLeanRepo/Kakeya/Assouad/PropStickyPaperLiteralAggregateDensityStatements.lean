import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMeasureStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpperStatements

/-!
# Aggregate density after literal unit rescaling

After final global balancing, per-source-tube density need not survive.
The paper only needs aggregate density of the rescaled pair.  The exact
literal Jacobian converts an aggregate source mass lower bound into a target
mass lower bound, while the quadratic paper-tube volume estimate bounds the
mass of the full target family.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PaperLiteralAggregateDensityStatement : Prop :=
  WZ2PaperShadingMassUpperStatement →
  ∀ {delta rho : ℝ},
    0 < delta →
    ∀ (hrho : 0 < rho),
      delta / rho ≤ 1 / 24 →
      ∀ {sourceFamily :
          Kakeya.Streamlined.TubeFamily delta},
        ∀ {anchor : Kakeya.DeltaTube rho},
          ∀ (familyData :
              WZ2PaperLiteralUnitRescaledFamilyData
                sourceFamily anchor hrho),
            ∀ (sourceShading :
                WZ1PaperTubeShading sourceFamily),
              ∀ (shadingData :
                  WZ2PaperLiteralUnitRescaledShadingData
                    familyData sourceShading),
                ∀ (imageMeasure :
                    WZ2PaperLiteralImageMeasureData
                      familyData sourceShading shadingData),
                  ∀ (sourceDensity lambda : ENNReal),
                    sourceDensity * sourceFamily.enncard *
                          Kakeya.realRpowENN delta 2 ≤
                        sourceShading.mass →
                    lambda *
                          (55296 * Kakeya.deltaTubeVolume 1) ≤
                        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
                          sourceDensity →
                    shadingData.targetShading.IsLambdaDense lambda

end Kakeya.Assouad

end
