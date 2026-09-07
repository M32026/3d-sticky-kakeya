import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperInfrastructure

/-!
# Literal-paper family and shading assembly

These are dependent-choice assembly leaves.  All one-tube geometry is
supplied by the separately frozen canonical-tube and image-carrier
propositions.
-/

noncomputable section

namespace Kakeya.Assouad

/-- One-to-one literal-paper unit-rescaled family. -/
structure WZ2PaperLiteralUnitRescaledFamilyData
    {delta rho : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) where
  targetFamily :
    Kakeya.Streamlined.TubeFamily (delta / rho)
  sourceIndex :
    Fin targetFamily.card → Fin sourceFamily.card
  sourceIndex_bijective :
    Function.Bijective sourceIndex
  target_line_class :
    WZ1PaperIsLineClass targetFamily
  target_axis :
    ∀ target,
      tubeAxisLine (targetFamily.tube target) =
        wz2PaperLiteralUnitRescalingMap anchor hrho ''
          tubeAxisLine (sourceFamily.tube (sourceIndex target))

/-- Choose the canonical target tube independently for every source index. -/
def WZ2PaperLiteralUnitRescaledFamilyStatement : Prop :=
  WZ2PaperLiteralCanonicalUnitRescaledTubeStatement →
    ∀ {delta rho : ℝ},
      ∀ (hrho : 0 < rho),
        rho ≤ 1 →
        ∀ (sourceFamily :
            Kakeya.Streamlined.TubeFamily delta),
          WZ1PaperIsLineClass sourceFamily →
          ∀ (anchor : Kakeya.DeltaTube rho),
            WZ1PaperTubeInLineClass anchor →
            (∀ source,
              WZ1PaperTubeCovers
                (sourceFamily.tube source) anchor) →
            Nonempty
              (WZ2PaperLiteralUnitRescaledFamilyData
                sourceFamily anchor hrho)

/-- Literal cubical image shading on a chosen one-to-one target family. -/
structure WZ2PaperLiteralUnitRescaledShadingData
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (familyData :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho)
    (sourceShading : WZ1PaperTubeShading sourceFamily) where
  targetShading :
    WZ1PaperTubeShading familyData.targetFamily
  target_carrier_eq :
    ∀ target,
      targetShading.carrier target =
        wz1PaperCubicalSaturation (delta / rho)
          (wz2PaperLiteralUnitRescalingMap anchor hrho ''
            sourceShading.carrier (familyData.sourceIndex target))
  target_cubical :
    WZ1PaperIsCubicalShading targetShading

/--
Build the legal literal-paper image shading once the one-tube image-carrier
theorem has been supplied.
-/
def WZ2PaperLiteralUnitRescaledShadingStatement : Prop :=
  WZ2PaperLiteralImageCarrierStatement →
    ∀ {delta rho : ℝ},
      0 < delta →
      ∀ (hrho : 0 < rho),
        rho ≤ 1 →
        delta / rho ≤ 1 / 24 →
        ∀ {sourceFamily :
            Kakeya.Streamlined.TubeFamily delta},
          WZ1PaperIsLineClass sourceFamily →
          ∀ {anchor : Kakeya.DeltaTube rho},
            WZ1PaperTubeInLineClass anchor →
            (∀ source,
              WZ1PaperTubeCovers
                (sourceFamily.tube source) anchor) →
            ∀ (familyData :
                WZ2PaperLiteralUnitRescaledFamilyData
                  sourceFamily anchor hrho),
              ∀ (sourceShading :
                  WZ1PaperTubeShading sourceFamily),
                Nonempty
                  (WZ2PaperLiteralUnitRescaledShadingData
                    familyData sourceShading)

end Kakeya.Assouad

end
