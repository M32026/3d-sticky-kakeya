import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRootFamilyStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRootTransverseEnvelopeStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCWATransferStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCanonicalDilatedRescaledTubeStatements

/-!
# Complete actual-scale-one witness for a literal target family

Package the singleton vertical-root cover together with the complete
historical unit-rescaled fiber over its unique parent.

The source literal target family already carries its top-level normalized
Convex-Wolff bound.  The root-relative historical rescaling contributes the
fixed transverse inverse-Jacobian loss `10000`.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperLiteralUnitRootScaleData
    {delta sigma : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube sigma}
    {hsigma : 0 < sigma}
    {literalFamily :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hsigma}
    (rootFamily :
      WZ2PaperLiteralUnitRootFamilyData literalFamily)
    (htargetScale :
      delta / sigma ≤ 1 ∧ (1 : ℝ) ≤ 1)
    (C : ENNReal) where
  scaleData :
    WZ2PaperLiteralScaleCoverData
      literalFamily.targetFamily
      1
      C
  coarse_eq :
    scaleData.coarse = wz2PaperLiteralUnitRootFamily
  cover_eq :
    HEq scaleData.cover rootFamily.cover

def WZ2PaperLiteralUnitRootScaleStatement : Prop :=
  WZ2PaperUnitRootTransverseEnvelopeStatement →
  WZ2PaperIndexedConvexWolffTransferStatement →
  WZ2PaperCanonicalDilatedUnitRescaledTubeStatement →
  ∀ {delta sigma : ℝ},
    0 < delta →
    ∀ (hsigma : 0 < sigma),
      ∀ (hdeltaSigma : delta ≤ sigma),
      ∀ {sourceFamily :
          Kakeya.Streamlined.TubeFamily delta},
        ∀ {anchor : Kakeya.DeltaTube sigma},
          ∀ {literalFamily :
              WZ2PaperLiteralUnitRescaledFamilyData
                sourceFamily anchor hsigma},
            ∀ (rootFamily :
                WZ2PaperLiteralUnitRootFamilyData literalFamily),
              ∀ {C : ENNReal},
                1 ≤ C →
                WZ2PaperConvexWolffBound
                  literalFamily.targetFamily C →
                  Nonempty
                    (WZ2PaperLiteralUnitRootScaleData
                      rootFamily
                      ⟨(div_le_one hsigma).mpr hdeltaSigma,
                        le_rfl⟩
                      ((10000 : ENNReal) * C))

end Kakeya.Assouad

end
