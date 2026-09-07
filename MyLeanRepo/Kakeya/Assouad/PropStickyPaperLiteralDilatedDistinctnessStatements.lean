import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralSeparationConstants

/-!
# Essential distinctness after literal rescaling from a doubled anchor cover

The selected middle parents in the paper fiber tree lie in the doubled
`sigma`-anchor, rather than in its strict `sigma / 2` fiber.  The ordinary
strict-cover lower-distortion theorem therefore does not directly apply.

This leaf isolates the exact pairwise metric estimate needed after weighted
middle-parent selection.  It does not construct a family, a cover, or any
nearby-scale CWA data.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PaperLiteralDilatedStrongSeparationStatement : Prop :=
  ∀ {rho sigma : ℝ},
    0 < rho →
    rho ≤ sigma →
    ∀ (hsigma : 0 < sigma),
      sigma ≤ 1 →
      ∀ (sourceFirst sourceSecond : Kakeya.DeltaTube rho),
        ∀ (anchor : Kakeya.DeltaTube sigma),
        WZ1PaperTubeInLineClass sourceFirst →
        WZ1PaperTubeInLineClass sourceSecond →
        WZ1PaperTubeInLineClass anchor →
        WZ2PaperDilatedTubeCovers 2 sourceFirst anchor →
        WZ2PaperDilatedTubeCovers 2 sourceSecond anchor →
        wz2PaperLiteralSourceSeparationFactor * rho <
          wz1PaperLineDistance sourceFirst sourceSecond →
        ∀ (targetFirst targetSecond :
            Kakeya.DeltaTube (rho / sigma)),
          WZ1PaperTubeInLineClass targetFirst →
          WZ1PaperTubeInLineClass targetSecond →
          tubeAxisLine targetFirst =
              wz2PaperLiteralUnitRescalingMap anchor hsigma ''
                tubeAxisLine sourceFirst →
          tubeAxisLine targetSecond =
              wz2PaperLiteralUnitRescalingMap anchor hsigma ''
                tubeAxisLine sourceSecond →
            1600 * (rho / sigma) <
              wz1PaperLineDistance targetFirst targetSecond

end Kakeya.Assouad

end
