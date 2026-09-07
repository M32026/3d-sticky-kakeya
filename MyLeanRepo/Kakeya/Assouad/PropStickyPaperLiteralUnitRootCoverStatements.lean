import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralCanonicalRescaledTube
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralTreeCoverStatements

/-!
# Unit-scale vertical root cover for literal target tubes

For requested target scales above `1 / 2`, Assouad's nearby-scale window may
use actual scale `1`.  The literal image of every source tube strictly
covered by the fixed `sigma` anchor lies in a factor-two cover by one fixed
vertical unit tube.

The root carrier contains the whole paper crop box, so carrier containment
is independent of the fine radius.  The line-cover estimate uses the strict
source-to-anchor geometry and the literal rescaling's fixed transverse
normalization.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The fixed vertical unit tube used at the root of the literal target tree. -/
def wz2PaperLiteralUnitRootTube : Kakeya.DeltaTube 1 where
  base := 0
  direction := e3
  direction_unit := e3_norm

def WZ2PaperLiteralUnitRootCoverStatement : Prop :=
  ∀ {delta sigma : ℝ},
    ∀ (hsigma : 0 < sigma),
      sigma ≤ 1 →
      ∀ (source : Kakeya.DeltaTube delta),
        ∀ (anchor : Kakeya.DeltaTube sigma),
          WZ1PaperTubeInLineClass source →
          WZ1PaperTubeInLineClass anchor →
          WZ1PaperTubeCovers source anchor →
          ∀ (target : Kakeya.DeltaTube (delta / sigma)),
            WZ1PaperTubeInLineClass target →
            tubeAxisLine target =
                wz2PaperLiteralUnitRescalingMap anchor hsigma ''
                  tubeAxisLine source →
              WZ2PaperDilatedTubeCovers 2
                  target wz2PaperLiteralUnitRootTube ∧
                WZ2PaperTubeCarrierCovers
                  target wz2PaperLiteralUnitRootTube

end Kakeya.Assouad

end
