import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingStatements

/-!
# Canonical literal image-axis tube from a doubled anchor cover

This is the literal-map analogue of the historical dilated canonical tube
interface.  It is separated because the two target-data structures record
different rescaling maps and are not interchangeable.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PaperLiteralCanonicalDilatedUnitRescaledTubeStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hrho : 0 < rho),
      rho ≤ 1 →
      ∀ (source : Kakeya.DeltaTube delta)
        (anchor : Kakeya.DeltaTube rho),
        WZ1PaperTubeInLineClass source →
        WZ1PaperTubeInLineClass anchor →
        WZ2PaperDilatedTubeCovers 2 source anchor →
          Nonempty
            (WZ2PaperLiteralCanonicalUnitRescaledTubeData
              source anchor hrho)

end Kakeya.Assouad

end
