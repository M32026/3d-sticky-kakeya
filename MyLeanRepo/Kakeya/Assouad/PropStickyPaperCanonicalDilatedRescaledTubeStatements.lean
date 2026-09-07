import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCanonicalRescaledTubeStatements

/-!
# Canonical image-axis tube from a doubled anchor cover

The paper fiber tree supplies only a factor-two cover between an intermediate
parent and the larger anchor.  The fixed transverse rescaling still sends such
an `L₃` source axis to an axis represented by an `L₃` target tube.
-/

noncomputable section

namespace Kakeya.Assouad

def WZ2PaperCanonicalDilatedUnitRescaledTubeStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ hrho : 0 < rho,
      rho ≤ 1 →
      ∀ (source : Kakeya.DeltaTube delta)
        (anchor : Kakeya.DeltaTube rho),
        WZ1PaperTubeInLineClass source →
        WZ1PaperTubeInLineClass anchor →
        WZ2PaperDilatedTubeCovers 2 source anchor →
          Nonempty
            (WZ2PaperCanonicalUnitRescaledTubeData
              source anchor hrho)

end Kakeya.Assouad

end
