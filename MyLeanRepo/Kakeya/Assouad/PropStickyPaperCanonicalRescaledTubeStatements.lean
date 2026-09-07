import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics

/-!
# Canonical exact image-axis tube under paper unit rescaling

The fixed transverse constant `c(3) = 1 / 100` is chosen so that the image of
every `L₃` source line covered by one `L₃` anchor line is again represented by
an `L₃` tube.  This record packages that target tube and its exact axis
provenance.
-/

noncomputable section

namespace Kakeya.Assouad

structure WZ2PaperCanonicalUnitRescaledTubeData
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) where
  target : Kakeya.DeltaTube (delta / rho)
  target_line_class : WZ1PaperTubeInLineClass target
  target_axis :
    tubeAxisLine target =
      wz1PaperUnitRescalingMap anchor hrho ''
        tubeAxisLine source

def WZ2PaperCanonicalUnitRescaledTubeStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ hrho : 0 < rho,
      rho ≤ 1 →
      ∀ (source : Kakeya.DeltaTube delta)
        (anchor : Kakeya.DeltaTube rho),
        WZ1PaperTubeInLineClass source →
        WZ1PaperTubeInLineClass anchor →
        WZ1PaperTubeCovers source anchor →
          Nonempty
            (WZ2PaperCanonicalUnitRescaledTubeData
              source anchor hrho)

end Kakeya.Assouad

end
