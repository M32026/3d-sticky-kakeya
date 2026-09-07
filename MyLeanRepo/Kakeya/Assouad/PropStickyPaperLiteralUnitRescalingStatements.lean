import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics

/-!
# Literal paper unit rescaling for WZ2 `prop: sticky`

The source paper defines the affine map, after sending the anchor line to the
vertical axis, by

> `(x₁, ..., xₙ) ↦ (c x₁ / rho, ..., c xₙ₋₁ / rho, c xₙ)`.

The fixed choice below is `c = 1 / 100`.  Unlike
`wz1PaperUnitRescalingMap`, it scales the longitudinal coordinate by the same
fixed constant.  This leaves enough crop margin for the union of
`delta / rho` grid cubes intersecting the transformed shading.
-/

noncomputable section

namespace Kakeya.Assouad

/-- A canonical target tube with the exact literal-paper image axis. -/
structure WZ2PaperLiteralCanonicalUnitRescaledTubeData
    {delta rho : ℝ}
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) where
  target : Kakeya.DeltaTube (delta / rho)
  target_line_class :
    WZ1PaperTubeInLineClass target
  target_axis :
    tubeAxisLine target =
      wz2PaperLiteralUnitRescalingMap anchor hrho ''
        tubeAxisLine source

/--
Construct the exact image-axis target tube for the literal paper map.
-/
def WZ2PaperLiteralCanonicalUnitRescaledTubeStatement : Prop :=
  ∀ {delta rho : ℝ},
    ∀ (hrho : 0 < rho),
      rho ≤ 1 →
      ∀ (source : Kakeya.DeltaTube delta)
        (anchor : Kakeya.DeltaTube rho),
        WZ1PaperTubeInLineClass source →
        WZ1PaperTubeInLineClass anchor →
        WZ1PaperTubeCovers source anchor →
          Nonempty
            (WZ2PaperLiteralCanonicalUnitRescaledTubeData
              source anchor hrho)

/--
Legality of the paper image shading.

If a source set lies in one covered cropped paper tube, then every
`delta / rho` grid cube meeting its literal-paper affine image lies in the
cropped target paper tube with the exact image axis.
-/
def WZ2PaperLiteralImageCarrierStatement : Prop :=
  ∀ {delta rho : ℝ},
    0 < delta →
    ∀ (hrho : 0 < rho),
      rho ≤ 1 →
      delta / rho ≤ 1 / 24 →
      ∀ (source : Kakeya.DeltaTube delta)
        (anchor : Kakeya.DeltaTube rho)
        (target : Kakeya.DeltaTube (delta / rho)),
        WZ1PaperTubeInLineClass source →
        WZ1PaperTubeInLineClass anchor →
        WZ1PaperTubeInLineClass target →
        WZ1PaperTubeCovers source anchor →
        tubeAxisLine target =
            wz2PaperLiteralUnitRescalingMap anchor hrho ''
              tubeAxisLine source →
        ∀ sourceSet : Set Point3,
          sourceSet ⊆ wz1PaperTubeCarrier source →
          wz1PaperCubicalSaturation (delta / rho)
              (wz2PaperLiteralUnitRescalingMap anchor hrho ''
                sourceSet) ⊆
            wz1PaperTubeCarrier target

end Kakeya.Assouad

end
