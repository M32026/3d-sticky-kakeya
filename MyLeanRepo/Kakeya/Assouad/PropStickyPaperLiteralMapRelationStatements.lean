import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingStatements

/-!
# Relation between the historical and literal paper rescalings

The two maps have identical transverse coordinates.  The literal paper map
additionally multiplies the longitudinal coordinate by `1 / 100`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Compress only the third coordinate by the fixed paper constant. -/
def wz2PaperLongitudinalCompression (point : Point3) : Point3 :=
  WithLp.toLp 2 ![point 0, point 1, (1 / 100 : ℝ) * point 2]

def WZ2PaperLiteralMapCoordinateRelationStatement : Prop :=
  ∀ {rho : ℝ},
    ∀ (anchor : Kakeya.DeltaTube rho),
      ∀ (hrho : 0 < rho),
        ∀ point : Point3,
          wz2PaperLiteralUnitRescalingMap anchor hrho point =
            wz2PaperLongitudinalCompression
              (wz1PaperUnitRescalingMap anchor hrho point)

/--
The literal image of an arbitrary set is the longitudinal compression of its
historical image.
-/
def WZ2PaperLiteralMapImageRelationStatement : Prop :=
  WZ2PaperLiteralMapCoordinateRelationStatement →
    ∀ {rho : ℝ},
      ∀ (anchor : Kakeya.DeltaTube rho),
        ∀ (hrho : 0 < rho),
          ∀ source : Set Point3,
            wz2PaperLiteralUnitRescalingMap anchor hrho '' source =
              wz2PaperLongitudinalCompression ''
                (wz1PaperUnitRescalingMap anchor hrho '' source)

end Kakeya.Assouad

end
