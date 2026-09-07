import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralMapRelationStatements

/-!
# Historical and literal paper map relations

The two maps have identical transverse coordinates.  The literal map
additionally compresses the third coordinate by `1 / 100`.
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_literal_map_coordinate_relation :
    WZ2PaperLiteralMapCoordinateRelationStatement := by
  intro rho anchor hrho point
  let rotated : Point3 :=
    householderToE3
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
      (point - wz1TubeAxisZeroPoint anchor)
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · dsimp only [rotated]
    simp [wz2PaperLiteralUnitRescalingMap,
      wz1PaperUnitRescalingMap, unitRescalingMap,
      wz2PaperLongitudinalCompression,
      transverseScaleLin_coord0, PiLp.smul_apply,
      PiLp.toLp_apply]
    field_simp [hrho.ne']
  · dsimp only [rotated]
    simp [wz2PaperLiteralUnitRescalingMap,
      wz1PaperUnitRescalingMap, unitRescalingMap,
      wz2PaperLongitudinalCompression,
      transverseScaleLin_coord1, PiLp.smul_apply,
      PiLp.toLp_apply]
    field_simp [hrho.ne']
  · dsimp only [rotated]
    simp [wz2PaperLiteralUnitRescalingMap,
      wz1PaperUnitRescalingMap, unitRescalingMap,
      wz2PaperLongitudinalCompression,
      transverseScaleLin_coord2, PiLp.smul_apply,
      PiLp.toLp_apply]

theorem wz2_paper_literal_map_image_relation :
    WZ2PaperLiteralMapImageRelationStatement := by
  intro hcoordinate rho anchor hrho source
  have hmap :
      wz2PaperLiteralUnitRescalingMap anchor hrho =
        wz2PaperLongitudinalCompression ∘
          wz1PaperUnitRescalingMap anchor hrho := by
    funext point
    exact hcoordinate anchor hrho point
  rw [hmap]
  exact
    (Set.image_image wz2PaperLongitudinalCompression
      (wz1PaperUnitRescalingMap anchor hrho) source).symm

end Kakeya.Assouad

end
