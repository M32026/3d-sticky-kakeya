import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageTransportStatements

/-!
# Exact Jacobian of the literal paper unit rescaling

The map is the ordinary transverse unit rescaling at scale `rho`, followed by
isotropic multiplication by `1 / 100`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

theorem wz2_paper_literal_unit_rescaling_volume :
    WZ2PaperLiteralUnitRescalingVolumeStatement := by
  intro rho anchor hrho source hsource
  let transverseMap : Point3 → Point3 :=
    unitRescalingMap
      (wz1TubeAxisZeroPoint anchor)
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
      rho hrho
  let fixedScale : Point3 → Point3 :=
    fun point => (1 / 100 : ℝ) • point
  have hmap :
      wz2PaperLiteralUnitRescalingMap anchor hrho =
        fixedScale ∘ transverseMap := by
    funext point
    rfl
  have himage :
      wz2PaperLiteralUnitRescalingMap anchor hrho '' source =
        fixedScale '' (transverseMap '' source) := by
    rw [hmap]
    exact Set.image_comp fixedScale transverseMap source
  rw [himage]
  have hfixedPositive : (0 : ℝ) < 1 / 100 := by
    norm_num
  have hfixed :
      volume (fixedScale '' (transverseMap '' source)) =
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          volume (transverseMap '' source) :=
    Kakeya.Streamlined.GeometricLemmas.volume_smul3
      (hL := hfixedPositive)
  rw [hfixed]
  have htransverse :
      volume (transverseMap '' source) =
        ENNReal.ofReal ((1 / rho : ℝ) ^ 2) *
          volume source :=
    unitRescalingMap_volume
      (wz1TubeAxisZeroPoint anchor)
      (wz1PaperDirection anchor)
      (wz1PaperDirection_norm anchor)
      rho hrho source hsource
  rw [htransverse, mul_assoc]

end Kakeya.Assouad

end
