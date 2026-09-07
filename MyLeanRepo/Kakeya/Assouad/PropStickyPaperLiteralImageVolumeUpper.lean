import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageVolumeUpperStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMultiplicity

/-!
# Union-volume upper bound for a literal cubical image

Combine the image multiplicity floor, quadratic target mass upper bound, and
the generic multiplicity-floor volume inequality.
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_literal_image_volume_upper :
    WZ2PaperLiteralImageVolumeUpperStatement := by
  intro h_floor h_mass h_vol delta rho hdelta hrho hscale
    sourceFamily anchor familyData sourceShading shadingData
    multiplicityFloor volumeUpper h_mult_source h_ineq
  have h_image_mult : WZ2PaperLiteralImageMultiplicityStatement :=
    wz2_paper_literal_image_multiplicity
  have h_target_floor :
      ∀ targetPoint ∈ shadingData.targetShading.union,
        multiplicityFloor ≤
          (shadingData.targetShading.pointMultiplicity targetPoint : ENNReal) :=
    h_floor h_image_mult
      (familyData := familyData)
      (sourceShading := sourceShading)
      (shadingData := shadingData)
      (multiplicityFloor := multiplicityFloor)
      h_mult_source
  have hscale_pos : 0 < delta / rho :=
    div_pos hdelta hrho
  have h_mass_bound :
      shadingData.targetShading.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / rho) 2 *
            familyData.targetFamily.enncard :=
    h_mass
      (scale := delta / rho)
      hscale_pos
      hscale
      (family := familyData.targetFamily)
      familyData.target_line_class
      shadingData.targetShading
  exact h_vol
    (family := familyData.targetFamily)
    shadingData.targetShading
    multiplicityFloor
    ((55296 * Kakeya.deltaTubeVolume 1) *
      Kakeya.realRpowENN (delta / rho) 2 *
        familyData.targetFamily.enncard)
    volumeUpper
    h_target_floor
    h_mass_bound
    h_ineq

end Kakeya.Assouad

end
