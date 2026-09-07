import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RescaledFiberLocalConfig
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescaledShading
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingVolume
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralImageMeasure
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralAggregateDensity

/-!
# Refining one frozen rescaled metric fibre

Literal cubical saturation and the public-family reindexing are monotone in
the source shading.  Thus a newly rescaled subfibre is a genuine subshading
of the frozen Node 3 rescaled fibre.  Extremality then transfers once the
relative rescaled mass loss is supplied and absorbed.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

lemma wz1PaperCubicalSaturation_mono
    {scale : ℝ} {first second : Set Point3}
    (hsub : first ⊆ second) :
    wz1PaperCubicalSaturation scale first ⊆
      wz1PaperCubicalSaturation scale second := by
  rintro point ⟨sourcePoint, hsource, hgrid⟩
  exact ⟨sourcePoint, hsub hsource, hgrid⟩

/-- Literal unit-rescaled cubical shadings are monotone in their source
shadings when the target family is fixed. -/
lemma literalUnitRescaledShading_subshading
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {familyData : WZ2PaperLiteralUnitRescaledFamilyData
      sourceFamily anchor hrho}
    {source selected : WZ1PaperTubeShading sourceFamily}
    (hsub : PaperIsSubshading selected source)
    (sourceImage : WZ2PaperLiteralUnitRescaledShadingData
      familyData source)
    (selectedImage : WZ2PaperLiteralUnitRescaledShadingData
      familyData selected) :
    PaperIsSubshading selectedImage.targetShading
      sourceImage.targetShading := by
  intro target point hpoint
  rw [selectedImage.target_carrier_eq target] at hpoint
  rw [sourceImage.target_carrier_eq target]
  apply wz1PaperCubicalSaturation_mono (first :=
    wz2PaperLiteralUnitRescalingMap anchor hrho ''
      selected.carrier (familyData.sourceIndex target))
  · rintro imagePoint ⟨sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, hsub _ hsourcePoint, rfl⟩
  · exact hpoint

/-- Reindexing a literal subshading onto the frozen public family preserves
the carrierwise subshading relation. -/
lemma publicShading_subshading
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal : WZ2PaperLiteralUnitRescaledFamilyData
      sourceFamily anchor hrho}
    {jacobianConstant : ENNReal}
    (certificate : WZ2PaperAssouadToLiteralRescalingCertificate
      hrho normalization literal jacobianConstant)
    {source selected : WZ1PaperTubeShading literal.targetFamily}
    (hsub : PaperIsSubshading selected source) :
    PaperIsSubshading (certificate.publicShading selected)
      (certificate.publicShading source) := by
  intro publicIndex point hpoint
  exact hsub (certificate.section6Index.symm publicIndex) hpoint

/-- Transfer the frozen rescaled-fibre extremality to a literal/public
subshading after paying an explicit relative mass loss. -/
theorem rescaledSubfiber_extremal
    {delta rho sigma sourceLoss targetLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading selectedShading : WZ1PaperTubeShading sourceFamily}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (fiber : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := sourceLoss)
      sourceShading anchor hrho)
    (hsourceSelected : PaperIsSubshading selectedShading sourceShading)
    (selectedImage : WZ2PaperLiteralUnitRescaledShadingData
      fiber.familyData selectedShading)
    (massLoss : ENNReal)
    (hmassLossPos : 0 < massLoss)
    (hmassLossFinite : massLoss ≠ ⊤)
    (hmass : massLoss⁻¹ *
        (fiber.rescalingCertificate.publicShading
          fiber.literalShading.targetShading).mass ≤
      (fiber.rescalingCertificate.publicShading
        selectedImage.targetShading).mass)
    (hloss : sourceLoss ≤ targetLoss)
    (hslack : massLoss *
        Kakeya.realRpowENN (delta / rho) targetLoss ≤
      Kakeya.realRpowENN (delta / rho) sourceLoss)
    (htargetLoss : 0 < targetLoss) :
    WZ2PaperCroppedIsExtremal sigma targetLoss
      fiber.rescalingCertificate.publicFamily
      (fiber.rescalingCertificate.publicShading
        selectedImage.targetShading) := by
  have hliteralSub : PaperIsSubshading selectedImage.targetShading
      fiber.literalShading.targetShading :=
    literalUnitRescaledShading_subshading hsourceSelected
      fiber.literalShading selectedImage
  have hpublicSub : PaperIsSubshading
      (fiber.rescalingCertificate.publicShading
        selectedImage.targetShading)
      (fiber.rescalingCertificate.publicShading
        fiber.literalShading.targetShading) :=
    publicShading_subshading fiber.rescalingCertificate hliteralSub
  have hcubical : WZ1PaperIsCubicalShading
      (fiber.rescalingCertificate.publicShading
        selectedImage.targetShading) :=
    fiber.rescalingCertificate.publicShading_cubical
      selectedImage.target_cubical
  exact transfer_cropped_extremal_to_subshading massLoss
    hmassLossPos hmassLossFinite fiber.extremal hpublicSub hmass hcubical
    hloss hslack fiber.extremal.delta_pos fiber.extremal.delta_le_one
    htargetLoss

/-- Rebuild density of a rescaled subfibre directly from its source mass.
Nearby pure CWA and the volume upper bound are inherited from the frozen
rescaled fibre; the literal Jacobian supplies the new density lower bound. -/
theorem rescaledSubfiber_extremal_of_source_density
    {delta rho sigma sourceLoss targetLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading selectedShading : WZ1PaperTubeShading sourceFamily}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (fiber : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := sourceLoss)
      sourceShading anchor hrho)
    (hsourceSelected : PaperIsSubshading selectedShading sourceShading)
    (selectedImage : WZ2PaperLiteralUnitRescaledShadingData
      fiber.familyData selectedShading)
    (sourceDensity : ENNReal)
    (hsourceDensity : sourceDensity * sourceFamily.enncard *
        Kakeya.realRpowENN delta 2 ≤ selectedShading.mass)
    (hloss : sourceLoss ≤ targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hscaleSmall : delta / rho ≤ 1 / 24)
    (hdensityAbsorb :
      Kakeya.realRpowENN (delta / rho) targetLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * sourceDensity) :
    WZ2PaperCroppedIsExtremal sigma targetLoss
      fiber.rescalingCertificate.publicFamily
      (fiber.rescalingCertificate.publicShading
        selectedImage.targetShading) := by
  have hdelta : 0 < delta := by
    have hratio := fiber.extremal.delta_pos
    rcases div_pos_iff.mp hratio with hpositive | hnegative
    · exact hpositive.1
    · exact False.elim ((not_lt_of_ge hrho.le) hnegative.2)
  rcases wz2_paper_literal_image_measure
      wz2_paper_literal_unit_rescaling_volume fiber.familyData
      selectedShading selectedImage with ⟨imageMeasure⟩
  have hliteralDense : selectedImage.targetShading.IsLambdaDense
      (Kakeya.realRpowENN (delta / rho) targetLoss) :=
    wz2_paper_literal_aggregate_density wz2_paper_shading_mass_upper
      hdelta hrho hscaleSmall fiber.familyData selectedShading
      selectedImage imageMeasure sourceDensity
      (Kakeya.realRpowENN (delta / rho) targetLoss)
      hsourceDensity hdensityAbsorb
  have hpublicDense :
      (fiber.rescalingCertificate.publicShading
        selectedImage.targetShading).IsLambdaDense
        (Kakeya.realRpowENN (delta / rho) targetLoss) := by
    rw [Kakeya.Streamlined.Shading.IsLambdaDense,
      fiber.rescalingCertificate.publicBody_mass_eq,
      fiber.rescalingCertificate.publicShading_mass_eq]
    exact hliteralDense
  have hliteralSub : PaperIsSubshading selectedImage.targetShading
      fiber.literalShading.targetShading :=
    literalUnitRescaledShading_subshading hsourceSelected
      fiber.literalShading selectedImage
  have hpublicSub : PaperIsSubshading
      (fiber.rescalingCertificate.publicShading
        selectedImage.targetShading)
      (fiber.rescalingCertificate.publicShading
        fiber.literalShading.targetShading) :=
    publicShading_subshading fiber.rescalingCertificate hliteralSub
  have hunionSub :
      (fiber.rescalingCertificate.publicShading
        selectedImage.targetShading).union ⊆
      (fiber.rescalingCertificate.publicShading
        fiber.literalShading.targetShading).union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hpublicSub index hpoint⟩
  let oldExtremal := fiber.extremal.mono_loss hloss
  exact {
    delta_pos := oldExtremal.delta_pos
    delta_le_one := oldExtremal.delta_le_one
    nonempty := oldExtremal.nonempty
    cwa_nearby_scales := oldExtremal.cwa_nearby_scales
    cubical := fiber.rescalingCertificate.publicShading_cubical
      selectedImage.target_cubical
    dense := hpublicDense
    volume_upper := (MeasureTheory.measure_mono hunionSub).trans
      oldExtremal.volume_upper
  }

end Kakeya.Assouad.PureWZ2

end
