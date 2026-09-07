import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CoaxialLineClass
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Output

/-!
# Local grain configuration carried by one public rescaled fiber

The public ordinary family in a `WZ2PaperPureRescaledFullFiberOutput` is the
family on which pure nearby-scale CWA is asserted. Its cropped shading is a
reindexing of the literal Section 6 shading along coaxial tubes. Consequently
the public family inherits the paper line class, while cubicality and
extremality are already recorded by the output.

This deliberately does not claim a cropped top-level CWA. Such a conclusion
would require an additional ordinary-support hypothesis which is not part of
the frozen Node 3 output.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The fields of one rescaled fiber which are available without any support
strengthening of the frozen sticky output. -/
structure PureWZ2RescaledFiberLocalConfig
    (sigma loss delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  shading : WZ1PaperTubeShading family
  line_class : WZ1PaperIsLineClass family
  cubical : WZ1PaperIsCubicalShading shading
  extremal : WZ2PaperCroppedIsExtremal sigma loss family shading
  nearby_cwa :
    WZ2PaperPureCWAAtNearbyScales family
      (Kakeya.realRpowENN delta (-loss))

namespace WZ2PaperAssouadToLiteralRescalingCertificate

/-- Reindexing a literal line-class family along coaxial tubes preserves the
paper line class on the public ordinary family. -/
theorem publicFamily_line_class
    {delta rho : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {anchor : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {normalization : WZ2PaperAssouadUnitRescalingData anchor}
    {literal :
      WZ2PaperLiteralUnitRescaledFamilyData
        sourceFamily anchor hrho}
    {jacobianConstant : ENNReal}
    (certificate :
      WZ2PaperAssouadToLiteralRescalingCertificate
        hrho normalization literal jacobianConstant)
    (hliteral : WZ1PaperIsLineClass literal.targetFamily) :
    WZ1PaperIsLineClass certificate.publicFamily := by
  intro publicIndex
  let literalIndex := certificate.section6Index.symm publicIndex
  have hindex : certificate.section6Index literalIndex = publicIndex :=
    certificate.section6Index.apply_symm_apply publicIndex
  apply Kakeya.Assouad.PureWZ2.paperTubeInLineClass_of_same_axis
    (hliteral literalIndex)
  calc
    tubeAxisLine (certificate.publicFamily.tube publicIndex) =
        tubeAxisLine
          (certificate.publicFamily.tube
            (certificate.section6Index literalIndex)) := by rw [hindex]
    _ = tubeAxisLine (literal.targetFamily.tube literalIndex) :=
      certificate.same_axis literalIndex

end WZ2PaperAssouadToLiteralRescalingCertificate

/-- Extract the honest local configuration supplied by one public rescaled
full fiber. -/
def WZ2PaperPureRescaledFullFiberOutput.toLocalConfig
    {delta rho sigma loss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading fine}
    {parentTube : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (fiber :
      WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := loss)
        sourceShading parentTube hrho) :
    PureWZ2RescaledFiberLocalConfig sigma loss (delta / rho) :=
  { family := fiber.rescalingCertificate.publicFamily
    shading := fiber.rescalingCertificate.publicShading
      fiber.literalShading.targetShading
    line_class :=
      fiber.rescalingCertificate.publicFamily_line_class
        fiber.familyData.target_line_class
    cubical := fiber.extremal.cubical
    extremal := fiber.extremal
    nearby_cwa := fiber.extremal.cwa_nearby_scales }

end Kakeya.Assouad

end
