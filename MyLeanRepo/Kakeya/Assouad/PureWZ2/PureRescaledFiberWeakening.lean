import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Output

/-!
# Loss weakening for one public rescaled fiber

The literal family, shading, Assouad-to-literal certificate, and source
cardinality equality do not depend on the exposed loss.  Only the cropped
extremality field is weakened.
-/

noncomputable section

namespace Kakeya.Assouad

noncomputable def WZ2PaperPureRescaledFullFiberOutput.mono_loss
    {delta rho sigma firstLoss secondLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading fine}
    {parentTube : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (data :
      WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := firstLoss)
        sourceShading parentTube hrho)
    (loss_le : firstLoss ≤ secondLoss) :
    WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := secondLoss)
      sourceShading parentTube hrho where
  familyData := data.familyData
  literalShading := data.literalShading
  jacobianConstant := data.jacobianConstant
  jacobianConstant_one := data.jacobianConstant_one
  jacobianConstant_finite := data.jacobianConstant_finite
  rescalingCertificate := data.rescalingCertificate
  extremal := data.extremal.mono_loss loss_le
  source_cardinality_eq := data.source_cardinality_eq

end Kakeya.Assouad

end
