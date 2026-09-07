import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LiteralExactImageOrdinaryShading
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Output

/-!
# Pure critical witness behind one rescaled cropped fiber

The public rescaled-fiber output carries a cropped cubical shading.  Node 2,
however, supplies a critical-volume floor only for ordinary unit-segment
shadings.  The two models must therefore be connected by explicit provenance;
an arbitrary cropped extremizer cannot be passed to the pure floor.

This record stores the ordinary configuration used for criticality together
with the existing Section 6 output.  The union inclusion is the exact
comparison needed to transfer the pure lower volume bound to the literal
target shading used by the multiplicity argument.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure PureWZ2CriticalRescaledFiberWitness
    {delta rho sigma loss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading fine)
    (parentTube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho) where
  output :
    WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := loss)
      sourceShading parentTube hrho
  ordinaryFamily :
    Kakeya.Streamlined.TubeFamily (delta / rho)
  ordinaryShading :
    Kakeya.Streamlined.TubeShading ordinaryFamily
  ordinary_nonempty : ordinaryFamily.Nonempty
  ordinary_cwa :
    WZ2PaperPureCWAAtNearbyScales ordinaryFamily
      (Kakeya.realRpowENN (delta / rho) (-loss))
  ordinary_dense :
    ordinaryShading.IsLambdaDense
      (Kakeya.realRpowENN (delta / rho) loss)
  ordinary_union_subset_target :
    ordinaryShading.union ⊆
      output.literalShading.targetShading.union

namespace WZ2PaperPureRescaledFullFiberOutput

/--
Attach a pure critical witness directly from the exact literal image of the
cropped source shading.

The explicit carrier-containment premise is the only geometric point not
already stored by the public rescaled-fiber output.  The density premise is a
scalar consequence of the same source-mass absorption used for the cubical
literal target.
-/
noncomputable def withCroppedExactImage
    {delta rho sigma loss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading fine}
    {parentTube : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (output :
      WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := loss)
        sourceShading parentTube hrho)
    (image_subset_public :
      ∀ publicIndex,
        wz2PaperLiteralUnitRescalingMap parentTube hrho ''
            sourceShading.carrier
              (output.familyData.sourceIndex
                (output.rescalingCertificate.section6Index.symm
                  publicIndex)) ⊆
          (output.rescalingCertificate.publicFamily.tube
            publicIndex).carrier)
    (ordinaryDense :
      (output.rescalingCertificate.literalExactCroppedImageShading
        sourceShading image_subset_public).IsLambdaDense
          (Kakeya.realRpowENN (delta / rho) loss)) :
    PureWZ2CriticalRescaledFiberWitness
      (sigma := sigma) (loss := loss)
      sourceShading parentTube hrho where
  output := output
  ordinaryFamily :=
    output.rescalingCertificate.publicFamily
  ordinaryShading :=
    output.rescalingCertificate.literalExactCroppedImageShading
      sourceShading image_subset_public
  ordinary_nonempty := output.extremal.nonempty
  ordinary_cwa := output.extremal.cwa_nearby_scales
  ordinary_dense := ordinaryDense
  ordinary_union_subset_target :=
    output.rescalingCertificate
      |>.literalExactCroppedImageShading_union_subset
        sourceShading image_subset_public output.literalShading

/--
Attach the pure critical witness carried by an ordinary source subshading.

The target ordinary shading consists of the exact literal affine images.
Its carrier legality and union inclusion are geometric identities; the only
quantitative input is the density of this exact-image shading.
-/
noncomputable def withOrdinaryExactImage
    {delta rho sigma loss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading fine}
    {parentTube : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (output :
      WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := loss)
        sourceShading parentTube hrho)
    (ordinarySource :
      Kakeya.Streamlined.TubeShading fine)
    (ordinarySource_subset :
      ∀ index,
        ordinarySource.carrier index ⊆
          sourceShading.carrier index)
    (ordinaryDense :
      (output.rescalingCertificate.literalExactImageShading
        ordinarySource).IsLambdaDense
          (Kakeya.realRpowENN (delta / rho) loss)) :
    PureWZ2CriticalRescaledFiberWitness
      (sigma := sigma) (loss := loss)
      sourceShading parentTube hrho where
  output := output
  ordinaryFamily :=
    output.rescalingCertificate.publicFamily
  ordinaryShading :=
    output.rescalingCertificate.literalExactImageShading
      ordinarySource
  ordinary_nonempty := output.extremal.nonempty
  ordinary_cwa := output.extremal.cwa_nearby_scales
  ordinary_dense := ordinaryDense
  ordinary_union_subset_target :=
    output.rescalingCertificate
      |>.literalExactImageShading_union_subset
        ordinarySource sourceShading ordinarySource_subset
        output.literalShading

end WZ2PaperPureRescaledFullFiberOutput

end Kakeya.Assouad

end
