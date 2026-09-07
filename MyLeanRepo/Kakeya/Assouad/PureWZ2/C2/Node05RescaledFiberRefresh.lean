import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12Output

/-!
# Same-family refresh of a public rescaled fiber

Changing the source shading on a fixed literal rescaled family preserves the
structural part of the public output.  Density of the refreshed public shading
is deliberately an explicit input: it does not follow from source-shading
containment.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Literal cubical rescaling is monotone in the source shading when the
rescaled family data is fixed. -/
theorem WZ2PaperLiteralUnitRescaledShadingData.target_union_subset_of_source_subset
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {parentTube : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    {sourceShading newSourceShading : WZ1PaperTubeShading fine}
    {familyData :
      WZ2PaperLiteralUnitRescaledFamilyData fine parentTube hrho}
    (oldLiteral :
      WZ2PaperLiteralUnitRescaledShadingData familyData sourceShading)
    (newLiteral :
      WZ2PaperLiteralUnitRescaledShadingData familyData newSourceShading)
    (hsub : ∀ index,
      newSourceShading.carrier index ⊆ sourceShading.carrier index) :
    newLiteral.targetShading.union ⊆
      oldLiteral.targetShading.union := by
  rintro point ⟨target, hpoint⟩
  refine ⟨target, ?_⟩
  rw [newLiteral.target_carrier_eq target] at hpoint
  rw [oldLiteral.target_carrier_eq target]
  rcases hpoint with ⟨imagePoint, himagePoint, hgrid⟩
  exact
    ⟨imagePoint,
      Set.image_mono (hsub (familyData.sourceIndex target)) himagePoint,
      hgrid⟩

namespace WZ2PaperPureRescaledFullFiberOutput

/--
Refresh a rescaled-fiber output after passing to a subshading on the same
source family and the same literal target family.

All structural fields are inherited from the old output.  Cubicality comes
from the new literal shading.  The volume upper bound is monotone under the
source carrier containment.  Density is required separately because it is
not monotone in this direction.
-/
noncomputable def refreshSameFamily
    {delta rho sigma loss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading newSourceShading : WZ1PaperTubeShading fine}
    {parentTube : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (oldOutput :
      WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := loss)
        sourceShading parentTube hrho)
    (newLiteral :
      WZ2PaperLiteralUnitRescaledShadingData
        oldOutput.familyData newSourceShading)
    (hsub : ∀ index,
      newSourceShading.carrier index ⊆ sourceShading.carrier index)
    (newDense :
      (oldOutput.rescalingCertificate.publicShading
          newLiteral.targetShading).IsLambdaDense
        (Kakeya.realRpowENN (delta / rho) loss)) :
    WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := loss)
      newSourceShading parentTube hrho := by
  have targetUnionSubset :
      newLiteral.targetShading.union ⊆
        oldOutput.literalShading.targetShading.union :=
    WZ2PaperLiteralUnitRescaledShadingData.target_union_subset_of_source_subset
      (oldLiteral := oldOutput.literalShading)
      (newLiteral := newLiteral) hsub
  have publicVolumeUpper :
      volume
          (oldOutput.rescalingCertificate.publicShading
            newLiteral.targetShading).union ≤
        Kakeya.realRpowENN (delta / rho) (sigma - loss) := by
    rw [oldOutput.rescalingCertificate.publicShading_union_eq]
    exact
      (measure_mono targetUnionSubset).trans <| by
        rw [← oldOutput.rescalingCertificate.publicShading_union_eq]
        exact oldOutput.extremal.volume_upper
  exact
    { familyData := oldOutput.familyData
      literalShading := newLiteral
      jacobianConstant := oldOutput.jacobianConstant
      jacobianConstant_one := oldOutput.jacobianConstant_one
      jacobianConstant_finite := oldOutput.jacobianConstant_finite
      rescalingCertificate := oldOutput.rescalingCertificate
      extremal :=
        { delta_pos := oldOutput.extremal.delta_pos
          delta_le_one := oldOutput.extremal.delta_le_one
          nonempty := oldOutput.extremal.nonempty
          cwa_nearby_scales := oldOutput.extremal.cwa_nearby_scales
          cubical :=
            oldOutput.rescalingCertificate.publicShading_cubical
              newLiteral.target_cubical
          dense := newDense
          volume_upper := publicVolumeUpper }
      source_cardinality_eq := oldOutput.source_cardinality_eq }

end WZ2PaperPureRescaledFullFiberOutput

end Kakeya.Assouad

end
