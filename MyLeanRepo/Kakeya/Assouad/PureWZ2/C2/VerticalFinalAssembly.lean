import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64IsotropicRetubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.RawGlobalGrains

/-!
# Final pure C2 assembly after Proposition 6.4 rediscretization

The analytic Proposition 6.4 normalization produces AD control on the exact
affine image at scale `sourceDelta / normalization`.  Paper Lemma 3.5 then
rediscretizes that image by ordinary tubes and cubical shadings at a possibly
larger scale.  These are different operations and their scales are not
identified here.

`PureWZ2VerticalRediscretizationData` is the geometric output that the omitted
Lemma-8 argument must supply.  In particular, public pure nearby-scale CWA,
local grains, extremality, and the cubical shading all live on one final
dependent configuration.  Global AD is recorded on that actual final
shading; its producer must use the source slab estimate through the two
geometric changes of variables.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Paper-faithful geometric output of the vertical Lemma-8 rediscretization.

The source-parent and axis fields prevent the final ordinary family from being
an unrelated extremizer.
-/
structure PureWZ2VerticalRediscretizationData
    {sourceDelta sigma rawLoss extensionConstant : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    {raw :
      PureWZ2RawC2GlobalGrainData
        sourceShading sigma C rawLoss extensionConstant}
    {slabCenter anchorHeight halfHeight normalization : ℝ}
    (normalized :
      PureWZ2Proposition64NormalizedData
        raw slabCenter anchorHeight halfHeight normalization)
    (finalDelta outputLoss : ℝ) where
  translation : Point3
  translation_height : translation 2 = 0
  isotropicCenter : Point3
  isotropicScale : ℝ
  isotropicScale_pos : 0 < isotropicScale
  family : Kakeya.Streamlined.TubeFamily finalDelta
  shading : WZ1PaperTubeShading family
  sourceParent : Fin family.card → Fin sourceFamily.card
  axis_provenance :
    ∀ target,
      tubeAxisLine (family.tube target) =
        pureWZ2Proposition64IsotropicMap isotropicCenter isotropicScale ''
          (pureWZ2Proposition64TranslatedMap raw.slope slabCenter anchorHeight
            halfHeight normalization translation ''
            tubeAxisLine (sourceFamily.tube (sourceParent target)))
  shading_near_source_image :
    ∀ target,
      shading.carrier target ⊆
        Metric.cthickening (6 * finalDelta)
          (pureWZ2Proposition64IsotropicMap isotropicCenter isotropicScale ''
            (pureWZ2Proposition64TranslatedMap raw.slope slabCenter
              anchorHeight halfHeight normalization translation ''
              sourceShading.carrier (sourceParent target)))
  line_class : WZ1PaperIsLineClass family
  bounded_base : HasBoundedBase family 4
  extremal :
    WZ2PaperCroppedIsExtremal
      sigma outputLoss family shading
  top_level_cwa :
    WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN finalDelta (-outputLoss))
  localGrains :
    PureWZ2LocalGrainData shading sigma
      (Kakeya.realRpowENN finalDelta (-outputLoss))
  planeMap_vertical_bound :
    ∀ point : {point : Point3 // point ∈ shading.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  /-- The paper's final slope, whose domain is literally `[-1,1]`. -/
  f : PureWZ2C2SlopeFunction
  f_normalized : PureWZ2C2SlopeIsNormalized f
  f_eq_on_active :
    ∀ z : PureWZ2UnitInterval,
      horizontalSlice shading.union z.1 ≠ ∅ →
        f z = normalized.slope
          (isotropicCenter 2 + z.1 / isotropicScale)
  final_global_ad :
    ∀ z : PureWZ2UnitInterval,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (f z))
          (horizontalSlice shading.union z.1))
        finalDelta (1 - sigma)
          (Kakeya.realRpowENN finalDelta (-outputLoss))

/-- Legacy exact-image cleanup boundary.  This is an intermediate package,
not the final vertical rediscretization: the latter must additionally include
the isotropic similarity and the resulting slope/AD provenance. -/
structure PureWZ2Proposition64Lemma35CleanupData
    {sourceDelta sigma rawLoss extensionConstant : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    {raw :
      PureWZ2RawC2GlobalGrainData
        sourceShading sigma C rawLoss extensionConstant}
    {slabCenter anchorHeight halfHeight normalization finalDelta outputLoss : ℝ}
    {translation : Point3}
    {normalized :
      PureWZ2Proposition64NormalizedData
        raw slabCenter anchorHeight halfHeight normalization}
    (image :
      PureWZ2Proposition64ActualImageRediscretizationData
        (targetDelta := finalDelta) raw.slope slabCenter anchorHeight
          halfHeight normalization translation normalized.halfHeight_pos
          normalized.normalization_pos sourceFamily sourceShading) where
  line_class : WZ1PaperIsLineClass image.family
  extremal :
    WZ2PaperCroppedIsExtremal
      sigma outputLoss image.family image.shading
  top_level_cwa :
    WZ2PaperConvexWolffBound image.family
      (Kakeya.realRpowENN finalDelta (-outputLoss))
  localGrains :
    PureWZ2LocalGrainData image.shading sigma
      (Kakeya.realRpowENN finalDelta (-outputLoss))
  planeMap_vertical_bound :
    ∀ point : {point : Point3 // point ∈ image.shading.union},
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  analytic_scale_le : sourceDelta / normalization ≤ finalDelta
  global_constant_le :
    1152 * C ≤ Kakeya.realRpowENN finalDelta (-outputLoss)

namespace PureWZ2VerticalRediscretizationData

/-- Assemble the canonical pure C2 configuration.

The factor `36` is explicit: analytic normalization costs `6`, and the
one-sided cubical projection perturbation costs another `6`.
-/
noncomputable def toC2GrainConfiguration
    {sourceDelta sigma rawLoss extensionConstant : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal}
    {raw :
      PureWZ2RawC2GlobalGrainData
        sourceShading sigma C rawLoss extensionConstant}
    {slabCenter anchorHeight halfHeight normalization finalDelta outputLoss : ℝ}
    {normalized :
      PureWZ2Proposition64NormalizedData
        raw slabCenter anchorHeight halfHeight normalization}
    (data :
      PureWZ2VerticalRediscretizationData
        normalized finalDelta outputLoss) :
    PureWZ2C2GrainConfiguration sigma outputLoss finalDelta where
  family := data.family
  shading := data.shading
  line_class := data.line_class
  bounded_base := data.bounded_base
  cubical := data.extremal.cubical
  extremal := data.extremal
  top_level_cwa := data.top_level_cwa
  globalGrains :=
    { f := data.f
      normalized := data.f_normalized
      global_ad := data.final_global_ad }
  localGrains := data.localGrains

end PureWZ2VerticalRediscretizationData

end Kakeya.Assouad

end
