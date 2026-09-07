import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ExactDiagonalGlobalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SaturationPlaneMapExtension

/-!
# Same-cell witnesses for the exact diagonal shading

The final joint target shading is the literal target-grid saturation of the
synchronized exact affine image.  This file exposes that carrierwise
provenance without changing the family or making another spatial selection.
-/

noncomputable section

namespace Kakeya.Assouad

open Set
open PureWZ2ExternalWeightRegularizationData

namespace PureWZ2AffineDiagonalCleanupQuotientAssemblyData

/-- Every point in a final target carrier has an exact-image witness from the
same tube index and the same target grid cell. -/
theorem finalTargetShading_tubeWitness
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (index : Fin assembly.finalTargetSubfamily.family.card)
    (point : Point3)
    (hpoint : point ∈ assembly.finalTargetShading.carrier index) :
    ∃ source : {source : Point3 //
        source ∈ assembly.finalExactShading.carrier index},
      dist point (source : Point3) ≤
        affineScale.targetDelta * Real.sqrt 3 := by
  have hpointSaturation : point ∈
      wz1PaperCubicalSaturation affineScale.targetDelta
        (pureWZ2AffineDiagonalMapCentered
            affineScale.slopeData.frameSlope cleanup.raw.center
            affineScale.slopeData.heightScale
            affineScale.slopeData.transverseScale 1 ''
          (cleanupTargetSourceShading (regularized := regularized)
            (cleanup := cleanup) data).carrier
              (assembly.joint.finalTargetIndex index)) := by
    change point ∈ (cleanupTargetShading (cleanup := cleanup) data).carrier
      (assembly.joint.finalTargetIndex index) at hpoint
    rwa [cleanupTargetShading_carrier_eq_saturation
      (regularized := regularized) (cleanup := cleanup) data] at hpoint
  rcases wz1PaperCubicalSaturation_exists_source_dist_le
      affineScale.targetDelta_pos _ hpointSaturation with
    ⟨source, hsourceImage, hdist⟩
  have hsourceSaturation : source ∈
      wz1PaperCubicalSaturation affineScale.targetDelta
        (pureWZ2AffineDiagonalMapCentered
            affineScale.slopeData.frameSlope cleanup.raw.center
            affineScale.slopeData.heightScale
            affineScale.slopeData.transverseScale 1 ''
          (cleanupTargetSourceShading (regularized := regularized)
            (cleanup := cleanup) data).carrier
              (assembly.joint.finalTargetIndex index)) :=
    ⟨source, hsourceImage, rfl⟩
  have hsourceTarget : source ∈
      assembly.finalTargetShading.carrier index := by
    change source ∈ (cleanupTargetShading (cleanup := cleanup) data).carrier
      (assembly.joint.finalTargetIndex index)
    rw [cleanupTargetShading_carrier_eq_saturation
      (regularized := regularized) (cleanup := cleanup) data]
    exact hsourceSaturation
  refine ⟨⟨source, ?_⟩, hdist⟩
  change source ∈ (cleanupTargetExactShading
    (regularized := regularized) (cleanup := cleanup) data).carrier
      (assembly.joint.finalTargetIndex index)
  rw [cleanupTargetExactShading_carrier]
  exact ⟨hsourceImage, hsourceTarget⟩

/-- Union-level version of the same-cell witness. -/
theorem finalTargetShading_exactWitness
    {sigma epsilon delta : ℝ}
    {band : PureWZ2Lemma32DerivativeBandAssembly sigma epsilon delta}
    {subband : PureWZ2MassPopularSubbandData band}
    {popular : PureWZ2SubbandPopularBoxData subband}
    {affineScale : PureWZ2AffineDiagonalScaleData subband}
    {scheduleConstant outputConstant sourceScheduleConstant : ENNReal}
    {levelCount outputLevelCount parentLevelCount : ℕ}
    {regularized : PureWZ2PopularSourceRegularizationData
      popular scheduleConstant levelCount}
    {cleanup : PureWZ2AffineDiagonalSelectedLocalizedCleanupData
      popular affineScale regularized}
    {data : PureWZ2AffineDiagonalCleanupSourceRegularizationData
      cleanup outputConstant outputLevelCount}
    (assembly : PureWZ2AffineDiagonalCleanupQuotientAssemblyData data
      sourceScheduleConstant parentLevelCount)
    (point : {point : Point3 // point ∈ assembly.finalTargetShading.union}) :
    ∃ source : {source : Point3 //
        source ∈ assembly.finalExactShading.union},
      dist (point : Point3) (source : Point3) ≤
        affineScale.targetDelta * Real.sqrt 3 := by
  rcases point.property with ⟨index, hpoint⟩
  rcases assembly.finalTargetShading_tubeWitness index point hpoint with
    ⟨source, hdist⟩
  exact ⟨⟨source, ⟨index, source.property⟩⟩, hdist⟩

end PureWZ2AffineDiagonalCleanupQuotientAssemblyData

end Kakeya.Assouad

end
