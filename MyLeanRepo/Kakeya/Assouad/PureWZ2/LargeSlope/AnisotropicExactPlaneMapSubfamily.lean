import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicExactPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicRetubingSubfamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GrainSubfamilyRestriction

/-!
# Restrict an exact anisotropic plane-map package to a tube subfamily

The target exact-image shading and the source local-grain shading are
restricted by the same source indices.  The inverse-transpose plane map is
therefore the literal restriction of the ambient one.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Restrict an exact anisotropic plane-map package along a genuine source
tube subfamily. -/
def PureWZ2AnisotropicExactPlaneMapData.subfamily
    {sourceDelta targetDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {center : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g center hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    (exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal)
    (selected : Kakeya.Streamlined.TubeSubfamily sourceFamily) :
    PureWZ2AnisotropicExactPlaneMapData (raw.subfamily selected)
      (sourceLocal.subfamily selected) := by
  let restrictedRaw := raw.subfamily selected
  let restrictedSourceLocal := sourceLocal.subfamily selected
  let inclusion :
      {point : Point3 // point ∈ restrictedRaw.exactShading.union} →
        {point : Point3 // point ∈ raw.exactShading.union} :=
    fun point => ⟨point, by
      rcases point.property with ⟨index, sourcePoint, hsourcePoint, heq⟩
      exact ⟨selected.embedding index, sourcePoint, hsourcePoint, heq⟩⟩
  let planeMap :
      {point : Point3 // point ∈ restrictedRaw.exactShading.union} → Point3 :=
    fun point => exact.planeMap (inclusion point)
  have hinclusion : LipschitzWith 1 inclusion := by
    intro first second
    simpa [inclusion, Subtype.edist_eq]
  refine {
    K := exact.K
    planeMap := planeMap
    planeMap_eq := ?_
    planeMap_lipschitz := ?_
    planeMap_unit := ?_
    planeMap_incidence_source := ?_
    planeMap_incidence := ?_
  }
  · funext target
    change exact.planeMap (inclusion target) =
      restrictedRaw.exactPlaneMap restrictedSourceLocal.planeMap target
    rw [exact.planeMap_eq]
    rfl
  · simpa [planeMap, Function.comp_def] using
      exact.planeMap_lipschitz.comp hinclusion
  · intro point
    exact exact.planeMap_unit (inclusion point)
  · intro index point hpoint
    have hambient : point ∈
        raw.exactShading.carrier (selected.embedding index) := by
      exact hpoint
    have hincidence := exact.planeMap_incidence_source
      (selected.embedding index) point hambient
    change |inner ℝ
        ((anisotropicPaperTargetFamily selected.family g c d m center
          targetDelta hcd hm).tube index).direction
        (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ 3 * sourceDelta
    rw [anisotropicPaperTargetFamily_subfamily_tube]
    exact hincidence
  · intro index point hpoint
    have hambient : point ∈
        raw.exactShading.carrier (selected.embedding index) := by
      exact hpoint
    have hincidence := exact.planeMap_incidence
      (selected.embedding index) point hambient
    change |inner ℝ
        ((anisotropicPaperTargetFamily selected.family g c d m center
          targetDelta hcd hm).tube index).direction
        (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ targetDelta
    rw [anisotropicPaperTargetFamily_subfamily_tube]
    exact hincidence

end Kakeya.Assouad

end
