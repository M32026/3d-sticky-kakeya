import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicExactPlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperPopularBox

/-!
# Mass-popular normalization box in exact anisotropic coordinates

The second spatial localization in paper Lemma 8 is performed after the
anisotropic map.  Its width is chosen at the reciprocal of the transported
plane-map Lipschitz scale.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The exact-image plane field restricted to a mass-popular box. -/
structure PureWZ2AnisotropicExactPopularBoxData
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
    (width : ℝ) where
  popular : PureWZ2PaperPopularBoxData raw.exactShading width
  planeMap :
    {point : Point3 // point ∈ popular.restricted.union} → Point3
  planeMap_eq : planeMap = fun point :
      {point : Point3 // point ∈ popular.restricted.union} => exact.planeMap
    ⟨point, paperSubshading_union_subset
      popular.restricted_subshading point.property⟩
  planeMap_lipschitz : LipschitzWith exact.K planeMap
  planeMap_unit : ∀ point, ‖planeMap point‖ = 1
  planeMap_incidence :
    ∀ index point,
      ∀ hpoint : point ∈ popular.restricted.carrier index,
        |inner ℝ
            ((anisotropicPaperTargetFamily sourceFamily g c d m center
              targetDelta hcd hm).tube index).direction
            (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ targetDelta

/-- Choose the Lemma-8 box and restrict the exact inverse-transpose field to
it.  No cubical saturation has occurred yet. -/
theorem PureWZ2AnisotropicExactPlaneMapData.toPopularBox
    {sourceDelta targetDelta c d m sigma width : ℝ}
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
    (hwidth : 0 < width) (hwidthOne : width ≤ 1) :
    Nonempty (PureWZ2AnisotropicExactPopularBoxData exact width) := by
  rcases pureWZ2_paper_popular_box raw.exactShading
      hwidth hwidthOne with ⟨popular⟩
  let inclusion :
      {point : Point3 // point ∈ popular.restricted.union} →
        {point : Point3 // point ∈ raw.exactShading.union} :=
    fun point => ⟨point, paperSubshading_union_subset
      popular.restricted_subshading point.property⟩
  have hinclusion : LipschitzWith 1 inclusion := by
    intro first second
    simpa only [inclusion, Subtype.edist_eq, ENNReal.coe_one, one_mul]
      using (le_refl (edist (first : Point3) (second : Point3)))
  let planeMap := fun point => exact.planeMap (inclusion point)
  exact ⟨{
    popular := popular
    planeMap := planeMap
    planeMap_eq := rfl
    planeMap_lipschitz := by
      simpa only [planeMap, inclusion, Function.comp_def, mul_one] using
        exact.planeMap_lipschitz.comp hinclusion
    planeMap_unit := fun point => exact.planeMap_unit (inclusion point)
    planeMap_incidence := by
      intro index point hpoint
      have hambient : point ∈ raw.exactShading.carrier index :=
        popular.restricted_subshading index hpoint
      simpa only [planeMap, inclusion] using
        exact.planeMap_incidence index point hambient
  }⟩

end Kakeya.Assouad

end
