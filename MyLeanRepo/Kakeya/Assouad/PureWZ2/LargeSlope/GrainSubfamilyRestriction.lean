import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ConfigurationRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Restrict C2 grain fields to a genuine tube subfamily

This is the indexed counterpart of `ConfigurationRestriction`.  It retains
the actual selected tube family instead of zero-extending its shading back to
the ambient family.  In particular, any public ordinary nearby-scale CWA
already carried by the selected family remains available to later consumers.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The union of a restricted paper shading embeds in the ambient union. -/
theorem restrictPaperShading_union_subset
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (shading : WZ1PaperTubeShading family) :
    (restrictPaperShading selected shading).union ⊆ shading.union := by
  rintro point ⟨index, hpoint⟩
  exact ⟨selected.embedding index, hpoint⟩

/-- Reindex a C2 global-grain field on a genuine tube subfamily. -/
def PureWZ2C2GlobalGrainData.subfamily
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2C2GlobalGrainData shading sigma C)
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    PureWZ2C2GlobalGrainData
      (restrictPaperShading selected shading) sigma C where
  f := data.f
  normalized := data.normalized
  global_ad := by
    intro z
    exact (data.global_ad z).weaken_subset <| by
      apply Set.image_mono
      rintro point ⟨hpoint, hheight⟩
      exact ⟨restrictPaperShading_union_subset selected shading hpoint, hheight⟩

/-- Reindex a local plane-map field on a genuine tube subfamily. -/
def PureWZ2LocalGrainData.subfamily
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2LocalGrainData shading sigma C)
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    PureWZ2LocalGrainData
      (restrictPaperShading selected shading) sigma C := by
  let inclusionMap :
      {point : Point3 //
        point ∈ (restrictPaperShading selected shading).union} →
        {point : Point3 // point ∈ shading.union} :=
    fun point => ⟨point,
      restrictPaperShading_union_subset selected shading point.property⟩
  have hinclusion : LipschitzWith 1 inclusionMap := by
    intro first second
    simpa [inclusionMap, Subtype.edist_eq]
  refine {
    planeMap := fun point => data.planeMap (inclusionMap point)
    planeMap_lipschitz := by
      simpa [Function.comp_def] using data.planeMap_lipschitz.comp hinclusion
    planeMap_unit := fun point => data.planeMap_unit (inclusionMap point)
    planeMap_incidence := ?_
    local_ad := ?_
  }
  · intro index point hpoint
    have hambient : point ∈ shading.carrier (selected.embedding index) := hpoint
    have h := data.planeMap_incidence
      (selected.embedding index) point hambient
    simpa [inclusionMap, selected.tube_eq] using h
  · intro rho hdeltaRho hrhoOne point
    exact (data.local_ad rho hdeltaRho hrhoOne (inclusionMap point))
      |>.weaken_subset <| by
        rintro value ⟨source, ⟨hsource, hball⟩, rfl⟩
        exact ⟨source,
          ⟨restrictPaperShading_union_subset selected shading hsource,
            by simpa [inclusionMap] using hball⟩, rfl⟩

/-- Proposition-21 compatibility restricts to the same selected family. -/
theorem PureWZ2LocalGlobalCompatibility.subfamily
    {sigma loss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma loss delta}
    (compatibility : PureWZ2LocalGlobalCompatibility cfg)
    (selected : Kakeya.Streamlined.TubeSubfamily cfg.family) :
    let shading := restrictPaperShading selected cfg.shading
    let globalGrains := cfg.globalGrains.subfamily selected
    let localGrains := cfg.localGrains.subfamily selected
    (∀ index, ‖(selected.family.tube index).base‖ ≤ 5) ∧
      (∀ point, 1 / 4 ≤ |localGrains.planeMap point 0|) ∧
      (∀ point,
        |localGrains.planeMap point 1 -
          cfg.globalGrains.slope (point.1 2) *
            localGrains.planeMap point 0| ≤ 1 / 10) := by
  dsimp only
  constructor
  · intro index
    rw [selected.tube_eq]
    exact compatibility.tube_base_local (selected.embedding index)
  constructor
  · intro point
    exact compatibility.normal_first
      ⟨point, restrictPaperShading_union_subset selected cfg.shading
        point.property⟩
  · intro point
    exact compatibility.normal_tilt
      ⟨point, restrictPaperShading_union_subset selected cfg.shading
        point.property⟩

end Kakeya.Assouad

end
