import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Refinement

/-!
# Restriction of pure grain data

These monotonicity constructions depend only on the paper-facing grain
records, not on a particular sticky or terminal-scale producer.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Restrict a Pure local-grain package through an indexed tube subfamily. -/
def PureWZ2LocalGrainData.restrictSubfamilyWithShading
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2LocalGrainData sourceShading sigma C)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (refined : WZ1PaperTubeShading selected.family)
    (hsub : ∀ index, refined.carrier index ⊆
      sourceShading.carrier (selected.embedding index)) :
    PureWZ2LocalGrainData refined sigma C where
  planeMap point := data.planeMap ⟨point, by
    rcases point.property with ⟨index, hpoint⟩
    exact ⟨selected.embedding index, hsub index hpoint⟩⟩
  planeMap_lipschitz := by
    intro first second
    exact data.planeMap_lipschitz
      ⟨first, by
        rcases first.property with ⟨index, hpoint⟩
        exact ⟨selected.embedding index, hsub index hpoint⟩⟩
      ⟨second, by
        rcases second.property with ⟨index, hpoint⟩
        exact ⟨selected.embedding index, hsub index hpoint⟩⟩
  planeMap_unit := by
    intro point
    exact data.planeMap_unit
      ⟨point, by
        rcases point.property with ⟨index, hpoint⟩
        exact ⟨selected.embedding index, hsub index hpoint⟩⟩
  planeMap_incidence := by
    intro index point hpoint
    simpa only [selected.tube_eq] using
      data.planeMap_incidence (selected.embedding index) point
        (hsub index hpoint)
  local_ad := by
    intro rho hdeltaRho hrhoOne point
    let ambientPoint : {point : Point3 // point ∈ sourceShading.union} :=
      ⟨point, by
        rcases point.property with ⟨index, hpoint⟩
        exact ⟨selected.embedding index, hsub index hpoint⟩⟩
    apply (data.local_ad rho hdeltaRho hrhoOne ambientPoint).mono
    rintro value ⟨target, htarget, rfl⟩
    refine ⟨target, ⟨?_, htarget.2⟩, rfl⟩
    rcases htarget.1 with ⟨index, hpoint⟩
    exact ⟨selected.embedding index, hsub index hpoint⟩

/-- Restrict a Pure global-grain package through an indexed tube subfamily. -/
def PureWZ2LipschitzGlobalGrainData.restrictSubfamilyWithShading
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2LipschitzGlobalGrainData sourceShading sigma C)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (refined : WZ1PaperTubeShading selected.family)
    (hsub : ∀ index, refined.carrier index ⊆
      sourceShading.carrier (selected.embedding index)) :
    PureWZ2LipschitzGlobalGrainData refined sigma C where
  f := data.f
  lipschitz := data.lipschitz
  paper_ad := by
    intro z
    apply (data.paper_ad z).mono
    rintro value ⟨point, hpoint, rfl⟩
    refine ⟨point, ⟨?_, hpoint.2⟩, rfl⟩
    rcases hpoint.1 with ⟨index, hcarrier⟩
    exact ⟨selected.embedding index, hsub index hcarrier⟩

/-- Restrict a bounded global-grain package through an indexed tube
subfamily, retaining the same bounded slope representative. -/
def PureWZ2BoundedLipschitzGlobalGrainData.restrictSubfamilyWithShading
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2BoundedLipschitzGlobalGrainData sourceShading sigma C)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (refined : WZ1PaperTubeShading selected.family)
    (hsub : ∀ index, refined.carrier index ⊆
      sourceShading.carrier (selected.embedding index)) :
    PureWZ2BoundedLipschitzGlobalGrainData refined sigma C where
  toPureWZ2LipschitzGlobalGrainData :=
    data.toPureWZ2LipschitzGlobalGrainData.restrictSubfamilyWithShading
      selected refined hsub
  f_bound := data.f_bound

end Kakeya.Assouad
