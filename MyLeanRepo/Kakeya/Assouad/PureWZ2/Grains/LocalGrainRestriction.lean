import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RelaxedLocalGrainData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADTransport

/-!
# Restrict local grain data to a paper subshading

A common spatial refinement does not alter the normal attached to a surviving
point.  Lipschitz and incidence bounds therefore restrict directly, while
the local AD estimate follows from monotonicity under subsets.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The union of a paper subshading is contained in the source union. -/
lemma paper_subshading_union_subset
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {selected source : WZ1PaperTubeShading family}
    (hsub : PaperIsSubshading selected source) :
    selected.union ⊆ source.union := by
  rintro point ⟨index, hpoint⟩
  exact ⟨index, hsub index hpoint⟩

/-- Restrict relaxed local grain data to a paper subshading. -/
def PureWZ2RelaxedLocalGrainData.restrict
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source selected : WZ1PaperTubeShading family}
    {C : ENNReal} {L : NNReal}
    (data : PureWZ2RelaxedLocalGrainData source sigma C L)
    (hsub : PaperIsSubshading selected source) :
    PureWZ2RelaxedLocalGrainData selected sigma C L := by
  let hunion : selected.union ⊆ source.union :=
    paper_subshading_union_subset hsub
  let planeMap : {point : Point3 // point ∈ selected.union} → Point3 :=
    fun point => data.planeMap ⟨point, hunion point.prop⟩
  refine
    { planeMap := planeMap
      planeMap_lipschitz := ?_
      planeMap_unit := ?_
      planeMap_incidence := ?_
      local_ad := ?_ }
  · intro first second
    exact data.planeMap_lipschitz
      ⟨first, hunion first.prop⟩ ⟨second, hunion second.prop⟩
  · intro point
    exact data.planeMap_unit ⟨point, hunion point.prop⟩
  · intro index point hpoint
    exact data.planeMap_incidence index point (hsub index hpoint)
  · intro rho hdeltaRho hrhoOne point
    let sourcePoint : {point : Point3 // point ∈ source.union} :=
      ⟨point, hunion point.prop⟩
    have hsourceAD := data.local_ad rho hdeltaRho hrhoOne sourcePoint
    apply hsourceAD.mono_set
    rintro value ⟨other, hother, rfl⟩
    refine ⟨other, ?_, rfl⟩
    exact ⟨hunion hother.1, hother.2⟩

/-- Restrict strict local grain data to a paper subshading. -/
def PureWZ2LocalGrainData.restrict
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source selected : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2LocalGrainData source sigma C)
    (hsub : PaperIsSubshading selected source) :
    PureWZ2LocalGrainData selected sigma C :=
  (PureWZ2RelaxedLocalGrainData.restrict
    (data := ({
      planeMap := data.planeMap
      planeMap_lipschitz := data.planeMap_lipschitz
      planeMap_unit := data.planeMap_unit
      planeMap_incidence := data.planeMap_incidence
      local_ad := data.local_ad
    } : PureWZ2RelaxedLocalGrainData source sigma C 1)) hsub).to_strict

@[simp] theorem PureWZ2LocalGrainData.restrict_planeMap
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source selected : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2LocalGrainData source sigma C)
    (hsub : PaperIsSubshading selected source)
    (point : {point : Point3 // point ∈ selected.union}) :
    (data.restrict hsub).planeMap point =
      data.planeMap
        ⟨point, paper_subshading_union_subset hsub point.property⟩ := by
  rfl

/-- Reindex relaxed local grains along a genuine tube subfamily. -/
def PureWZ2RelaxedLocalGrainData.restrictSubfamily
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal} {L : NNReal}
    (data : PureWZ2RelaxedLocalGrainData source sigma C L)
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    PureWZ2RelaxedLocalGrainData
      (restrictPaperShading selected source) sigma C L := by
  have hunion : (restrictPaperShading selected source).union ⊆
      source.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨selected.embedding index, hpoint⟩
  let planeMap :
      {point : Point3 //
        point ∈ (restrictPaperShading selected source).union} → Point3 :=
    fun point => data.planeMap ⟨point, hunion point.prop⟩
  refine {
    planeMap := planeMap
    planeMap_lipschitz := ?_
    planeMap_unit := ?_
    planeMap_incidence := ?_
    local_ad := ?_
  }
  · intro first second
    exact data.planeMap_lipschitz
      ⟨first, hunion first.prop⟩ ⟨second, hunion second.prop⟩
  · intro point
    exact data.planeMap_unit ⟨point, hunion point.prop⟩
  · intro index point hpoint
    have hraw := data.planeMap_incidence
      (selected.embedding index) point hpoint
    simpa only [selected.tube_eq] using hraw
  · intro rho hdeltaRho hrhoOne point
    have hraw := data.local_ad rho hdeltaRho hrhoOne
      ⟨point, hunion point.prop⟩
    apply hraw.mono_set
    rintro value ⟨other, hother, rfl⟩
    exact ⟨other, ⟨hunion hother.1, hother.2⟩, rfl⟩

/-- Reindex strict local grains along a genuine tube subfamily.  The shading
is the literal restriction, so the point function and every local AD set are
unchanged; incidence transports through the subfamily tube identity. -/
def PureWZ2LocalGrainData.restrictSubfamily
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2LocalGrainData source sigma C)
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    PureWZ2LocalGrainData
      (restrictPaperShading selected source) sigma C := by
  have hunion : (restrictPaperShading selected source).union ⊆
      source.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨selected.embedding index, hpoint⟩
  let planeMap :
      {point : Point3 //
        point ∈ (restrictPaperShading selected source).union} → Point3 :=
    fun point => data.planeMap ⟨point, hunion point.prop⟩
  refine {
    planeMap := planeMap
    planeMap_lipschitz := ?_
    planeMap_unit := ?_
    planeMap_incidence := ?_
    local_ad := ?_
  }
  · intro first second
    exact data.planeMap_lipschitz
      ⟨first, hunion first.prop⟩ ⟨second, hunion second.prop⟩
  · intro point
    exact data.planeMap_unit ⟨point, hunion point.prop⟩
  · intro index point hpoint
    have hraw := data.planeMap_incidence
      (selected.embedding index) point hpoint
    simpa only [selected.tube_eq] using hraw
  · intro rho hdeltaRho hrhoOne point
    have hraw := data.local_ad rho hdeltaRho hrhoOne
      ⟨point, hunion point.prop⟩
    apply hraw.mono_set
    rintro value ⟨other, hother, rfl⟩
    exact ⟨other, ⟨hunion hother.1, hother.2⟩, rfl⟩

end Kakeya.Assouad

end
