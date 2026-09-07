import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2CubicalRefinement

/-!
# Common spatial hull of a paper subshading

A tube-dependent refinement can be replaced by the common spatial
restriction of its source to the refined union.  The replacement has exactly
the same union and at least the same shaded mass, but every surviving point
keeps all of its source tube memberships.  This is the form needed for honest
nested finite-scale iteration.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Restrict every carrier of `source` by the one common spatial set
`candidate.union`. -/
def paperCommonSpatialHull
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (source candidate : WZ1PaperTubeShading F) :
    WZ1PaperTubeShading F where
  carrier index := source.carrier index ∩ candidate.union
  measurable_carrier index :=
    (source.measurable_carrier index).inter
      (measurableSet_shading_union candidate)
  subset_body index :=
    Set.inter_subset_left.trans (source.subset_body index)

lemma paperCommonSpatialHull_subshading
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (source candidate : WZ1PaperTubeShading F) :
    PaperIsSubshading (paperCommonSpatialHull source candidate) source :=
  fun _ => Set.inter_subset_left

/-- The original candidate embeds carrierwise into its common spatial hull. -/
lemma paperCommonSpatialHull_candidate_subshading
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {source candidate : WZ1PaperTubeShading F}
    (hsub : PaperIsSubshading candidate source) :
    PaperIsSubshading candidate
      (paperCommonSpatialHull source candidate) := by
  intro index point hpoint
  exact ⟨hsub index hpoint, ⟨index, hpoint⟩⟩

/-- A subshading and its common spatial hull have exactly the same union. -/
lemma paperCommonSpatialHull_union
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {source candidate : WZ1PaperTubeShading F}
    (hsub : PaperIsSubshading candidate source) :
    (paperCommonSpatialHull source candidate).union = candidate.union := by
  apply Set.Subset.antisymm
  · rintro point ⟨index, hpoint⟩
    exact hpoint.2
  · intro point hpoint
    rcases hpoint with ⟨index, hindex⟩
    exact ⟨index, hsub index hindex, ⟨index, hindex⟩⟩

/-- Passing to the common spatial hull never loses candidate mass. -/
lemma paperCommonSpatialHull_mass_lower
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {source candidate : WZ1PaperTubeShading F}
    (hsub : PaperIsSubshading candidate source) :
    candidate.mass ≤ (paperCommonSpatialHull source candidate).mass := by
  apply Finset.sum_le_sum
  intro index _
  exact measure_mono
    (paperCommonSpatialHull_candidate_subshading hsub index)

/-- At every surviving point, the hull restores the complete active index set
of the source shading. -/
lemma paperCommonSpatialHull_pointMultiplicity_eq
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (source candidate : WZ1PaperTubeShading F) :
    ∀ point ∈ (paperCommonSpatialHull source candidate).union,
      (paperCommonSpatialHull source candidate).pointMultiplicity point =
        source.pointMultiplicity point := by
  intro point hpoint
  rcases hpoint with ⟨witness, hwitness⟩
  have hcandidate : point ∈ candidate.union := hwitness.2
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  ext index
  simp [paperCommonSpatialHull, hcandidate]

/-- Cubical source and candidate shadings give a cubical common spatial
hull. -/
lemma paperCommonSpatialHull_cubical
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {source candidate : WZ1PaperTubeShading F}
    (hsource : WZ1PaperIsCubicalShading source)
    (hcandidate : WZ1PaperIsCubicalShading candidate) :
    WZ1PaperIsCubicalShading
      (paperCommonSpatialHull source candidate) := by
  intro index point hpoint other hother
  have hsourceOther : other ∈ source.carrier index :=
    hsource index point hpoint.1 hother
  rcases hpoint.2 with ⟨witness, hwitness⟩
  have hcandidateOther : other ∈ candidate.carrier witness :=
    hcandidate witness point hwitness hother
  exact ⟨hsourceOther, ⟨witness, hcandidateOther⟩⟩

/-- Any paper AD statement depending only on the shaded union transports
definitionally to the common spatial hull. -/
lemma paperCommonSpatialHull_ad
    {delta sigma queryScale alpha : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {source candidate : WZ1PaperTubeShading F}
    (hsub : PaperIsSubshading candidate source)
    (plane center : Point3) (C : ENNReal)
    (hAD : PureWZ2PaperADSet1
      (scalarProjection plane
        (candidate.union ∩
          Metric.closedBall center (Real.sqrt queryScale)))
      queryScale alpha C) :
    PureWZ2PaperADSet1
      (scalarProjection plane
        ((paperCommonSpatialHull source candidate).union ∩
          Metric.closedBall center (Real.sqrt queryScale)))
      queryScale alpha C := by
  rw [paperCommonSpatialHull_union hsub]
  exact hAD

end Kakeya.Assouad.PureWZ2

end
