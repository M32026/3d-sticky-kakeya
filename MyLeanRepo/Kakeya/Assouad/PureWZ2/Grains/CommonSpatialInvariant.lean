import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSpatialHull
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.JointFiniteVariationLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiplicityPreservingVariation

/-!
# Characterizing multiplicity-preserving spatial restrictions

The finite grain iteration records two facts about every current shading: it
is a subshading of the original source, and every surviving point has the same
point multiplicity as in the source.  Together these facts say more than a
cardinality identity.  They force the current shading to be exactly the common
spatial restriction of the source to the current union.

Consequently a later common-spatial refinement may be formed relative to the
current shading or relative to the original source with definitionally the
same carriers.  This is the invariant needed to rebuild geometric one-scale
certificates on a genuinely nested current shading.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

attribute [local instance] Classical.propDecidable

/-- Shadings are determined by their carrier fields; the remaining fields are
proofs. -/
private lemma shading_ext_carrier
    {family : Kakeya.Streamlined.BodyFamily}
    (first second : Kakeya.Streamlined.Shading family)
    (hcarrier : ∀ index, first.carrier index = second.carrier index) :
    first = second := by
  cases first with
  | mk firstCarrier firstMeasurable firstSubset =>
    cases second with
    | mk secondCarrier secondMeasurable secondSubset =>
      rw [Kakeya.Streamlined.Shading.mk.injEq]
      funext index
      exact hcarrier index

/-- A multiplicity-preserving subshading is exactly the source restricted by
the common spatial set `current.union`. -/
lemma carrier_eq_source_inter_union_of_multiplicity_eq
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source current : WZ1PaperTubeShading family}
    (hsub : PaperIsSubshading current source)
    (hmultiplicity : ∀ point ∈ current.union,
      current.pointMultiplicity point = source.pointMultiplicity point)
    (index : Fin family.card) :
    current.carrier index = source.carrier index ∩ current.union := by
  ext point
  constructor
  · intro hpoint
    exact ⟨hsub index hpoint, ⟨index, hpoint⟩⟩
  · rintro ⟨hpointSource, hpointUnion⟩
    exact
      (paper_carrier_mem_iff_of_subshading_of_multiplicity_eq
        hsub hpointUnion (hmultiplicity point hpointUnion) index).mpr
        hpointSource

/-- The current shading is its own common-spatial hull inside the source. -/
lemma eq_commonSpatialHull_of_multiplicity_eq
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source current : WZ1PaperTubeShading family}
    (hsub : PaperIsSubshading current source)
    (hmultiplicity : ∀ point ∈ current.union,
      current.pointMultiplicity point = source.pointMultiplicity point) :
    current = paperCommonSpatialHull source current := by
  apply shading_ext_carrier
  intro index
  exact carrier_eq_source_inter_union_of_multiplicity_eq
    hsub hmultiplicity index

/-- Rebase a later common-spatial refinement from a multiplicity-preserving
current shading to the original source. -/
lemma commonSpatialHull_current_eq_source
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source current candidate : WZ1PaperTubeShading family}
    (hcurrentSub : PaperIsSubshading current source)
    (hcurrentMultiplicity : ∀ point ∈ current.union,
      current.pointMultiplicity point = source.pointMultiplicity point)
    (hcandidateSub : PaperIsSubshading candidate current) :
    paperCommonSpatialHull current candidate =
      paperCommonSpatialHull source candidate := by
  apply shading_ext_carrier
  intro index
  ext point
  constructor
  · rintro ⟨hpointCurrent, hpointCandidate⟩
    exact ⟨hcurrentSub index hpointCurrent, hpointCandidate⟩
  · rintro ⟨hpointSource, hpointCandidate⟩
    have hpointCurrentUnion : point ∈ current.union := by
      rcases hpointCandidate with ⟨candidateIndex, hcandidateIndex⟩
      exact ⟨candidateIndex, hcandidateSub candidateIndex hcandidateIndex⟩
    have hpointCurrent : point ∈ current.carrier index :=
      (paper_carrier_mem_iff_of_subshading_of_multiplicity_eq
        hcurrentSub hpointCurrentUnion
          (hcurrentMultiplicity point hpointCurrentUnion) index).mpr
        hpointSource
    exact ⟨hpointCurrent, hpointCandidate⟩

/-- A common-spatial refinement made on the current shading preserves the
original source multiplicity at every surviving point. -/
lemma commonSpatialHull_current_pointMultiplicity_eq_source
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source current candidate : WZ1PaperTubeShading family}
    (hcurrentSub : PaperIsSubshading current source)
    (hcurrentMultiplicity : ∀ point ∈ current.union,
      current.pointMultiplicity point = source.pointMultiplicity point)
    (hcandidateSub : PaperIsSubshading candidate current) :
    ∀ point ∈ (paperCommonSpatialHull current candidate).union,
      (paperCommonSpatialHull current candidate).pointMultiplicity point =
        source.pointMultiplicity point := by
  rw [commonSpatialHull_current_eq_source
    hcurrentSub hcurrentMultiplicity hcandidateSub]
  exact paperCommonSpatialHull_pointMultiplicity_eq source candidate

/-- The rebased hull is a genuine next step inside the current shading. -/
lemma commonSpatialHull_current_subshading
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (current candidate : WZ1PaperTubeShading family) :
    PaperIsSubshading
      (paperCommonSpatialHull current candidate) current :=
  paperCommonSpatialHull_subshading current candidate

/-- A cubical current shading and cubical candidate produce a cubical next
shading. -/
lemma commonSpatialHull_current_cubical
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {current candidate : WZ1PaperTubeShading family}
    (hcurrentCubical : WZ1PaperIsCubicalShading current)
    (hcandidateCubical : WZ1PaperIsCubicalShading candidate) :
    WZ1PaperIsCubicalShading
      (paperCommonSpatialHull current candidate) :=
  paperCommonSpatialHull_cubical hcurrentCubical hcandidateCubical

/-- When the candidate is already a subshading of the current shading, the
hull has exactly the candidate union. -/
lemma commonSpatialHull_current_union
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {current candidate : WZ1PaperTubeShading family}
    (hcandidateSub : PaperIsSubshading candidate current) :
    (paperCommonSpatialHull current candidate).union = candidate.union :=
  paperCommonSpatialHull_union hcandidateSub

/-- Passing from a current-relative candidate to its common-spatial hull does
not lose any additional shaded mass. -/
lemma commonSpatialHull_current_mass_lower
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {current candidate : WZ1PaperTubeShading family}
    (hcandidateSub : PaperIsSubshading candidate current) :
    candidate.mass ≤ (paperCommonSpatialHull current candidate).mass :=
  paperCommonSpatialHull_mass_lower hcandidateSub

/-- Upgrade one tube-dependent candidate carrying both geometric conclusions
to the common-spatial one-scale interface.  No independent intersection is
formed: variation and AD are assumed on the same candidate, and the hull has
exactly that candidate union. -/
theorem commonSpatialHull_joint_one_scale
    {delta sigma spatialScale localScale variationScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (current candidate : WZ1PaperTubeShading family)
    (planeMap : Point3 → Point3)
    (constant leftFactor rightFactor : ENNReal)
    (hcandidateSub : PaperIsSubshading candidate current)
    (hcurrentCubical : WZ1PaperIsCubicalShading current)
    (hcandidateCubical : WZ1PaperIsCubicalShading candidate)
    (hvariation : ∀ first ∈ candidate.union,
      ∀ second ∈ candidate.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale)
    (hlocalAD : ∀ point ∈ candidate.union,
      IsADSet1
        (scalarProjection (planeMap point)
          (candidate.union ∩
            Metric.closedBall point (Real.sqrt localScale)))
        localScale (1 - sigma) constant)
    (hmass : leftFactor * current.mass ≤
      rightFactor * candidate.mass) :
    ∃ next : WZ1PaperTubeShading family,
      PaperIsSubshading next current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = current.pointMultiplicity point) ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) ∧
      (∀ point ∈ next.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (next.union ∩
              Metric.closedBall point (Real.sqrt localScale)))
          localScale (1 - sigma) constant) ∧
      leftFactor * current.mass ≤ rightFactor * next.mass := by
  let next := paperCommonSpatialHull current candidate
  have hunion : next.union = candidate.union :=
    paperCommonSpatialHull_union hcandidateSub
  refine ⟨next, paperCommonSpatialHull_subshading current candidate,
    paperCommonSpatialHull_cubical hcurrentCubical hcandidateCubical,
    paperCommonSpatialHull_pointMultiplicity_eq current candidate, ?_, ?_, ?_⟩
  · simpa only [hunion] using hvariation
  · simpa only [hunion] using hlocalAD
  · exact hmass.trans <| by
      gcongr
      exact paperCommonSpatialHull_mass_lower hcandidateSub

/-- Iterate tube-dependent candidates which already carry variation and AD
jointly.  The common-spatial hull is inserted at every stage, so all previous
estimates survive and the final shading retains complete source memberships
at every surviving point. -/
theorem joint_finite_iteration_of_common_candidates
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (hsourceCubical : WZ1PaperIsCubicalShading source)
    (planeMap : Point3 → Point3)
    (N : ℕ)
    (spatialScale localScale variationScale : ℕ → ℝ)
    (constant : ENNReal)
    (leftFactor rightFactor : ℕ → ENNReal)
    (candidateStep : ∀ index : ℕ, index < N →
      ∀ current : WZ1PaperTubeShading family,
        PaperIsSubshading current source →
        WZ1PaperIsCubicalShading current →
        (∀ point ∈ current.union,
          current.pointMultiplicity point = source.pointMultiplicity point) →
        ∃ candidate : WZ1PaperTubeShading family,
          PaperIsSubshading candidate current ∧
          WZ1PaperIsCubicalShading candidate ∧
          (∀ first ∈ candidate.union, ∀ second ∈ candidate.union,
            dist first second ≤ spatialScale index →
              dist (planeMap first) (planeMap second) ≤
                variationScale index) ∧
          (∀ point ∈ candidate.union,
            IsADSet1
              (scalarProjection (planeMap point)
                (candidate.union ∩ Metric.closedBall point
                  (Real.sqrt (localScale index))))
              (localScale index) (1 - sigma) constant) ∧
          leftFactor index * current.mass ≤
            rightFactor index * candidate.mass) :
    ∃ final : WZ1PaperTubeShading family,
      PaperIsSubshading final source ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point = source.pointMultiplicity point) ∧
      (∀ index, index < N →
        ∀ first ∈ final.union, ∀ second ∈ final.union,
          dist first second ≤ spatialScale index →
            dist (planeMap first) (planeMap second) ≤
              variationScale index) ∧
      (∀ index, index < N → ∀ point ∈ final.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (final.union ∩ Metric.closedBall point
              (Real.sqrt (localScale index))))
          (localScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range N, leftFactor index) * source.mass ≤
        (∏ index ∈ Finset.range N, rightFactor index) * final.mass := by
  apply joint_finite_variation_local_ad_iteration
    source hsourceCubical planeMap N spatialScale localScale
      variationScale constant leftFactor rightFactor
  intro index hindex current hcurrentSub hcurrentCubical
    hcurrentMultiplicity
  rcases candidateStep index hindex current hcurrentSub hcurrentCubical
      hcurrentMultiplicity with
    ⟨candidate, hcandidateSub, hcandidateCubical, hvariation,
      hlocalAD, hmass⟩
  exact commonSpatialHull_joint_one_scale
    current candidate planeMap constant (leftFactor index)
      (rightFactor index) hcandidateSub hcurrentCubical
      hcandidateCubical hvariation hlocalAD hmass

end Kakeya.Assouad.PureWZ2

end
