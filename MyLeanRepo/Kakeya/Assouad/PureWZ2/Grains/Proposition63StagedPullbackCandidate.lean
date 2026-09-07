import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentFinePullback

/-!
# Explicit staged candidate for the Proposition 6.3 coarse-to-fine pullback

This module names the four geometric stages hidden inside
`Proposition63CurrentShadingReentryData.candidate_joint_interval_of_outer_coarse`.
The output stops at the paper common-spatial hull.  In particular, it does
not restore extremality and does not apply a mass-loss restoration step.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

private theorem propertyThreeFinePullbackShading_eq_of_union_eq'
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    {first second : WZ1PaperTubeShading coarse}
    (hunion : first.union = second.union) :
    propertyThreeFinePullbackShading cover fineShading first =
      propertyThreeFinePullbackShading cover fineShading second := by
  have hcarrier :
      (propertyThreeFinePullbackShading cover fineShading first).carrier =
        (propertyThreeFinePullbackShading cover fineShading second).carrier := by
    funext index
    rw [propertyThreeFinePullbackShading_carrier,
      propertyThreeFinePullbackShading_carrier, hunion]
  cases hfirst : propertyThreeFinePullbackShading cover fineShading first with
  | mk firstCarrier firstMeasurable firstSubset =>
      cases hsecond :
          propertyThreeFinePullbackShading cover fineShading second with
      | mk secondCarrier secondMeasurable secondSubset =>
          have : firstCarrier = secondCarrier := by
            simpa only [hfirst, hsecond] using hcarrier
          subst secondCarrier
          rfl

/-- Zero-extend the normalized coarse candidate to the complete coarse
family of the outer sticky witness. -/
noncomputable def proposition63CoarseZeroExtension
    {delta sigma outerLoss coarseInputLoss coarseNormalizationLoss : ℝ}
    {fineFamily : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fineFamily}
    {rho : WZ2PaperRequestedScale delta}
    {outerLogExponent coarseNormalizationExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent)
    (coarseCandidate :
      WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index)) :
    WZ1PaperTubeShading outer.coarse :=
  extendShading
    { family := coarseNormalized.croppedFamily
      embedding := ancestorEmbedding
      tube_eq := ancestor_tube_eq }
    coarseCandidate

/-- Pull the coarse zero-extension through Property (P), and take the common
hull in the normalized fine family. -/
noncomputable def proposition63NormalizedAmbientPropertyThreeCommonHull
    {delta sigma initialInputLoss normalizationLoss reentryLoss outerLoss
      coarseInputLoss coarseNormalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {fineNormalizationExponent outerLogExponent
      coarseNormalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource
      fineNormalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent)
    (coarseCandidate :
      WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index)) :
    WZ1PaperTubeShading fineReentry.normalization.croppedFamily :=
  ambientPropertyThreeCommonHull outer <|
    proposition63CoarseZeroExtension outer coarseNormalized coarseCandidate
      ancestorEmbedding ancestor_tube_eq

/-- Zero-extend the normalized fine candidate back to the fixed root family. -/
noncomputable def proposition63FineExtendCandidate
    {delta sigma initialInputLoss normalizationLoss reentryLoss outerLoss
      coarseInputLoss coarseNormalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {fineNormalizationExponent outerLogExponent
      coarseNormalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource
      fineNormalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent)
    (coarseCandidate :
      WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index)) :
    WZ1PaperTubeShading initialNormalized.croppedFamily :=
  fineReentry.extendCandidate <|
    proposition63NormalizedAmbientPropertyThreeCommonHull fineReentry outer
      coarseNormalized coarseCandidate ancestorEmbedding ancestor_tube_eq

/-- The final paper candidate: restore all current tube memberships over the
pulled-back candidate's spatial union, without restoring extremality. -/
noncomputable def proposition63FinalPaperCommonSpatialHull
    {delta sigma initialInputLoss normalizationLoss reentryLoss outerLoss
      coarseInputLoss coarseNormalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {fineNormalizationExponent outerLogExponent
      coarseNormalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource
      fineNormalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent)
    (coarseCandidate :
      WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index)) :
    WZ1PaperTubeShading initialNormalized.croppedFamily :=
  paperCommonSpatialHull current <|
    proposition63FineExtendCandidate fineReentry outer coarseNormalized
      coarseCandidate ancestorEmbedding ancestor_tube_eq

/-- The normalized candidate is insensitive to the carrierwise presentation
of the coarse candidate: only its geometric union is used. -/
theorem proposition63NormalizedAmbientPropertyThreeCommonHull_eq_of_union_eq
    {delta sigma initialInputLoss normalizationLoss reentryLoss outerLoss
      coarseInputLoss coarseNormalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {fineNormalizationExponent outerLogExponent
      coarseNormalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource
      fineNormalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent)
    (first second : WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (hunion : first.union = second.union) :
    proposition63NormalizedAmbientPropertyThreeCommonHull fineReentry outer
        coarseNormalized first ancestorEmbedding ancestor_tube_eq =
      proposition63NormalizedAmbientPropertyThreeCommonHull fineReentry outer
        coarseNormalized second ancestorEmbedding ancestor_tube_eq := by
  have hextendedUnion :
      (proposition63CoarseZeroExtension outer coarseNormalized first
          ancestorEmbedding ancestor_tube_eq).union =
        (proposition63CoarseZeroExtension outer coarseNormalized second
          ancestorEmbedding ancestor_tube_eq).union := by
    calc
      _ = first.union := by
        simpa only [proposition63CoarseZeroExtension] using
          extendShading_union
            { family := coarseNormalized.croppedFamily
              embedding := ancestorEmbedding
              tube_eq := ancestor_tube_eq } first
      _ = second.union := hunion
      _ = _ := by
        simpa only [proposition63CoarseZeroExtension] using
          (extendShading_union
            { family := coarseNormalized.croppedFamily
              embedding := ancestorEmbedding
              tube_eq := ancestor_tube_eq } second).symm
  have hpullback := propertyThreeFinePullbackShading_eq_of_union_eq'
    outer.cover outer.refined hextendedUnion
  simp only [proposition63NormalizedAmbientPropertyThreeCommonHull,
    ambientPropertyThreeCommonHull, ambientPropertyThreePullback]
  rw [hpullback]

/-- The explicitly staged final candidate carries the same six receipts as
`candidate_joint_interval_of_outer_coarse`: subshading, cubicality, exact
point multiplicity, plane variation, interval covering, and the raw mass
ledger. -/
theorem Proposition63CurrentShadingReentryData.explicit_staged_pullback_candidate
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      outerLoss coarseInputLoss coarseNormalizationLoss queryScale
      spatialScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {fineNormalizationExponent outerLogExponent
      coarseNormalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource
      fineNormalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      coarseNormalizationExponent)
    (coarseCurrent coarseCandidate :
      WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, coarseCurrent.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        coarseCurrent.mass)
    (planeMap : Point3 → Point3)
    (resolutionScale windowScale : NNReal)
    (constant coarseLeft coarseRight : ENNReal)
    (hcoarseSub : PaperIsSubshading coarseCandidate coarseCurrent)
    (hcoarseCubical : WZ1PaperIsCubicalShading coarseCandidate)
    (hcoarseVariation : ∀ first ∈ coarseCandidate.union,
      ∀ second ∈ coarseCandidate.union, dist first second ≤ spatialScale →
        dist (planeMap first) (planeMap second) ≤ variationScale)
    (hcoarseInterval : PureWZ2IntervalCoveringAt coarseCandidate planeMap
      queryScale resolutionScale windowScale constant)
    (hcoarseMass : coarseLeft * coarseCurrent.mass ≤
      coarseRight * coarseCandidate.mass)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta) :
    let next := proposition63FinalPaperCommonSpatialHull fineReentry outer
      coarseNormalized coarseCandidate ancestorEmbedding ancestor_tube_eq
    PaperIsSubshading next current ∧
    WZ1PaperIsCubicalShading next ∧
    (∀ point ∈ next.union,
      next.pointMultiplicity point = current.pointMultiplicity point) ∧
    (∀ first ∈ next.union, ∀ second ∈ next.union,
      dist first second ≤ spatialScale →
        dist (planeMap first) (planeMap second) ≤ variationScale) ∧
    PureWZ2IntervalCoveringAt next planeMap queryScale
      resolutionScale windowScale constant ∧
    proposition63DependentFinePullbackLeft fineReentry outer
        ancestorRetentionFactor coarseLeft * current.mass ≤
      proposition63DependentFinePullbackRight fineReentry coarseRight *
        next.mass := by
  let selected : Kakeya.Streamlined.TubeSubfamily outer.coarse :=
    { family := coarseNormalized.croppedFamily
      embedding := ancestorEmbedding
      tube_eq := ancestor_tube_eq }
  let outerCandidate := proposition63CoarseZeroExtension outer coarseNormalized
    coarseCandidate ancestorEmbedding ancestor_tube_eq
  let pullback := propertyThreeFinePullbackShading
    outer.cover outer.refined outerCandidate
  let candidate := proposition63NormalizedAmbientPropertyThreeCommonHull
    fineReentry outer coarseNormalized coarseCandidate ancestorEmbedding
      ancestor_tube_eq
  have houterUnion : outerCandidate.union = coarseCandidate.union := by
    simpa only [outerCandidate, proposition63CoarseZeroExtension, selected]
      using extendShading_union selected coarseCandidate
  have houterMass : outerCandidate.mass = coarseCandidate.mass := by
    simpa only [outerCandidate, proposition63CoarseZeroExtension, selected]
      using extendShading_mass selected coarseCandidate
  have houterSub : PaperIsSubshading outerCandidate
      outer.croppedCoarseShading := by
    intro outerIndex point hpoint
    by_cases himage : ∃ selectedIndex,
        selected.embedding selectedIndex = outerIndex
    · rcases himage with ⟨selectedIndex, rfl⟩
      change point ∈ (extendShading selected coarseCandidate).carrier
        (selected.embedding selectedIndex) at hpoint
      rw [extendShading_carrier_mem] at hpoint
      exact current_sub_outer selectedIndex
        (hcoarseSub selectedIndex hpoint)
    · change point ∈ (extendShading selected coarseCandidate).carrier
        outerIndex at hpoint
      rw [extendShading_carrier_empty himage] at hpoint
      exact False.elim hpoint
  have houterCubical : WZ1PaperIsCubicalShading outerCandidate := by
    simpa only [outerCandidate, proposition63CoarseZeroExtension, selected]
      using extendShading_cubical selected hcoarseCubical
  have hpullbackCubical : WZ1PaperIsCubicalShading pullback :=
    propertyThreeFinePullbackShading_cubical outer.cover outer.refined
      outerCandidate outer.refined_cubical scaleFactor hscaleFactor hrhoAligned
  have hcandidateSub : PaperIsSubshading candidate
      fineReentry.normalization.croppedRefined := by
    simpa only [candidate, proposition63NormalizedAmbientPropertyThreeCommonHull]
      using ambientPropertyThreeCommonHull_subshading outer outerCandidate
  have hcandidateCubical : WZ1PaperIsCubicalShading candidate := by
    simpa only [candidate, proposition63NormalizedAmbientPropertyThreeCommonHull]
      using ambientPropertyThreeCommonHull_cubical outer outerCandidate
        fineReentry.normalization.cropped_cubical hpullbackCubical
  have hpullbackSubset : pullback.union ⊆ outerCandidate.union :=
    propertyThreeFinePullbackShading_union_subset outer.cover outer.refined
      outerCandidate houterCubical
  have hpullbackCoarse : pullback.union ⊆ coarseCandidate.union := by
    intro point hpoint
    exact houterUnion ▸ hpullbackSubset hpoint
  have hcandidateUnion : candidate.union = pullback.union := by
    simpa only [candidate, proposition63NormalizedAmbientPropertyThreeCommonHull,
      pullback] using ambientPropertyThreeCommonHull_union outer outerCandidate
  have hcandidateVariation : ∀ first ∈ candidate.union,
      ∀ second ∈ candidate.union, dist first second ≤ spatialScale →
        dist (planeMap first) (planeMap second) ≤ variationScale := by
    intro first hfirst second hsecond hdistance
    exact hcoarseVariation first
      (hpullbackCoarse (hcandidateUnion ▸ hfirst)) second
      (hpullbackCoarse (hcandidateUnion ▸ hsecond)) hdistance
  have hcandidateInterval : PureWZ2IntervalCoveringAt candidate planeMap
      queryScale resolutionScale windowScale constant := by
    intro point center
    have hpointPullback : (point : Point3) ∈ pullback.union :=
      hcandidateUnion ▸ point.property
    have hcover := hcoarseInterval
      ⟨point, hpullbackCoarse hpointPullback⟩ center
    apply (show (Metric.externalCoveringNumber resolutionScale
        (scalarProjection (planeMap point)
            (candidate.union ∩ Metric.closedBall (point : Point3)
              (Real.sqrt queryScale)) ∩
          Metric.closedBall center (windowScale : ℝ)) : ENNReal) ≤
        (Metric.externalCoveringNumber resolutionScale
          (scalarProjection (planeMap point)
              (coarseCandidate.union ∩ Metric.closedBall (point : Point3)
                (Real.sqrt queryScale)) ∩
            Metric.closedBall center (windowScale : ℝ)) : ENNReal) by
      exact_mod_cast Metric.externalCoveringNumber_mono_set (by
        rintro value ⟨⟨other, hother, rfl⟩, hvalue⟩
        exact ⟨⟨other, ⟨hpullbackCoarse (hcandidateUnion ▸ hother.1),
          hother.2⟩, rfl⟩, hvalue⟩)).trans hcover
  have hcoarseComparison :
      (coarseLeft * ancestorRetentionFactor⁻¹) *
          outer.croppedCoarseShading.mass ≤
        coarseRight * outerCandidate.mass := by
    calc
      _ = coarseLeft * (ancestorRetentionFactor⁻¹ *
          outer.croppedCoarseShading.mass) := by ring
      _ ≤ coarseLeft * coarseCurrent.mass := by gcongr
      _ ≤ coarseRight * coarseCandidate.mass := hcoarseMass
      _ = coarseRight * outerCandidate.mass := by rw [houterMass]
  have hpullbackMass :=
    propertyThreeFinePullback_mass_lower_of_sticky_comparison
      outer outerCandidate fineReentry.reentry_extremal.delta_pos
      houterSub houterCubical (coarseLeft * ancestorRetentionFactor⁻¹)
      coarseRight hcoarseComparison
  let pullbackFactor : ENNReal :=
    coarseLeft * ancestorRetentionFactor⁻¹ *
      (proposition63OuterCoarsePullbackCost outer)⁻¹ *
      wz2PaperPureRefinementFraction delta outerLogExponent
  have hnormalizedMass : pullbackFactor *
        fineReentry.normalization.croppedRefined.mass ≤
      coarseRight * pullback.mass := by
    calc
      _ = (coarseLeft * ancestorRetentionFactor⁻¹ *
          (proposition63OuterCoarsePullbackCost outer)⁻¹) *
          (wz2PaperPureRefinementFraction delta outerLogExponent *
            fineReentry.normalization.croppedRefined.mass) := by
        simp only [pullbackFactor]
        ring
      _ ≤ (coarseLeft * ancestorRetentionFactor⁻¹ *
          (proposition63OuterCoarsePullbackCost outer)⁻¹) *
          outer.refined.mass := mul_le_mul_left' outer.retained_mass _
      _ ≤ coarseRight * pullback.mass := by
        simpa only [pullback, proposition63OuterCoarsePullbackCost]
          using hpullbackMass
  have hpullbackCommonMass : pullback.mass ≤ candidate.mass := by
    calc
      pullback.mass =
          (ambientPropertyThreePullback outer outerCandidate).mass := by
        rw [ambientPropertyThreePullback_mass]
      _ ≤ candidate.mass := by
        change (ambientPropertyThreePullback outer outerCandidate).mass ≤
          (paperCommonSpatialHull fineReentry.normalization.croppedRefined
            (ambientPropertyThreePullback outer outerCandidate)).mass
        exact paperCommonSpatialHull_mass_lower
          (ambientPropertyThreePullback_subshading outer outerCandidate)
  have hcandidateMass : pullbackFactor *
        fineReentry.normalization.croppedRefined.mass ≤
      coarseRight * candidate.mass :=
    hnormalizedMass.trans (mul_le_mul_left' hpullbackCommonMass coarseRight)
  have hrootMass :
      (pullbackFactor * ((73 / 100 : ENNReal) *
          fineReentry.normalizationWeight)) * current.mass ≤
        (coarseRight * fineReentry.regularized.regularizationLoss) *
          candidate.mass := by
    calc
      _ = pullbackFactor * (((73 / 100 : ENNReal) *
          fineReentry.normalizationWeight) * current.mass) := by ring
      _ ≤ pullbackFactor * (fineReentry.regularized.regularizationLoss *
          fineReentry.normalization.croppedRefined.mass) :=
        mul_le_mul_left' fineReentry.reentryMassRetention pullbackFactor
      _ = fineReentry.regularized.regularizationLoss *
          (pullbackFactor * fineReentry.normalization.croppedRefined.mass) := by
        ring
      _ ≤ fineReentry.regularized.regularizationLoss *
          (coarseRight * candidate.mass) :=
        mul_le_mul_left' hcandidateMass _
      _ = (coarseRight * fineReentry.regularized.regularizationLoss) *
          candidate.mass := by ring
  let ambientCandidate := proposition63FineExtendCandidate fineReentry outer
    coarseNormalized coarseCandidate ancestorEmbedding ancestor_tube_eq
  have hambientSub : PaperIsSubshading ambientCandidate current := by
    simpa only [ambientCandidate, proposition63FineExtendCandidate]
      using fineReentry.extendCandidate_subshading hcandidateSub
  have hambientCubical : WZ1PaperIsCubicalShading ambientCandidate := by
    change WZ1PaperIsCubicalShading
      (fineReentry.extendCandidate candidate)
    exact extendShading_cubical fineReentry.regularized.selected
      hcandidateCubical
  have hambientUnion : ambientCandidate.union = candidate.union := by
    simpa only [ambientCandidate, proposition63FineExtendCandidate]
      using fineReentry.extendCandidate_union candidate
  let next := proposition63FinalPaperCommonSpatialHull fineReentry outer
    coarseNormalized coarseCandidate ancestorEmbedding ancestor_tube_eq
  have hnextDef : next = paperCommonSpatialHull current ambientCandidate := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change PaperIsSubshading (paperCommonSpatialHull current ambientCandidate)
      current
    exact paperCommonSpatialHull_subshading current ambientCandidate
  · change WZ1PaperIsCubicalShading
      (paperCommonSpatialHull current ambientCandidate)
    exact paperCommonSpatialHull_cubical fineReentry.current_cubical
      hambientCubical
  · change ∀ point ∈ (paperCommonSpatialHull current ambientCandidate).union,
      (paperCommonSpatialHull current ambientCandidate).pointMultiplicity point =
        current.pointMultiplicity point
    exact paperCommonSpatialHull_pointMultiplicity_eq current ambientCandidate
  · change ∀ first ∈ (paperCommonSpatialHull current ambientCandidate).union,
      ∀ second ∈ (paperCommonSpatialHull current ambientCandidate).union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale
    rw [paperCommonSpatialHull_union hambientSub, hambientUnion]
    exact hcandidateVariation
  · change PureWZ2IntervalCoveringAt
      (paperCommonSpatialHull current ambientCandidate) planeMap queryScale
        resolutionScale windowScale constant
    intro point center
    have hpointAmbient : (point : Point3) ∈ ambientCandidate.union := by
      rw [← paperCommonSpatialHull_union hambientSub]
      exact point.property
    have hpointCandidate : (point : Point3) ∈ candidate.union := by
      rw [← hambientUnion]
      exact hpointAmbient
    have hcover := hcandidateInterval ⟨point, hpointCandidate⟩ center
    simpa only [paperCommonSpatialHull_union hambientSub, hambientUnion] using
      hcover
  · simpa only [proposition63DependentFinePullbackLeft,
      proposition63DependentFinePullbackRight, pullbackFactor] using
      hrootMass.trans (mul_le_mul_left' (by
        calc
          candidate.mass = ambientCandidate.mass := by
            change candidate.mass = (fineReentry.extendCandidate candidate).mass
            exact (fineReentry.extendCandidate_mass candidate).symm
          _ ≤ next.mass := by
            rw [hnextDef]
            exact paperCommonSpatialHull_mass_lower hambientSub)
        (coarseRight * fineReentry.regularized.regularizationLoss))

end Kakeya.Assouad.PureWZ2

end
