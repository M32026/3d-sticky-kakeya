import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentOneScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSpatialPropertyThreePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeFinePullbackMass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63AlignedFiniteSchedule

/-!
# Pulling a dependent coarse full-grain step back to the root family

The dependent LOW/HIGH argument and its line-hit selection first live on a
normalization of the outer sticky cover's coarse family.  The finite
Proposition 6.3 iterator, however, must remain on its fixed fine family.  This
module performs the paper's whole-cell pullback through that same outer cover.
It first zero-extends the coarse candidate along its recorded ancestor
embedding, then pulls the selected coarse cells back to the outer fine
shading, and finally restores all current fine-tube memberships by taking a
common spatial hull.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/-- The multiplicity cost in the whole-cell pullback through one sticky
cover. -/
def proposition63OuterCoarsePullbackCost
    {delta sigma outputLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss) source rho logExponent) :
    ENNReal :=
  stickyCoarseMultiplicityCap outer * stickyCoarseMultiplicityCap outer *
    stickyFiberMultiplicityCap outer

/-- Exact left factor obtained by pulling a coarse candidate through the
outer sticky cover and composing with the current fine re-entry. -/
def proposition63DependentFinePullbackLeft
    {delta sigma outputLoss initialInputLoss normalizationLoss reentryLoss : ℝ}
    {rho : WZ2PaperRequestedScale delta}
    {outerLogExponent normalizationExponent : ℕ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    (ancestorRetentionFactor coarseLeft : ENNReal) : ENNReal :=
  coarseLeft * ancestorRetentionFactor⁻¹ *
      (proposition63OuterCoarsePullbackCost outer)⁻¹ *
      wz2PaperPureRefinementFraction delta outerLogExponent *
    ((73 / 100 : ENNReal) * fineReentry.normalizationWeight)

/-- Exact right factor obtained by composing the coarse candidate loss with
the current fine re-entry regularization. -/
def proposition63DependentFinePullbackRight
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (coarseRight : ENNReal) : ENNReal :=
  coarseRight * fineReentry.regularized.regularizationLoss

/-- Extend an interval-covering candidate from a current re-entry family and
take the common-spatial hull in the fixed current family.  Because both
zero-extension and the hull preserve the candidate union, the interval
estimate is transported without any enlargement of its covering constant. -/
theorem Proposition63CurrentShadingReentryData.candidate_joint_interval
    {delta sigma initialInputLoss normalizationLoss reentryLoss queryScale
      spatialScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (candidate : WZ1PaperTubeShading data.normalization.croppedFamily)
    (planeMap : Point3 → Point3)
    (resolutionScale windowScale : NNReal)
    (constant leftFactor rightFactor : ENNReal)
    (hsub : PaperIsSubshading candidate data.normalization.croppedRefined)
    (hcubical : WZ1PaperIsCubicalShading candidate)
    (hvariation : ∀ first ∈ candidate.union, ∀ second ∈ candidate.union,
      dist first second ≤ spatialScale →
        dist (planeMap first) (planeMap second) ≤ variationScale)
    (hinterval : PureWZ2IntervalCoveringAt candidate planeMap queryScale
      resolutionScale windowScale constant)
    (hmass : leftFactor * current.mass ≤ rightFactor * candidate.mass) :
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
      PaperIsSubshading next current ∧
      WZ1PaperIsCubicalShading next ∧
      (∀ point ∈ next.union,
        next.pointMultiplicity point = current.pointMultiplicity point) ∧
      (∀ first ∈ next.union, ∀ second ∈ next.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale) ∧
      PureWZ2IntervalCoveringAt next planeMap queryScale
        resolutionScale windowScale constant ∧
      leftFactor * current.mass ≤ rightFactor * next.mass := by
  let ambientCandidate := data.extendCandidate candidate
  have hambientSub : PaperIsSubshading ambientCandidate current :=
    data.extendCandidate_subshading hsub
  have hambientCubical : WZ1PaperIsCubicalShading ambientCandidate :=
    extendShading_cubical data.regularized.selected hcubical
  have hambientVariation : ∀ first ∈ ambientCandidate.union,
      ∀ second ∈ ambientCandidate.union,
        dist first second ≤ spatialScale →
          dist (planeMap first) (planeMap second) ≤ variationScale := by
    simpa only [ambientCandidate, data.extendCandidate_union candidate] using
      hvariation
  have hambientInterval : PureWZ2IntervalCoveringAt ambientCandidate planeMap
      queryScale resolutionScale windowScale constant := by
    intro point center
    have hpointCandidate : (point : Point3) ∈ candidate.union := by
      rw [← data.extendCandidate_union candidate]
      exact point.property
    have hcover := hinterval ⟨point, hpointCandidate⟩ center
    simpa only [ambientCandidate, data.extendCandidate_union candidate] using
      hcover
  have hambientMass : leftFactor * current.mass ≤
      rightFactor * ambientCandidate.mass := by
    simpa only [ambientCandidate, data.extendCandidate_mass candidate] using
      hmass
  let next := paperCommonSpatialHull current ambientCandidate
  have hunion : next.union = ambientCandidate.union :=
    paperCommonSpatialHull_union hambientSub
  refine ⟨next, paperCommonSpatialHull_subshading current ambientCandidate,
    paperCommonSpatialHull_cubical data.current_cubical hambientCubical,
    paperCommonSpatialHull_pointMultiplicity_eq current ambientCandidate,
    ?_, ?_, ?_⟩
  · simpa only [hunion] using hambientVariation
  · intro point center
    have hpointAmbient : (point : Point3) ∈ ambientCandidate.union := by
      rw [← hunion]
      exact point.property
    have hcover := hambientInterval ⟨point, hpointAmbient⟩ center
    simpa only [hunion] using hcover
  · exact hambientMass.trans <| by
      gcongr
      exact paperCommonSpatialHull_mass_lower hambientSub

/-- A candidate constructed on a mass-retaining normalization of the outer
coarse pair pulls back to the fixed fine family used by the root iterator.
The coarse candidate must be cubical at the outer requested scale; this makes
its whole-cell fine pullback a subset of the same geometric union, so the
local AD and plane-map variation estimates restrict without perturbation. -/
theorem Proposition63CurrentShadingReentryData.candidate_joint_one_scale_of_outer_coarse
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      outerLoss coarseInputLoss coarseNormalizationLoss
      localScale spatialScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
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
      normalizationExponent)
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
    (constant coarseLeft coarseRight : ENNReal)
    (hcoarseSub : PaperIsSubshading coarseCandidate coarseCurrent)
    (hcoarseCubical : WZ1PaperIsCubicalShading coarseCandidate)
    (hcoarseVariation : ∀ first ∈ coarseCandidate.union,
      ∀ second ∈ coarseCandidate.union, dist first second ≤ spatialScale →
        dist (planeMap first) (planeMap second) ≤ variationScale)
    (hcoarseAD : ∀ point ∈ coarseCandidate.union,
      IsADSet1
        (scalarProjection (planeMap point)
          (coarseCandidate.union ∩ Metric.closedBall point
            (Real.sqrt localScale)))
        localScale (1 - sigma) constant)
    (hcoarseMass : coarseLeft * coarseCurrent.mass ≤
      coarseRight * coarseCandidate.mass)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta) :
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
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
            (next.union ∩ Metric.closedBall point
              (Real.sqrt localScale)))
          localScale (1 - sigma) constant) ∧
      proposition63DependentFinePullbackLeft fineReentry outer
          ancestorRetentionFactor coarseLeft * current.mass ≤
        proposition63DependentFinePullbackRight fineReentry coarseRight *
          next.mass := by
  let selected : Kakeya.Streamlined.TubeSubfamily outer.coarse :=
    { family := coarseNormalized.croppedFamily
      embedding := ancestorEmbedding
      tube_eq := ancestor_tube_eq }
  let outerCandidate : WZ1PaperTubeShading outer.coarse :=
    extendShading selected coarseCandidate
  have houterUnion : outerCandidate.union = coarseCandidate.union := by
    simpa only [outerCandidate] using extendShading_union selected coarseCandidate
  have houterMass : outerCandidate.mass = coarseCandidate.mass := by
    simpa only [outerCandidate] using extendShading_mass selected coarseCandidate
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
  have houterCubical : WZ1PaperIsCubicalShading outerCandidate :=
    extendShading_cubical selected hcoarseCubical
  let pullback := propertyThreeFinePullbackShading
    outer.cover outer.refined outerCandidate
  let candidate := ambientPropertyThreeCommonHull outer outerCandidate
  have hpullbackCubical : WZ1PaperIsCubicalShading pullback :=
    propertyThreeFinePullbackShading_cubical outer.cover outer.refined
      outerCandidate outer.refined_cubical scaleFactor hscaleFactor
      hrhoAligned
  have hcandidateSub : PaperIsSubshading candidate
      fineReentry.normalization.croppedRefined :=
    ambientPropertyThreeCommonHull_subshading outer outerCandidate
  have hcandidateCubical : WZ1PaperIsCubicalShading candidate :=
    ambientPropertyThreeCommonHull_cubical outer outerCandidate
      fineReentry.normalization.cropped_cubical hpullbackCubical
  have hpullbackSubset : pullback.union ⊆ outerCandidate.union :=
    propertyThreeFinePullbackShading_union_subset outer.cover outer.refined
      outerCandidate houterCubical
  have hpullbackCoarse : pullback.union ⊆ coarseCandidate.union := by
    intro point hpoint
    exact houterUnion ▸ hpullbackSubset hpoint
  have hcandidateUnion : candidate.union = pullback.union :=
    ambientPropertyThreeCommonHull_union outer outerCandidate
  have hcandidateVariation : ∀ first ∈ candidate.union,
      ∀ second ∈ candidate.union, dist first second ≤ spatialScale →
        dist (planeMap first) (planeMap second) ≤ variationScale := by
    intro first hfirst second hsecond hdistance
    apply hcoarseVariation first
      (hpullbackCoarse (hcandidateUnion ▸ hfirst)) second
      (hpullbackCoarse (hcandidateUnion ▸ hsecond)) hdistance
  have hcandidateAD : ∀ point ∈ candidate.union,
      IsADSet1
        (scalarProjection (planeMap point)
          (candidate.union ∩ Metric.closedBall point
            (Real.sqrt localScale)))
        localScale (1 - sigma) constant := by
    intro point hpoint
    have hpointPullback : point ∈ pullback.union := hcandidateUnion ▸ hpoint
    apply (hcoarseAD point (hpullbackCoarse hpointPullback)).mono
    rintro value ⟨other, hother, rfl⟩
    exact ⟨other, ⟨hpullbackCoarse (hcandidateUnion ▸ hother.1),
      hother.2⟩, rfl⟩
  have hcoarseComparison :
      (coarseLeft * ancestorRetentionFactor⁻¹) *
          outer.croppedCoarseShading.mass ≤
        coarseRight * outerCandidate.mass := by
    calc
      (coarseLeft * ancestorRetentionFactor⁻¹) *
          outer.croppedCoarseShading.mass =
        coarseLeft * (ancestorRetentionFactor⁻¹ *
          outer.croppedCoarseShading.mass) := by ring
      _ ≤ coarseLeft * coarseCurrent.mass := by gcongr
      _ ≤ coarseRight * coarseCandidate.mass := hcoarseMass
      _ = coarseRight * outerCandidate.mass := by
        rw [houterMass]
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
      pullbackFactor * fineReentry.normalization.croppedRefined.mass =
          (coarseLeft * ancestorRetentionFactor⁻¹ *
            (proposition63OuterCoarsePullbackCost outer)⁻¹) *
          (wz2PaperPureRefinementFraction delta outerLogExponent *
            fineReentry.normalization.croppedRefined.mass) := by
        simp only [pullbackFactor]
        ring
      _ ≤ (coarseLeft * ancestorRetentionFactor⁻¹ *
            (proposition63OuterCoarsePullbackCost outer)⁻¹) *
          outer.refined.mass :=
        mul_le_mul_left' outer.retained_mass
          (coarseLeft * ancestorRetentionFactor⁻¹ *
            (proposition63OuterCoarsePullbackCost outer)⁻¹)
      _ ≤ coarseRight * pullback.mass := by
        simpa only [pullback, proposition63OuterCoarsePullbackCost]
          using hpullbackMass
  have hpullbackCommonMass : pullback.mass ≤ candidate.mass := by
    calc
      pullback.mass =
          (ambientPropertyThreePullback outer outerCandidate).mass := by
        rw [ambientPropertyThreePullback_mass]
      _ ≤ candidate.mass := by
        exact paperCommonSpatialHull_mass_lower
          (ambientPropertyThreePullback_subshading outer outerCandidate)
  have hcandidateMass : pullbackFactor *
        fineReentry.normalization.croppedRefined.mass ≤
      coarseRight * candidate.mass :=
    hnormalizedMass.trans (mul_le_mul_left' hpullbackCommonMass coarseRight)
  have hrootMass :
      (pullbackFactor *
          ((73 / 100 : ENNReal) * fineReentry.normalizationWeight)) *
          current.mass ≤
        (coarseRight * fineReentry.regularized.regularizationLoss) *
          candidate.mass := by
    calc
      (pullbackFactor *
          ((73 / 100 : ENNReal) * fineReentry.normalizationWeight)) *
          current.mass =
        pullbackFactor *
          (((73 / 100 : ENNReal) * fineReentry.normalizationWeight) *
            current.mass) := by ring
      _ ≤ pullbackFactor *
          (fineReentry.regularized.regularizationLoss *
            fineReentry.normalization.croppedRefined.mass) :=
        mul_le_mul_left' fineReentry.reentryMassRetention pullbackFactor
      _ = fineReentry.regularized.regularizationLoss *
          (pullbackFactor *
            fineReentry.normalization.croppedRefined.mass) := by ring
      _ ≤ fineReentry.regularized.regularizationLoss *
          (coarseRight * candidate.mass) :=
        mul_le_mul_left' hcandidateMass
          fineReentry.regularized.regularizationLoss
      _ = (coarseRight * fineReentry.regularized.regularizationLoss) *
          candidate.mass := by ring
  simpa only [proposition63DependentFinePullbackLeft,
    proposition63DependentFinePullbackRight, pullbackFactor] using
    fineReentry.candidate_joint_one_scale candidate planeMap constant
      (pullbackFactor *
        ((73 / 100 : ENNReal) * fineReentry.normalizationWeight))
      (coarseRight * fineReentry.regularized.regularizationLoss)
      hcandidateSub hcandidateCubical hcandidateVariation hcandidateAD
      hrootMass

/-- Interval-native version of the dependent whole-cell pullback.  It uses
the same selected-coarse extension, Property-(P) fine pullback, cardinality
cancellation, and common-spatial hull as
`candidate_joint_one_scale_of_outer_coarse`, but transports the localized
interval estimate directly instead of assuming a completed one-scale AD
bound. -/
theorem Proposition63CurrentShadingReentryData.candidate_joint_interval_of_outer_coarse
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
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
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
  let outerCandidate : WZ1PaperTubeShading outer.coarse :=
    extendShading selected coarseCandidate
  have houterUnion : outerCandidate.union = coarseCandidate.union := by
    simpa only [outerCandidate] using extendShading_union selected coarseCandidate
  have houterMass : outerCandidate.mass = coarseCandidate.mass := by
    simpa only [outerCandidate] using extendShading_mass selected coarseCandidate
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
  have houterCubical : WZ1PaperIsCubicalShading outerCandidate :=
    extendShading_cubical selected hcoarseCubical
  let pullback := propertyThreeFinePullbackShading
    outer.cover outer.refined outerCandidate
  let candidate := ambientPropertyThreeCommonHull outer outerCandidate
  have hpullbackCubical : WZ1PaperIsCubicalShading pullback :=
    propertyThreeFinePullbackShading_cubical outer.cover outer.refined
      outerCandidate outer.refined_cubical scaleFactor hscaleFactor
      hrhoAligned
  have hcandidateSub : PaperIsSubshading candidate
      fineReentry.normalization.croppedRefined :=
    ambientPropertyThreeCommonHull_subshading outer outerCandidate
  have hcandidateCubical : WZ1PaperIsCubicalShading candidate :=
    ambientPropertyThreeCommonHull_cubical outer outerCandidate
      fineReentry.normalization.cropped_cubical hpullbackCubical
  have hpullbackSubset : pullback.union ⊆ outerCandidate.union :=
    propertyThreeFinePullbackShading_union_subset outer.cover outer.refined
      outerCandidate houterCubical
  have hpullbackCoarse : pullback.union ⊆ coarseCandidate.union := by
    intro point hpoint
    exact houterUnion ▸ hpullbackSubset hpoint
  have hcandidateUnion : candidate.union = pullback.union :=
    ambientPropertyThreeCommonHull_union outer outerCandidate
  have hcandidateVariation : ∀ first ∈ candidate.union,
      ∀ second ∈ candidate.union, dist first second ≤ spatialScale →
        dist (planeMap first) (planeMap second) ≤ variationScale := by
    intro first hfirst second hsecond hdistance
    apply hcoarseVariation first
      (hpullbackCoarse (hcandidateUnion ▸ hfirst)) second
      (hpullbackCoarse (hcandidateUnion ▸ hsecond)) hdistance
  have hcandidateInterval : PureWZ2IntervalCoveringAt candidate planeMap
      queryScale resolutionScale windowScale constant := by
    intro point center
    have hpointPullback : (point : Point3) ∈ pullback.union :=
      hcandidateUnion ▸ point.property
    have hpointCoarse : (point : Point3) ∈ coarseCandidate.union :=
      hpullbackCoarse hpointPullback
    have hcover := hcoarseInterval ⟨point, hpointCoarse⟩ center
    have hset :
        scalarProjection (planeMap point)
              (candidate.union ∩ Metric.closedBall (point : Point3)
                (Real.sqrt queryScale)) ∩
            Metric.closedBall center (windowScale : ℝ) ⊆
          scalarProjection (planeMap point)
              (coarseCandidate.union ∩ Metric.closedBall (point : Point3)
                (Real.sqrt queryScale)) ∩
            Metric.closedBall center (windowScale : ℝ) := by
      rintro value ⟨⟨other, hother, rfl⟩, hvalue⟩
      exact ⟨⟨other, ⟨hpullbackCoarse (hcandidateUnion ▸ hother.1),
        hother.2⟩, rfl⟩, hvalue⟩
    have hmono :
        (Metric.externalCoveringNumber resolutionScale
          (scalarProjection (planeMap point)
                (candidate.union ∩ Metric.closedBall (point : Point3)
                  (Real.sqrt queryScale)) ∩
              Metric.closedBall center (windowScale : ℝ)) : ENNReal) ≤
          (Metric.externalCoveringNumber resolutionScale
            (scalarProjection (planeMap point)
                (coarseCandidate.union ∩ Metric.closedBall (point : Point3)
                  (Real.sqrt queryScale)) ∩
              Metric.closedBall center (windowScale : ℝ)) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set hset
    exact hmono.trans hcover
  have hcoarseComparison :
      (coarseLeft * ancestorRetentionFactor⁻¹) *
          outer.croppedCoarseShading.mass ≤
        coarseRight * outerCandidate.mass := by
    calc
      (coarseLeft * ancestorRetentionFactor⁻¹) *
          outer.croppedCoarseShading.mass =
        coarseLeft * (ancestorRetentionFactor⁻¹ *
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
      pullbackFactor * fineReentry.normalization.croppedRefined.mass =
          (coarseLeft * ancestorRetentionFactor⁻¹ *
            (proposition63OuterCoarsePullbackCost outer)⁻¹) *
          (wz2PaperPureRefinementFraction delta outerLogExponent *
            fineReentry.normalization.croppedRefined.mass) := by
        simp only [pullbackFactor]
        ring
      _ ≤ (coarseLeft * ancestorRetentionFactor⁻¹ *
            (proposition63OuterCoarsePullbackCost outer)⁻¹) *
          outer.refined.mass :=
        mul_le_mul_left' outer.retained_mass
          (coarseLeft * ancestorRetentionFactor⁻¹ *
            (proposition63OuterCoarsePullbackCost outer)⁻¹)
      _ ≤ coarseRight * pullback.mass := by
        simpa only [pullback, proposition63OuterCoarsePullbackCost]
          using hpullbackMass
  have hpullbackCommonMass : pullback.mass ≤ candidate.mass := by
    calc
      pullback.mass =
          (ambientPropertyThreePullback outer outerCandidate).mass := by
        rw [ambientPropertyThreePullback_mass]
      _ ≤ candidate.mass :=
        paperCommonSpatialHull_mass_lower
          (ambientPropertyThreePullback_subshading outer outerCandidate)
  have hcandidateMass : pullbackFactor *
        fineReentry.normalization.croppedRefined.mass ≤
      coarseRight * candidate.mass :=
    hnormalizedMass.trans (mul_le_mul_left' hpullbackCommonMass coarseRight)
  have hrootMass :
      (pullbackFactor *
          ((73 / 100 : ENNReal) * fineReentry.normalizationWeight)) *
          current.mass ≤
        (coarseRight * fineReentry.regularized.regularizationLoss) *
          candidate.mass := by
    calc
      (pullbackFactor *
          ((73 / 100 : ENNReal) * fineReentry.normalizationWeight)) *
          current.mass =
        pullbackFactor *
          (((73 / 100 : ENNReal) * fineReentry.normalizationWeight) *
            current.mass) := by ring
      _ ≤ pullbackFactor *
          (fineReentry.regularized.regularizationLoss *
            fineReentry.normalization.croppedRefined.mass) :=
        mul_le_mul_left' fineReentry.reentryMassRetention pullbackFactor
      _ = fineReentry.regularized.regularizationLoss *
          (pullbackFactor *
            fineReentry.normalization.croppedRefined.mass) := by ring
      _ ≤ fineReentry.regularized.regularizationLoss *
          (coarseRight * candidate.mass) :=
        mul_le_mul_left' hcandidateMass
          fineReentry.regularized.regularizationLoss
      _ = (coarseRight * fineReentry.regularized.regularizationLoss) *
          candidate.mass := by ring
  simpa only [proposition63DependentFinePullbackLeft,
    proposition63DependentFinePullbackRight, pullbackFactor] using
    fineReentry.candidate_joint_interval candidate planeMap resolutionScale
      windowScale constant
      (pullbackFactor *
        ((73 / 100 : ENNReal) * fineReentry.normalizationWeight))
      (coarseRight * fineReentry.regularized.regularizationLoss)
      hcandidateSub hcandidateCubical hcandidateVariation hcandidateInterval
      hrootMass

/-- Run the coarse full-grain/Fubini selection and then pull its whole-cell
output back through the outer sticky cover to the fixed fine family.  This is
the exact candidate shape required by the root finite iterator. -/
theorem Proposition63CurrentShadingReentryData.dependentFullGrainCandidate
    {delta sigma initialInputLoss normalizationLoss reentryLoss outerLoss
      coarseInputLoss coarseNormalizationLoss coarseReentryLoss firstLoss
      secondLoss localScale sqrtScale spatialScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
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
      normalizationExponent)
    (coarseCurrent : WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (coarseReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := coarseReentryLoss) coarseNormalized coarseCurrent)
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
    (sourceLeftFactor sourceRightFactor : ENNReal)
    (coefficient : NNReal)
    (uniformPreparationLoss : ENNReal) (uniformCoverBudget : ℕ)
    (step : Proposition63UniformFullGrainStepData
      (firstLoss := firstLoss) (secondLoss := secondLoss)
      (queryScale := localScale) (sqrtScale := sqrtScale)
      coarseReentry planeMap sourceLeftFactor sourceRightFactor coefficient
      uniformPreparationLoss uniformCoverBudget)
    (hlocalPos : 0 < localScale) (hlocalSmall : localScale ≤ 1 / 4)
    (hsqrtEq : sqrtScale = Real.sqrt localScale)
    (hsqrtPos : 0 < sqrtScale)
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hlipschitz : LipschitzWith coefficient planeMap)
    (hcoverBudgetPos : 0 < uniformCoverBudget)
    (hvariationBudget :
      (coefficient : ℝ) * spatialScale ≤ variationScale)
    (constant : ENNReal)
    (hconstant : Kakeya.realRpowENN rho.1 (-secondLoss) ≤ constant)
    (hrhoSmall : rho.1 ≤ 1 / 12)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta) :
    let volumeFloor := Kakeya.realRpowENN rho.1 (secondLoss + 2)
    let coarseLeft :=
      proposition63UniformLineFactor volumeFloor sqrtScale hsqrtPos *
        (((1 : ENNReal) / 2) / (2 * (uniformCoverBudget : ENNReal))) *
        sourceLeftFactor
    let coarseRight := sourceRightFactor * (uniformPreparationLoss * 2)
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
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
            (next.union ∩ Metric.closedBall point
              (Real.sqrt localScale)))
          localScale (1 - sigma) constant) ∧
      proposition63DependentFinePullbackLeft fineReentry outer
          ancestorRetentionFactor coarseLeft * current.mass ≤
        proposition63DependentFinePullbackRight fineReentry coarseRight *
          next.mass := by
  dsimp only
  let volumeFloor := Kakeya.realRpowENN rho.1 (secondLoss + 2)
  let coarseLeft :=
    proposition63UniformLineFactor volumeFloor sqrtScale hsqrtPos *
      (((1 : ENNReal) / 2) / (2 * (uniformCoverBudget : ENNReal))) *
      sourceLeftFactor
  let coarseRight := sourceRightFactor * (uniformPreparationLoss * 2)
  rcases coarseReentry.lineHitCandidate_joint_one_scale_of_extremal_budget
      planeMap step.original step.prepared step.cells hlocalPos hlocalSmall
      hsqrtEq hsqrtPos step.plane_unit coefficient hcoefficientOne hlipschitz
      uniformCoverBudget hcoverBudgetPos step.cover_budget spatialScale
      variationScale hvariationBudget constant hconstant sourceLeftFactor
      sourceRightFactor uniformPreparationLoss step.preparation_budget
      step.incoming_mass hrhoSmall with
    ⟨coarseCandidate, hcoarseSub, hcoarseCubical, _hcoarseMultiplicity,
      hcoarseVariation, hcoarseAD, hcoarseMass⟩
  exact fineReentry.candidate_joint_one_scale_of_outer_coarse outer
    coarseNormalized coarseCurrent coarseCandidate ancestorEmbedding
    ancestor_tube_eq current_sub_outer ancestorRetentionFactor
    current_retained_mass planeMap constant coarseLeft coarseRight hcoarseSub
    hcoarseCubical hcoarseVariation hcoarseAD hcoarseMass scaleFactor
    hscaleFactor hrhoAligned

/-- All runtime-dependent data for one paper Lemma 4.11 step, together with
preselected bounds by the fixed left/right factors of the finite iterator. -/
structure Proposition63DependentFullGrainStepData
    {delta sigma initialInputLoss normalizationLoss reentryLoss outerLoss
      firstLoss secondLoss sqrtScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    (planeMap : Point3 → Point3)
    (coefficient : NNReal)
    (uniformPreparationLoss : ENNReal) (uniformCoverBudget : ℕ)
    (targetLeft targetRight : ENNReal) where
  coarseInputLoss : ℝ
  coarseNormalizationLoss : ℝ
  coarseReentryLoss : ℝ
  coarseSource : PureWZ2ExtremalConfiguration sigma coarseInputLoss rho.1
  coarseNormalized : PureWZ2CroppedCriticalNormalizationData
    (outputLoss := coarseNormalizationLoss) coarseSource
      normalizationExponent
  coarseCurrent : WZ1PaperTubeShading coarseNormalized.croppedFamily
  coarseReentry : Proposition63CurrentShadingReentryData
    (reentryLoss := coarseReentryLoss) coarseNormalized coarseCurrent
  ancestorEmbedding :
    Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card
  ancestor_tube_eq : ∀ index,
    coarseNormalized.croppedFamily.tube index =
      outer.coarse.tube (ancestorEmbedding index)
  current_sub_outer : ∀ index, coarseCurrent.carrier index ⊆
    outer.croppedCoarseShading.carrier (ancestorEmbedding index)
  ancestorRetentionFactor : ENNReal
  current_retained_mass :
    ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
      coarseCurrent.mass
  sourceLeftFactor : ENNReal
  sourceRightFactor : ENNReal
  coarseStep : Proposition63UniformFullGrainStepData
    (firstLoss := firstLoss) (secondLoss := secondLoss)
    (queryScale := rho.1) (sqrtScale := sqrtScale)
    coarseReentry planeMap sourceLeftFactor sourceRightFactor coefficient
    uniformPreparationLoss uniformCoverBudget
  scaleFactor : ℕ
  scaleFactor_pos : 0 < scaleFactor
  rho_aligned : rho.1 = (scaleFactor : ℝ) * delta
  left_budget : targetLeft ≤
    proposition63DependentFinePullbackLeft fineReentry outer
      ancestorRetentionFactor
      (proposition63UniformLineFactor
          (Kakeya.realRpowENN rho.1 (secondLoss + 2)) sqrtScale
          coarseStep.cells.scale_pos *
        (((1 : ENNReal) / 2) / (2 * (uniformCoverBudget : ENNReal))) *
        sourceLeftFactor)
  right_budget :
    proposition63DependentFinePullbackRight fineReentry
        (sourceRightFactor * (uniformPreparationLoss * 2)) ≤
      targetRight

/-- Standard paper-order producer for one packaged dependent full-grain step.
It runs the dependent LOW/HIGH dichotomy, CWA boundary preparation, and fresh
balancing on the actual normalized outer coarse family.  Only the final two
scalar comparisons and the Lemma 4.12 integer alignment remain external. -/
theorem proposition63_dependentFullGrainStep_of_dependentLowHigh
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss outerLoss
      coarseInputLoss coarseNormalizationLoss coarseReentryLoss innerLoss
      targetLoss middleLoss finalLoss epsilon₁ epsilon₃ lowScale : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {coarseSource : PureWZ2ExtremalConfiguration
      sigma coarseInputLoss rho.1}
    (coarseNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := coarseNormalizationLoss) coarseSource
      normalizationExponent)
    (coarseCurrent : WZ1PaperTubeShading coarseNormalized.croppedFamily)
    (coarseReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := coarseReentryLoss) coarseNormalized coarseCurrent)
    (ancestorEmbedding :
      Fin coarseNormalized.croppedFamily.card ↪ Fin outer.coarse.card)
    (ancestor_tube_eq : ∀ index,
      coarseNormalized.croppedFamily.tube index =
        outer.coarse.tube (ancestorEmbedding index))
    (current_sub_outer : ∀ index, coarseCurrent.carrier index ⊆
      outer.croppedCoarseShading.carrier (ancestorEmbedding index))
    (ancestorRetentionFactor : ENNReal)
    (ancestorRetentionFactor_pos : 0 < ancestorRetentionFactor)
    (ancestorRetentionFactor_ne_top : ancestorRetentionFactor ≠ ⊤)
    (current_retained_mass :
      ancestorRetentionFactor⁻¹ * outer.croppedCoarseShading.mass ≤
        coarseCurrent.mass)
    {tau : WZ2PaperRequestedScale rho.1}
    (dependent : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      (proposition63DependentCoarseReentryOfCurrent outer coarseNormalized
        coarseCurrent coarseReentry ancestorEmbedding ancestor_tube_eq
        current_sub_outer ancestorRetentionFactor
        ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
        current_retained_mass) tau)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := dependent.ambientRefined)
      (tau := tau.1) epsilon₁ epsilon₃)
    (planeMap : Point3 → Point3)
    (coefficient : NNReal) (incidenceBound : ℝ)
    (uniformPreparationLoss : ENNReal)
    (uniformCoverBudget : ℕ)
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneUnit : ∀ point ∈ (dependent.commonPropertyThree propP).union,
      ‖planeMap point‖ = 1)
    (hplaneIncidence : ∀ index point,
      ∀ hpoint : point ∈ propP.propertyOne.carrier index,
        |@Inner.inner ℝ Point3 _
          (coarseReentry.normalization.croppedFamily.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hreentryTarget : coarseReentry.reentryNormalizationLoss ≤ targetLoss)
    (htargetLoss : 0 < targetLoss)
    (hrhoOne : rho.1 < 1)
    (hmassSlack : proposition63DependentPropertyThreeMassLoss
        rho.1 innerLogExponent * Kakeya.realRpowENN rho.1 targetLoss ≤
      Kakeya.realRpowENN rho.1 coarseReentry.reentryNormalizationLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hlowScale : 0 < lowScale) (hlowScaleSmall : lowScale ≤ 1 / 10000)
    (hlowConstant : Kakeya.realRpowENN lowScale (-1) ≤
      Kakeya.realRpowENN rho.1 (-targetLoss))
    (htauSqrt : tau.1 = Real.sqrt rho.1)
    (htauSmall : tau.1 ≤ 1 / 12)
    (hrhoSmall : rho.1 ≤ 1 / 1000)
    (hrhoTau : rho.1 ≤ tau.1)
    (htauSq : tau.1 ^ 2 ≤ 4 * rho.1)
    (htauOne : tau.1 ≤ 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hrhoLog : rho.1 ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hpropertyThreeFull :
      ∀ index point, point ∈ propP.propertyThree.carrier index →
        Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
            ENNReal.ofReal tau.1 ≤
          volume (propP.propertyThree.carrier index ∩
            Metric.closedBall point tau.1))
    (haxis : 4 * (6 * rho.1) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          (((5832 * Real.rpow rho.1 (sigma - outerLoss) *
              Real.rpow tau.1 (3 - sigma - 2 * innerLoss)) /
              (Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
                tau.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth rho.1 tau.1 incidenceBound
              coefficient /
              rho.1 + 2)) ≤
        C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
    (heffectiveOne : (1 : ENNReal) ≤
      C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma))
    (heffectiveTop : C *
      Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma) ≠ ⊤)
    (hhighConstant : 10 *
        (C * Kakeya.realRpowENN (tau.1 / rho.1) (1 - sigma)) ≤
      Kakeya.realRpowENN rho.1 (-targetLoss))
    (hfirstMiddle : targetLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (hmultiplicitySlack :
      (((Nat.log 2 coarseReentry.normalization.croppedFamily.card + 1 : ℕ) :
          ENNReal) * Kakeya.realRpowENN rho.1 middleLoss) ≤
        Kakeya.realRpowENN rho.1 targetLoss)
    (hrhoSmall24 : rho.1 ≤ 1 / 24)
    (hperiodicScale : 50 * rho.1 ≤ tau.1)
    (htauPos : 0 < tau.1)
    (hboundaryScalar :
      2 * 24000000 *
          (Kakeya.realRpowENN rho.1 (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (rho.1 / tau.1)) <
        Kakeya.realRpowENN rho.1 middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (hbalancingSlack : proposition63FreshBalancingEnvelope rho.1 *
        Kakeya.realRpowENN rho.1 finalLoss ≤
      Kakeya.realRpowENN rho.1 middleLoss)
    (cover_budget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * (coefficient : ℝ)) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN rho.1 (-finalLoss) *
              Kakeya.realRpowENN (1 / rho.1) (1 - sigma))) ≤
        (uniformCoverBudget : ENNReal))
    (preparation_budget : proposition63UniformPreparationLoss
        coarseReentry.normalization.croppedFamily ≤ uniformPreparationLoss)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
    (targetLeft targetRight : ENNReal)
    (left_budget : targetLeft ≤
      proposition63DependentFinePullbackLeft fineReentry outer
        ancestorRetentionFactor
        (proposition63UniformLineFactor
            (Kakeya.realRpowENN rho.1 (finalLoss + 2)) tau.1 htauPos *
          (((1 : ENNReal) / 2) / (2 * (uniformCoverBudget : ENNReal))) *
          ((proposition63DependentPropertyThreeMassLoss
              rho.1 innerLogExponent)⁻¹ *
            ((73 / 100 : ENNReal) *
              coarseReentry.normalizationWeight))))
    (right_budget : proposition63DependentFinePullbackRight fineReentry
        (coarseReentry.regularized.regularizationLoss *
          (uniformPreparationLoss * 2)) ≤ targetRight) :
    Nonempty (Proposition63DependentFullGrainStepData
      (firstLoss := targetLoss) (secondLoss := finalLoss)
      (sqrtScale := tau.1) fineReentry outer planeMap coefficient
      uniformPreparationLoss uniformCoverBudget targetLeft targetRight) := by
  let sourceLeftFactor : ENNReal :=
    (proposition63DependentPropertyThreeMassLoss
      rho.1 innerLogExponent)⁻¹ *
      ((73 / 100 : ENNReal) * coarseReentry.normalizationWeight)
  let sourceRightFactor : ENNReal :=
    coarseReentry.regularized.regularizationLoss
  let canonicalStep := Classical.choice <|
    proposition63_uniformFullGrainStep_of_dependentLowHigh outer
      coarseNormalized coarseCurrent coarseReentry ancestorEmbedding
      ancestor_tube_eq current_sub_outer ancestorRetentionFactor
      ancestorRetentionFactor_pos ancestorRetentionFactor_ne_top
      current_retained_mass dependent propP planeMap coefficient
      incidenceBound uniformCoverBudget hplaneLipschitz hplaneUnit
      hplaneIncidence
      hreentryTarget htargetLoss hrhoOne
      hmassSlack hsigma hsigmaOne hlowScale hlowScaleSmall hlowConstant
      htauSqrt htauSmall hrhoSmall hrhoTau htauSq htauOne
      hepsilon₁ hepsilon₃ hepsilonSum logScale hrhoLog hlog
      hpropertyThreeFull haxis C harithmetic heffectiveOne heffectiveTop
      hhighConstant hfirstMiddle hmiddleLoss hmultiplicitySlack hrhoSmall24
      hperiodicScale htauPos hboundaryScalar hmiddleFinal hfinalLoss
      hbalancingSlack cover_budget
  let coarseStep := canonicalStep.monoPreparationLoss preparation_budget
  exact ⟨{
    coarseInputLoss := coarseInputLoss
    coarseNormalizationLoss := coarseNormalizationLoss
    coarseReentryLoss := coarseReentryLoss
    coarseSource := coarseSource
    coarseNormalized := coarseNormalized
    coarseCurrent := coarseCurrent
    coarseReentry := coarseReentry
    ancestorEmbedding := ancestorEmbedding
    ancestor_tube_eq := ancestor_tube_eq
    current_sub_outer := current_sub_outer
    ancestorRetentionFactor := ancestorRetentionFactor
    current_retained_mass := current_retained_mass
    sourceLeftFactor := sourceLeftFactor
    sourceRightFactor := sourceRightFactor
    coarseStep := coarseStep
    scaleFactor := scaleFactor
    scaleFactor_pos := hscaleFactor
    rho_aligned := hrhoAligned
    left_budget := by
      simpa only [sourceLeftFactor, coarseStep, canonicalStep] using left_budget
    right_budget := by
      simpa only [sourceRightFactor] using right_budget
  }⟩

/-- Convert one packaged dependent coarse step into the fixed-family candidate
contract consumed by the root iterator. -/
theorem Proposition63DependentFullGrainStepData.toFineCandidate
    {delta sigma initialInputLoss normalizationLoss reentryLoss outerLoss
      firstLoss secondLoss sqrtScale spatialScale variationScale : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    {fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current}
    {rho : WZ2PaperRequestedScale delta}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent}
    {planeMap : Point3 → Point3}
    {coefficient : NNReal}
    {uniformPreparationLoss : ENNReal} {uniformCoverBudget : ℕ}
    {targetLeft targetRight : ENNReal}
    (data : Proposition63DependentFullGrainStepData
      (firstLoss := firstLoss) (secondLoss := secondLoss)
      (sqrtScale := sqrtScale) fineReentry outer planeMap coefficient
      uniformPreparationLoss uniformCoverBudget targetLeft targetRight)
    (hlocalPos : 0 < rho.1) (hlocalSmall : rho.1 ≤ 1 / 4)
    (hsqrtEq : sqrtScale = Real.sqrt rho.1)
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (hlipschitz : LipschitzWith coefficient planeMap)
    (hcoverBudgetPos : 0 < uniformCoverBudget)
    (hvariationBudget :
      (coefficient : ℝ) * spatialScale ≤ variationScale)
    (constant : ENNReal)
    (hconstant : Kakeya.realRpowENN rho.1 (-secondLoss) ≤ constant)
    (hrhoSmall : rho.1 ≤ 1 / 12) :
    ∃ next : WZ1PaperTubeShading initialNormalized.croppedFamily,
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
            (next.union ∩ Metric.closedBall point (Real.sqrt rho.1)))
          rho.1 (1 - sigma) constant) ∧
      targetLeft * current.mass ≤ targetRight * next.mass := by
  rcases fineReentry.dependentFullGrainCandidate outer data.coarseNormalized
      data.coarseCurrent data.coarseReentry data.ancestorEmbedding
      data.ancestor_tube_eq data.current_sub_outer
      data.ancestorRetentionFactor data.current_retained_mass planeMap
      data.sourceLeftFactor data.sourceRightFactor coefficient
      uniformPreparationLoss uniformCoverBudget data.coarseStep hlocalPos
      hlocalSmall hsqrtEq data.coarseStep.cells.scale_pos hcoefficientOne
      hlipschitz hcoverBudgetPos hvariationBudget constant hconstant hrhoSmall
      data.scaleFactor data.scaleFactor_pos data.rho_aligned with
    ⟨next, hsub, hcubical, hmultiplicity, hvariation, hlocalAD, hmass⟩
  refine ⟨next, hsub, hcubical, hmultiplicity, hvariation, hlocalAD, ?_⟩
  calc
    targetLeft * current.mass ≤
        proposition63DependentFinePullbackLeft fineReentry outer
            data.ancestorRetentionFactor
            (proposition63UniformLineFactor
                (Kakeya.realRpowENN rho.1 (secondLoss + 2)) sqrtScale
                data.coarseStep.cells.scale_pos *
              (((1 : ENNReal) / 2) /
                (2 * (uniformCoverBudget : ENNReal))) *
              data.sourceLeftFactor) * current.mass :=
      mul_le_mul_right' data.left_budget current.mass
    _ ≤ proposition63DependentFinePullbackRight fineReentry
          (data.sourceRightFactor * (uniformPreparationLoss * 2)) *
        next.mass := hmass
    _ ≤ targetRight * next.mass :=
      mul_le_mul_right' data.right_budget next.mass

/-- Root finite iteration driven by genuine dependent two-cover full-grain
steps.  Each runtime coarse candidate is pulled back through its own outer
sticky cover before the iterator advances, so every output remains a shading
of the fixed root family. -/
theorem proposition63_finite_dependent_fullGrain_iteration_from_root
    {sigma inputLoss normalizationLoss densityLoss currentLoss weightLoss
      reentryLoss stickyLoss firstLoss secondLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent logExponent N : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent
        densityLoss)
    (planeMap : Point3 → Point3)
    (requested : Fin N → WZ2PaperRequestedScale delta)
    (queryScale sqrtScale spatialScale variationScale : ℕ → ℝ)
    (constant : ENNReal)
    (leftFactor rightFactor : ℕ → ENNReal)
    (uniformPreparationLoss : ℕ → ENNReal)
    (uniformCoverBudget : ℕ → ℕ)
    (parameters : Proposition63RootFiniteReentryParameters
      (currentLoss := currentLoss) (weightLoss := weightLoss)
      (reentryLoss := reentryLoss) (N := N) root leftFactor rightFactor)
    (coefficient : NNReal)
    (hcoefficientOne : 1 ≤ (coefficient : ℝ))
    (planeLipschitz : LipschitzWith coefficient planeMap)
    (variationBudget : ∀ index, index < N →
      (coefficient : ℝ) * spatialScale index ≤ variationScale index)
    (hSticky : ∀ reentrySource :
        PureWZ2ExtremalConfiguration sigma reentryLoss delta,
      ∀ reentryNormalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := parameters.reentryNormalizationLoss) reentrySource
          normalizationExponent,
      ∀ rho : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
        rho.1 ≤ Real.rpow delta stickyLoss →
        Nonempty (PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          reentryNormalized.croppedRefined rho logExponent))
    (requested_lower : ∀ index,
      Real.rpow delta (1 - stickyLoss) ≤ (requested index).1)
    (requested_upper : ∀ index,
      (requested index).1 ≤ Real.rpow delta stickyLoss)
    (query_eq : ∀ index (index_lt : index < N),
      queryScale index = (requested ⟨index, index_lt⟩).1)
    (query_small : ∀ index (index_lt : index < N),
      queryScale index ≤ 1 / 4)
    (sqrt_eq : ∀ index (index_lt : index < N),
      sqrtScale index = Real.sqrt (queryScale index))
    (coverBudget_pos : ∀ index, index < N →
      0 < uniformCoverBudget index)
    (target_constant : ∀ index (index_lt : index < N),
      Kakeya.realRpowENN (queryScale index) (-secondLoss) ≤ constant)
    (rho_small : ∀ index (index_lt : index < N),
      queryScale index ≤ 1 / 12)
    (stepData : ∀ index : ℕ, ∀ index_lt : index < N,
      ∀ current : WZ1PaperTubeShading root.normalization.croppedFamily,
        ∀ current_sub : PaperIsSubshading current
          root.normalization.croppedRefined,
        ∀ current_cubical : WZ1PaperIsCubicalShading current,
        ∀ current_multiplicity : ∀ point ∈ current.union,
          current.pointMultiplicity point =
            root.normalization.croppedRefined.pointMultiplicity point,
        ∀ current_mass_ledger :
          (∏ prior ∈ Finset.range index, leftFactor prior) *
              root.normalization.croppedRefined.mass ≤
            (∏ prior ∈ Finset.range index, rightFactor prior) * current.mass,
        ∀ current_mass_pos : 0 < current.mass,
        ∀ data : Proposition63CurrentShadingReentryData
          (reentryLoss := reentryLoss) root.normalization current,
        data.normalizationWeight =
          proposition63CanonicalReentryWeight delta weightLoss →
        data.levelCount =
          proposition63CanonicalNearbyLevelCount normalizationLoss →
        ∀ sticky : PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          data.normalization.croppedRefined
          (requested ⟨index, index_lt⟩) logExponent,
          Nonempty (Proposition63DependentFullGrainStepData
            (firstLoss := firstLoss) (secondLoss := secondLoss)
            (sqrtScale := sqrtScale index) data sticky planeMap coefficient
            (uniformPreparationLoss index) (uniformCoverBudget index)
            (leftFactor index) (rightFactor index))) :
    ∃ final : WZ1PaperTubeShading root.normalization.croppedFamily,
      PaperIsSubshading final root.normalization.croppedRefined ∧
      WZ1PaperIsCubicalShading final ∧
      (∀ point ∈ final.union,
        final.pointMultiplicity point =
          root.normalization.croppedRefined.pointMultiplicity point) ∧
      (∀ index, index < N → ∀ first ∈ final.union,
        ∀ second ∈ final.union, dist first second ≤ spatialScale index →
          dist (planeMap first) (planeMap second) ≤ variationScale index) ∧
      (∀ index, index < N → ∀ point ∈ final.union,
        IsADSet1
          (scalarProjection (planeMap point)
            (final.union ∩ Metric.closedBall point
              (Real.sqrt (queryScale index))))
          (queryScale index) (1 - sigma) constant) ∧
      (∏ index ∈ Finset.range N, leftFactor index) *
          root.normalization.croppedRefined.mass ≤
        (∏ index ∈ Finset.range N, rightFactor index) * final.mass ∧
      0 < final.mass := by
  apply joint_finite_variation_local_ad_iteration_of_mass_pos (sigma := sigma)
    root.normalization.croppedRefined root.normalization.cropped_cubical
      (cropped_extremal_shading_mass_pos
        root.normalization.final_extremal root.normalization.line_class
        parameters.delta_small)
      planeMap N spatialScale queryScale variationScale constant
      leftFactor rightFactor parameters.leftFactor_pos
  intro index index_lt current current_sub current_cubical
    current_multiplicity current_mass_ledger current_mass_pos
  rcases parameters.prepareWithCanonicalWeight index index_lt current
      current_sub current_cubical current_multiplicity current_mass_ledger
      current_mass_pos with
    ⟨data, normalization_weight, levelCount_eq, hnormalizationLoss⟩
  have hStickyData :
      ∀ reentrySource : PureWZ2ExtremalConfiguration sigma reentryLoss delta,
        ∀ reentryNormalized : PureWZ2CroppedCriticalNormalizationData
          (outputLoss := data.reentryNormalizationLoss) reentrySource
            normalizationExponent,
          ∀ rho : WZ2PaperRequestedScale delta,
            Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
            rho.1 ≤ Real.rpow delta stickyLoss →
              Nonempty (PureWZ2PropStickyData
                (sigma := sigma) (outputLoss := stickyLoss)
                reentryNormalized.croppedRefined rho logExponent) := by
    rw [hnormalizationLoss]
    exact hSticky
  rcases proposition63CurrentShadingReentry_sticky data hStickyData
      (requested ⟨index, index_lt⟩)
      (requested_lower ⟨index, index_lt⟩)
      (requested_upper ⟨index, index_lt⟩) with ⟨sticky⟩
  let step := Classical.choice <|
    stepData index index_lt current current_sub current_cubical
      current_multiplicity current_mass_ledger current_mass_pos data
      normalization_weight levelCount_eq sticky
  have hquerySmallRequested :
      (requested ⟨index, index_lt⟩).1 ≤ 1 / 4 := by
    rw [← query_eq index index_lt]
    exact query_small index index_lt
  have hsqrtRequested :
      sqrtScale index = Real.sqrt (requested ⟨index, index_lt⟩).1 := by
    rw [← query_eq index index_lt]
    exact sqrt_eq index index_lt
  have hconstantRequested :
      Kakeya.realRpowENN (requested ⟨index, index_lt⟩).1
          (-secondLoss) ≤ constant := by
    rw [← query_eq index index_lt]
    exact target_constant index index_lt
  have hrhoSmallRequested :
      (requested ⟨index, index_lt⟩).1 ≤ 1 / 12 := by
    rw [← query_eq index index_lt]
    exact rho_small index index_lt
  simpa only [query_eq index index_lt] using step.toFineCandidate
    (source.extremal.delta_pos.trans_le
      (requested ⟨index, index_lt⟩).2.1)
    hquerySmallRequested hsqrtRequested hcoefficientOne
    planeLipschitz (coverBudget_pos index index_lt)
    (variationBudget index index_lt) constant
    hconstantRequested hrhoSmallRequested

end Kakeya.Assouad.PureWZ2

end
