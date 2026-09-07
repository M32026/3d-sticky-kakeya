import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallNestedPointCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScalePlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichBoundarySlackSchedule

/-!
# Restore the first call-3 point cover to its call-2 ancestor

This file contains the family-generic transport needed by the four-call
assembly.  It zero-extends the first point cover through the call2-to-call3
re-entry and immediately restores extremality relative to the call-2 rich
terminal ambient.  Every scalar loss used by the restoration remains an
explicit hypothesis.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The concrete call2-ancestor witness retained alongside the completed
nested point cover.  In addition to the exact ancestor union and retained
factor, this package records that the nested chain starts at that very
restored shading and exposes both mass-retention receipts. -/
structure Proposition63AncestorRestoredNestedPointCoverData
    {delta sigma inputLoss normalizationLoss restoredFirstLoss reentryLoss
      sqrtStickyLoss secondLoss finalLoss tauScale sqrtScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily)
    (planeMap : Point3 → Point3) (tauConstant sqrtConstant : ENNReal)
    (nestedWeightLoss : ℝ) (originalUnion : Set Point3)
    (expectedRestoredFactor : ENNReal) where
  restoredFirst : Proposition63LiftedPointCoverData
    (outputLoss := restoredFirstLoss) (queryScale := delta)
    (spatialRadius := tauScale) initialNormalized current planeMap tauConstant
  restored_union : restoredFirst.state.shading.union = originalUnion
  restored_factor : restoredFirst.retainedFactor = expectedRestoredFactor
  nested : Proposition63NestedPointCoverData
    (firstLoss := restoredFirstLoss) (reentryLoss := reentryLoss)
    (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
    (finalLoss := finalLoss) (queryScale := delta) (tauScale := tauScale)
    (sqrtScale := sqrtScale) initialNormalized planeMap tauConstant sqrtConstant
  nested_current_eq : nested.current = restoredFirst.state.shading
  nestedCanonicalWeight : nested.reentry.normalizationWeight =
    proposition63CanonicalReentryWeight delta nestedWeightLoss
  nestedCanonicalWeightUpper : nested.reentry.weightUpper =
    (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
      Kakeya.realRpowENN delta 2
  nestedCanonicalLevel : nested.reentry.levelCount =
    proposition63CanonicalNearbyLevelCount normalizationLoss
  nested_first_retained :
    nested.firstRetainedFactor * nested.current.mass ≤ nested.first.shading.mass
  nestedFirstRetainedFactor : nested.firstRetainedFactor = 1
  nested_second_retained : nested.secondRetainedFactor *
    nested.reentry.normalization.croppedRefined.mass ≤ nested.second.shading.mass
  nestedSecondRetainedFactor : nested.secondRetainedFactor =
    (81 / 400 : ENNReal) *
      (((Nat.log 2 nested.sqrtSticky.selected.family.card + 1 : ℕ) :
        ENNReal))⁻¹ * wz2PaperPureRefinementFraction delta 61
  nestedPreparationLoss : nested.prepared.preparationLoss ≤
    proposition63UniformPreparationLoss initialNormalized.croppedFamily

/-- Replace the public fourth call by its unweakened internal kernel and expose
the preceding third and second calls as the first two calls of the resulting
three-call schedule.  The public monotonicity transport preserves the source
loss, so the call-boundary certificates are inherited from the four-call
schedule. -/
noncomputable def proposition63_rich_three_call_schedule_of_four_call_kernel
    {sigma publicLoss discreteBudget tailBudget sigmaBudget : ℝ}
    (schedule : Proposition63RichFourCallScheduleData sigma publicLoss)
    (kernel : Proposition63RichInternalKernelScheduleData sigma publicLoss
      discreteBudget tailBudget sigmaBudget schedule.fourth) :
    Proposition63RichThreeCallScheduleData sigma kernel.internalLoss where
  third := kernel.internalSchedule
  secondOutputLoss := schedule.thirdOutputLoss
  secondOutputLoss_eq := by
    rw [schedule.thirdOutputLoss_eq]
    have hsource := congrArg
      Proposition63RichStickyKernelScheduleData.sourceLoss kernel.public_eq
    have hsource' : schedule.fourth.sourceLoss =
        kernel.internalSchedule.sourceLoss := by
      simpa only [Proposition63RichStickyKernelScheduleData.mono_loss] using hsource
    exact congrArg (fun loss : ℝ => loss / 16) hsource'
  secondOutputLoss_pos := schedule.thirdOutputLoss_pos
  secondOutputLoss_lt_thirdSource := by
    have hsource := congrArg
      Proposition63RichStickyKernelScheduleData.sourceLoss kernel.public_eq
    simpa only [Proposition63RichStickyKernelScheduleData.mono_loss] using
      schedule.thirdOutputLoss_lt_fourthSource.trans_le hsource.le
  second := schedule.third
  firstOutputLoss := schedule.secondOutputLoss
  firstOutputLoss_eq := schedule.secondOutputLoss_eq
  firstOutputLoss_pos := schedule.secondOutputLoss_pos
  firstOutputLoss_lt_secondSource :=
    schedule.secondOutputLoss_lt_thirdSource
  first := schedule.second

/-- Pull the first point cover on the call-3 ambient back through the
call2-to-call3 re-entry.  The retained factor is the literal composition of
the re-entry trace, the call-3 rich refinement, and the first cover. -/
theorem proposition63_four_call_restore_first_to_call2_ancestor
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss firstLoss outputLoss queryScale
      spatialRadius : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (planeMap : Point3 → Point3) (constant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := queryScale)
      (spatialRadius := spatialRadius) targetReentry.normalization
      (extendShading target.data.selected target.data.refined) planeMap
      constant)
    (parentLoss : ℝ)
    (hdeltaLtOne : delta < 1)
    (hnormalizationParent : outerNormalizationLoss ≤ parentLoss)
    (hparentRetention :
      Kakeya.realRpowENN delta parentLoss ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta outerNormalizationLoss)
    (hparentOutput : parentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        (targetReentry.regularized.regularizationLoss⁻¹ *
          (((73 / 100 : ENNReal) * targetReentry.normalizationWeight) *
            (wz2PaperPureRefinementFraction delta 61 *
              first.retainedFactor))) 1 *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta parentLoss) :
    ∃ result : Proposition63LiftedPointCoverData
        (outputLoss := outputLoss) (queryScale := queryScale)
        (spatialRadius := spatialRadius) outerReentry.toNormalizationData
        (extendShading outer.data.selected outer.data.refined) planeMap
        constant,
      result.state.shading.union = first.state.shading.union ∧
        result.retainedFactor =
          targetReentry.regularized.regularizationLoss⁻¹ *
            (((73 / 100 : ENNReal) * targetReentry.normalizationWeight) *
              (wz2PaperPureRefinementFraction delta 61 *
                first.retainedFactor)) := by
  let parent : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily :=
    extendShading outer.data.selected outer.data.refined
  let candidate : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily :=
    targetReentry.extendCandidate first.state.shading
  let retainedFactor : ENNReal :=
    targetReentry.regularized.regularizationLoss⁻¹ *
      (((73 / 100 : ENNReal) * targetReentry.normalizationWeight) *
        (wz2PaperPureRefinementFraction delta 61 * first.retainedFactor))
  have firstSubNormalized : PaperIsSubshading first.state.shading
      targetReentry.normalization.croppedRefined := by
    intro index point hpoint
    exact extendShading_subshading target.data.selected
      target.data.subshading index (first.state.subshading index hpoint)
  have candidateSub : PaperIsSubshading candidate parent :=
    targetReentry.extendCandidate_subshading firstSubNormalized
  have candidateCubical : WZ1PaperIsCubicalShading candidate :=
    extendShading_cubical targetReentry.regularized.selected
      first.state.extremal.cubical
  have candidateUnion : candidate.union = first.state.shading.union :=
    targetReentry.extendCandidate_union first.state.shading
  have candidateMass : candidate.mass = first.state.shading.mass :=
    targetReentry.extendCandidate_mass first.state.shading
  have candidateCover : PureWZ2PointCenteredCoveringAt candidate planeMap
      (Real.toNNReal queryScale) spatialRadius constant := by
    intro point
    have hpoint : (point : Point3) ∈ first.state.shading.union := by
      rw [← candidateUnion]
      exact point.property
    simpa only [candidateUnion] using first.cover ⟨point, hpoint⟩
  have hregularizationPos :
      0 < targetReentry.regularized.regularizationLoss := by
    rw [targetReentry.regularized.regularizationLoss_eq]
    positivity
  have hregularizationTop :
      targetReentry.regularized.regularizationLoss ≠ ⊤ := by
    rw [targetReentry.regularized.regularizationLoss_eq]
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  have retainedPos : 0 < retainedFactor := by
    dsimp only [retainedFactor]
    apply ENNReal.mul_pos
    · exact ENNReal.inv_ne_zero.mpr hregularizationTop
    · exact (ENNReal.mul_pos
        (ENNReal.mul_pos (by norm_num : (73 / 100 : ENNReal) ≠ 0)
          targetReentry.normalization_weight_ne_zero).ne'
        (ENNReal.mul_pos
          (pure_refinement_fraction_pos_ne_top
            targetReentry.reentry_extremal.delta_pos
            hdeltaLtOne 61).1.ne'
          first.retained_factor_pos.ne').ne').ne'
  have retainedTop : retainedFactor ≠ ⊤ := by
    dsimp only [retainedFactor]
    apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr hregularizationPos.ne'
    · apply ENNReal.mul_ne_top
      · exact ENNReal.mul_ne_top
          (ENNReal.div_ne_top (by norm_num) (by norm_num))
          targetReentry.normalization_weight_ne_top
      · exact ENNReal.mul_ne_top
          (pure_refinement_fraction_pos_ne_top
            targetReentry.reentry_extremal.delta_pos
            hdeltaLtOne 61).2
          first.retained_factor_ne_top
  have retained : retainedFactor * parent.mass ≤ candidate.mass := by
    have hscaledReentry := mul_le_mul_right
      targetReentry.reentryMassRetention
      targetReentry.regularized.regularizationLoss⁻¹
    calc
      retainedFactor * parent.mass =
          (wz2PaperPureRefinementFraction delta 61 * first.retainedFactor) *
            (targetReentry.regularized.regularizationLoss⁻¹ *
              (((73 / 100 : ENNReal) *
                targetReentry.normalizationWeight) * parent.mass)) := by
        dsimp only [retainedFactor, parent]
        ring
      _ ≤ (wz2PaperPureRefinementFraction delta 61 * first.retainedFactor) *
          targetReentry.normalization.croppedRefined.mass := by
        gcongr
        calc
          targetReentry.regularized.regularizationLoss⁻¹ *
                (((73 / 100 : ENNReal) *
                  targetReentry.normalizationWeight) * parent.mass) ≤
              targetReentry.regularized.regularizationLoss⁻¹ *
                (targetReentry.regularized.regularizationLoss *
                  targetReentry.normalization.croppedRefined.mass) :=
            hscaledReentry
          _ = targetReentry.normalization.croppedRefined.mass := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel
              hregularizationPos.ne' hregularizationTop, one_mul]
      _ = first.retainedFactor *
          (wz2PaperPureRefinementFraction delta 61 *
            targetReentry.normalization.croppedRefined.mass) := by ring
      _ ≤ first.retainedFactor * target.data.refined.mass := by
        exact mul_le_mul_right target.total_mass_retention _
      _ = first.retainedFactor *
          (extendShading target.data.selected target.data.refined).mass := by
        rw [extendShading_mass]
      _ ≤ first.state.shading.mass := first.retained
      _ = candidate.mass := candidateMass.symm
  have parentExtremal : WZ2PaperCroppedIsExtremal sigma parentLoss
      outerReentry.toNormalizationData.croppedFamily parent :=
    sticky_zero_extension_extremal
      outerReentry.toNormalizationData.final_extremal outer.data
      hnormalizationParent hparentRetention
  have parentCWA : WZ2PaperConvexWolffBound
      outerReentry.toNormalizationData.croppedFamily
      (Kakeya.realRpowENN delta (-parentLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := outerReentry.toNormalizationData.croppedRefined)
      (_shading2 := parent)
      outerReentry.toNormalizationData.cropped_top_level_cwa
      hnormalizationParent targetReentry.reentry_extremal.delta_pos
      targetReentry.reentry_extremal.delta_le_one
  rcases proposition63_point_cover_on_extremal_parent
      outerReentry.toNormalizationData parent parentExtremal parentCWA
      candidate candidateSub candidateCubical planeMap constant candidateCover
      retainedFactor retained retainedPos retainedTop hparentOutput houtputLoss
      (by simpa only [retainedFactor] using hrestore) with
    ⟨result, resultUnion, resultFactor⟩
  refine ⟨result, resultUnion.trans candidateUnion, ?_⟩
  exact resultFactor

/-- Density-lift variant of the call2 ancestor restoration.  Extremality of
the zero-extended call3 candidate comes from the cardinality-aware density
lift, rather than from charging its raw retained mass through Lemma 4.3.  The
raw three-stage mass factor is retained only in the output bookkeeping. -/
theorem proposition63_four_call_restore_first_to_call2_ancestor_of_density_lift
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss firstLoss outputLoss queryScale
      spatialRadius : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (planeMap : Point3 → Point3) (constant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := queryScale)
      (spatialRadius := spatialRadius) targetReentry.normalization
      (extendShading target.data.selected target.data.refined) planeMap
      constant)
    (parentLoss : ℝ)
    (hdeltaLtOne : delta < 1)
    (hnormalizationParent : outerNormalizationLoss ≤ parentLoss)
    (hparentRetention :
      Kakeya.realRpowENN delta parentLoss ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta outerNormalizationLoss)
    (hcurrentOutput : parentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hdensityLift :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper) *
          Kakeya.realRpowENN delta outputLoss ≤
        targetReentry.normalizationWeight *
          Kakeya.realRpowENN delta firstLoss) :
    ∃ result : Proposition63LiftedPointCoverData
        (outputLoss := outputLoss) (queryScale := queryScale)
        (spatialRadius := spatialRadius) outerReentry.toNormalizationData
        (extendShading outer.data.selected outer.data.refined) planeMap
        constant,
      result.state.shading.union = first.state.shading.union ∧
        result.retainedFactor =
          targetReentry.regularized.regularizationLoss⁻¹ *
            (((73 / 100 : ENNReal) * targetReentry.normalizationWeight) *
              (wz2PaperPureRefinementFraction delta 61 *
                first.retainedFactor)) := by
  let parent : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily :=
    extendShading outer.data.selected outer.data.refined
  let candidate : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily :=
    targetReentry.extendCandidate first.state.shading
  let nextShading := paperCommonSpatialHull parent candidate
  let retainedFactor : ENNReal :=
    targetReentry.regularized.regularizationLoss⁻¹ *
      (((73 / 100 : ENNReal) * targetReentry.normalizationWeight) *
        (wz2PaperPureRefinementFraction delta 61 * first.retainedFactor))
  have firstSubNormalized : PaperIsSubshading first.state.shading
      targetReentry.normalization.croppedRefined := by
    intro index point hpoint
    exact extendShading_subshading target.data.selected
      target.data.subshading index (first.state.subshading index hpoint)
  have candidateSub : PaperIsSubshading candidate parent :=
    targetReentry.extendCandidate_subshading firstSubNormalized
  have candidateCubical : WZ1PaperIsCubicalShading candidate :=
    extendShading_cubical targetReentry.regularized.selected
      first.state.extremal.cubical
  have candidateUnion : candidate.union = first.state.shading.union :=
    targetReentry.extendCandidate_union first.state.shading
  have candidateMass : candidate.mass = first.state.shading.mass :=
    targetReentry.extendCandidate_mass first.state.shading
  have candidateCover : PureWZ2PointCenteredCoveringAt candidate planeMap
      (Real.toNNReal queryScale) spatialRadius constant := by
    intro point
    have hpoint : (point : Point3) ∈ first.state.shading.union := by
      rw [← candidateUnion]
      exact point.property
    simpa only [candidateUnion] using first.cover ⟨point, hpoint⟩
  have parentExtremal : WZ2PaperCroppedIsExtremal sigma parentLoss
      outerReentry.toNormalizationData.croppedFamily parent :=
    sticky_zero_extension_extremal
      outerReentry.toNormalizationData.final_extremal outer.data
      hnormalizationParent hparentRetention
  have candidateExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      outerReentry.toNormalizationData.croppedFamily candidate :=
    targetReentry.extendCandidate_extremal parentExtremal firstSubNormalized
      first.state.extremal.cubical first.state.extremal hcurrentOutput
      houtputLoss hdensityLift
  have nextSub : PaperIsSubshading nextShading parent :=
    paperCommonSpatialHull_subshading _ _
  have nextCubical : WZ1PaperIsCubicalShading nextShading :=
    paperCommonSpatialHull_cubical parentExtremal.cubical candidateCubical
  have nextUnion : nextShading.union = candidate.union :=
    paperCommonSpatialHull_union candidateSub
  have nextMass : candidate.mass ≤ nextShading.mass :=
    paperCommonSpatialHull_mass_lower candidateSub
  have nextExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      outerReentry.toNormalizationData.croppedFamily nextShading :=
    { delta_pos := candidateExtremal.delta_pos
      delta_le_one := candidateExtremal.delta_le_one
      nonempty := candidateExtremal.nonempty
      cwa_nearby_scales := candidateExtremal.cwa_nearby_scales
      cubical := nextCubical
      dense := candidateExtremal.dense.trans nextMass
      volume_upper := by
        rw [nextUnion]
        exact candidateExtremal.volume_upper }
  have parentCWA : WZ2PaperConvexWolffBound
      outerReentry.toNormalizationData.croppedFamily
      (Kakeya.realRpowENN delta (-parentLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := outerReentry.toNormalizationData.croppedRefined)
      (_shading2 := parent)
      outerReentry.toNormalizationData.cropped_top_level_cwa
      hnormalizationParent targetReentry.reentry_extremal.delta_pos
      targetReentry.reentry_extremal.delta_le_one
  have nextCWA : WZ2PaperConvexWolffBound
      outerReentry.toNormalizationData.croppedFamily
      (Kakeya.realRpowENN delta (-outputLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := parent) (_shading2 := nextShading) parentCWA
      hcurrentOutput targetReentry.reentry_extremal.delta_pos
      targetReentry.reentry_extremal.delta_le_one
  have nextCover : PureWZ2PointCenteredCoveringAt nextShading planeMap
      (Real.toNNReal queryScale) spatialRadius constant := by
    intro point
    have hpoint : (point : Point3) ∈ candidate.union := by
      rw [← nextUnion]
      exact point.property
    simpa only [nextUnion] using candidateCover ⟨point, hpoint⟩
  have hregularizationPos :
      0 < targetReentry.regularized.regularizationLoss := by
    rw [targetReentry.regularized.regularizationLoss_eq]
    positivity
  have hregularizationTop :
      targetReentry.regularized.regularizationLoss ≠ ⊤ := by
    rw [targetReentry.regularized.regularizationLoss_eq]
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  have retainedPos : 0 < retainedFactor := by
    dsimp only [retainedFactor]
    apply ENNReal.mul_pos
    · exact ENNReal.inv_ne_zero.mpr hregularizationTop
    · exact (ENNReal.mul_pos
        (ENNReal.mul_pos (by norm_num : (73 / 100 : ENNReal) ≠ 0)
          targetReentry.normalization_weight_ne_zero).ne'
        (ENNReal.mul_pos
          (pure_refinement_fraction_pos_ne_top
            targetReentry.reentry_extremal.delta_pos hdeltaLtOne 61).1.ne'
          first.retained_factor_pos.ne').ne').ne'
  have retainedTop : retainedFactor ≠ ⊤ := by
    dsimp only [retainedFactor]
    apply ENNReal.mul_ne_top
    · exact ENNReal.inv_ne_top.mpr hregularizationPos.ne'
    · apply ENNReal.mul_ne_top
      · exact ENNReal.mul_ne_top
          (ENNReal.div_ne_top (by norm_num) (by norm_num))
          targetReentry.normalization_weight_ne_top
      · exact ENNReal.mul_ne_top
          (pure_refinement_fraction_pos_ne_top
            targetReentry.reentry_extremal.delta_pos hdeltaLtOne 61).2
          first.retained_factor_ne_top
  have retainedCandidate : retainedFactor * parent.mass ≤ candidate.mass := by
    have hscaledReentry := mul_le_mul_right targetReentry.reentryMassRetention
      targetReentry.regularized.regularizationLoss⁻¹
    calc
      retainedFactor * parent.mass =
          (wz2PaperPureRefinementFraction delta 61 * first.retainedFactor) *
            (targetReentry.regularized.regularizationLoss⁻¹ *
              (((73 / 100 : ENNReal) *
                targetReentry.normalizationWeight) * parent.mass)) := by
        dsimp only [retainedFactor, parent]
        ring
      _ ≤ (wz2PaperPureRefinementFraction delta 61 * first.retainedFactor) *
          targetReentry.normalization.croppedRefined.mass := by
        gcongr
        calc
          targetReentry.regularized.regularizationLoss⁻¹ *
                (((73 / 100 : ENNReal) *
                  targetReentry.normalizationWeight) * parent.mass) ≤
              targetReentry.regularized.regularizationLoss⁻¹ *
                (targetReentry.regularized.regularizationLoss *
                  targetReentry.normalization.croppedRefined.mass) :=
            hscaledReentry
          _ = targetReentry.normalization.croppedRefined.mass := by
            rw [← mul_assoc, ENNReal.inv_mul_cancel
              hregularizationPos.ne' hregularizationTop, one_mul]
      _ = first.retainedFactor *
          (wz2PaperPureRefinementFraction delta 61 *
            targetReentry.normalization.croppedRefined.mass) := by ring
      _ ≤ first.retainedFactor * target.data.refined.mass := by
        exact mul_le_mul_right target.total_mass_retention _
      _ = first.retainedFactor *
          (extendShading target.data.selected target.data.refined).mass := by
        rw [extendShading_mass]
      _ ≤ first.state.shading.mass := first.retained
      _ = candidate.mass := candidateMass.symm
  have retained : retainedFactor * parent.mass ≤ nextShading.mass :=
    retainedCandidate.trans nextMass
  let state : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := outputLoss) parent :=
    { shading := nextShading
      subshading := nextSub
      extremal := nextExtremal
      cwa := nextCWA }
  let result : Proposition63LiftedPointCoverData
      (outputLoss := outputLoss) (queryScale := queryScale)
      (spatialRadius := spatialRadius) outerReentry.toNormalizationData
      parent planeMap constant :=
    { state := state
      multiplicity := paperCommonSpatialHull_pointMultiplicity_eq
        parent candidate
      retainedFactor := retainedFactor
      retained := retained
      retained_factor_pos := retainedPos
      retained_factor_ne_top := retainedTop
      cover := nextCover }
  refine ⟨result, nextUnion.trans candidateUnion, ?_⟩
  rfl

/-- Restore the call3 first cover to the call2 ambient by density lift, then
run the fourth/internal three-call schedule with call2 retained as the root.
All scalar certificates for the new call2-rooted re-entry and the second
robust localization are supplied by the caller. -/
theorem proposition63_four_call_complete_sqrt_on_call2_ancestor_of_density_lift
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss targetReentryLoss targetLoss innerFirstLoss
      restoredFirstLoss tauScale densityLoss reentryLoss
      reentryNormalizationLoss weightLoss sqrtStickyLoss secondLoss epsilon₁
      epsilon₃ middleLoss finalLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    {incidenceBound : ℝ}
    (currentMap : PaperWZ1WeakPlaneMapData
      (extendShading outer.data.selected outer.data.refined) incidenceBound)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient currentMap.planeMap)
    (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := innerFirstLoss) (queryScale := delta)
      (spatialRadius := tauScale) targetReentry.normalization
      (extendShading target.data.selected target.data.refined)
      currentMap.planeMap tauConstant)
    (parentLoss : ℝ)
    (hdeltaLtOne : delta < 1)
    (hnormalizationParent : outerNormalizationLoss ≤ parentLoss)
    (hparentRetention :
      Kakeya.realRpowENN delta parentLoss ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta outerNormalizationLoss)
    (hcurrentOutput : parentLoss ≤ restoredFirstLoss)
    (hrestoredFirstLoss : 0 < restoredFirstLoss)
    (hdensityLift :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper) *
          Kakeya.realRpowENN delta restoredFirstLoss ≤
        targetReentry.normalizationWeight *
          Kakeya.realRpowENN delta innerFirstLoss)
    (absorption : Proposition63CurrentReentryAbsorptionData
      outerSourceLoss outerNormalizationLoss densityLoss restoredFirstLoss
      weightLoss reentryLoss
      (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaAbsorption : delta ≤ absorption.delta₀)
    (houterNormalizationLoss : 0 < outerNormalizationLoss)
    (htwoNormalization : 2 * outerNormalizationLoss ≤ reentryLoss)
    (hfirstReentry : restoredFirstLoss ≤ reentryLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (richSchedule : Proposition63RichThreeCallScheduleData
      sigma sqrtStickyLoss)
    (hreentryLoss : reentryLoss = richSchedule.third.sourceLoss)
    (hthirdNormalization :
      reentryNormalizationLoss = richSchedule.third.normalizationLoss)
    (hdeltaThird : delta ≤ richSchedule.third.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtLower : Real.rpow delta (1 - sqrtStickyLoss) ≤ sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤ Real.rpow delta sqrtStickyLoss)
    (hsqrtOne : sqrtRequested.1 ≤ 1)
    (boundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      sqrtStickyLoss reentryNormalizationLoss)
    (hdeltaBoundary : delta ≤ boundaryAbsorption.delta₀)
    (gridAbsorption : Proposition63RobustGridPruningAbsorptionData
      reentryNormalizationLoss epsilon₁)
    (hdeltaGridAbsorption : delta ≤ gridAbsorption.delta₀)
    (crossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent outerLoss reentryNormalizationLoss weightLoss 4
        (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaCrossAbsorption : delta ≤ crossAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : sqrtRequested.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              reentryNormalizationLoss sqrtStickyLoss
              sqrtRequested.1 sqrtRequested.1 /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                sqrtRequested.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta sqrtRequested.1
              incidenceBound coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN
          (sqrtRequested.1 / delta) (1 - sigma))
    (hnormalizationSecond : reentryNormalizationLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (restoreAbsorption :
      Proposition63RobustPointCoverRestorationAbsorptionData
        reentryNormalizationLoss secondLoss 61)
    (hdeltaRestore : delta ≤ restoreAbsorption.delta₀)
    (hsecondMiddle : secondLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (multiplicityAbsorption : Proposition63FullGrainLogAbsorptionData
      secondLoss middleLoss)
    (hdeltaMultiplicity : delta ≤ multiplicityAbsorption.delta₀)
    (hbalancingBoundary :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / sqrtRequested.1)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (balancingAbsorption : Proposition63FullGrainBalancingAbsorptionData
      middleLoss finalLoss)
    (hdeltaBalancing : delta ≤ balancingAbsorption.delta₀) :
    Nonempty (Proposition63NestedPointCoverData
      (firstLoss := restoredFirstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := delta)
      (tauScale := tauScale) (sqrtScale := sqrtRequested.1)
      outerReentry.toNormalizationData currentMap.planeMap tauConstant
      (C * Kakeya.realRpowENN
        (sqrtRequested.1 / delta) (1 - sigma))) := by
  rcases proposition63_four_call_restore_first_to_call2_ancestor_of_density_lift
      outer targetReentry htargetReentryLoss target currentMap.planeMap
      tauConstant first parentLoss hdeltaLtOne hnormalizationParent
      hparentRetention hcurrentOutput hrestoredFirstLoss hdensityLift with
    ⟨restored, _hrestoredUnion, _hrestoredFactor⟩
  exact restored.toNestedPointCoverViaFourthRobustOfAbsorptions outer
    currentMap hplaneLipschitz tauConstant absorption hdeltaAbsorption
    houterNormalizationLoss htwoNormalization hfirstReentry
    hrestoredFirstLoss hreentryNormalizationLoss hreentryHalf richSchedule
    hreentryLoss hthirdNormalization hdeltaThird sqrtRequested hsqrtLower
    hsqrtUpper hsqrtOne boundaryAbsorption hdeltaBoundary gridAbsorption
    hdeltaGridAbsorption crossAbsorption hdeltaCrossAbsorption hrobustScale
    hrobustSmall hkappa htargetSmall hdeltaSmall hsqrtSq hsigma hsigmaOne
    hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog hlog haxis C
    harithmetic hnormalizationSecond hsecondLoss restoreAbsorption
    hdeltaRestore hsecondMiddle hmiddleLoss multiplicityAbsorption
    hdeltaMultiplicity hbalancingBoundary hmiddleFinal hfinalLoss
    balancingAbsorption hdeltaBalancing

/-- Complete the call2-rooted square-root localization while retaining the
actual restored first cover and its exact ancestry receipts. -/
theorem proposition63_four_call_complete_sqrt_on_call2_ancestor_with_restored_first
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss targetReentryLoss targetLoss innerFirstLoss
      restoredFirstLoss tauScale densityLoss reentryLoss
      reentryNormalizationLoss weightLoss sqrtStickyLoss secondLoss epsilon₁
      epsilon₃ middleLoss finalLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    {incidenceBound : ℝ}
    (currentMap : PaperWZ1WeakPlaneMapData
      (extendShading outer.data.selected outer.data.refined) incidenceBound)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient currentMap.planeMap)
    (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := innerFirstLoss) (queryScale := delta)
      (spatialRadius := tauScale) targetReentry.normalization
      (extendShading target.data.selected target.data.refined)
      currentMap.planeMap tauConstant)
    (parentLoss : ℝ)
    (hdeltaLtOne : delta < 1)
    (hnormalizationParent : outerNormalizationLoss ≤ parentLoss)
    (hparentRetention :
      Kakeya.realRpowENN delta parentLoss ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta outerNormalizationLoss)
    (hcurrentOutput : parentLoss ≤ restoredFirstLoss)
    (hrestoredFirstLoss : 0 < restoredFirstLoss)
    (hdensityLift :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper) *
          Kakeya.realRpowENN delta restoredFirstLoss ≤
        targetReentry.normalizationWeight *
          Kakeya.realRpowENN delta innerFirstLoss)
    (absorption : Proposition63CurrentReentryAbsorptionData
      outerSourceLoss outerNormalizationLoss densityLoss restoredFirstLoss
      weightLoss reentryLoss
      (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaAbsorption : delta ≤ absorption.delta₀)
    (houterNormalizationLoss : 0 < outerNormalizationLoss)
    (htwoNormalization : 2 * outerNormalizationLoss ≤ reentryLoss)
    (hfirstReentry : restoredFirstLoss ≤ reentryLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (richSchedule : Proposition63RichThreeCallScheduleData sigma sqrtStickyLoss)
    (hreentryLoss : reentryLoss = richSchedule.third.sourceLoss)
    (hthirdNormalization :
      reentryNormalizationLoss = richSchedule.third.normalizationLoss)
    (hdeltaThird : delta ≤ richSchedule.third.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtLower : Real.rpow delta (1 - sqrtStickyLoss) ≤ sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤ Real.rpow delta sqrtStickyLoss)
    (hsqrtOne : sqrtRequested.1 ≤ 1)
    (boundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      sqrtStickyLoss reentryNormalizationLoss)
    (hdeltaBoundary : delta ≤ boundaryAbsorption.delta₀)
    (gridAbsorption : Proposition63RobustGridPruningAbsorptionData
      reentryNormalizationLoss epsilon₁)
    (hdeltaGridAbsorption : delta ≤ gridAbsorption.delta₀)
    (crossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent outerLoss reentryNormalizationLoss weightLoss 4
        (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaCrossAbsorption : delta ≤ crossAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : sqrtRequested.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              reentryNormalizationLoss sqrtStickyLoss
              sqrtRequested.1 sqrtRequested.1 /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                sqrtRequested.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta sqrtRequested.1
              incidenceBound coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN
          (sqrtRequested.1 / delta) (1 - sigma))
    (hnormalizationSecond : reentryNormalizationLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (restoreAbsorption : Proposition63RobustPointCoverRestorationAbsorptionData
      reentryNormalizationLoss secondLoss 61)
    (hdeltaRestore : delta ≤ restoreAbsorption.delta₀)
    (hsecondMiddle : secondLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (multiplicityAbsorption : Proposition63FullGrainLogAbsorptionData
      secondLoss middleLoss)
    (hdeltaMultiplicity : delta ≤ multiplicityAbsorption.delta₀)
    (hbalancingBoundary :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / sqrtRequested.1)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (balancingAbsorption : Proposition63FullGrainBalancingAbsorptionData
      middleLoss finalLoss)
    (hdeltaBalancing : delta ≤ balancingAbsorption.delta₀) :
    Nonempty (Proposition63AncestorRestoredNestedPointCoverData
      (restoredFirstLoss := restoredFirstLoss)
      (reentryLoss := reentryLoss) (sqrtStickyLoss := sqrtStickyLoss)
      (secondLoss := secondLoss) (finalLoss := finalLoss)
      (tauScale := tauScale) (sqrtScale := sqrtRequested.1)
      outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined)
      currentMap.planeMap tauConstant
      (C * Kakeya.realRpowENN (sqrtRequested.1 / delta) (1 - sigma))
      weightLoss
      first.state.shading.union
      (targetReentry.regularized.regularizationLoss⁻¹ *
        (((73 / 100 : ENNReal) * targetReentry.normalizationWeight) *
          (wz2PaperPureRefinementFraction delta 61 * first.retainedFactor)))) := by
  rcases proposition63_four_call_restore_first_to_call2_ancestor_of_density_lift
      outer targetReentry htargetReentryLoss target currentMap.planeMap
      tauConstant first parentLoss hdeltaLtOne hnormalizationParent
      hparentRetention hcurrentOutput hrestoredFirstLoss hdensityLift with
    ⟨restored, hrestoredUnion, hrestoredFactor⟩
  have restoredSubNormalized : PaperIsSubshading restored.state.shading
      outerReentry.toNormalizationData.croppedRefined := by
    exact fun index point hpoint =>
      extendShading_subshading outer.data.selected outer.data.subshading index <|
        restored.state.subshading index hpoint
  rcases restored.nextReentryAndThirdRichOfAbsorption
      outerReentry.toNormalizationData restoredSubNormalized absorption
      hdeltaAbsorption houterNormalizationLoss htwoNormalization
      hfirstReentry hrestoredFirstLoss hreentryNormalizationLoss hreentryHalf
      richSchedule hreentryLoss hthirdNormalization hdeltaThird sqrtRequested
      hsqrtLower hsqrtUpper with
    ⟨reentry, ⟨sqrtTarget⟩, hweight, hweightUpper, hlevel, hnormalization⟩
  let restoredMap : PaperWZ1WeakPlaneMapData restored.state.shading
      incidenceBound := paperWeakPlaneMapRestrict currentMap
        restored.state.subshading
  let normalizedMap : PaperWZ1WeakPlaneMapData
      reentry.normalization.croppedRefined incidenceBound :=
    reentry.normalizedPlaneMap restoredMap
  let sqrtTargetMap : PaperWZ1WeakPlaneMapData
      sqrtTarget.data.refined incidenceBound :=
    sqrtTarget.terminalPlaneMap normalizedMap
  have hsqrtTargetReentryLoss : 0 < reentryLoss := by
    rw [hreentryLoss]
    exact richSchedule.third.sourceLoss_pos
  have receipts :=
    Proposition63RichTerminalStickyData.robustTauRuntimeReceipts_of_absorptions
      outer reentry hsqrtTargetReentryLoss sqrtTarget hnormalization
      gridAbsorption crossAbsorption hdeltaGridAbsorption
      hdeltaCrossAbsorption hrobustScale hweight hweightUpper hlevel
      (reentry.reentry_extremal.delta_pos.trans_le sqrtRequested.2.1)
      hsqrtOne hrobustSmall
  rcases receipts with ⟨hgridError, hcrossCall⟩
  have htargetPos : 0 < sqrtRequested.1 :=
    reentry.reentry_extremal.delta_pos.trans_le sqrtRequested.2.1
  have hsqrtLowerThree : Real.rpow delta (1 - sqrtStickyLoss) ≤
      3 * sqrtRequested.1 := hsqrtLower.trans <| by nlinarith [htargetPos]
  have hdeltaGrid := boundaryAbsorption.grid_le
    reentry.reentry_extremal.delta_pos hdeltaBoundary htargetPos
      hsqrtLowerThree
  have hperiodic := boundaryAbsorption.periodic
    reentry.reentry_extremal.delta_pos hdeltaBoundary htargetPos
      hsqrtLowerThree
  have hboundaryScalarActual := boundaryAbsorption.absorb
    reentry.reentry_extremal.delta_pos hdeltaBoundary htargetPos
      hsqrtLowerThree
  have hboundaryActual := sqrtTarget.boundaryCWA_of_scalar
    hsqrtTargetReentryLoss (hdeltaSmall.trans (by norm_num)) <| by
      simpa only [hnormalization] using hboundaryScalarActual
  have harithmeticActual :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              reentry.reentryNormalizationLoss sqrtStickyLoss
              sqrtRequested.1 sqrtRequested.1 /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                sqrtRequested.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta sqrtRequested.1
              incidenceBound coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN
          (sqrtRequested.1 / delta) (1 - sigma) := by
    simpa only [hnormalization] using harithmetic
  have hrestoreActual : proposition63Lemma43MassLoss
        ((81 / 400 : ENNReal) *
          (((Nat.log 2 sqrtTarget.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹ * wz2PaperPureRefinementFraction delta 61) 1 *
        Kakeya.realRpowENN delta secondLoss ≤
      Kakeya.realRpowENN delta reentry.reentryNormalizationLoss := by
    exact (restoreAbsorption.absorbLocal reentry.normalization
      sqrtTarget.data.selected hdeltaRestore).trans_eq
        (congrArg (Kakeya.realRpowENN delta) hnormalization.symm)
  rcases proposition63_robust_tau_local_point_cover_data_of_cwa outer reentry
      restored.state.subshading hsqrtTargetReentryLoss sqrtTarget
      currentMap.planeMap incidenceBound sqrtTargetMap.unit hplaneLipschitz
      sqrtTargetMap.incidence sqrtRequested.2.1 hdeltaGrid htargetPos
      hsqrtOne hperiodic hboundaryActual hgridError hrobustSmall hcrossCall
      hkappa htargetSmall hdeltaSmall (by linarith [htargetPos]) hsqrtSq
      hsigma hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog
      hlog haxis C harithmeticActual (hdeltaSmall.trans_lt (by norm_num))
      (hnormalization.trans_le hnormalizationSecond) hsecondLoss
      hrestoreActual with
    ⟨second, hfactor, hsecondSubset⟩
  let nestedFirstState : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := restoredFirstLoss)
      restored.state.shading := {
    shading := restored.state.shading
    subshading := fun _ _ hpoint => hpoint
    extremal := restored.state.extremal
    cwa := restored.state.cwa
  }
  let analytic : Proposition63NestedPointCoverAnalyticData
      (firstLoss := restoredFirstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (queryScale := delta) (tauScale := tauScale)
      (sqrtScale := sqrtRequested.1) outerReentry.toNormalizationData
      currentMap.planeMap tauConstant
      (C * Kakeya.realRpowENN
        (sqrtRequested.1 / delta) (1 - sigma)) := {
    current := restored.state.shading
    first := nestedFirstState
    first_multiplicity := fun _ _ => rfl
    firstCover := restored.cover
    firstRetainedFactor := 1
    first_retained := by simp [nestedFirstState]
    first_retained_factor_pos := by simp
    first_retained_factor_ne_top := by simp
    reentry := reentry
    sqrtRequested := sqrtRequested
    sqrt_requested_eq := rfl
    sqrtSticky := sqrtTarget.data
    second := second.state
    secondCover := second.cover
    second_union_subset_sqrt_sticky := hsecondSubset
    secondRetainedFactor := second.retainedFactor
    second_retained := second.retained
    second_retained_factor_pos := second.retained_factor_pos
    second_retained_factor_ne_top := second.retained_factor_ne_top
  }
  have cardLogLe :
      ((Nat.log 2 analytic.reentry.normalization.croppedFamily.card + 1 :
          ℕ) : ENNReal) ≤ proposition63OneScaleLogEnvelope delta := by
    have raw := proposition63_cropped_cardLog_le_oneScaleEnvelope
      analytic.reentry.normalization
      (hdeltaMultiplicity.trans multiplicityAbsorption.delta₀_le_tiny)
    exact le_trans (by
      exact_mod_cast Nat.add_le_add_right
        (Nat.log_mono_right <| Nat.le_mul_of_pos_left _ (by norm_num)) 1) raw
  have multiplicitySlack :
      (((Nat.log 2 analytic.reentry.normalization.croppedFamily.card + 1 :
          ℕ) : ENNReal) * Kakeya.realRpowENN delta middleLoss) ≤
        Kakeya.realRpowENN delta secondLoss :=
    (mul_le_mul_left cardLogLe _).trans <|
      multiplicityAbsorption.absorbEnvelope
        analytic.reentry.reentry_extremal.delta_pos hdeltaMultiplicity
  have htargetPos : 0 < sqrtRequested.1 :=
    analytic.reentry.reentry_extremal.delta_pos.trans_le sqrtRequested.2.1
  have hperiodicGrid := boundaryAbsorption.periodic
    analytic.reentry.reentry_extremal.delta_pos hdeltaBoundary htargetPos <|
      hsqrtLower.trans (by nlinarith [htargetPos])
  have hgridSideLeTarget :
      gridSide (sqrtRequested.1 / 2) ≤ sqrtRequested.1 := by
    have sqrtThreeGeOne : 1 ≤ Real.sqrt 3 :=
      Real.one_le_sqrt.mpr (by norm_num)
    unfold gridSide
    rw [show 2 * (sqrtRequested.1 / 2) / Real.sqrt 3 =
        sqrtRequested.1 / Real.sqrt 3 by ring]
    exact div_le_self htargetPos.le sqrtThreeGeOne
  have hperiodicScale : 50 * delta ≤ sqrtRequested.1 :=
    hperiodicGrid.trans hgridSideLeTarget
  rcases proposition63_prepare_extremalShading_constantMultiplicity_with_loss
      analytic.second hsecondMiddle hmiddleLoss multiplicitySlack with
    ⟨prepared, _hpreparedLoss⟩
  rcases proposition63_fresh_balancedExtremalCells_of_cwa_scalar
      analytic.second prepared analytic.reentry.normalization.line_class
      (hdeltaSmall.trans (by norm_num)) hperiodicScale
      (outerReentry.toNormalizationData.final_extremal.delta_pos.trans_le
        sqrtRequested.2.1) hsqrtOne hbalancingBoundary with
    ⟨fresh⟩
  have hbalancingSlack := balancingAbsorption.absorb
    analytic.reentry.reentry_extremal.delta_pos hdeltaBalancing
  let finalPrepared := fresh.toConstantMultiplicity hmiddleFinal hfinalLoss
    ((mul_le_mul_right' fresh.freshLoss_le_envelope
      (Kakeya.realRpowENN delta finalLoss)).trans hbalancingSlack)
  have hpreparationLoss : finalPrepared.preparationLoss ≤
      proposition63UniformPreparationLoss
        outerReentry.toNormalizationData.croppedFamily := by
    simp only [finalPrepared,
      Proposition63FreshBalancedExtremalCellsData.toConstantMultiplicity]
    rw [fresh.preparedLoss_eq, _hpreparedLoss]
    have hcard : analytic.reentry.normalization.croppedFamily.card ≤
        outerReentry.toNormalizationData.croppedFamily.card := by
      rw [analytic.reentry.normalization_croppedFamily]
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        analytic.reentry.regularized.selected.embedding
        analytic.reentry.regularized.selected.embedding.injective
    have hlog :
        ((Nat.log 2 analytic.reentry.normalization.croppedFamily.card + 1 :
            ℕ) : ENNReal) ≤
          ((Nat.log 2 outerReentry.toNormalizationData.croppedFamily.card +
            1 : ℕ) : ENNReal) := by
      exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right hcard) 1
    unfold proposition63UniformPreparationLoss
    exact mul_le_mul hlog fresh.freshLoss_le_envelope bot_le bot_le
  let nested : Proposition63NestedPointCoverData
      (firstLoss := restoredFirstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := delta)
      (tauScale := tauScale) (sqrtScale := sqrtRequested.1)
      outerReentry.toNormalizationData currentMap.planeMap tauConstant
      (C * Kakeya.realRpowENN
        (sqrtRequested.1 / delta) (1 - sigma)) := {
    current := analytic.current
    first := analytic.first
    first_multiplicity := analytic.first_multiplicity
    firstCover := analytic.firstCover
    firstRetainedFactor := analytic.firstRetainedFactor
    first_retained := analytic.first_retained
    first_retained_factor_pos := analytic.first_retained_factor_pos
    first_retained_factor_ne_top := analytic.first_retained_factor_ne_top
    reentry := analytic.reentry
    sqrtRequested := analytic.sqrtRequested
    sqrt_requested_eq := analytic.sqrt_requested_eq
    sqrtSticky := analytic.sqrtSticky
    second := analytic.second
    secondCover := analytic.secondCover
    second_union_subset_sqrt_sticky :=
      analytic.second_union_subset_sqrt_sticky
    secondRetainedFactor := analytic.secondRetainedFactor
    second_retained := analytic.second_retained
    second_retained_factor_pos := analytic.second_retained_factor_pos
    second_retained_factor_ne_top := analytic.second_retained_factor_ne_top
    prepared := finalPrepared
    cells := fresh.cells }
  refine ⟨{
    restoredFirst := restored
    restored_union := hrestoredUnion
    restored_factor := hrestoredFactor
    nested := nested
    nested_current_eq := rfl
    nestedCanonicalWeight := hweight
    nestedCanonicalWeightUpper := hweightUpper
    nestedCanonicalLevel := hlevel
    nested_first_retained := nested.first_retained
    nestedFirstRetainedFactor := rfl
    nested_second_retained := nested.second_retained
    nestedSecondRetainedFactor := by simpa only using hfactor
    nestedPreparationLoss := hpreparationLoss
  }⟩

/-- Convenience form of the call2-rooted square-root localization: the final
three-call schedule is reconstructed from a four-call public schedule and the
unweakened internal kernel behind its fourth call. -/
theorem proposition63_four_call_complete_sqrt_on_call2_ancestor_of_density_lift_of_kernel
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss targetReentryLoss targetLoss innerFirstLoss
      restoredFirstLoss tauScale densityLoss reentryLoss
      reentryNormalizationLoss weightLoss publicLoss discreteBudget tailBudget
      sigmaBudget secondLoss epsilon₁ epsilon₃ middleLoss finalLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    {incidenceBound : ℝ}
    (currentMap : PaperWZ1WeakPlaneMapData
      (extendShading outer.data.selected outer.data.refined) incidenceBound)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient currentMap.planeMap)
    (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := innerFirstLoss) (queryScale := delta)
      (spatialRadius := tauScale) targetReentry.normalization
      (extendShading target.data.selected target.data.refined)
      currentMap.planeMap tauConstant)
    (parentLoss : ℝ)
    (hdeltaLtOne : delta < 1)
    (hnormalizationParent : outerNormalizationLoss ≤ parentLoss)
    (hparentRetention :
      Kakeya.realRpowENN delta parentLoss ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta outerNormalizationLoss)
    (hcurrentOutput : parentLoss ≤ restoredFirstLoss)
    (hrestoredFirstLoss : 0 < restoredFirstLoss)
    (hdensityLift :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper) *
          Kakeya.realRpowENN delta restoredFirstLoss ≤
        targetReentry.normalizationWeight *
          Kakeya.realRpowENN delta innerFirstLoss)
    (absorption : Proposition63CurrentReentryAbsorptionData
      outerSourceLoss outerNormalizationLoss densityLoss restoredFirstLoss
      weightLoss reentryLoss
      (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaAbsorption : delta ≤ absorption.delta₀)
    (houterNormalizationLoss : 0 < outerNormalizationLoss)
    (htwoNormalization : 2 * outerNormalizationLoss ≤ reentryLoss)
    (hfirstReentry : restoredFirstLoss ≤ reentryLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (schedule : Proposition63RichFourCallScheduleData sigma publicLoss)
    (kernel : Proposition63RichInternalKernelScheduleData sigma publicLoss
      discreteBudget tailBudget sigmaBudget schedule.fourth)
    (hreentryLoss : reentryLoss = schedule.fourth.sourceLoss)
    (hfourthNormalization :
      reentryNormalizationLoss = schedule.fourth.normalizationLoss)
    (hdeltaThird : delta ≤ kernel.internalSchedule.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtLower :
      Real.rpow delta (1 - kernel.internalLoss) ≤ sqrtRequested.1)
    (hsqrtUpper :
      sqrtRequested.1 ≤ Real.rpow delta kernel.internalLoss)
    (hsqrtOne : sqrtRequested.1 ≤ 1)
    (boundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      kernel.internalLoss reentryNormalizationLoss)
    (hdeltaBoundary : delta ≤ boundaryAbsorption.delta₀)
    (gridAbsorption : Proposition63RobustGridPruningAbsorptionData
      reentryNormalizationLoss epsilon₁)
    (hdeltaGridAbsorption : delta ≤ gridAbsorption.delta₀)
    (crossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent outerLoss reentryNormalizationLoss weightLoss 4
        (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaCrossAbsorption : delta ≤ crossAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : sqrtRequested.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              reentryNormalizationLoss kernel.internalLoss
              sqrtRequested.1 sqrtRequested.1 /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                sqrtRequested.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta sqrtRequested.1
              incidenceBound coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN
          (sqrtRequested.1 / delta) (1 - sigma))
    (hnormalizationSecond : reentryNormalizationLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (restoreAbsorption :
      Proposition63RobustPointCoverRestorationAbsorptionData
        reentryNormalizationLoss secondLoss 61)
    (hdeltaRestore : delta ≤ restoreAbsorption.delta₀)
    (hsecondMiddle : secondLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (multiplicityAbsorption : Proposition63FullGrainLogAbsorptionData
      secondLoss middleLoss)
    (hdeltaMultiplicity : delta ≤ multiplicityAbsorption.delta₀)
    (hbalancingBoundary :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / sqrtRequested.1)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (balancingAbsorption : Proposition63FullGrainBalancingAbsorptionData
      middleLoss finalLoss)
    (hdeltaBalancing : delta ≤ balancingAbsorption.delta₀) :
    Nonempty (Proposition63NestedPointCoverData
      (firstLoss := restoredFirstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := kernel.internalLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := delta)
      (tauScale := tauScale) (sqrtScale := sqrtRequested.1)
      outerReentry.toNormalizationData currentMap.planeMap tauConstant
      (C * Kakeya.realRpowENN
        (sqrtRequested.1 / delta) (1 - sigma))) := by
  let richSchedule :=
    proposition63_rich_three_call_schedule_of_four_call_kernel schedule kernel
  have hsource := congrArg
    Proposition63RichStickyKernelScheduleData.sourceLoss kernel.public_eq
  have hsource' : schedule.fourth.sourceLoss =
      kernel.internalSchedule.sourceLoss := by
    simpa only [Proposition63RichStickyKernelScheduleData.mono_loss] using hsource
  have hnormalization := congrArg
    Proposition63RichStickyKernelScheduleData.normalizationLoss kernel.public_eq
  have hnormalization' : schedule.fourth.normalizationLoss =
      kernel.internalSchedule.normalizationLoss := by
    simpa only [Proposition63RichStickyKernelScheduleData.mono_loss] using
      hnormalization
  apply proposition63_four_call_complete_sqrt_on_call2_ancestor_of_density_lift
    outer targetReentry htargetReentryLoss target currentMap hplaneLipschitz
    tauConstant first parentLoss hdeltaLtOne hnormalizationParent
    hparentRetention hcurrentOutput hrestoredFirstLoss hdensityLift absorption
    hdeltaAbsorption houterNormalizationLoss htwoNormalization hfirstReentry
    hreentryNormalizationLoss hreentryHalf richSchedule
    (hreentryLoss.trans hsource')
    (hfourthNormalization.trans hnormalization') hdeltaThird sqrtRequested
    hsqrtLower hsqrtUpper hsqrtOne boundaryAbsorption hdeltaBoundary
    gridAbsorption hdeltaGridAbsorption crossAbsorption hdeltaCrossAbsorption
    hrobustScale hrobustSmall hkappa htargetSmall hdeltaSmall hsqrtSq hsigma
    hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog hlog haxis C
    harithmetic hnormalizationSecond hsecondLoss restoreAbsorption
    hdeltaRestore hsecondMiddle hmiddleLoss multiplicityAbsorption
    hdeltaMultiplicity hbalancingBoundary hmiddleFinal hfinalLoss
    balancingAbsorption hdeltaBalancing

end Kakeya.Assouad.PureWZ2
