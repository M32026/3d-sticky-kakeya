import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9PreRuntimeHierarchy

/-!
# Canonical sampled-coarse preliminary grain terminal

This module connects the sampled coarse plane map to the independent
preliminary M7/M8 schedule.  The ambient re-entry is not a free input: it is
the loss-only retargeting of the exact coarse re-entry carried by the same
sticky output.  After current-shading re-entry, the outer binding is indexed
definitionally by the normalization stored in the returned root map.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

/-- Run the first grain-structure iteration on the actual sampled coarse
family.  All scalar thresholds were frozen before Node 3; the only explicit
geometric premise is the strict axial certificate on this exact coarse
re-entry. -/
theorem RegularizedAlignedSampledPlaninessData.runPreliminaryM8
    {sigma outputLoss delta : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {requested : WZ2PaperRequestedScale delta}
    {normalizationExponent logExponent : ℕ}
    {sticky : PureWZ2ReentrantPropStickyData
      (sigma := sigma)
      (outputLoss := cutoff.sampledM8RootLosses.stickyLoss)
      sourceShading requested normalizationExponent logExponent}
    {outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := sticky.data.coarse)
      (Kakeya.realRpowENN requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      outputConstant levelCount}
    (regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) sticky.data nearbySchedule)
    (hdelta : 0 < delta)
    {coefficient : ℝ} {K : ℕ}
    (sampled : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized) hdelta K)
    (selectedExtremal : WZ2PaperCroppedIsExtremal sigma
      cutoff.sampledM8RootLosses.selectedLoss
      regularized.restriction.selectedCoarse.family
      sampled.coarseMap.sampled.selected)
    (hnormalizationWeightZero : normalizationWeight ≠ 0)
    (hnormalizationWeightTop : normalizationWeight ≠ ⊤)
    (hextensionAbsorb :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (regularized.regularized.regularizationLoss * weightUpper) *
            Kakeya.realRpowENN requested.1
              cutoff.sampledM8RootLosses.currentLoss ≤
        normalizationWeight *
          Kakeya.realRpowENN requested.1
            cutoff.sampledM8RootLosses.selectedLoss)
    (coarseAxialEighth : ∀ tube point,
      point ∈
          (cutoff.sampledM8RootLosses.ambientReentry sticky).geometry.frame ''
            (cutoff.sampledM8RootLosses.ambientReentry sticky).geometry.ordinaryRefined.carrier tube →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (hscaleOuter : requested.1 ≤ cutoff.outerScaleCeiling)
    (hsigmaOne : sigma < 1) :
    ∃ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := cutoff.sampledM8RootLosses.reentryLoss)
        (cutoff.sampledM8RootLosses.ambientReentry sticky).toNormalizationData
        sampled.ambientShading,
      ∃ rootMap : Proposition63RootPlaneMapData
          (densityLoss := cutoff.sampledM8.gridLoss)
          (incidence := requested.1) reentry 1,
        Nonempty (Proposition63PreliminaryLocalGrainData
          (localLoss := cutoff.initial.localLoss)
          (reentryLoss := cutoff.preliminaryProducerLoss)
          rootMap.root.normalization) := by
  let losses := cutoff.sampledM8RootLosses
  let ambientReentry := losses.ambientReentry sticky
  have rhoPos : 0 < requested.1 := sticky.data.coarse_extremal.delta_pos
  have rhoOne : requested.1 ≤ 1 :=
    hscaleOuter.trans cutoff.outerScaleCeiling_le_one
  have rhoCutoff : requested.1 ≤ cutoff.sampledM8Cutoff.delta₀ :=
    hscaleOuter.trans cutoff.outerScaleCeiling_le_preliminaryM8
  have stickyCurrent : cutoff.sampledM8RootLosses.stickyLoss ≤
      cutoff.sampledM8RootLosses.currentLoss := by
    rw [cutoff.sampledM8RootLosses.currentLoss_eq]
    linarith [cutoff.sampledM8RootLosses.stickyLoss_pos]
  have currentReentry : cutoff.sampledM8RootLosses.currentLoss ≤
      cutoff.sampledM8RootLosses.reentryLoss := by
    rw [cutoff.sampledM8RootLosses.currentLoss_eq,
      cutoff.sampledM8RootLosses.reentryLoss_eq]
    linarith [cutoff.sampledM8RootLosses.stickyLoss_pos]
  have currentPos : 0 < cutoff.sampledM8RootLosses.currentLoss := by
    rw [cutoff.sampledM8RootLosses.currentLoss_eq]
    linarith [cutoff.sampledM8RootLosses.stickyLoss_pos]
  have reentryNormalizationPos :
      0 < cutoff.sampledM8RootLosses.reentryNormalizationLoss := by
    rw [cutoff.sampledM8RootLosses.reentryNormalizationLoss_eq]
    linarith [cutoff.sampledM8RootLosses.stickyLoss_pos]
  have twiceAmbientNormalization :
      2 * cutoff.sampledM8RootLosses.ambientNormalizationLoss ≤
        cutoff.sampledM8RootLosses.reentryLoss := by
    rw [cutoff.sampledM8RootLosses.ambientNormalizationLoss_eq,
      cutoff.sampledM8RootLosses.reentryLoss_eq]
    linarith [cutoff.sampledM8RootLosses.stickyLoss_pos]
  have reentryHalf : cutoff.sampledM8RootLosses.reentryLoss ≤
      cutoff.sampledM8RootLosses.reentryNormalizationLoss / 2 := by
    rw [cutoff.sampledM8RootLosses.reentryLoss_eq,
      cutoff.sampledM8RootLosses.reentryNormalizationLoss_eq]
    nlinarith
  have gridDensity := cutoff.sampledM8Cutoff.grid_density rhoPos rhoCutoff
  rcases sampled.prepareGrainStructureRootOfAmbientReentryWithAxial
      regularized hdelta ambientReentry selectedExtremal stickyCurrent
      hnormalizationWeightZero hnormalizationWeightTop hextensionAbsorb
      cutoff.sampledM8RootLosses.currentAbsorption
      (rhoCutoff.trans cutoff.sampledM8Cutoff.delta₀_le_currentReentry)
      currentReentry currentPos reentryNormalizationPos
      twiceAmbientNormalization reentryHalf gridDensity coarseAxialEighth with
    ⟨reentry, _weight, _level, normalization, rootMap, rootAxial⟩
  have rootSourcePos : 0 < cutoff.sampledM8RootLosses.reentryLoss :=
    currentPos.trans_le currentReentry
  have rootNormalizationPos : 0 < reentry.reentryNormalizationLoss := by
    rw [normalization]
    exact reentryNormalizationPos
  let canonicalReentry :=
    rootMap.root.normalization.toPropStickyReentryData
      rootSourcePos rootNormalizationPos
  let schedule := cutoff.sampledM8.schedule.specialize rhoPos rhoOne
  let inputs := cutoff.sampledM8Cutoff.outerBindingInputs canonicalReentry
    le_rfl (by rw [normalization]) rhoPos rhoCutoff 1
  refine ⟨reentry, rootMap, ?_⟩
  exact proposition63_preliminary_local_grain_of_root_map_outer_inputs reentry
    rootMap rootSourcePos rootNormalizationPos rootAxial schedule 1
    cutoff.sampledM8.gridLoss_le_mid inputs
    (by
      rw [normalization]
      simpa only [schedule,
        Proposition63Lemma412PreRuntimeScheduleData.specialize] using
        cutoff.sampledM8RootLosses.reentryNormalization_le_outerInput)
    (by
      have producerPos : 0 < cutoff.preliminaryProducerLoss := by
        have gridPos := cutoff.sampledM8.gridLoss_pos
        rw [cutoff.sampledM8.gridLoss_eq] at gridPos
        linarith
      rw [cutoff.sampledM8.gridLoss_eq]
      linarith)
    (by
      rw [normalization]
      exact cutoff.sampledM8RootLosses.reentryNormalization_lt_producer.le)
    (rhoCutoff.trans cutoff.sampledM8Cutoff.delta₀_le_terminal |>.trans
      cutoff.sampledM8.scale_small)
    rhoPos.le
    (by linarith [cutoff.sampledM8.gridLoss_pos,
      cutoff.sampledM8.gridLoss_lt_sigma])
    hsigmaOne
    (cutoff.sampledM8.interpolation rhoPos
      (rhoCutoff.trans cutoff.sampledM8Cutoff.delta₀_le_terminal))
    (cutoff.sampledM8.fine rhoPos
      (rhoCutoff.trans cutoff.sampledM8Cutoff.delta₀_le_terminal))

end Kakeya.Assouad.PureWZ2

end
