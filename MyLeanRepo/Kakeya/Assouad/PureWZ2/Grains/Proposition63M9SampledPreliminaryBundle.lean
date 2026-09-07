import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9SampledCoarseAssembly

/-!
# Bundled sampled-coarse preliminary M8 output

The existential preliminary-M8 interface forgets the normalization-loss and
axial receipts produced while constructing its root. This module keeps those
receipts together with the exact sampled family, shading, and plane map.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

/-- The first sampled preliminary M8 output, retaining the re-entry receipts
needed by the following rich call. Every dependent field uses the exact
sampled shading and the exact root map selected by the runtime construction. -/
structure Proposition63M9SampledPreliminaryData
    {sigma outputLoss : Real}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {aligned : Proposition63M9AlignedSampledStickyData cutoff}
    {normalizationWeight weightUpper : ENNReal}
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)}
    (regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) aligned.sticky.data nearbySchedule)
    {coefficient : Real} {K : Nat}
    (sampled : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      aligned.rootDelta_pos K) where
  reentry : Proposition63CurrentShadingReentryData
    (reentryLoss := cutoff.sampledM8RootLosses.reentryLoss)
    (cutoff.sampledM8RootLosses.ambientReentry aligned.sticky
      |>.toNormalizationData)
    sampled.ambientShading
  normalization_loss_eq : reentry.reentryNormalizationLoss =
    cutoff.sampledM8RootLosses.reentryNormalizationLoss
  rootMap : Proposition63RootPlaneMapData
    (densityLoss := cutoff.sampledM8.gridLoss)
    (incidence := aligned.aligned.requested.1) reentry 1
  root_axial_eighth : forall tube point,
    point ∈ rootMap.root.normalization.frame ''
        rootMap.root.normalization.ordinaryRefined.carrier tube ->
      |point (2 : Fin 3)| <= 1 / 8
  preliminary : Proposition63PreliminaryLocalGrainData
    (localLoss := cutoff.initial.localLoss)
    (reentryLoss := cutoff.preliminaryProducerLoss)
    rootMap.root.normalization
  preliminary_incidence_eq :
    preliminary.incidence = aligned.aligned.requested.1
  preliminary_lipschitz_eq : preliminary.lipschitz = 1

/-- Construct the bundled preliminary output without projecting away the
normalization-loss or axial receipts. -/
theorem RegularizedAlignedSampledPlaninessData.runPreliminaryM8BundleOfReceipts
    {sigma outputLoss : Real}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {aligned : Proposition63M9AlignedSampledStickyData cutoff}
    {normalizationWeight weightUpper : ENNReal}
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)}
    (regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) aligned.sticky.data nearbySchedule)
    {coefficient : Real} {K : Nat}
    (sampled : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      aligned.rootDelta_pos K)
    (extremality : Proposition63M9SampledExtremalityInputs regularized sampled)
    (hnormalizationWeightZero : normalizationWeight ≠ 0)
    (hnormalizationWeightTop : normalizationWeight ≠ ⊤)
    (hextensionAbsorb :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (regularized.regularized.regularizationLoss * weightUpper) *
            Kakeya.realRpowENN aligned.aligned.requested.1
              cutoff.sampledM8RootLosses.currentLoss <=
        normalizationWeight *
          Kakeya.realRpowENN aligned.aligned.requested.1
            cutoff.sampledM8RootLosses.selectedLoss)
    (hsigmaOne : sigma < 1) :
    Nonempty (Proposition63M9SampledPreliminaryData
      cutoff regularized sampled) := by
  let losses := cutoff.sampledM8RootLosses
  let ambientReentry := losses.ambientReentry aligned.sticky
  have rhoPos : 0 < aligned.aligned.requested.1 :=
    aligned.sticky.data.coarse_extremal.delta_pos
  have rhoOne : aligned.aligned.requested.1 <= 1 :=
    aligned.scale_le_outerScaleCeiling.trans cutoff.outerScaleCeiling_le_one
  have rhoCutoff : aligned.aligned.requested.1 <=
      cutoff.sampledM8Cutoff.delta₀ :=
    aligned.scale_le_outerScaleCeiling.trans
      cutoff.outerScaleCeiling_le_preliminaryM8
  have stickyCurrent : cutoff.sampledM8RootLosses.stickyLoss <=
      cutoff.sampledM8RootLosses.currentLoss := by
    rw [cutoff.sampledM8RootLosses.currentLoss_eq]
    linarith [cutoff.sampledM8RootLosses.stickyLoss_pos]
  have currentReentry : cutoff.sampledM8RootLosses.currentLoss <=
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
      2 * cutoff.sampledM8RootLosses.ambientNormalizationLoss <=
        cutoff.sampledM8RootLosses.reentryLoss := by
    rw [cutoff.sampledM8RootLosses.ambientNormalizationLoss_eq,
      cutoff.sampledM8RootLosses.reentryLoss_eq]
    linarith [cutoff.sampledM8RootLosses.stickyLoss_pos]
  have reentryHalf : cutoff.sampledM8RootLosses.reentryLoss <=
      cutoff.sampledM8RootLosses.reentryNormalizationLoss / 2 := by
    rw [cutoff.sampledM8RootLosses.reentryLoss_eq,
      cutoff.sampledM8RootLosses.reentryNormalizationLoss_eq]
    nlinarith
  have gridDensity := cutoff.sampledM8Cutoff.grid_density rhoPos rhoCutoff
  rcases sampled.prepareGrainStructureRootOfAmbientReentryWithAxial
      regularized aligned.rootDelta_pos ambientReentry
      (sampled.m9SampledExtremal regularized extremality) stickyCurrent
      hnormalizationWeightZero hnormalizationWeightTop hextensionAbsorb
      cutoff.sampledM8RootLosses.currentAbsorption
      (rhoCutoff.trans cutoff.sampledM8Cutoff.delta₀_le_currentReentry)
      currentReentry currentPos reentryNormalizationPos
      twiceAmbientNormalization reentryHalf gridDensity
      aligned.coarseAxialEighth with
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
  rcases proposition63_preliminary_local_grain_of_root_map_outer_inputs_with_receipts
      (localLoss := cutoff.initial.localLoss)
      (terminalReentryLoss := cutoff.preliminaryProducerLoss) reentry
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
        (rhoCutoff.trans cutoff.sampledM8Cutoff.delta₀_le_terminal)) with
    ⟨preliminary, preliminaryIncidence, preliminaryLipschitz⟩
  exact Nonempty.intro {
    reentry := reentry
    normalization_loss_eq := normalization
    rootMap := rootMap
    root_axial_eighth := rootAxial
    preliminary := preliminary
    preliminary_incidence_eq := preliminaryIncidence
    preliminary_lipschitz_eq := preliminaryLipschitz
  }

end Kakeya.Assouad.PureWZ2

end
