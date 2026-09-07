import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9SampledPreliminaryBundle

/-!
# First rich call on the exact sampled preliminary family

This module re-roots the first power-scale rich call on the literal sampled
coarse family produced by the preliminary M8 construction.  In particular,
the family, shading, root plane map, normalization-loss receipt, and strict
axial receipt are all those stored in `Proposition63M9SampledPreliminaryData`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

/-- Re-enter the exact sampled preliminary shading at the fixed source and
normalization losses of the first rich call. -/
theorem Proposition63M9SampledPreliminaryData.prepareFirstRich
    {sigma outputLoss : Real}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
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
    {regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) aligned.sticky.data nearbySchedule}
    {coefficient : Real} {K : Nat}
    {sampled : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      aligned.rootDelta_pos K}
    (preliminary : Proposition63M9SampledPreliminaryData
      cutoff regularized sampled) :
    ∃ current : Proposition63CurrentShadingReentryData
        (reentryLoss := cutoff.firstRichSchedule.sourceLoss)
        preliminary.rootMap.root.normalization
        preliminary.preliminary.shading,
      current.reentryNormalizationLoss =
        cutoff.firstRichSchedule.normalizationLoss := by
  let absorption :=
    cutoff.sampledM8RootLosses.sampledFirstRichAbsorption
  have scale_le_absorption : aligned.aligned.requested.1 ≤
      absorption.delta₀ :=
    aligned.scale_le_outerScaleCeiling.trans
      cutoff.outerScaleCeiling_le_sampledFirstRich
  let rootData : Proposition63RootNormalizationData
      (outputLoss := preliminary.reentry.reentryNormalizationLoss)
      preliminary.reentry.ordinarySource 0
      (cutoff.firstRichSchedule.sourceLoss / 16) :=
    Proposition63RootNormalizationData.ofNormalization
      preliminary.rootMap.root.normalization
      (by
        exact absorption.density_absorb
          aligned.sticky.data.coarse_extremal.delta_pos
          scale_le_absorption)
  have delta_le_absorption : aligned.aligned.requested.1 ≤
      absorption.delta₀ := scale_le_absorption
  have ambientTwo : (2 : ENNReal) < Kakeya.realRpowENN
      aligned.aligned.requested.1
        (-preliminary.reentry.reentryNormalizationLoss) := by
    rw [preliminary.normalization_loss_eq]
    exact absorption.ambient_two
      aligned.sticky.data.coarse_extremal.delta_pos delta_le_absorption
  rcases rootData.finiteNearbySchedule
      (reentryLoss := cutoff.firstRichSchedule.sourceLoss)
      (by
        rw [preliminary.normalization_loss_eq]
        rw [cutoff.sampledM8RootLosses.reentryNormalizationLoss_eq]
        linarith [cutoff.sampledM8RootLosses.stickyLoss_pos])
      ambientTwo
      (by
        rw [preliminary.normalization_loss_eq]
        rw [cutoff.sampledM8RootLosses.reentryNormalizationLoss_eq]
        have gap :=
          cutoff.sampledM8RootLosses.reentry_lt_nextSource_sixteenth
        rw [cutoff.sampledM8RootLosses.reentryLoss_eq] at gap
        calc
          2 * (256 * cutoff.sampledM8RootLosses.stickyLoss) =
              4 * (128 * cutoff.sampledM8RootLosses.stickyLoss) := by ring
          _ ≤ 4 * (cutoff.firstRichSchedule.sourceLoss / 16) :=
            (mul_le_mul_of_nonneg_left gap.le (by norm_num))
          _ ≤ cutoff.firstRichSchedule.sourceLoss := by
            linarith [cutoff.firstRichSchedule.sourceLoss_pos])
    with ⟨nearby⟩
  have regularizationAbsorb :=
    absorption.regularization_absorb
      rootData.normalization preliminary.normalization_loss_eq nearby rfl
      (by rw [preliminary.normalization_loss_eq])
      aligned.sticky.data.coarse_extremal.delta_pos delta_le_absorption
  rcases rootData.currentShadingReentryFromExtremal
      preliminary.preliminary.shading nearby ambientTwo
      preliminary.preliminary.extremal
      cutoff.preliminaryProducerLoss_lt_firstSource.le
      (by
        exact preliminary.preliminary.extremal.nonempty |> fun _ =>
          lt_of_lt_of_le cutoff.preliminaryStickyLoss_pos
            cutoff.preliminaryStickyLoss_lt_planiness.le |> fun h =>
          lt_of_lt_of_le h cutoff.planinessLoss_lt_producer.le)
      cutoff.firstRichSchedule.normalizationLoss
      cutoff.firstRichSchedule.normalizationLoss_pos
      cutoff.firstRichSchedule.sourceLoss_le_half
      (by
        simpa only [cutoff.preliminaryProducerLoss_eq] using
          absorption.canonical_weight_absorb
            aligned.sticky.data.coarse_extremal.delta_pos delta_le_absorption)
      (absorption.trace_fixed_absorb
        aligned.sticky.data.coarse_extremal.delta_pos delta_le_absorption)
      (absorption.paper_fixed_absorb
        aligned.sticky.data.coarse_extremal.delta_pos delta_le_absorption)
      regularizationAbsorb
      preliminary.preliminary.subshading
      preliminary.preliminary.cubical
      (delta_le_absorption.trans
        absorption.delta₀_le_tiny |>.trans
          (by norm_num))
    with ⟨current, _weight, _weightUpper, _level, normalizationLossEq⟩
  exact ⟨current, normalizationLossEq⟩

/-- The first paper power-scale call on the exact sampled preliminary family.
The returned local-grain map is the restriction of the stored sampled root
map through the same current-shading re-entry. -/
structure Proposition63M9SampledFirstRichBoundaryData
    {sigma outputLoss : Real}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
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
    {regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) aligned.sticky.data nearbySchedule}
    {coefficient : Real} {K : Nat}
    {sampled : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      aligned.rootDelta_pos K}
    (preliminary : Proposition63M9SampledPreliminaryData
      cutoff regularized sampled) where
  current : Proposition63CurrentShadingReentryData
    (reentryLoss := cutoff.firstRichSchedule.sourceLoss)
    preliminary.rootMap.root.normalization preliminary.preliminary.shading
  current_normalization_loss : current.reentryNormalizationLoss =
    cutoff.firstRichSchedule.normalizationLoss
  power : Proposition63PowerScale aligned.aligned.requested.1 sigma
  terminal : Proposition63RichTerminalStickyData
    (sigma := sigma) (outputLoss := cutoff.initial.stickyLoss)
    current.normalization.croppedRefined
    (current.normalization.toPropStickyReentryData
      cutoff.firstRichSchedule.sourceLoss_pos
      current.reentry_normalization_loss_pos) power.requested
  localGrains : Proposition63InitialWeakLocalGrainData
    (incidence := aligned.aligned.requested.1)
    current.normalization.croppedRefined sigma
    (Kakeya.realRpowENN aligned.aligned.requested.1
      (-cutoff.initial.localLoss)) 1

namespace Proposition63M9SampledFirstRichBoundaryData

/-- Reentrant projection of the retained rich terminal. -/
noncomputable def sticky
    {sigma outputLoss : Real}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
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
    {regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) aligned.sticky.data nearbySchedule}
    {coefficient : Real} {K : Nat}
    {sampled : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      aligned.rootDelta_pos K}
    {preliminary : Proposition63M9SampledPreliminaryData
      cutoff regularized sampled}
    (first : Proposition63M9SampledFirstRichBoundaryData preliminary) :
    PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := cutoff.initial.stickyLoss)
      first.current.normalization.croppedRefined first.power.requested 0 61 :=
  first.terminal.toReentrant <| by
    have axialWindow : ∀ index point,
        point ∈ first.current.normalization.frame ''
            first.current.normalization.ordinaryRefined.carrier index →
          |point (2 : Fin 3)| ≤ 1 / 8 := by
      intro index point hpoint
      dsimp [Proposition63CurrentShadingReentryData.normalization,
        proposition63IdentityFullOrdinaryNormalization] at hpoint
      exact first.current.ordinaryAxialWindowOf preliminary.root_axial_eighth
        index point (by simpa using hpoint)
    simpa [PureWZ2CroppedCriticalNormalizationData.toPropStickyReentryData]
      using axialWindow

end Proposition63M9SampledFirstRichBoundaryData

/-- Execute the first rich call directly from the bundled sampled preliminary
output, without changing its family, shading, or root map. -/
theorem Proposition63M9SampledPreliminaryData.runFirstRich
    {sigma outputLoss : Real}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
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
    {regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) aligned.sticky.data nearbySchedule}
    {coefficient : Real} {K : Nat}
    {sampled : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      aligned.rootDelta_pos K}
    (preliminary : Proposition63M9SampledPreliminaryData
      cutoff regularized sampled)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    Nonempty (Proposition63M9SampledFirstRichBoundaryData preliminary) := by
  rcases preliminary.prepareFirstRich with
    ⟨current, currentNormalizationLoss⟩
  have delta_lt_one : aligned.aligned.requested.1 < 1 :=
    aligned.scale_le_outerScaleCeiling.trans
      cutoff.outerScaleCeiling_le_preliminaryReentry |>.trans
        cutoff.preliminaryReentryAbsorption.delta₀_le_tiny |>.trans_lt
          (by norm_num)
  rcases proposition63_power_scale
      aligned.sticky.data.coarse_extremal.delta_pos delta_lt_one
      hsigma hsigmaOne with ⟨power⟩
  have window := power.first_sticky_window
    aligned.sticky.data.coarse_extremal.delta_pos delta_lt_one.le
    cutoff.initial.sticky_le_power cutoff.initial.power_le_one_sub_sticky
  have delta_le_firstRich : aligned.aligned.requested.1 ≤
      cutoff.firstRichSchedule.delta₀ :=
    aligned.scale_le_outerScaleCeiling.trans
      cutoff.outerScaleCeiling_le_firstRich
  rcases proposition63CurrentShadingReentry_richTerminalSticky current
      cutoff.firstRichSchedule rfl currentNormalizationLoss
      delta_le_firstRich power.requested window.1 window.2 with ⟨terminal⟩
  let localGrains := current.normalizedLocalGrains
    (localGrains := preliminary.preliminary.localGrains)
  rw [preliminary.preliminary_incidence_eq,
    preliminary.preliminary_lipschitz_eq] at localGrains
  exact ⟨{
    current := current
    current_normalization_loss := currentNormalizationLoss
    power := power
    terminal := terminal
    localGrains := localGrains
  }⟩

end Kakeya.Assouad.PureWZ2

end
