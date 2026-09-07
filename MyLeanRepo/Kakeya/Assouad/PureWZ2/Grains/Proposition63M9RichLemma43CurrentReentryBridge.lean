import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9TwoCallRobustSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootNormalization

/-!
# Proposition 6.3 M9: rich Lemma 4.3 current-shading re-entry bridge

This file exposes the structural bridge from an ambient-restored Lemma 4.3
output to the existing current-shading re-entry machinery.  The Lemma 4.3
record itself supplies extremality, subshading, and cubicality.  The caller
supplies only the synchronized root normalization and the common root-cutoff
receipt.  The finite nearby schedule and all scalar absorption receipts are
constructed from the pre-runtime two-call schedule.

No second rich call is run here.  In particular, the first rich coarse family
is not identified with any family selected by the second call.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Convert an ambient-restored Lemma 4.3 output into the exact current-shading
re-entry expected before the second rich call.  All geometric provenance is
inherited from `root` and `lemma43`; no family-dependent scalar hypothesis is
left to the runtime caller. -/
theorem proposition63_m9_rich_lemma43_current_reentry
    {sigma outputLoss delta inputLoss incidenceBudget : ℝ}
    (twoCall : Proposition63M9TwoCallRobustScheduleData sigma outputLoss)
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := twoCall.schedule.first.normalizationLoss) source
      normalizationExponent (twoCall.schedule.second.sourceLoss / 8))
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma)
      (sourceLoss := twoCall.schedule.first.normalizationLoss)
      (targetLoss := twoCall.schedule.firstOutputLoss)
      root.normalization.croppedRefined incidenceBudget)
    (hdelta : 0 < delta) (hdeltaCutoff : delta ≤ twoCall.rootCutoff) :
    ∃ current : Proposition63CurrentShadingReentryData
        (reentryLoss := twoCall.schedule.second.sourceLoss)
        root.normalization lemma43.shading,
      current.normalizationWeight =
          proposition63CanonicalReentryWeight delta
            (twoCall.schedule.second.sourceLoss / 2) ∧
        current.weightUpper =
          (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2 ∧
        current.levelCount =
          proposition63CanonicalNearbyLevelCount
            twoCall.schedule.first.normalizationLoss ∧
        current.reentryNormalizationLoss =
          twoCall.schedule.second.normalizationLoss := by
  let absorption := twoCall.currentReentryAbsorption
  have hdeltaAbsorption : delta ≤ absorption.delta₀ :=
    hdeltaCutoff.trans twoCall.rootCutoff_le_currentReentry
  have ambientTwo := absorption.ambient_two hdelta hdeltaAbsorption
  rcases root.finiteNearbySchedule
      (reentryLoss := twoCall.schedule.second.sourceLoss)
      twoCall.schedule.first.normalizationLoss_pos ambientTwo
      (by
        have hnormalization :=
          twoCall.schedule.first.normalizationLoss_lt_output
        have hfirstOutput := twoCall.schedule.firstOutputLoss_eq
        linarith [hnormalization,
          hfirstOutput, twoCall.schedule.second.sourceLoss_pos]) with
    ⟨schedule⟩
  have regularizationAbsorb := absorption.regularization_absorb
    root.normalization rfl schedule rfl rfl hdelta hdeltaAbsorption
  exact root.currentShadingReentryFromExtremal lemma43.shading schedule
    ambientTwo lemma43.extremal
    twoCall.schedule.firstOutputLoss_lt_secondSource.le
    twoCall.schedule.firstOutputLoss_pos
    twoCall.schedule.second.normalizationLoss
    twoCall.schedule.second.normalizationLoss_pos
    twoCall.schedule.second.sourceLoss_le_half
    (absorption.canonical_weight_absorb hdelta hdeltaAbsorption)
    (absorption.trace_fixed_absorb hdelta hdeltaAbsorption)
    (absorption.paper_fixed_absorb hdelta hdeltaAbsorption)
    regularizationAbsorb lemma43.subshading lemma43.cubical
    (hdeltaAbsorption.trans absorption.delta₀_le_tiny |>.trans (by norm_num))

end Kakeya.Assouad.PureWZ2

end
