import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9NestedSchedule

/-!
# Proposition 6.3 M9: rebase the direct robust preliminary output

The inner robust middle ends on an exact `q`-scale normalization.  This file
weakens only its numerical loss labels to the outer hierarchy chosen before
runtime, without changing the coarse family, shading, frame, or plane map.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

namespace Proposition63M9RobustInitialPreliminaryData

variable
    {sigma outputLoss : ℝ}
    {critical : PureWZ2CriticalPackage sigma}
    {schedule : Proposition63M9NestedScheduleData sigma outputLoss critical}
    {externalCutoff : ℝ}
    (data : Proposition63M9RobustInitialPreliminaryData critical
      schedule.inner schedule.innerCutoff externalCutoff)

/-- Retarget the exact second-call coarse re-entry to the root losses of the
outer first-chart schedule.  This is a loss-only weakening. -/
noncomputable def outerRootReentry : PureWZ2PropStickyReentryData
    (sigma := sigma) data.middle.second.sticky.croppedCoarseShading 0
    schedule.outerCutoff.preliminaryRootSourceLoss
    schedule.outerCutoff.preliminaryRootNormalizationLoss :=
  data.middle.secondCoarseReentry.mono_losses
    (schedule.inner_second_coarse_source_le_outer_root_source data.middle)
    (schedule.inner_second_coarse_normalization_le_outer_root_normalization
      data.middle)
    (by
      rw [schedule.outerCutoff.preliminaryRootSourceLoss_eq]
      exact half_pos schedule.outerCutoff.preliminaryStickyLoss_pos)
    (by
      rw [schedule.outerCutoff.preliminaryRootNormalizationLoss_eq]
      exact schedule.outerCutoff.preliminaryStickyLoss_pos)
    (by
      rw [schedule.outerCutoff.preliminaryRootSourceLoss_eq,
        schedule.outerCutoff.preliminaryRootNormalizationLoss_eq])

/-- The q-scale normalization used by the outer first-rich re-entry. -/
noncomputable def outerRootNormalization :=
  data.outerRootReentry.toNormalizationData

/-- Add the density receipt required by the outer current-shading re-entry.
The runtime hypothesis is only that the already selected `q` lies below the
outer pre-runtime ceiling. -/
noncomputable def outerRoot
    (hqOuter :
      (schedule.innerCutoff.twoCall.secondQRequested data.r_pos
        data.r_le_robustCutoff).1 ≤ schedule.outerCutoff.outerScaleCeiling) :
    Proposition63RootNormalizationData
      (outputLoss := schedule.outerCutoff.preliminaryRootNormalizationLoss)
      data.outerRootReentry.ordinarySource 0
      schedule.outerCutoff.preliminaryReentryDensityLoss :=
  Proposition63RootNormalizationData.ofPropStickyReentry
    data.outerRootReentry <|
      schedule.outerCutoff.preliminaryReentryAbsorption.density_absorb
        data.middle.second.lemma412.extremal.delta_pos
        (hqOuter.trans
          schedule.outerCutoff.outerScaleCeiling_le_preliminaryReentry)

/-- The inner Lemma-4.12 output, with only its public loss bounds weakened to
the exact outer preliminary budgets.  All geometric data remain unchanged. -/
noncomputable def outerPreliminary : Proposition63PreliminaryLocalGrainData
    (localLoss := schedule.outerCutoff.initial.localLoss)
    (reentryLoss := schedule.outerCutoff.preliminaryProducerLoss)
    data.outerRootNormalization where
  shading := data.middle.second.lemma412.shading
  subshading := by
    intro index point pointMem
    exact data.middle.secondCoarsePreliminary.subshading index pointMem
  cubical := data.middle.second.lemma412.cubical
  extremal := data.middle.second.lemma412.extremal.mono_loss
    schedule.inner_preGrain_lt_outer_preliminaryProducer.le
  topLevelCWA := by
    apply weaken_convex_wolff_bound
      data.middle.second.lemma412.top_level_cwa
    exact realRpowENN_antitone
      data.middle.second.lemma412.extremal.delta_pos
      data.middle.second.lemma412.extremal.delta_le_one
      (by
        linarith [
          schedule.inner_preGrain_lt_outer_preliminaryProducer])
  incidence := data.middle.secondCoarsePreliminary.incidence
  lipschitz := data.middle.secondCoarsePreliminary.lipschitz
  incidence_nonnegative :=
    data.middle.secondCoarsePreliminary.incidence_nonnegative
  localGrains := by
    exact (Proposition63InitialWeakLocalGrainData.ofRelaxed
      data.middle.second.lemma412.localGrains).weakenLoss
        data.middle.second.lemma412.extremal.delta_pos
        data.middle.second.lemma412.extremal.delta_le_one
        schedule.inner_preGrain_lt_outer_local.le

/-- The same rebased preliminary package, definitionally viewed on the root
carrying the outer density receipt. -/
noncomputable def outerPreliminaryOnRoot
    (hqOuter :
      (schedule.innerCutoff.twoCall.secondQRequested data.r_pos
        data.r_le_robustCutoff).1 ≤ schedule.outerCutoff.outerScaleCeiling) :
    Proposition63PreliminaryLocalGrainData
      (localLoss := schedule.outerCutoff.initial.localLoss)
      (reentryLoss := schedule.outerCutoff.preliminaryProducerLoss)
      (data.outerRoot hqOuter).normalization := by
  simpa only [outerRoot, Proposition63RootNormalizationData.ofPropStickyReentry,
    Proposition63RootNormalizationData.ofNormalization,
    outerRootNormalization] using data.outerPreliminary

/-- The strict axial window is unchanged by the loss-only reindexing. -/
theorem outerRootAxialWindow : ∀ index point,
    point ∈ data.outerRootReentry.geometry.frame ''
        data.outerRootReentry.geometry.ordinaryRefined.carrier index →
      |point (2 : Fin 3)| ≤ 1 / 8 := by
  simpa only [outerRootReentry, PureWZ2PropStickyReentryData.mono_losses]
    using data.middle.secondCoarseAxialWindow

end Proposition63M9RobustInitialPreliminaryData

end Kakeya.Assouad.PureWZ2

end
