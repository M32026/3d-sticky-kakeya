import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9NestedPreliminary
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9GenericFirstRichBoundary
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9GenericFirstRichTerminalBundle

/-!
# Proposition 6.3 M9: outer first-rich call on the direct preliminary output

This module re-enters the exact `q`-scale Lemma-4.12 shading produced by the
inner robust middle and runs the outer hierarchy's first rich call.  The weak
map is the same measurable Lemma-4.7 map retained by the inner construction.
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

private abbrev q : ℝ :=
  (schedule.innerCutoff.twoCall.secondQRequested data.r_pos
    data.r_le_robustCutoff).1

/-- The globally measurable q-scale map carried by the inner Lemma 4.12
output, viewed on the loss-rebased outer preliminary shading. -/
noncomputable def outerPreliminaryMap : PaperWZ1WeakPlaneMapData
    data.outerPreliminary.shading data.outerPreliminary.incidence :=
  data.middle.secondCoarsePreliminaryMap

theorem outerPreliminaryMap_cellwise : ∀ first second,
    wz1PaperGridIndex data.q first = wz1PaperGridIndex data.q second →
      data.outerPreliminaryMap.planeMap first =
        data.outerPreliminaryMap.planeMap second :=
  data.middle.secondCoarsePreliminaryMap_cellwise

theorem outerPreliminaryLocalGrains_planeMap_eq
    (point : {point : Point3 // point ∈ data.outerPreliminary.shading.union}) :
    data.outerPreliminary.localGrains.planeMap point =
      data.outerPreliminaryMap.planeMap point := by
  change data.middle.second.lemma412.localGrains.planeMap point =
    data.middle.second.lemma47.planeMap.planeMap point
  rw [data.middle.second.lemma412.same_plane_map point,
    data.middle.second.lemma47.same_plane_map]

private theorem outerNormalizedPreliminaryMap_lipschitz
    {hqOuter : data.q ≤ schedule.outerCutoff.outerScaleCeiling}
    (first : Proposition63GenericFirstRichBoundaryData
      (reentryLoss := schedule.outerCutoff.firstRichSchedule.sourceLoss)
      (data.outerRoot hqOuter) (data.outerPreliminaryOnRoot hqOuter)
      schedule.outerCutoff.firstRichSchedule) :
    LipschitzWith data.outerPreliminary.lipschitz
      (fun point : {point : Point3 //
          point ∈ first.current.normalization.croppedRefined.union} =>
        (first.normalizedPreliminaryMap
          data.outerPreliminaryMap).planeMap point) := by
  apply LipschitzWith.of_dist_le_mul
  intro left right
  change dist (data.middle.second.lemma47.planeMap.planeMap left)
      (data.middle.second.lemma47.planeMap.planeMap right) ≤
    (data.outerPreliminary.lipschitz : ℝ) * dist left right
  have leftLemma47 : (left : Point3) ∈
      data.middle.second.lemma47.shading.union :=
    paperSubshading_union data.middle.second.lemma412.subshading
      (first.normalized_union_subset_preliminary left.prop)
  have rightLemma47 : (right : Point3) ∈
      data.middle.second.lemma47.shading.union :=
    paperSubshading_union data.middle.second.lemma412.subshading
      (first.normalized_union_subset_preliminary right.prop)
  exact data.middle.second.lemma47.lipschitz.dist_le_mul
    ⟨left, leftLemma47⟩ ⟨right, rightLemma47⟩

/-- The exact base radius of the outer first-rich stage is the q-scale
selected by the inner robust middle. -/
@[simp] theorem q_eq_second_requested : data.q =
    (schedule.innerCutoff.twoCall.secondQRequested data.r_pos
      data.r_le_robustCutoff).1 :=
  rfl

/-- Run the next rich call on the exact q-scale preliminary pair. -/
theorem runOuterFirstRich
    (hqOuter : data.q ≤ schedule.outerCutoff.outerScaleCeiling) :
    Nonempty (Proposition63GenericFirstRichBoundaryData
      (reentryLoss := schedule.outerCutoff.firstRichSchedule.sourceLoss)
      (data.outerRoot hqOuter) (data.outerPreliminaryOnRoot hqOuter)
      schedule.outerCutoff.firstRichSchedule) := by
  have qPos : 0 < data.q :=
    data.middle.second.lemma412.extremal.delta_pos
  have qLeAbsorption : data.q ≤
      schedule.outerCutoff.preliminaryReentryAbsorption.delta₀ :=
    hqOuter.trans
      schedule.outerCutoff.outerScaleCeiling_le_preliminaryReentry
  have qLeSchedule : data.q ≤
      schedule.outerCutoff.firstRichSchedule.delta₀ :=
    hqOuter.trans schedule.outerCutoff.outerScaleCeiling_le_firstRich
  have qLtOne : data.q < 1 :=
    qLeAbsorption.trans
      schedule.outerCutoff.preliminaryReentryAbsorption.delta₀_le_tiny
      |>.trans_lt (by norm_num)
  have twiceRootNormalization :
      2 * schedule.outerCutoff.preliminaryRootNormalizationLoss ≤
        schedule.outerCutoff.firstRichSchedule.sourceLoss := by
    rw [schedule.outerCutoff.preliminaryRootNormalizationLoss_eq,
      schedule.outerCutoff.preliminaryStickyLoss_eq]
    have small :=
      schedule.outerCutoff.sampledM8RootLosses
        |>.reentryNormalization_lt_nextSource
    rw [schedule.outerCutoff.sampledM8RootLosses
      |>.reentryNormalizationLoss_eq] at small
    linarith [schedule.outerCutoff.preliminaryStickyLoss_pos,
      schedule.outerCutoff.sampledM8RootLosses.stickyLoss_pos]
  exact (data.outerRoot hqOuter).runGenericFirstRich
    (data.outerPreliminaryOnRoot hqOuter)
    schedule.outerCutoff.preliminaryReentryAbsorption
    schedule.outerCutoff.firstRichSchedule qLeAbsorption qLeSchedule qLtOne
    critical.sigma_pos critical.sigma_lt_one
    (by
      rw [schedule.outerCutoff.preliminaryRootNormalizationLoss_eq]
      exact schedule.outerCutoff.preliminaryStickyLoss_pos)
    twiceRootNormalization
    schedule.outerCutoff.preliminaryProducerLoss_lt_firstSource.le
    (schedule.outerCutoff.preliminaryStickyLoss_pos.trans
      schedule.outerCutoff.preliminaryStickyLoss_lt_planiness |>.trans
        schedule.outerCutoff.planinessLoss_lt_producer)
    rfl schedule.outerCutoff.firstRichSchedule.normalizationLoss_pos
    schedule.outerCutoff.firstRichSchedule.sourceLoss_le_half
    schedule.outerCutoff.initial.sticky_le_power
    schedule.outerCutoff.initial.power_le_one_sub_sticky

/-- Package the normalized q-scale map together with the exact terminal
returned by the outer first-rich call. -/
noncomputable def outerTerminalBundle
    {hqOuter : data.q ≤ schedule.outerCutoff.outerScaleCeiling}
    (first : Proposition63GenericFirstRichBoundaryData
      (reentryLoss := schedule.outerCutoff.firstRichSchedule.sourceLoss)
      (data.outerRoot hqOuter) (data.outerPreliminaryOnRoot hqOuter)
      schedule.outerCutoff.firstRichSchedule) :
    Proposition63M9GenericFirstRichTerminalBundle first.terminal
      (first.normalizedPreliminaryMap data.outerPreliminaryMap)
      (data.outerPreliminary.lipschitz) :=
  Proposition63M9GenericFirstRichTerminalBundle.ofTerminal first.terminal
    (first.normalizedPreliminaryMap data.outerPreliminaryMap)
    data.outerPreliminary.lipschitz
      (data.outerNormalizedPreliminaryMap_lipschitz first)

theorem outerNormalizedMap_cellwise
    {hqOuter : data.q ≤ schedule.outerCutoff.outerScaleCeiling}
    (first : Proposition63GenericFirstRichBoundaryData
      (reentryLoss := schedule.outerCutoff.firstRichSchedule.sourceLoss)
      (data.outerRoot hqOuter) (data.outerPreliminaryOnRoot hqOuter)
      schedule.outerCutoff.firstRichSchedule) :
    ∀ left right,
      wz1PaperGridIndex data.q left = wz1PaperGridIndex data.q right →
        (first.normalizedPreliminaryMap data.outerPreliminaryMap).planeMap left =
          (first.normalizedPreliminaryMap data.outerPreliminaryMap).planeMap
            right :=
  first.normalizedPreliminaryMap_cellwise data.outerPreliminaryMap
    data.outerPreliminaryMap_cellwise

end Proposition63M9RobustInitialPreliminaryData

end Kakeya.Assouad.PureWZ2

end
