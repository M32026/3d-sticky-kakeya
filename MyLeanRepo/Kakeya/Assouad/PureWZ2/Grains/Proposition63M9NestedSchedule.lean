import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustInitialPreliminary

/-!
# Proposition 6.3 M9: nested pre-runtime schedule

The direct robust construction supplies the preliminary local grains for the
first chart.  Therefore its complete loss hierarchy must be chosen inside the
outer hierarchy that will run that chart and the final M8/tail.  Both layers
are frozen before the critical sequence chooses a runtime scale.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

structure Proposition63M9NestedScheduleData
    (sigma outputLoss : ℝ)
    (critical : PureWZ2CriticalPackage sigma) where
  outer : Proposition63M9PreRuntimeHierarchy sigma outputLoss
  outerCutoff : Proposition63M9PreNode3CutoffData outer
  inner : Proposition63M9PreRuntimeHierarchy sigma
    outerCutoff.preliminaryStickyLoss
  innerCutoff : Proposition63M9PreNode3CutoffData inner
  outerRootCutoff : ℝ
  outerRootCutoff_pos : 0 < outerRootCutoff
  outerRootCutoff_le_one : outerRootCutoff ≤ 1
  outer_h_le_scale : ∀ {q : ℝ}, 0 < q → q ≤ outerRootCutoff →
    Real.rpow q (2 / (2 + sigma)) ≤ outerCutoff.scaleCeiling
  outer_h_le_robust : ∀ {q : ℝ}, 0 < q → q ≤ outerRootCutoff →
    Real.rpow q (2 / (2 + sigma)) ≤ outerCutoff.twoCall.rootCutoff

/-- Freeze the outer chart/tail hierarchy first and the direct robust
preliminary hierarchy second.  No runtime radius or family appears in the
result. -/
theorem proposition63_m9_nested_schedule
    {sigma outputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (houtputLoss : 0 < outputLoss) :
    Nonempty (Proposition63M9NestedScheduleData
      sigma outputLoss critical) := by
  rcases proposition63_m9_pre_runtime_hierarchy critical critical.sigma_pos
      critical.sigma_lt_one houtputLoss with ⟨outer⟩
  rcases proposition63_m9_pre_node3_cutoff critical outer with
    ⟨outerCutoff⟩
  rcases proposition63_m9_pre_runtime_hierarchy critical critical.sigma_pos
      critical.sigma_lt_one outerCutoff.preliminaryStickyLoss_pos with
    ⟨inner⟩
  rcases proposition63_m9_pre_node3_cutoff critical inner with
    ⟨innerCutoff⟩
  have hExponentPos : 0 < 2 / (2 + sigma) := by
    exact div_pos (by norm_num) (by linarith [critical.sigma_pos])
  have outerRootThresholdPos :
      0 < min outerCutoff.scaleCeiling outerCutoff.twoCall.rootCutoff :=
    lt_min outerCutoff.scaleCeiling_pos outerCutoff.twoCall.rootCutoff_pos
  rcases pure_wz2_exists_delta₀_rpow_le
      outerRootThresholdPos hExponentPos with
    ⟨outerRootCutoff, outerRootCutoffPos, outerRootCutoffOne,
      outerRootCutoffPower⟩
  exact ⟨{
    outer := outer
    outerCutoff := outerCutoff
    inner := inner
    innerCutoff := innerCutoff
    outerRootCutoff := outerRootCutoff
    outerRootCutoff_pos := outerRootCutoffPos
    outerRootCutoff_le_one := outerRootCutoffOne
    outer_h_le_scale := fun {q} qPos qLe =>
      (outerRootCutoffPower q qPos qLe).trans (min_le_left _ _)
    outer_h_le_robust := fun {q} qPos qLe =>
      (outerRootCutoffPower q qPos qLe).trans (min_le_right _ _)
  }⟩

namespace Proposition63M9NestedScheduleData

variable {sigma outputLoss : ℝ}
    {critical : PureWZ2CriticalPackage sigma}
    (schedule : Proposition63M9NestedScheduleData
      sigma outputLoss critical)

theorem inner_preGrain_lt_outer_preliminarySticky :
    schedule.inner.preGrainLoss <
      schedule.outerCutoff.preliminaryStickyLoss :=
  schedule.inner.preGrain_lt_output

theorem inner_preGrain_lt_outer_preliminaryProducer :
    schedule.inner.preGrainLoss <
      schedule.outerCutoff.preliminaryProducerLoss :=
  schedule.inner_preGrain_lt_outer_preliminarySticky.trans <|
    schedule.outerCutoff.preliminaryStickyLoss_lt_planiness.trans
      schedule.outerCutoff.planinessLoss_lt_producer

theorem inner_preGrain_lt_outer_local :
    schedule.inner.preGrainLoss < schedule.outerCutoff.initial.localLoss :=
  schedule.inner_preGrain_lt_outer_preliminaryProducer.trans_le <| by
    rw [schedule.outerCutoff.preliminaryProducerLoss_eq]
    have sourceLtSticky :=
      schedule.outerCutoff.firstRichSchedule.sourceLoss_le_half.trans_lt <|
        (half_lt_self
          schedule.outerCutoff.firstRichSchedule.normalizationLoss_pos).trans <|
            schedule.outerCutoff.firstRichSchedule.normalizationLoss_lt_output
    linarith [schedule.outerCutoff.firstRichSchedule.sourceLoss_pos,
      schedule.outerCutoff.initial.sticky_lt_local]

/-- Exact form of the first-chart fine radius. -/
theorem firstChart_h_eq_root_power
    {q : ℝ} (hsigma : 0 < sigma) (hq : 0 < q)
    (power : Proposition63PowerScale q sigma) :
    power.h = Real.rpow q (2 / (2 + sigma)) := by
  have DeltaPos : 0 < power.Delta := by
    rw [power.Delta_eq]
    exact Real.rpow_pos_of_pos hq _
  rw [power.h_eq, power.Delta_eq]
  have quotient :
      q / Real.rpow q (sigma / (2 + sigma)) =
        Real.rpow q (1 - sigma / (2 + sigma)) := by
    calc
      q / Real.rpow q (sigma / (2 + sigma)) =
          Real.rpow q 1 / Real.rpow q (sigma / (2 + sigma)) := by simp
      _ = Real.rpow q (1 - sigma / (2 + sigma)) :=
        (Real.rpow_sub hq 1 (sigma / (2 + sigma))).symm
  rw [quotient]
  congr 1
  field_simp [show 2 + sigma ≠ 0 by
    linarith [hsigma]]
  ring

/-- The nested pre-runtime cutoff pulls the outer robust root ceiling back
through the exact first-chart ratio. -/
theorem firstChart_h_le_outer_scale
    {q : ℝ} (hq : 0 < q) (hqCutoff : q ≤ schedule.outerRootCutoff)
    (power : Proposition63PowerScale q sigma) :
    power.h ≤ schedule.outerCutoff.scaleCeiling := by
  rw [firstChart_h_eq_root_power schedule.outerCutoff.twoCall.scale.sigma_pos
    hq power]
  exact schedule.outer_h_le_scale hq hqCutoff

theorem firstChart_h_le_outer_robust
    {q : ℝ} (hq : 0 < q) (hqCutoff : q ≤ schedule.outerRootCutoff)
    (power : Proposition63PowerScale q sigma) :
    power.h ≤ schedule.outerCutoff.twoCall.rootCutoff := by
  rw [firstChart_h_eq_root_power schedule.outerCutoff.twoCall.scale.sigma_pos
    hq power]
  exact schedule.outer_h_le_robust hq hqCutoff

theorem inner_second_coarse_source_le_outer_root_source
    {r : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma
      schedule.innerCutoff.twoCall.schedule.first.sourceLoss r}
    {root : Proposition63RootNormalizationData
      (outputLoss :=
        schedule.innerCutoff.twoCall.schedule.first.normalizationLoss)
      source 0
      (schedule.innerCutoff.twoCall.schedule.second.sourceLoss / 8)}
    {hr : 0 < r} {hrRobust : r ≤ schedule.innerCutoff.twoCall.rootCutoff}
    (middle : Proposition63M9RobustMiddleData schedule.innerCutoff root
      hr hrRobust) :
    middle.secondTerminal.coarseSourceLoss ≤
      schedule.outerCutoff.preliminaryRootSourceLoss := by
  have twiceStickyLtOutput :
      2 * schedule.inner.stickyLoss <
        schedule.outerCutoff.preliminaryStickyLoss := by
    linarith [schedule.inner.two_sticky_le_lemma44,
      schedule.inner.lemma44_lt_lemma47,
      schedule.inner.lemma47Loss_lt_preGrain,
      schedule.inner.preGrain_lt_output]
  rw [schedule.outerCutoff.preliminaryRootSourceLoss_eq]
  have coarseLe : middle.secondTerminal.coarseSourceLoss ≤
      schedule.inner.stickyLoss / 3 := by
    linarith [middle.secondTerminal.coarseSourceLoss_budget]
  have stickyThirdLt : schedule.inner.stickyLoss / 3 <
      schedule.outerCutoff.preliminaryStickyLoss / 2 := by
    linarith [schedule.inner.sticky_pos]
  exact coarseLe.trans stickyThirdLt.le

theorem inner_second_coarse_normalization_le_outer_root_normalization
    {r : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma
      schedule.innerCutoff.twoCall.schedule.first.sourceLoss r}
    {root : Proposition63RootNormalizationData
      (outputLoss :=
        schedule.innerCutoff.twoCall.schedule.first.normalizationLoss)
      source 0
      (schedule.innerCutoff.twoCall.schedule.second.sourceLoss / 8)}
    {hr : 0 < r} {hrRobust : r ≤ schedule.innerCutoff.twoCall.rootCutoff}
    (middle : Proposition63M9RobustMiddleData schedule.innerCutoff root
      hr hrRobust) :
    middle.secondTerminal.coarseNormalizationLoss ≤
      schedule.outerCutoff.preliminaryRootNormalizationLoss := by
  have twiceStickyLtOutput :
      2 * schedule.inner.stickyLoss <
        schedule.outerCutoff.preliminaryStickyLoss := by
    linarith [schedule.inner.two_sticky_le_lemma44,
      schedule.inner.lemma44_lt_lemma47,
      schedule.inner.lemma47Loss_lt_preGrain,
      schedule.inner.preGrain_lt_output]
  rw [middle.secondTerminal.coarseNormalizationLoss_eq,
    schedule.outerCutoff.preliminaryRootNormalizationLoss_eq]
  have coarseLe : middle.secondTerminal.coarseSourceLoss ≤
      schedule.inner.stickyLoss / 3 := by
    linarith [middle.secondTerminal.coarseSourceLoss_budget]
  have normalizationLe : (7 / 2 : ℝ) *
      middle.secondTerminal.coarseSourceLoss ≤
      (7 / 6 : ℝ) * schedule.inner.stickyLoss := by
    nlinarith
  have stickyBound : (7 / 6 : ℝ) * schedule.inner.stickyLoss <
      schedule.outerCutoff.preliminaryStickyLoss := by
    linarith [schedule.inner.sticky_pos,
      schedule.outerCutoff.preliminaryStickyLoss_pos]
  exact normalizationLe.trans stickyBound.le

end Proposition63M9NestedScheduleData

end Kakeya.Assouad.PureWZ2

end
