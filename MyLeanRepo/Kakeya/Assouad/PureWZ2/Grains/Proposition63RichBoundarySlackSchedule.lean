import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichStickyKernel

/-!
# A rich Proposition 6.3 schedule with boundary slack

The ordinary rich-kernel schedule only records that its normalization loss is
smaller than its output loss.  Boundary pruning needs the quantitative gap
`4 * normalizationLoss < outputLoss`.  We obtain it without changing any
runtime witness: run the rich kernel at one eighth of the requested loss and
then weaken the complete rich terminal package to the requested loss.
-/

open scoped ENNReal NNReal

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- Increase the loss index of a rich terminal output while preserving its
terminal multiplicity certificate and exact coarse re-entry witness. -/
noncomputable def Proposition63RichTerminalStickyData.mono_loss
    {delta sigma firstLoss secondLoss sourceLoss normalizationLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := firstLoss) croppedShading reentry rho)
    (loss_le : firstLoss ≤ secondLoss) :
    Proposition63RichTerminalStickyData
      (outputLoss := secondLoss) croppedShading reentry rho := by
  let weakened : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := secondLoss) croppedShading rho 61 :=
    PureWZ2PropStickyData.mono_loss rich.data loss_le
  refine {
    data := weakened
    coarse_midpoint_local := rich.coarse_midpoint_local
    coarseSourceLoss := rich.coarseSourceLoss
    coarseNormalizationLoss := rich.coarseNormalizationLoss
    coarseSourceLoss_pos := rich.coarseSourceLoss_pos
    coarseNormalizationLoss_pos := rich.coarseNormalizationLoss_pos
    coarseSourceLoss_budget := rich.coarseSourceLoss_budget.trans loss_le
    coarseNormalizationLoss_eq := rich.coarseNormalizationLoss_eq
    coarseReentry := ?_
    coarse_reentry_axial_window_of_margin := ?_
    terminalLoss := rich.terminalLoss
    terminalLoss_pos := rich.terminalLoss_pos
    terminalLoss_le_output := rich.terminalLoss_le_output.trans loss_le
    terminal := by
      simpa only [weakened, PureWZ2PropStickyData.mono_loss]
        using rich.terminal
    canonical_rescaled_fiber := fun parent =>
      (rich.canonical_rescaled_fiber parent).mono_loss loss_le
    canonical_rescaled_fiber_unit_ball := fun parent => by
      simpa [WZ2PaperPureRescaledFullFiberOutput.mono_loss] using
        rich.canonical_rescaled_fiber_unit_ball parent
    terminal_fiber_mass_lower := ?_
    terminal_regularity_bound := ?_
    terminal_cellMass_power_lower := by
      change Kakeya.realRpowENN rho.1 3 *
          Kakeya.realRpowENN (delta / rho.1)
            (sigma + 2 * rich.terminalLoss) ≤
        rich.terminal.balanced.cellMass
      exact rich.terminal_cellMass_power_lower
    cross_degree := ?_
    total_mass_retention := ?_
  }
  · simpa only [weakened, PureWZ2PropStickyData.mono_loss]
      using rich.coarseReentry
  · intro rootAxialMargin index point pointMem
    simpa only [weakened, PureWZ2PropStickyData.mono_loss]
      using rich.coarse_reentry_axial_window_of_margin
        rootAxialMargin index point pointMem
  · intro parent
    have powerLe : Kakeya.realRpowENN rho.1 secondLoss ≤
        Kakeya.realRpowENN rho.1 firstLoss :=
      pure_wz2_rpowENN_antitone rich.data.coarse_extremal.delta_pos
        rich.data.coarse_extremal.delta_le_one loss_le
    exact (mul_le_mul_right' (mul_le_mul_right' powerLe _) _).trans
      (rich.terminal_fiber_mass_lower parent)
  · change (rich.terminal.regularity : ENNReal) ≤
      Prop62PaperAudit.V4.logarithmicLoss delta ^ 10
    exact rich.terminal_regularity_bound
  · have rho_le_one : rho.1 ≤ 1 := rich.data.coarse_extremal.delta_le_one
    have power_mono :
        Kakeya.realRpowENN rho.1 secondLoss ≤
          Kakeya.realRpowENN rho.1 firstLoss :=
      pure_wz2_rpowENN_antitone
        rich.data.coarse_extremal.delta_pos rho_le_one loss_le
    calc
      Kakeya.realRpowENN rho.1 secondLoss *
            (rich.terminal.regularity * rich.terminal.muCoarse : ℕ)
          ≤ Kakeya.realRpowENN rho.1 firstLoss *
              (rich.terminal.regularity * rich.terminal.muCoarse : ℕ) := by
            gcongr
      _ ≤ rich.terminal.fineDegreeFloor := rich.cross_degree
  · simpa only [weakened, PureWZ2PropStickyData.mono_loss]
      using rich.total_mass_retention

/-- Increase the public loss of a complete rich schedule.  Runtime scale
windows are restricted using `delta ≤ delta₀ ≤ 1`, and the resulting rich
terminal output is transported by `Proposition63RichTerminalStickyData.mono_loss`. -/
noncomputable def Proposition63RichStickyKernelScheduleData.mono_loss
    {sigma firstLoss secondLoss : ℝ}
    (schedule : Proposition63RichStickyKernelScheduleData sigma firstLoss)
    (loss_le : firstLoss ≤ secondLoss) :
    Proposition63RichStickyKernelScheduleData sigma secondLoss where
  sourceLoss := schedule.sourceLoss
  normalizationLoss := schedule.normalizationLoss
  sourceLoss_eq := schedule.sourceLoss_eq
  delta₀ := schedule.delta₀
  sourceLoss_pos := schedule.sourceLoss_pos
  normalizationLoss_pos := schedule.normalizationLoss_pos
  sourceLoss_le_half := schedule.sourceLoss_le_half
  normalizationLoss_lt_output :=
    schedule.normalizationLoss_lt_output.trans_le loss_le
  delta₀_pos := schedule.delta₀_pos
  delta₀_le_one := schedule.delta₀_le_one
  runTerminal := by
    intro delta delta_pos delta_le croppedFamily croppedShading
      normalizationExponent reentry rho rho_lower rho_upper
    have delta_le_one : delta ≤ 1 := delta_le.trans schedule.delta₀_le_one
    have first_lower : Real.rpow delta (1 - firstLoss) ≤ rho.1 :=
      (Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one
        (by linarith)).trans rho_lower
    have first_upper : rho.1 ≤ Real.rpow delta firstLoss :=
      rho_upper.trans <|
        Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one loss_le
    rcases schedule.runTerminal delta delta_pos delta_le croppedFamily
        croppedShading reentry rho first_lower first_upper with ⟨rich⟩
    exact ⟨rich.mono_loss loss_le⟩
  runPlain := by
    intro delta delta_pos delta_le croppedFamily croppedShading
      normalizationExponent reentry rho rho_lower rho_upper
    have delta_le_one : delta ≤ 1 := delta_le.trans schedule.delta₀_le_one
    have first_lower : Real.rpow delta (1 - firstLoss) ≤ rho.1 :=
      (Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one
        (by linarith)).trans rho_lower
    have first_upper : rho.1 ≤ Real.rpow delta firstLoss :=
      rho_upper.trans <|
        Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one loss_le
    rcases schedule.runTerminal delta delta_pos delta_le croppedFamily
        croppedShading reentry rho first_lower first_upper with ⟨rich⟩
    exact ⟨(rich.mono_loss loss_le).data⟩
  run := by
    intro delta delta_pos delta_le croppedFamily croppedShading
      normalizationExponent reentry axial_window rho rho_lower rho_upper
    have delta_le_one : delta ≤ 1 := delta_le.trans schedule.delta₀_le_one
    have first_lower : Real.rpow delta (1 - firstLoss) ≤ rho.1 :=
      (Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one
        (by linarith)).trans rho_lower
    have first_upper : rho.1 ≤ Real.rpow delta firstLoss :=
      rho_upper.trans <|
        Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one loss_le
    rcases schedule.runTerminal delta delta_pos delta_le croppedFamily
        croppedShading reentry rho first_lower first_upper with ⟨rich⟩
    exact ⟨(rich.mono_loss loss_le).toReentrant axial_window⟩

/-- The unweakened rich kernel behind a public-output schedule.  The public
schedule is obtained only by monotonicity in the output loss, so its source
and normalization losses are definitionally the ones selected by the hidden
kernel.  Retaining this witness prevents later quantitative arguments from
mistaking the public iterator loss for the loss used by the analytic kernel. -/
structure Proposition63RichInternalKernelScheduleData
    (sigma publicLoss discreteBudget tailBudget sigmaBudget : ℝ)
    (publicSchedule :
      Proposition63RichStickyKernelScheduleData sigma publicLoss) where
  internalLoss : ℝ
  internalSchedule :
    Proposition63RichStickyKernelScheduleData sigma internalLoss
  internalLoss_pos : 0 < internalLoss
  internalLoss_lt_public : internalLoss < publicLoss
  internalLoss_lt_discrete : internalLoss < discreteBudget
  internalLoss_lt_tail : internalLoss < tailBudget
  internalLoss_lt_sigma : internalLoss < sigmaBudget
  internal_boundary_slack :
    4 * internalSchedule.normalizationLoss < internalLoss
  internalLoss_le_public : internalLoss ≤ publicLoss
  public_eq :
    publicSchedule = internalSchedule.mono_loss internalLoss_le_public

/-- A public-output rich schedule whose internal kernel loss is simultaneously
small relative to the discrete, tail, and sigma budgets.  None of these
auxiliary budgets restricts the public output index. -/
structure Proposition63RichBudgetedBoundarySlackScheduleData
    (sigma outputLoss discreteBudget tailBudget sigmaBudget : ℝ) where
  base : Proposition63RichStickyKernelScheduleData sigma outputLoss
  kernel : Proposition63RichInternalKernelScheduleData
    sigma outputLoss discreteBudget tailBudget sigmaBudget base
  output_boundary_slack : 4 * base.normalizationLoss < outputLoss
  discrete_boundary_slack : 4 * base.normalizationLoss < discreteBudget
  normalization_lt_discrete_half :
    base.normalizationLoss < discreteBudget / 2
  normalization_lt_tail : base.normalizationLoss < tailBudget
  tail_boundary_slack : 4 * base.normalizationLoss < tailBudget
  normalization_lt_sigma : base.normalizationLoss < sigmaBudget

/-- Run the rich kernel at one eighth of the minimum of all four positive
budgets, then transport the complete dependent output to the public loss. -/
theorem proposition63_rich_budgeted_boundary_slack_schedule
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss discreteBudget tailBudget sigmaBudget : ℝ)
    (outputLoss_pos : 0 < outputLoss)
    (outputLoss_le_one : outputLoss ≤ 1)
    (discreteBudget_pos : 0 < discreteBudget)
    (tailBudget_pos : 0 < tailBudget)
    (sigmaBudget_pos : 0 < sigmaBudget) :
    Nonempty (Proposition63RichBudgetedBoundarySlackScheduleData
      sigma outputLoss discreteBudget tailBudget sigmaBudget) := by
  let internalBudget : ℝ :=
    min outputLoss (min discreteBudget (min tailBudget sigmaBudget))
  let innerOutputLoss : ℝ := internalBudget / 8
  let hiddenOutputLoss : ℝ := innerOutputLoss / 8
  have internal_pos : 0 < internalBudget := by
    dsimp only [internalBudget]
    exact lt_min outputLoss_pos <|
      lt_min discreteBudget_pos <| lt_min tailBudget_pos sigmaBudget_pos
  have internal_le_output : internalBudget ≤ outputLoss := by
    dsimp only [internalBudget]
    exact min_le_left _ _
  have internal_le_discrete : internalBudget ≤ discreteBudget := by
    dsimp only [internalBudget]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have internal_le_tail : internalBudget ≤ tailBudget := by
    dsimp only [internalBudget]
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have internal_le_sigma : internalBudget ≤ sigmaBudget := by
    dsimp only [internalBudget]
    exact (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _)
  have inner_pos : 0 < innerOutputLoss := by
    dsimp only [innerOutputLoss]
    positivity
  have inner_le_output : innerOutputLoss ≤ outputLoss := by
    dsimp only [innerOutputLoss]
    linarith
  have inner_le_one : innerOutputLoss ≤ 1 := inner_le_output.trans outputLoss_le_one
  have hidden_pos : 0 < hiddenOutputLoss := by
    dsimp only [hiddenOutputLoss]
    positivity
  have hidden_le_inner : hiddenOutputLoss ≤ innerOutputLoss := by
    dsimp only [hiddenOutputLoss]
    linarith
  have hidden_le_one : hiddenOutputLoss ≤ 1 :=
    hidden_le_inner.trans inner_le_one
  rcases proposition63_rich_sticky_kernel sigma critical hiddenOutputLoss
      hidden_pos hidden_le_one with ⟨hidden⟩
  let inner := hidden.mono_loss hidden_le_inner
  let base := inner.mono_loss inner_le_output
  have normalization_lt_hidden := hidden.normalizationLoss_lt_output
  have output_slack : 4 * base.normalizationLoss < outputLoss := by
    dsimp only [base, Proposition63RichStickyKernelScheduleData.mono_loss]
    dsimp only [base, inner, Proposition63RichStickyKernelScheduleData.mono_loss]
    dsimp only [hiddenOutputLoss, innerOutputLoss] at normalization_lt_hidden
    linarith
  have discrete_slack : 4 * base.normalizationLoss < discreteBudget := by
    dsimp only [base, Proposition63RichStickyKernelScheduleData.mono_loss]
    dsimp only [base, inner, Proposition63RichStickyKernelScheduleData.mono_loss]
    dsimp only [hiddenOutputLoss, innerOutputLoss] at normalization_lt_hidden
    linarith
  have tail_slack : 4 * base.normalizationLoss < tailBudget := by
    dsimp only [base, Proposition63RichStickyKernelScheduleData.mono_loss]
    dsimp only [base, inner, Proposition63RichStickyKernelScheduleData.mono_loss]
    dsimp only [hiddenOutputLoss, innerOutputLoss] at normalization_lt_hidden
    linarith
  have norm_lt_sigma : base.normalizationLoss < sigmaBudget := by
    dsimp only [base, Proposition63RichStickyKernelScheduleData.mono_loss]
    dsimp only [base, inner, Proposition63RichStickyKernelScheduleData.mono_loss]
    dsimp only [hiddenOutputLoss, innerOutputLoss] at normalization_lt_hidden
    linarith
  exact ⟨{
    base := base
    kernel := {
      internalLoss := innerOutputLoss
      internalSchedule := inner
      internalLoss_pos := inner_pos
      internalLoss_lt_public := by
        dsimp only [innerOutputLoss]
        nlinarith
      internalLoss_lt_discrete := by
        dsimp only [innerOutputLoss]
        nlinarith
      internalLoss_lt_tail := by
        dsimp only [innerOutputLoss]
        nlinarith
      internalLoss_lt_sigma := by
        dsimp only [innerOutputLoss]
        nlinarith
      internal_boundary_slack := by
        dsimp only [inner, Proposition63RichStickyKernelScheduleData.mono_loss]
        dsimp only [hiddenOutputLoss] at normalization_lt_hidden
        linarith
      internalLoss_le_public := inner_le_output
      public_eq := rfl
    }
    output_boundary_slack := output_slack
    discrete_boundary_slack := discrete_slack
    normalization_lt_discrete_half := by
      linarith [base.normalizationLoss_pos]
    normalization_lt_tail := by
      linarith [base.normalizationLoss_pos, tail_slack]
    tail_boundary_slack := tail_slack
    normalization_lt_sigma := norm_lt_sigma
  }⟩

/-- A rich kernel schedule carrying the strict loss gap needed by boundary
pruning.  The base schedule still exposes all three runtime entry points. -/
structure Proposition63RichBoundarySlackScheduleData
    (sigma outputLoss : ℝ) where
  base : Proposition63RichStickyKernelScheduleData sigma outputLoss
  boundary_slack : 4 * base.normalizationLoss < outputLoss

/-- Construct a boundary-slack schedule by running the kernel at one eighth
of the public loss and transporting every rich runtime output monotonically. -/
theorem proposition63_rich_boundary_slack_schedule
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ)
    (outputLoss_pos : 0 < outputLoss)
    (outputLoss_le_one : outputLoss ≤ 1) :
    Nonempty (Proposition63RichBoundarySlackScheduleData
      sigma outputLoss) := by
  let innerOutputLoss : ℝ := outputLoss / 8
  have inner_pos : 0 < innerOutputLoss := by
    dsimp [innerOutputLoss]
    positivity
  have inner_le_one : innerOutputLoss ≤ 1 := by
    dsimp [innerOutputLoss]
    linarith
  have inner_le_output : innerOutputLoss ≤ outputLoss := by
    dsimp [innerOutputLoss]
    linarith
  rcases proposition63_rich_sticky_kernel sigma critical innerOutputLoss
      inner_pos inner_le_one with ⟨inner⟩
  let base : Proposition63RichStickyKernelScheduleData sigma outputLoss := {
    sourceLoss := inner.sourceLoss
    normalizationLoss := inner.normalizationLoss
    sourceLoss_eq := inner.sourceLoss_eq
    delta₀ := inner.delta₀
    sourceLoss_pos := inner.sourceLoss_pos
    normalizationLoss_pos := inner.normalizationLoss_pos
    sourceLoss_le_half := inner.sourceLoss_le_half
    normalizationLoss_lt_output := inner.normalizationLoss_lt_output.trans_le
      inner_le_output
    delta₀_pos := inner.delta₀_pos
    delta₀_le_one := inner.delta₀_le_one
    runTerminal := by
      intro delta delta_pos delta_le croppedFamily croppedShading
        normalizationExponent reentry rho rho_lower rho_upper
      have delta_le_one : delta ≤ 1 := delta_le.trans inner.delta₀_le_one
      have inner_lower : Real.rpow delta (1 - innerOutputLoss) ≤ rho.1 :=
        (Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one
          (by linarith)).trans rho_lower
      have inner_upper : rho.1 ≤ Real.rpow delta innerOutputLoss :=
        rho_upper.trans <|
          Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one
            inner_le_output
      rcases inner.runTerminal delta delta_pos delta_le croppedFamily
          croppedShading reentry rho inner_lower inner_upper with ⟨rich⟩
      exact ⟨rich.mono_loss inner_le_output⟩
    runPlain := by
      intro delta delta_pos delta_le croppedFamily croppedShading
        normalizationExponent reentry rho rho_lower rho_upper
      have delta_le_one : delta ≤ 1 := delta_le.trans inner.delta₀_le_one
      have inner_lower : Real.rpow delta (1 - innerOutputLoss) ≤ rho.1 :=
        (Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one
          (by linarith)).trans rho_lower
      have inner_upper : rho.1 ≤ Real.rpow delta innerOutputLoss :=
        rho_upper.trans <|
          Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one
            inner_le_output
      rcases inner.runTerminal delta delta_pos delta_le croppedFamily
          croppedShading reentry rho inner_lower inner_upper with ⟨rich⟩
      exact ⟨(rich.mono_loss inner_le_output).data⟩
    run := by
      intro delta delta_pos delta_le croppedFamily croppedShading
        normalizationExponent reentry axial_window rho rho_lower rho_upper
      have delta_le_one : delta ≤ 1 := delta_le.trans inner.delta₀_le_one
      have inner_lower : Real.rpow delta (1 - innerOutputLoss) ≤ rho.1 :=
        (Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one
          (by linarith)).trans rho_lower
      have inner_upper : rho.1 ≤ Real.rpow delta innerOutputLoss :=
        rho_upper.trans <|
          Real.rpow_le_rpow_of_exponent_ge delta_pos delta_le_one
            inner_le_output
      rcases inner.runTerminal delta delta_pos delta_le croppedFamily
          croppedShading reentry rho inner_lower inner_upper with ⟨rich⟩
      exact ⟨(rich.mono_loss inner_le_output).toReentrant axial_window⟩
  }
  refine ⟨{
    base := base
    boundary_slack := ?_
  }⟩
  dsimp [base]
  have normalization_lt_inner := inner.normalizationLoss_lt_output
  dsimp [innerOutputLoss] at normalization_lt_inner
  linarith

/-- Four rich calls in their backward dependency order, with the two
normalization gaps needed by the robust boundary-pruning calls recorded as
consequences of the schedules that actually produced the third and fourth
runtime outputs. -/
structure Proposition63RichFourCallBoundarySlackScheduleData
    (sigma outputLoss : ℝ) where
  base : Proposition63RichFourCallScheduleData sigma outputLoss
  third_boundary_slack :
    4 * base.third.normalizationLoss < base.thirdOutputLoss
  fourth_boundary_slack :
    4 * base.fourth.normalizationLoss < outputLoss

/-- Construct the four-call schedule backward.  The fourth schedule is first
chosen with slack at `outputLoss`; the third schedule is then chosen with
slack at the exact loss `fourth.sourceLoss / 16`.  The earlier two calls use
the ordinary rich kernel because no robust boundary receipt consumes their
normalization losses. -/
theorem proposition63_rich_four_call_boundary_slack_schedule
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ)
    (outputLoss_pos : 0 < outputLoss)
    (outputLoss_le_one : outputLoss ≤ 1) :
    Nonempty (Proposition63RichFourCallBoundarySlackScheduleData
      sigma outputLoss) := by
  rcases proposition63_rich_boundary_slack_schedule sigma critical outputLoss
      outputLoss_pos outputLoss_le_one with ⟨fourthSlack⟩
  let fourth := fourthSlack.base
  let thirdOutputLoss : ℝ := fourth.sourceLoss / 16
  have thirdOutputLoss_pos : 0 < thirdOutputLoss := by
    dsimp only [thirdOutputLoss]
    linarith [fourth.sourceLoss_pos]
  have thirdOutputLoss_lt_fourthSource :
      thirdOutputLoss < fourth.sourceLoss := by
    dsimp only [thirdOutputLoss]
    linarith [fourth.sourceLoss_pos]
  have thirdOutputLoss_le_one : thirdOutputLoss ≤ 1 := by
    dsimp only [thirdOutputLoss]
    linarith [fourth.sourceLoss_le_half,
      fourth.normalizationLoss_lt_output]
  rcases proposition63_rich_boundary_slack_schedule sigma critical
      thirdOutputLoss thirdOutputLoss_pos thirdOutputLoss_le_one with
    ⟨thirdSlack⟩
  let third := thirdSlack.base
  let secondOutputLoss : ℝ := third.sourceLoss / 16
  have secondOutputLoss_pos : 0 < secondOutputLoss := by
    dsimp only [secondOutputLoss]
    linarith [third.sourceLoss_pos]
  have secondOutputLoss_lt_thirdSource :
      secondOutputLoss < third.sourceLoss := by
    dsimp only [secondOutputLoss]
    linarith [third.sourceLoss_pos]
  have secondOutputLoss_le_one : secondOutputLoss ≤ 1 := by
    dsimp only [secondOutputLoss]
    linarith [third.sourceLoss_le_half, third.normalizationLoss_lt_output]
  rcases proposition63_rich_sticky_kernel sigma critical secondOutputLoss
      secondOutputLoss_pos secondOutputLoss_le_one with ⟨second⟩
  let firstOutputLoss : ℝ := second.sourceLoss / 16
  have firstOutputLoss_pos : 0 < firstOutputLoss := by
    dsimp only [firstOutputLoss]
    linarith [second.sourceLoss_pos]
  have firstOutputLoss_lt_secondSource :
      firstOutputLoss < second.sourceLoss := by
    dsimp only [firstOutputLoss]
    linarith [second.sourceLoss_pos]
  have firstOutputLoss_le_one : firstOutputLoss ≤ 1 := by
    dsimp only [firstOutputLoss]
    linarith [second.sourceLoss_le_half, second.normalizationLoss_lt_output]
  rcases proposition63_rich_sticky_kernel sigma critical firstOutputLoss
      firstOutputLoss_pos firstOutputLoss_le_one with ⟨first⟩
  let base : Proposition63RichFourCallScheduleData sigma outputLoss := {
    fourth := fourth
    thirdOutputLoss := thirdOutputLoss
    thirdOutputLoss_eq := rfl
    thirdOutputLoss_pos := thirdOutputLoss_pos
    thirdOutputLoss_lt_fourthSource := thirdOutputLoss_lt_fourthSource
    third := third
    secondOutputLoss := secondOutputLoss
    secondOutputLoss_eq := rfl
    secondOutputLoss_pos := secondOutputLoss_pos
    secondOutputLoss_lt_thirdSource := secondOutputLoss_lt_thirdSource
    second := second
    firstOutputLoss := firstOutputLoss
    firstOutputLoss_eq := rfl
    firstOutputLoss_pos := firstOutputLoss_pos
    firstOutputLoss_lt_secondSource := firstOutputLoss_lt_secondSource
    first := first
  }
  refine ⟨{
    base := base
    third_boundary_slack := ?_
    fourth_boundary_slack := ?_
  }⟩
  · simpa only [base, third] using thirdSlack.boundary_slack
  · simpa only [base, fourth] using fourthSlack.boundary_slack

/-- A four-call schedule whose public terminal loss is unchanged while its
last two kernels are selected inside independent discrete, tail, and sigma
budgets. -/
structure Proposition63RichFourCallBudgetedBoundarySlackScheduleData
    (sigma outputLoss discreteBudget tailBudget sigmaBudget : ℝ) where
  base : Proposition63RichFourCallScheduleData sigma outputLoss
  fourthKernel : Proposition63RichInternalKernelScheduleData
    sigma outputLoss discreteBudget tailBudget sigmaBudget base.fourth
  thirdOutputLoss_le_discrete : base.thirdOutputLoss ≤ discreteBudget
  secondOutputLoss_le_discrete : base.secondOutputLoss ≤ discreteBudget
  third_boundary_slack :
    4 * base.third.normalizationLoss < base.thirdOutputLoss
  fourth_boundary_slack :
    4 * base.fourth.normalizationLoss < outputLoss
  third_normalization_lt_discrete_half :
    base.third.normalizationLoss < discreteBudget / 2
  fourth_normalization_lt_discrete_half :
    base.fourth.normalizationLoss < discreteBudget / 2
  fourth_normalization_lt_tail :
    base.fourth.normalizationLoss < tailBudget
  fourth_normalization_lt_sigma :
    base.fourth.normalizationLoss < sigmaBudget
  fourth_tail_boundary_slack :
    4 * base.fourth.normalizationLoss < tailBudget

/-- Backward construction of the budgeted four-call schedule.  The public
fourth output remains exactly `outputLoss`; only the hidden kernel loss is
forced below the auxiliary budgets. -/
theorem proposition63_rich_four_call_budgeted_boundary_slack_schedule
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss discreteBudget tailBudget sigmaBudget : ℝ)
    (outputLoss_pos : 0 < outputLoss)
    (outputLoss_le_one : outputLoss ≤ 1)
    (discreteBudget_pos : 0 < discreteBudget)
    (tailBudget_pos : 0 < tailBudget)
    (sigmaBudget_pos : 0 < sigmaBudget) :
    Nonempty (Proposition63RichFourCallBudgetedBoundarySlackScheduleData
      sigma outputLoss discreteBudget tailBudget sigmaBudget) := by
  rcases proposition63_rich_budgeted_boundary_slack_schedule
      sigma critical outputLoss discreteBudget tailBudget sigmaBudget
      outputLoss_pos outputLoss_le_one discreteBudget_pos tailBudget_pos
      sigmaBudget_pos with ⟨fourthBudgeted⟩
  let fourth := fourthBudgeted.base
  let thirdOutputLoss : ℝ := fourth.sourceLoss / 16
  have thirdOutputLoss_pos : 0 < thirdOutputLoss := by
    dsimp only [thirdOutputLoss]
    linarith [fourth.sourceLoss_pos]
  have thirdOutputLoss_lt_fourthSource :
      thirdOutputLoss < fourth.sourceLoss := by
    dsimp only [thirdOutputLoss]
    linarith [fourth.sourceLoss_pos]
  have thirdOutputLoss_le_one : thirdOutputLoss ≤ 1 := by
    dsimp only [thirdOutputLoss]
    linarith [fourth.sourceLoss_le_half,
      fourth.normalizationLoss_lt_output]
  have thirdOutputLoss_le_discrete : thirdOutputLoss ≤ discreteBudget := by
    dsimp only [thirdOutputLoss]
    have fourthNormDiscrete :=
      fourthBudgeted.normalization_lt_discrete_half
    linarith [fourth.sourceLoss_le_half, fourth.sourceLoss_pos]
  rcases proposition63_rich_budgeted_boundary_slack_schedule
      sigma critical thirdOutputLoss discreteBudget tailBudget sigmaBudget
      thirdOutputLoss_pos thirdOutputLoss_le_one discreteBudget_pos
      tailBudget_pos sigmaBudget_pos with ⟨thirdBudgeted⟩
  let third := thirdBudgeted.base
  let secondOutputLoss : ℝ := third.sourceLoss / 16
  have secondOutputLoss_pos : 0 < secondOutputLoss := by
    dsimp only [secondOutputLoss]
    linarith [third.sourceLoss_pos]
  have secondOutputLoss_lt_thirdSource :
      secondOutputLoss < third.sourceLoss := by
    dsimp only [secondOutputLoss]
    linarith [third.sourceLoss_pos]
  have secondOutputLoss_le_one : secondOutputLoss ≤ 1 := by
    dsimp only [secondOutputLoss]
    linarith [third.sourceLoss_le_half, third.normalizationLoss_lt_output]
  have secondOutputLoss_le_discrete : secondOutputLoss ≤ discreteBudget := by
    dsimp only [secondOutputLoss]
    linarith [third.sourceLoss_pos, secondOutputLoss_lt_thirdSource,
      thirdOutputLoss_le_discrete, third.sourceLoss_le_half,
      third.normalizationLoss_lt_output]
  rcases proposition63_rich_sticky_kernel sigma critical secondOutputLoss
      secondOutputLoss_pos secondOutputLoss_le_one with ⟨second⟩
  let firstOutputLoss : ℝ := second.sourceLoss / 16
  have firstOutputLoss_pos : 0 < firstOutputLoss := by
    dsimp only [firstOutputLoss]
    linarith [second.sourceLoss_pos]
  have firstOutputLoss_lt_secondSource :
      firstOutputLoss < second.sourceLoss := by
    dsimp only [firstOutputLoss]
    linarith [second.sourceLoss_pos]
  have firstOutputLoss_le_one : firstOutputLoss ≤ 1 := by
    dsimp only [firstOutputLoss]
    linarith [second.sourceLoss_le_half, second.normalizationLoss_lt_output]
  rcases proposition63_rich_sticky_kernel sigma critical firstOutputLoss
      firstOutputLoss_pos firstOutputLoss_le_one with ⟨first⟩
  let base : Proposition63RichFourCallScheduleData sigma outputLoss := {
    fourth := fourth
    thirdOutputLoss := thirdOutputLoss
    thirdOutputLoss_eq := rfl
    thirdOutputLoss_pos := thirdOutputLoss_pos
    thirdOutputLoss_lt_fourthSource := thirdOutputLoss_lt_fourthSource
    third := third
    secondOutputLoss := secondOutputLoss
    secondOutputLoss_eq := rfl
    secondOutputLoss_pos := secondOutputLoss_pos
    secondOutputLoss_lt_thirdSource := secondOutputLoss_lt_thirdSource
    second := second
    firstOutputLoss := firstOutputLoss
    firstOutputLoss_eq := rfl
    firstOutputLoss_pos := firstOutputLoss_pos
    firstOutputLoss_lt_secondSource := firstOutputLoss_lt_secondSource
    first := first
  }
  refine ⟨{
    base := base
    fourthKernel := by
      simpa only [base, fourth] using fourthBudgeted.kernel
    thirdOutputLoss_le_discrete := ?_
    secondOutputLoss_le_discrete := ?_
    third_boundary_slack := ?_
    fourth_boundary_slack := ?_
    third_normalization_lt_discrete_half := ?_
    fourth_normalization_lt_discrete_half := ?_
    fourth_normalization_lt_tail := ?_
    fourth_normalization_lt_sigma := ?_
    fourth_tail_boundary_slack := ?_
  }⟩
  · simpa only [base] using thirdOutputLoss_le_discrete
  · simpa only [base] using secondOutputLoss_le_discrete
  · simpa only [base, third] using thirdBudgeted.output_boundary_slack
  · simpa only [base, fourth] using fourthBudgeted.output_boundary_slack
  · simpa only [base, third] using
      thirdBudgeted.normalization_lt_discrete_half
  · simpa only [base, fourth] using
      fourthBudgeted.normalization_lt_discrete_half
  · simpa only [base, fourth] using fourthBudgeted.normalization_lt_tail
  · simpa only [base, fourth] using fourthBudgeted.normalization_lt_sigma
  · simpa only [base, fourth] using fourthBudgeted.tail_boundary_slack

end Kakeya.Assouad.PureWZ2
