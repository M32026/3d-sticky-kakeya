import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichStickyKernel
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustLemma43Scales
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustDegreeCutoff
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RichLemma43AmbientRestoreAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RichLemma43ScalarInputs
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RichLemma43BroadAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9PaperCVWitness

/-!
# Proposition 6.3 M9: bundled robust two-call schedule

This package selects the two rich Proposition 6.2 calls together with the
robust Lemma 4.3 scale and degree cutoffs.  The degree cutoff applies to the
robust scale `kappa = r^(sigma / 16)`, so its contribution to the canonical
root cutoff is an explicit power preimage, not the degree cutoff itself.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The family-independent M9 data selected before the runtime root scale. -/
structure Proposition63M9TwoCallRobustScheduleData
    (sigma outputLoss : ℝ) where
  schedule : Proposition63RichTwoCallScheduleData sigma outputLoss
  outputLoss_le_sigma_half : outputLoss ≤ sigma / 2
  sigma_half_le_one_sub_outputLoss : sigma / 2 ≤ 1 - outputLoss
  firstOutputLoss_le_sigma_sixteenth :
    schedule.firstOutputLoss ≤ sigma / 16
  sigma_sixteenth_le_one_sub_firstOutputLoss :
    sigma / 16 ≤ 1 - schedule.firstOutputLoss
  scale : Proposition63M9RobustLemma43ScaleData sigma
    schedule.firstOutputLoss schedule.first.normalizationLoss
  degreeCutoff : Proposition63M9RobustDegreeCutoffData sigma
    schedule.firstOutputLoss
  degreeRootCutoff : ℝ
  degreeRootCutoff_pos : 0 < degreeRootCutoff
  degreeRootCutoff_le_one : degreeRootCutoff ≤ 1
  degreeRootCutoff_power : ∀ {r : ℝ}, 0 < r → r ≤ degreeRootCutoff →
    proposition63M9RobustLemma43Kappa r sigma ≤ degreeCutoff.delta₀
  ambientRestoreCutoff :
    Proposition63M9RichLemma43AmbientRestoreAbsorptionData
      schedule.first.normalizationLoss schedule.firstOutputLoss
  densityCutoff : Proposition63M9RichLemma43DensityCutoffData sigma
    schedule.first.normalizationLoss
    (2 - sigma + 3 * schedule.firstOutputLoss)
  broadCutoff : Proposition63M9RichLemma43BroadCutoffData sigma
    schedule.firstOutputLoss schedule.first.normalizationLoss
  cvWitness : Proposition63M9PaperCVConstantWitness
  cvEnvelope : Proposition63M9NormalizationPowerEnvelope cvWitness
    schedule.first.normalizationLoss
  currentReentryAbsorption : Proposition63CurrentReentryAbsorptionData
    schedule.first.sourceLoss schedule.first.normalizationLoss
    (schedule.second.sourceLoss / 8) schedule.firstOutputLoss
    (schedule.second.sourceLoss / 2) schedule.second.sourceLoss
    (proposition63CanonicalNearbyLevelCount schedule.first.normalizationLoss)

namespace Proposition63M9TwoCallRobustScheduleData

variable {sigma outputLoss : ℝ}
    (data : Proposition63M9TwoCallRobustScheduleData sigma outputLoss)

/-- The common cutoff for the two rich kernels and the scalar inputs of the
robust Lemma 4.3 stage, before the later current-reentry cost is included. -/
def preliminaryCutoff : ℝ :=
  min data.schedule.first.delta₀ <|
    min data.schedule.second.delta₀ <|
      min data.scale.cutoff <|
        min data.degreeRootCutoff <|
          min data.ambientRestoreCutoff.delta₀ <|
            min data.densityCutoff.delta₀ <|
              min data.broadCutoff.delta₀ data.cvEnvelope.cutoff

/-- The canonical root cutoff also pays the current-shading re-entry between
the two rich calls. -/
def rootCutoff : ℝ :=
  min data.preliminaryCutoff data.currentReentryAbsorption.delta₀

theorem preliminaryCutoff_pos : 0 < data.preliminaryCutoff := by
  exact lt_min data.schedule.first.delta₀_pos <|
    lt_min data.schedule.second.delta₀_pos <|
      lt_min data.scale.cutoff_pos <|
        lt_min data.degreeRootCutoff_pos <|
          lt_min data.ambientRestoreCutoff.delta₀_pos <|
            lt_min data.densityCutoff.delta₀_pos <|
              lt_min data.broadCutoff.delta₀_pos data.cvEnvelope.cutoff_pos

theorem rootCutoff_pos : 0 < data.rootCutoff := by
  exact lt_min data.preliminaryCutoff_pos
    data.currentReentryAbsorption.delta₀_pos

theorem rootCutoff_le_preliminary : data.rootCutoff ≤ data.preliminaryCutoff := by
  exact min_le_left _ _

theorem rootCutoff_le_one : data.rootCutoff ≤ 1 :=
  (rootCutoff_le_preliminary data).trans <|
    (min_le_left _ _).trans data.schedule.first.delta₀_le_one

theorem rootCutoff_le_first :
    data.rootCutoff ≤ data.schedule.first.delta₀ :=
  (rootCutoff_le_preliminary data).trans (min_le_left _ _)

theorem rootCutoff_le_second :
    data.rootCutoff ≤ data.schedule.second.delta₀ :=
  (rootCutoff_le_preliminary data).trans <|
    (min_le_right _ _).trans (min_le_left _ _)

theorem rootCutoff_le_scale :
    data.rootCutoff ≤ data.scale.cutoff :=
  (rootCutoff_le_preliminary data).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans (min_le_left _ _)

theorem rootCutoff_le_degreeRoot :
    data.rootCutoff ≤ data.degreeRootCutoff :=
  (rootCutoff_le_preliminary data).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)

theorem rootCutoff_le_ambientRestore :
    data.rootCutoff ≤ data.ambientRestoreCutoff.delta₀ :=
  (rootCutoff_le_preliminary data).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)

theorem rootCutoff_le_density :
    data.rootCutoff ≤ data.densityCutoff.delta₀ :=
  (rootCutoff_le_preliminary data).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)

theorem rootCutoff_le_broad :
    data.rootCutoff ≤ data.broadCutoff.delta₀ :=
  (rootCutoff_le_preliminary data).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)

theorem rootCutoff_le_cvEnvelope :
    data.rootCutoff ≤ data.cvEnvelope.cutoff :=
  (rootCutoff_le_preliminary data).trans <| (min_le_right _ _).trans <|
    (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_right _ _)

theorem rootCutoff_le_currentReentry :
    data.rootCutoff ≤ data.currentReentryAbsorption.delta₀ := by
  unfold rootCutoff
  exact min_le_right _ _

/-- Below the canonical root cutoff, the robust scale
`kappa = r^(sigma / 16)` is in the exact scale window required by the first
rich `runTerminal` call. -/
theorem first_runTerminal_kappa_window
    {r : ℝ} (hr : 0 < r) (hrCutoff : r ≤ data.rootCutoff) :
    r ≤ data.schedule.first.delta₀ ∧
      Real.rpow r (1 - data.schedule.firstOutputLoss) ≤
        proposition63M9RobustLemma43Kappa r sigma ∧
      proposition63M9RobustLemma43Kappa r sigma ≤
        Real.rpow r data.schedule.firstOutputLoss := by
  have hrOne : r ≤ 1 := hrCutoff.trans data.rootCutoff_le_one
  refine ⟨hrCutoff.trans data.rootCutoff_le_first, ?_, ?_⟩
  · unfold proposition63M9RobustLemma43Kappa
    exact Real.rpow_le_rpow_of_exponent_ge hr hrOne
      data.sigma_sixteenth_le_one_sub_firstOutputLoss
  · unfold proposition63M9RobustLemma43Kappa
    exact Real.rpow_le_rpow_of_exponent_ge hr hrOne
      data.firstOutputLoss_le_sigma_sixteenth

/-- The robust scale `kappa = r^(sigma / 16)`, packaged as the exact requested
scale for the first rich call. -/
noncomputable def firstKappaRequested
    {r : ℝ} (hr : 0 < r) (hrCutoff : r ≤ data.rootCutoff) :
    WZ2PaperRequestedScale r :=
  ⟨proposition63M9RobustLemma43Kappa r sigma,
    data.scale.root_le_kappa hr
      (hrCutoff.trans data.rootCutoff_le_scale),
    data.scale.kappa_le_one hr
      (hrCutoff.trans data.rootCutoff_le_scale)⟩

@[simp] theorem firstKappaRequested_value
    {r : ℝ} (hr : 0 < r) (hrCutoff : r ≤ data.rootCutoff) :
    (data.firstKappaRequested hr hrCutoff).1 =
      proposition63M9RobustLemma43Kappa r sigma :=
  rfl

/-- Run the first rich terminal at the definitionally exact robust scale
`kappa = r^(sigma / 16)`.  The kernel cutoff is checked at the base scale
`r`; only the requested-scale window is checked at `kappa`. -/
theorem first_runTerminal_exact_kappa
    {r : ℝ} (hr : 0 < r) (hrCutoff : r ≤ data.rootCutoff)
    (croppedFamily : Kakeya.Streamlined.TubeFamily r)
    (croppedShading : WZ1PaperTubeShading croppedFamily)
    {normalizationExponent : ℕ}
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      data.schedule.first.sourceLoss
      data.schedule.first.normalizationLoss) :
    Nonempty (Proposition63RichTerminalStickyData
      (outputLoss := data.schedule.firstOutputLoss) croppedShading reentry
      (data.firstKappaRequested hr hrCutoff)) := by
  have window := data.first_runTerminal_kappa_window hr hrCutoff
  exact data.schedule.first.runTerminal r hr window.1 croppedFamily
    croppedShading reentry (data.firstKappaRequested hr hrCutoff)
    window.2.1 window.2.2

/-- The second rich call may be made at the paper's exact scale
`q = r^(sigma / 2)`.  Its runtime cutoff is directly a root-scale cutoff; no
power preimage for `q` is needed. -/
theorem second_runTerminal_exact_q_window
    {r : ℝ} (hr : 0 < r) (hrCutoff : r ≤ data.rootCutoff) :
    r ≤ data.schedule.second.delta₀ ∧
      Real.rpow r (1 - outputLoss) ≤
        proposition63M9RobustLemma43Incidence r sigma ∧
      proposition63M9RobustLemma43Incidence r sigma ≤
        Real.rpow r outputLoss := by
  have hrOne : r ≤ 1 := hrCutoff.trans data.rootCutoff_le_one
  refine ⟨hrCutoff.trans data.rootCutoff_le_second, ?_, ?_⟩
  · unfold proposition63M9RobustLemma43Incidence
    exact Real.rpow_le_rpow_of_exponent_ge hr hrOne
      data.sigma_half_le_one_sub_outputLoss
  · unfold proposition63M9RobustLemma43Incidence
    exact Real.rpow_le_rpow_of_exponent_ge hr hrOne
      data.outputLoss_le_sigma_half

/-- The paper scale `q = r^(sigma / 2)`, packaged as the exact requested
scale for the second rich call. -/
noncomputable def secondQRequested
    {r : ℝ} (hr : 0 < r) (hrCutoff : r ≤ data.rootCutoff) :
    WZ2PaperRequestedScale r :=
  ⟨proposition63M9RobustLemma43Incidence r sigma, by
      have hrOne : r ≤ 1 := hrCutoff.trans data.rootCutoff_le_one
      have hsigmaHalfLeOne : sigma / 2 ≤ 1 := by
        have houtputLossPos : 0 < outputLoss := by
          exact data.schedule.second.normalizationLoss_pos.trans
            data.schedule.second.normalizationLoss_lt_output
        linarith [data.sigma_half_le_one_sub_outputLoss]
      unfold proposition63M9RobustLemma43Incidence
      calc
        r = Real.rpow r 1 := (Real.rpow_one r).symm
        _ ≤ Real.rpow r (sigma / 2) :=
          Real.rpow_le_rpow_of_exponent_ge hr hrOne hsigmaHalfLeOne,
    data.scale.incidence_le_one hr
      (hrCutoff.trans data.rootCutoff_le_scale)⟩

@[simp] theorem secondQRequested_value
    {r : ℝ} (hr : 0 < r) (hrCutoff : r ≤ data.rootCutoff) :
    (data.secondQRequested hr hrCutoff).1 =
      proposition63M9RobustLemma43Incidence r sigma :=
  rfl

/-- Run the second rich terminal at the definitionally exact paper scale
`q = r^(sigma / 2)`.  As for the first call, the kernel cutoff is imposed on
the base scale `r`, so no power preimage of the second cutoff is required. -/
theorem second_runTerminal_exact_q
    {r : ℝ} (hr : 0 < r) (hrCutoff : r ≤ data.rootCutoff)
    (croppedFamily : Kakeya.Streamlined.TubeFamily r)
    (croppedShading : WZ1PaperTubeShading croppedFamily)
    {normalizationExponent : ℕ}
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      data.schedule.second.sourceLoss
      data.schedule.second.normalizationLoss) :
    Nonempty (Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry
      (data.secondQRequested hr hrCutoff)) := by
  have window := data.second_runTerminal_exact_q_window hr hrCutoff
  exact data.schedule.second.runTerminal r hr window.1 croppedFamily
    croppedShading reentry (data.secondQRequested hr hrCutoff)
    window.2.1 window.2.2

/-- The explicit root-to-robust-scale bridge required by the degree
certificate.  In particular, this conclusion is about `kappa`, not `r`. -/
theorem kappa_le_degreeCutoff
    {r : ℝ} (hr : 0 < r) (hrCutoff : r ≤ data.rootCutoff) :
    proposition63M9RobustLemma43Kappa r sigma ≤
      data.degreeCutoff.delta₀ :=
  data.degreeRootCutoff_power hr
    (hrCutoff.trans data.rootCutoff_le_degreeRoot)

/-- The degree cutoff, evaluated at the exact first-call robust scale, forces
the terminal fine degree above the fixed close-count target. -/
theorem first_exact_kappa_degree
    {r : ℝ} (hr : 0 < r) (hrCutoff : r ≤ data.rootCutoff)
    {croppedFamily : Kakeya.Streamlined.TubeFamily r}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {normalizationExponent : ℕ}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      data.schedule.first.sourceLoss
      data.schedule.first.normalizationLoss}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := data.schedule.firstOutputLoss) croppedShading reentry
      (data.firstKappaRequested hr hrCutoff)) :
    (96 : ENNReal) * stickyCoarseCloseCount ≤
      (rich.terminal.fineDegreeFloor : ENNReal) := by
  apply rich.fineDegreeFloor_ge_fixed
  · exact data.schedule.firstOutputLoss_pos.le
  · exact (data.kappa_le_degreeCutoff hr hrCutoff).trans <|
      data.degreeCutoff.delta₀_le_small.trans (by norm_num)
  · exact data.degreeCutoff.degree_absorb
      (data.scale.kappa_pos hr
        (hrCutoff.trans data.rootCutoff_le_scale))
      (data.kappa_le_degreeCutoff hr hrCutoff)

end Proposition63M9TwoCallRobustScheduleData

/-- Freeze the first robust call and all intermediate cutoffs around one
already selected second rich schedule.  The returned equality prevents an
outer M9 assembly from mixing independently chosen second-kernel witnesses. -/
theorem proposition63_m9_two_call_robust_schedule_of_second
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    {outputLoss : ℝ}
    (second : Proposition63RichStickyKernelScheduleData sigma outputLoss)
    (houtputLoss_le : outputLoss ≤ sigma / 2)
    (hsigmaHalf : sigma / 2 ≤ 1 - outputLoss) :
    ∃ data : Proposition63M9TwoCallRobustScheduleData sigma outputLoss,
      data.schedule.second = second := by
  let firstOutputLoss : ℝ := second.sourceLoss / 16
  have firstOutputLossPos : 0 < firstOutputLoss := by
    dsimp only [firstOutputLoss]
    exact div_pos second.sourceLoss_pos (by norm_num)
  have secondSourceLtOutput : second.sourceLoss < outputLoss := by
    calc
      second.sourceLoss ≤ second.normalizationLoss / 2 :=
        second.sourceLoss_le_half
      _ < second.normalizationLoss := by
        linarith [second.normalizationLoss_pos]
      _ < outputLoss := second.normalizationLoss_lt_output
  have firstOutputLossLeOne : firstOutputLoss ≤ 1 := by
    dsimp only [firstOutputLoss]
    linarith [secondSourceLtOutput, houtputLoss_le, critical.sigma_lt_one]
  rcases proposition63_rich_sticky_kernel sigma critical firstOutputLoss
      firstOutputLossPos firstOutputLossLeOne with ⟨first⟩
  let schedule : Proposition63RichTwoCallScheduleData sigma outputLoss := {
    second := second
    firstOutputLoss := firstOutputLoss
    firstOutputLoss_eq := rfl
    firstOutputLoss_pos := firstOutputLossPos
    firstOutputLoss_lt_secondSource := by
      dsimp only [firstOutputLoss]
      linarith [second.sourceLoss_pos]
    first := first
  }
  rcases proposition63_m9_paperCVConstantWitness_exists with ⟨cvWitness⟩
  rcases cvWitness.exists_normalizationPowerEnvelope
      schedule.first.normalizationLoss_pos with ⟨cvEnvelope⟩
  have firstOutputLoss_lt_sigma_thirtysecond :
      schedule.firstOutputLoss < sigma / 32 := by
    rw [schedule.firstOutputLoss_eq]
    change second.sourceLoss / 16 < sigma / 32
    linarith [secondSourceLtOutput, houtputLoss_le]
  have firstOutputLoss_le_sigma_sixteenth :
      schedule.firstOutputLoss ≤ sigma / 16 := by
    linarith [critical.sigma_pos, firstOutputLoss_lt_sigma_thirtysecond]
  have sigma_sixteenth_le_one_sub_firstOutputLoss :
      sigma / 16 ≤ 1 - schedule.firstOutputLoss := by
    linarith [critical.sigma_lt_one, firstOutputLoss_lt_sigma_thirtysecond]
  have robustBroadGap :
      5 * schedule.firstOutputLoss +
          2 * schedule.first.normalizationLoss < sigma / 4 := by
    linarith [schedule.first.normalizationLoss_lt_output,
      firstOutputLoss_lt_sigma_thirtysecond]
  rcases proposition63_m9_robust_lemma43_scales sigma
      schedule.firstOutputLoss schedule.first.normalizationLoss
      critical.sigma_pos critical.sigma_lt_one robustBroadGap with ⟨scale⟩
  have degreeGap : 4 * schedule.firstOutputLoss < sigma := by
    linarith [critical.sigma_pos, firstOutputLoss_lt_sigma_thirtysecond]
  rcases proposition63_m9_robust_degree_cutoff sigma
      schedule.firstOutputLoss degreeGap with ⟨degreeCutoff⟩
  have kappaExponentPos : 0 < sigma / 16 := by
    linarith [critical.sigma_pos]
  rcases pure_wz2_exists_delta₀_rpow_le degreeCutoff.delta₀_pos
      kappaExponentPos with
    ⟨degreeRootCutoff, degreeRootCutoffPos, degreeRootCutoffOne,
      degreeRootCutoffPower⟩
  have ambientRestoreGap :
      schedule.first.normalizationLoss < schedule.firstOutputLoss :=
    schedule.first.normalizationLoss_lt_output
  rcases proposition63_m9_rich_lemma43_ambient_restore_absorption
      schedule.first.normalizationLoss schedule.firstOutputLoss
      ambientRestoreGap with ⟨ambientRestoreCutoff⟩
  have densityGap :
      0 < (2 - sigma + 3 * schedule.firstOutputLoss) + sigma -
        2 * schedule.first.normalizationLoss - 2 := by
    have normalizationLtOutput := schedule.first.normalizationLoss_lt_output
    linarith [schedule.firstOutputLoss_pos]
  rcases proposition63_m9_rich_lemma43_density_cutoff sigma
      schedule.first.normalizationLoss
      (2 - sigma + 3 * schedule.firstOutputLoss) densityGap with
    ⟨densityCutoff⟩
  rcases proposition63_m9_rich_lemma43_broad_cutoff sigma
      schedule.firstOutputLoss schedule.first.normalizationLoss
      robustBroadGap with ⟨broadCutoff⟩
  have firstSourceLtDensity :
      schedule.first.sourceLoss < schedule.second.sourceLoss / 8 := by
    calc
      schedule.first.sourceLoss ≤ schedule.first.normalizationLoss / 2 :=
        schedule.first.sourceLoss_le_half
      _ < schedule.firstOutputLoss / 2 := by
        linarith [schedule.first.normalizationLoss_lt_output]
      _ = schedule.second.sourceLoss / 32 := by
        rw [schedule.firstOutputLoss_eq]
        ring
      _ < schedule.second.sourceLoss / 8 := by
        linarith [schedule.second.sourceLoss_pos]
  have densityCurrentLtWeight :
      schedule.second.sourceLoss / 8 + schedule.firstOutputLoss <
        schedule.second.sourceLoss / 2 := by
    rw [schedule.firstOutputLoss_eq]
    linarith [schedule.second.sourceLoss_pos]
  have weightLtReentry : schedule.second.sourceLoss / 2 <
      schedule.second.sourceLoss := by
    linarith [schedule.second.sourceLoss_pos]
  have currentRegularizationGap :
      0 < schedule.second.sourceLoss - schedule.second.sourceLoss / 2 -
        2 * schedule.first.normalizationLoss := by
    have hnormalization : schedule.first.normalizationLoss <
        schedule.second.sourceLoss / 16 := by
      rw [← schedule.firstOutputLoss_eq]
      exact schedule.first.normalizationLoss_lt_output
    linarith [schedule.second.sourceLoss_pos]
  rcases proposition63_current_reentry_absorption
      schedule.first.sourceLoss schedule.first.normalizationLoss
      (schedule.second.sourceLoss / 8) schedule.firstOutputLoss
      (schedule.second.sourceLoss / 2) schedule.second.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        schedule.first.normalizationLoss)
      firstSourceLtDensity schedule.first.normalizationLoss_pos
      densityCurrentLtWeight weightLtReentry
      (proposition63CanonicalNearbyLevelCount_pos
        schedule.first.normalizationLoss_pos)
      schedule.second.sourceLoss_pos currentRegularizationGap with
    ⟨currentReentryAbsorption⟩
  let data : Proposition63M9TwoCallRobustScheduleData sigma outputLoss := {
    schedule := schedule
    outputLoss_le_sigma_half := houtputLoss_le
    sigma_half_le_one_sub_outputLoss := hsigmaHalf
    firstOutputLoss_le_sigma_sixteenth :=
      firstOutputLoss_le_sigma_sixteenth
    sigma_sixteenth_le_one_sub_firstOutputLoss :=
      sigma_sixteenth_le_one_sub_firstOutputLoss
    scale := scale
    degreeCutoff := degreeCutoff
    degreeRootCutoff := degreeRootCutoff
    degreeRootCutoff_pos := degreeRootCutoffPos
    degreeRootCutoff_le_one := degreeRootCutoffOne
    degreeRootCutoff_power := by
      intro r hr hrRoot
      exact degreeRootCutoffPower r hr hrRoot
    ambientRestoreCutoff := ambientRestoreCutoff
    densityCutoff := densityCutoff
    broadCutoff := broadCutoff
    cvWitness := cvWitness
    cvEnvelope := cvEnvelope
    currentReentryAbsorption := currentReentryAbsorption
  }
  exact ⟨data, rfl⟩

/-- Freeze both rich calls and every robust M9 cutoff before the runtime scale
and family are chosen. -/
theorem proposition63_m9_two_call_robust_schedule
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ) (houtputLoss : 0 < outputLoss)
    (houtputLoss_le : outputLoss ≤ sigma / 2)
    (hsigmaHalf : sigma / 2 ≤ 1 - outputLoss) :
    Nonempty (Proposition63M9TwoCallRobustScheduleData
      sigma outputLoss) := by
  have houtputLossOne : outputLoss ≤ 1 := by
    linarith [critical.sigma_pos]
  rcases proposition63_rich_sticky_kernel sigma critical outputLoss
      houtputLoss houtputLossOne with ⟨second⟩
  rcases proposition63_m9_two_call_robust_schedule_of_second
      sigma critical second houtputLoss_le hsigmaHalf with ⟨data, _⟩
  exact ⟨data⟩

end Kakeya.Assouad.PureWZ2

end
