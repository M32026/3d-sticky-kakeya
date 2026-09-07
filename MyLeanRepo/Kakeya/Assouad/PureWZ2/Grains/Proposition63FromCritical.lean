import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63CriticalCeiling
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PowerScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RootSequentialReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentLocalVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentOneScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentFinePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentStepArithmetic
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FullGrainThreshold
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63OneScaleFullGrainCell
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63OneScaleFullGrainGlobal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63OneScaleMultiplicityPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63OneScaleFullGrainCandidate
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63UniformLineHitBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FiniteFullGrainIteration
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63UniformFullGrainStepProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63LineHitGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CoarseTopLevelCWABridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CWAPropertyP
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63SafePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RetainedZeroExtensionFinitePlaniness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FirstStage
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63CommonSliceRescaled
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ChartRescaled
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ChartNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63SlopeExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63StickyReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichLemma44
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma47
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma412
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63CoarseGlobalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PopularShiftedGridCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingFinal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ConfigurationWeakening

/-!
# Proposition 6.3 from the critical package

This is the top-level, paper-order assembly for `wz2_63.tex`.  In particular,
the losses below are chosen before the fine scale, the first sticky request is
made at the exact power scale `Delta = tau^(sigma/(2+sigma))`, and the second
sticky request is made only after the Lemma 4.3 refinement has been converted
back to an ordinary critical source.  The final normalization is the genuine
popular-box isotropic rescaling.

The small-scale inequalities are deliberately kept visible at the leaves
which consume them.  The records in this file only freeze their strict order;
they do not permit a replacement family, an empty shading, or an identity
rescaling.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

/-- The losses used after the second Proposition 6.2 application, together
with the finite Lemma 4.7 schedule selected before runtime data.  The final
Lemma 4.7 loss and the number of scales are fixed first; only after backward
iteration exposes its input loss are the sticky and Lemma 4.4 losses chosen. -/
structure Proposition63TerminalLossHierarchy
    (sigma outputLoss : ℝ) where
  N : ℕ
  stickyLoss : ℝ
  lemma44Loss : ℝ
  lemma47Loss : ℝ
  preGrainLoss : ℝ
  lemma47Schedule : Proposition63ExtremalFiniteLipschitzScheduleData
    sigma lemma47Loss N
  N_two : 2 ≤ N
  N_budget : (2 : ℝ) / N < lemma47Loss
  sticky_pos : 0 < stickyLoss
  sticky_lt_lemma44 : stickyLoss < lemma44Loss
  two_sticky_le_lemma44 : 2 * stickyLoss ≤ lemma44Loss
  sticky_le_lemma47_root_source :
    stickyLoss ≤ lemma47Schedule.rootSourceLoss
  two_sticky_le_lemma47_root_normalization :
    2 * stickyLoss ≤ lemma47Schedule.rootNormalizationLoss
  lemma44_le_lemma47_input : lemma44Loss ≤ lemma47Schedule.inputLoss
  lemma47_input_le_final : lemma47Schedule.inputLoss ≤ lemma47Loss
  lemma44_lt_lemma47 : lemma44Loss < lemma47Loss
  lemma47_lt_preGrain : lemma47Loss < preGrainLoss
  preGrain_lt_output : preGrainLoss < outputLoss
  preGrain_lt_sigma_quarter : preGrainLoss < sigma / 4
  sticky_le_sigma_half : stickyLoss ≤ sigma / 2
  sigma_half_le_one_sub_sticky : sigma / 2 ≤ 1 - stickyLoss

/-- A concrete recursive choice realizing the paper's
`epsilon_3 << epsilon_4 << epsilon_5 << epsilon` hierarchy. -/
theorem proposition63_terminal_loss_hierarchy
    {sigma outputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (houtput : 0 < outputLoss) :
    Nonempty (Proposition63TerminalLossHierarchy sigma outputLoss) := by
  let budget : ℝ := min outputLoss (sigma / 4)
  have hbudget : 0 < budget := by
    dsimp only [budget]
    exact lt_min houtput (by positivity)
  let lemma47Loss : ℝ := budget / 4
  have lemma47LossPos : 0 < lemma47Loss := by
    dsimp only [lemma47Loss]
    positivity
  have lemma47LossOne : lemma47Loss ≤ 1 := by
    have hbudgetSigma : budget ≤ sigma / 4 := min_le_right _ _
    dsimp only [lemma47Loss]
    nlinarith [hsigmaOne]
  rcases exists_nat_gt (8 / budget) with ⟨N, hNlarge⟩
  have oneLtEightOverBudget : (1 : ℝ) < 8 / budget := by
    apply (lt_div_iff₀ hbudget).2
    have hbudgetSigma : budget ≤ sigma / 4 := min_le_right _ _
    linarith
  have NTwo : 2 ≤ N := by
    have oneLtN : (1 : ℝ) < N := oneLtEightOverBudget.trans hNlarge
    exact_mod_cast oneLtN
  have NPos : 0 < (N : ℝ) := by positivity
  have NBudget : (2 : ℝ) / N < lemma47Loss := by
    have scaled : 8 < budget * (N : ℝ) :=
      by simpa [mul_comm] using (div_lt_iff₀ hbudget).mp hNlarge
    rw [div_lt_iff₀ NPos]
    dsimp only [lemma47Loss]
    nlinarith
  rcases proposition63_extremal_finite_lipschitz_schedule sigma critical
      lemma47Loss lemma47LossPos lemma47LossOne N NTwo NBudget with
    ⟨lemma47Schedule⟩
  let lemma44Loss : ℝ :=
    min (lemma47Schedule.inputLoss / 2) (lemma47Loss / 2)
  let stickyLoss : ℝ := min (lemma44Loss / 4) <|
    min lemma47Schedule.rootSourceLoss
      (lemma47Schedule.rootNormalizationLoss / 2)
  have lemma44LossPos : 0 < lemma44Loss := by
    dsimp only [lemma44Loss]
    exact lt_min
      (div_pos lemma47Schedule.inputLoss_pos (by norm_num))
      (div_pos lemma47LossPos (by norm_num))
  have stickyLeBudget : stickyLoss ≤ budget / 32 := by
    have stickyLemma44 : stickyLoss ≤ lemma44Loss / 4 := min_le_left _ _
    have lemma44Upper := min_le_right
      (lemma47Schedule.inputLoss / 2) (lemma47Loss / 2)
    calc
      stickyLoss ≤ lemma44Loss / 4 := stickyLemma44
      _ ≤ (lemma47Loss / 2) / 4 := by gcongr
      _ = budget / 32 := by
        dsimp only [lemma47Loss]
        ring
  refine ⟨{
    N := N
    stickyLoss := stickyLoss
    lemma44Loss := lemma44Loss
    lemma47Loss := lemma47Loss
    preGrainLoss := budget / 2
    lemma47Schedule := lemma47Schedule
    N_two := NTwo
    N_budget := NBudget
    sticky_pos := by
      dsimp only [stickyLoss]
      exact lt_min (by positivity) <|
        lt_min lemma47Schedule.rootSourceLoss_pos
          (div_pos lemma47Schedule.rootNormalizationLoss_pos (by norm_num))
    sticky_lt_lemma44 := by
      have := min_le_left (lemma44Loss / 4)
        (min lemma47Schedule.rootSourceLoss
          (lemma47Schedule.rootNormalizationLoss / 2))
      dsimp only [stickyLoss]
      linarith
    two_sticky_le_lemma44 := by
      have := min_le_left (lemma44Loss / 4)
        (min lemma47Schedule.rootSourceLoss
          (lemma47Schedule.rootNormalizationLoss / 2))
      dsimp only [stickyLoss]
      linarith
    sticky_le_lemma47_root_source := by
      exact (min_le_right _ _).trans (min_le_left _ _)
    two_sticky_le_lemma47_root_normalization := by
      have := (min_le_right (lemma44Loss / 4)
        (min lemma47Schedule.rootSourceLoss
          (lemma47Schedule.rootNormalizationLoss / 2))).trans
            (min_le_right _ _)
      linarith
    lemma44_le_lemma47_input := by
      exact (min_le_left _ _).trans <| by
        linarith [lemma47Schedule.inputLoss_pos]
    lemma47_input_le_final := lemma47Schedule.inputLoss_le_output
    lemma44_lt_lemma47 := by
      have := min_le_right
        (lemma47Schedule.inputLoss / 2) (lemma47Loss / 2)
      dsimp only [lemma44Loss]
      linarith
    lemma47_lt_preGrain := by
      dsimp only [lemma47Loss]
      linarith
    preGrain_lt_output := by
      have hle : budget ≤ outputLoss := min_le_left _ _
      linarith
    preGrain_lt_sigma_quarter := by
      have hle : budget ≤ sigma / 4 := min_le_right _ _
      linarith
    sticky_le_sigma_half := by
      have hle : budget ≤ sigma / 4 := min_le_right _ _
      linarith [stickyLeBudget]
    sigma_half_le_one_sub_sticky := by
      have hle : budget ≤ sigma / 4 := min_le_right _ _
      linarith [stickyLeBudget, hsigmaOne]
  }⟩

/-- Run canonical Lemma 4.7 from the loss hierarchy selected in the required
order.  The two re-entry inequalities are consequences of the rich terminal's
coarse-loss budget and the hierarchy fields, not additional certificates. -/
theorem Proposition63TerminalLossHierarchy.runLemma47
    {delta sigma outputLoss lemma43SourceLoss lemma43Loss
      reentrySourceLoss reentryNormalizationLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) lemma43.shading normalizationExponent
        reentrySourceLoss reentryNormalizationLoss}
    (hierarchy : Proposition63TerminalLossHierarchy sigma outputLoss)
    (rich : Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := hierarchy.stickyLoss)
      lemma43.shading reentry rho)
    (lemma44 : Proposition63Lemma44Data
      lemma43 rich.data hierarchy.lemma44Loss)
    (hdeltaSchedule : rho.1 ≤ hierarchy.lemma47Schedule.delta₀)
    (haxial : ∀ index point,
      point ∈ reentry.geometry.frame ''
          reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8) :
    Nonempty (Proposition63Lemma47Data lemma44 hierarchy.lemma47Loss
      (Real.rpow rho.1 (-hierarchy.lemma47Loss))) := by
  have coarseSourceLe : rich.coarseSourceLoss ≤
      hierarchy.lemma47Schedule.rootSourceLoss := by
    have sourceLeSticky : rich.coarseSourceLoss ≤ hierarchy.stickyLoss := by
      linarith [rich.coarseSourceLoss_budget, rich.coarseSourceLoss_pos]
    exact sourceLeSticky.trans hierarchy.sticky_le_lemma47_root_source
  have coarseNormalizationLe : rich.coarseNormalizationLoss ≤
      hierarchy.lemma47Schedule.rootNormalizationLoss := by
    rw [rich.coarseNormalizationLoss_eq]
    have sourceLeSticky :
        3 * rich.coarseSourceLoss ≤ hierarchy.stickyLoss :=
      rich.coarseSourceLoss_budget
    have normalizationLeTwoSticky :
        (7 / 2 : ℝ) * rich.coarseSourceLoss ≤
          2 * hierarchy.stickyLoss := by
      linarith [rich.coarseSourceLoss_pos]
    exact normalizationLeTwoSticky.trans
      hierarchy.two_sticky_le_lemma47_root_normalization
  exact proposition63_paper_lemma47_of_extremal_finite_schedule rich lemma44
    hierarchy.lemma47Schedule hdeltaSchedule coarseSourceLe
    coarseNormalizationLe hierarchy.lemma44_le_lemma47_input haxial

/-- Losses for the first Proposition 6.2 application, chosen only after the
second application has exposed its required input loss. -/
structure Proposition63InitialLossHierarchy
    (sigma secondInputLoss : ℝ) where
  stickyLoss : ℝ
  localLoss : ℝ
  lemma43SourceLoss : ℝ
  sticky_pos : 0 < stickyLoss
  sticky_lt_local : stickyLoss < localLoss
  local_lt_lemma43 : localLoss < lemma43SourceLoss
  lemma43SourceLoss_eq_three_sticky :
    lemma43SourceLoss = 3 * stickyLoss
  lemma43_lt_secondInput : lemma43SourceLoss < secondInputLoss
  sticky_le_power : stickyLoss ≤ sigma / (2 + sigma)
  power_le_one_sub_sticky : sigma / (2 + sigma) ≤ 1 - stickyLoss
  lemma43_lt_sigma_quarter : lemma43SourceLoss < sigma / 4

/-- Concrete nested losses for the first half of Proposition 6.3. -/
theorem proposition63_initial_loss_hierarchy
    {sigma secondInputLoss : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hinput : 0 < secondInputLoss) :
    Nonempty (Proposition63InitialLossHierarchy sigma secondInputLoss) := by
  let budget : ℝ := min secondInputLoss (sigma / 8)
  have hbudget : 0 < budget := by
    dsimp only [budget]
    exact lt_min hinput (by positivity)
  have hbudgetInput : budget ≤ secondInputLoss := min_le_left _ _
  have hbudgetSigma : budget ≤ sigma / 8 := min_le_right _ _
  refine ⟨{
    stickyLoss := budget / 4
    localLoss := budget / 2
    lemma43SourceLoss := 3 * budget / 4
    sticky_pos := by positivity
    sticky_lt_local := by linarith
    local_lt_lemma43 := by linarith
    lemma43SourceLoss_eq_three_sticky := by
      change 3 * budget / 4 = 3 * (budget / 4)
      ring
    lemma43_lt_secondInput := by linarith
    sticky_le_power := ?_
    power_le_one_sub_sticky := ?_
    lemma43_lt_sigma_quarter := by linarith
  }⟩
  · have hdenom : 0 < 2 + sigma := by linarith
    have hpower : sigma / 8 ≤ sigma / (2 + sigma) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) hdenom]
      nlinarith
    exact (by linarith : budget / 4 ≤ sigma / 8) |>.trans hpower
  · have hsigmaHalf : sigma / 2 < 1 := by linarith
    have hpowerHalf : sigma / (2 + sigma) ≤ sigma / 2 := by
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 + sigma)
        (by norm_num : (0 : ℝ) < 2)]
      nlinarith
    have hstickySmall : budget / 4 ≤ sigma / 32 := by linarith
    linarith

/-- The exact power scale lies in the first sticky range. -/
theorem Proposition63PowerScale.first_sticky_window
    {tau sigma stickyLoss : ℝ}
    (power : Proposition63PowerScale tau sigma)
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hlower : stickyLoss ≤ sigma / (2 + sigma))
    (hupper : sigma / (2 + sigma) ≤ 1 - stickyLoss) :
    Real.rpow tau (1 - stickyLoss) ≤ power.requested.1 ∧
      power.requested.1 ≤ Real.rpow tau stickyLoss := by
  rw [power.requested_eq, power.Delta_eq]
  constructor
  · exact Real.rpow_le_rpow_of_exponent_ge htau htauOne hupper
  · exact Real.rpow_le_rpow_of_exponent_ge htau htauOne hlower

/-- The same exact `Delta` is a legal second sticky request on the normalized
fine scale `h = tau / Delta`; this is precisely `h^(sigma/2)=Delta`. -/
theorem Proposition63PowerScale.second_sticky_window
    {tau sigma stickyLoss : ℝ}
    (power : Proposition63PowerScale tau sigma)
    (hsticky : stickyLoss ≤ sigma / 2)
    (hsigmaUpper : sigma / 2 ≤ 1 - stickyLoss) :
    Real.rpow power.h (1 - stickyLoss) ≤ power.Delta ∧
      power.Delta ≤ Real.rpow power.h stickyLoss := by
  rw [← power.scale_identity]
  constructor
  · exact Real.rpow_le_rpow_of_exponent_ge power.h_pos power.h_le_one
      hsigmaUpper
  · exact Real.rpow_le_rpow_of_exponent_ge power.h_pos power.h_le_one
      hsticky

/-- The exact coarse scale `Delta` regarded as a requested scale on the
first rescaled metric fibre.  Its admissibility is the identity
`h^(sigma/2) = Delta`, not a nearby-scale replacement. -/
noncomputable def Proposition63PowerScale.secondRequested
    {tau sigma : ℝ}
    (power : Proposition63PowerScale tau sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    WZ2PaperRequestedScale power.h :=
  ⟨power.Delta, by
      have hDelta : 0 < power.Delta := by
        rw [← power.scale_identity]
        exact Real.rpow_pos_of_pos power.h_pos _
      rw [power.h_eq]
      exact (div_le_iff₀ hDelta).2 (by
        simpa [pow_two] using power.tau_le_Delta_sq),
    by
      rw [← power.requested_eq]
      exact power.requested.2.2⟩

@[simp] theorem Proposition63PowerScale.secondRequested_value
    {tau sigma : ℝ}
    (power : Proposition63PowerScale tau sigma)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    (power.secondRequested hsigma hsigmaOne).1 = power.Delta :=
  rfl

/-- Start Proposition 6.3 from the frozen critical and sticky packages, in
the quantifier order required by the paper: Node 3 chooses its input loss,
then normalization chooses an arbitrarily small scale, and only then is the
exact power scale requested. -/
theorem proposition63_first_sticky_power_scale
    {normalizationExponent logExponent : ℕ}
    (hRealizationAt : PureWZ2PropStickyRealizationAt
      normalizationExponent logExponent)
    {sigma : ℝ} (critical : PureWZ2CriticalPackage sigma)
    (stickyLoss deltaBound : ℝ)
    (hstickyLoss : 0 < stickyLoss)
    (hstickyPower : stickyLoss ≤ sigma / (2 + sigma))
    (hpowerUpper : sigma / (2 + sigma) ≤ 1 - stickyLoss)
    (hdeltaBound : 0 < deltaBound)
    (hdeltaBoundOne : deltaBound < 1) :
    ∃ sourceLoss normalizationLoss delta : ℝ,
      ∃ source : PureWZ2ExtremalConfiguration sigma sourceLoss delta,
      ∃ normalized : PureWZ2CroppedCriticalNormalizationData
          (outputLoss := normalizationLoss) source normalizationExponent,
      ∃ base : PureWZ2GrainBaseConfig sigma stickyLoss delta,
      ∃ power : Proposition63PowerScale delta sigma,
      ∃ sticky : PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          base.shading power.requested logExponent,
        0 < sourceLoss ∧ 0 < normalizationLoss ∧
          0 < delta ∧ delta ≤ deltaBound := by
  rcases pure_wz2_grain_base_config_with_sticky_pair_at
      hRealizationAt sigma critical stickyLoss stickyLoss deltaBound
      hstickyLoss le_rfl hstickyLoss hdeltaBound with
    ⟨sourceLoss, normalizationLoss, delta, source, normalized, base,
      hNormProvision, _hChartProvision, hsourceLoss, _hnormalizationLoss,
      hdelta, hdeltaLe, _hbase_family, _hbase_shading⟩
  have hdeltaOne : delta < 1 := hdeltaLe.trans_lt hdeltaBoundOne
  rcases proposition63_power_scale hdelta hdeltaOne critical.sigma_pos
      critical.sigma_lt_one with ⟨power⟩
  have hwindow := power.first_sticky_window hdelta
    base.extremal.delta_le_one
    hstickyPower hpowerUpper
  rcases hNormProvision power.requested hwindow.1 hwindow.2 with ⟨sticky⟩
  exact ⟨sourceLoss, normalizationLoss, delta, source, normalized, base,
    power, sticky, hsourceLoss, _hnormalizationLoss, hdelta, hdeltaLe⟩

/- First Proposition 6.2 on the actual preliminary local-grain refinement.

Unlike `proposition63_first_sticky_power_scale`, this entry point does not
apply stickiness directly to the first normalization.  Node 3 first exposes
its required input loss; the caller then supplies the Lemmas 4.8/4.12
refinement and its trace-regularized normalization.  The returned local-grain
package is definitionally attached to the sticky source shading. -/
/-
theorem proposition63_first_sticky_power_scale_of_local_grain_reentry
    {normalizationExponent logExponent : ℕ}
    (hStickyAt : PureWZ2CroppedPropStickyAt
      normalizationExponent logExponent)
    {sigma : ℝ} (critical : PureWZ2CriticalPackage sigma)
    (stickyLoss deltaBound : ℝ)
    (hstickyLoss : 0 < stickyLoss)
    (hstickyPower : stickyLoss ≤ sigma / (2 + sigma))
    (hpowerUpper : sigma / (2 + sigma) ≤ 1 - stickyLoss)
    (hdeltaBound : 0 < deltaBound)
    (hdeltaBoundOne : deltaBound < 1) :
    ∃ inputLoss stickyBound : ℝ,
      0 < inputLoss ∧ 0 < stickyBound ∧ stickyBound ≤ deltaBound ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ stickyBound →
        ∀ initialInputLoss initialNormalizationLoss : ℝ,
          ∀ initialSource : PureWZ2ExtremalConfiguration
            sigma initialInputLoss delta,
          ∀ initialNormalized : PureWZ2CroppedCriticalNormalizationData
            (outputLoss := initialNormalizationLoss) initialSource
            normalizationExponent,
          ∀ localLoss localIncidence : ℝ,
          ∀ localL : NNReal,
          ∀ localShading : WZ1PaperTubeShading
            initialNormalized.croppedFamily,
          ∀ localGrains : Proposition63InitialWeakLocalGrainData
            (incidence := localIncidence) localShading sigma
            (Kakeya.realRpowENN delta (-localLoss)) localL,
          ∀ prepared : Proposition63InitialLocalGrainReentryData
            (delta := delta) (sigma := sigma)
            (initialInputLoss := initialInputLoss)
            (normalizationLoss := initialNormalizationLoss)
            (reentryLoss := inputLoss)
            (localLoss := localLoss)
            (initialSource := initialSource)
            (normalizationExponent := normalizationExponent)
            initialNormalized localShading localGrains,
            ∃ power : Proposition63PowerScale delta sigma,
              ∃ sticky : PureWZ2PropStickyData
                (sigma := sigma) (outputLoss := stickyLoss)
                prepared.normalization.croppedRefined power.requested
                logExponent,
                0 < delta ∧ delta ≤ deltaBound ∧
                Nonempty (Proposition63InitialWeakLocalGrainData
                  (incidence := localIncidence)
                  prepared.normalization.croppedRefined sigma
                  (Kakeya.realRpowENN delta (-localLoss)) localL) := by
  rcases hStickyAt sigma critical stickyLoss hstickyLoss with
    ⟨inputLoss, nodeBound, hinputLoss, hnodeBound, hnodeBoundOne, hSticky⟩
  let stickyBound : ℝ := min nodeBound deltaBound
  have hstickyBound : 0 < stickyBound := by
    dsimp only [stickyBound]
    exact lt_min hnodeBound hdeltaBound
  have hstickyBoundNode : stickyBound ≤ nodeBound := min_le_left _ _
  have hstickyBoundExternal : stickyBound ≤ deltaBound := min_le_right _ _
  refine ⟨inputLoss, stickyBound, hinputLoss, hstickyBound,
    hstickyBoundExternal, ?_⟩
  intro delta hdelta hdeltaSticky initialInputLoss initialNormalizationLoss
    initialSource initialNormalized localLoss localIncidence localL
    localShading localGrains prepared
  have hdeltaOne : delta < 1 :=
    (hdeltaSticky.trans hstickyBoundExternal).trans_lt hdeltaBoundOne
  rcases proposition63_power_scale hdelta hdeltaOne critical.sigma_pos
      critical.sigma_lt_one with ⟨power⟩
  have hwindow := power.first_sticky_window hdelta hdeltaOne.le
    hstickyPower hpowerUpper
  rcases proposition63InitialLocalGrainReentry_sticky prepared
      (hSticky delta hdelta (hdeltaSticky.trans hstickyBoundNode))
      power.requested hwindow.1 hwindow.2 with ⟨sticky, hlocal⟩
  exact ⟨power, sticky, hdelta,
    hdeltaSticky.trans hstickyBoundExternal, hlocal⟩
-/

/-- Preselect the rich Node 3 schedule, then run its first call at the exact
Proposition 6.3 power scale after an arbitrary preliminary local-grain
refinement has been re-entered.  The schedule, including both re-entry
losses, is fixed before `delta` and before the preliminary data. -/
theorem proposition63_first_rich_sticky_power_scale_of_local_grain_reentry
    {sigma : ℝ} (critical : PureWZ2CriticalPackage sigma)
    (stickyLoss deltaBound : ℝ)
    (hstickyLoss : 0 < stickyLoss)
    (hstickyLossOne : stickyLoss ≤ 1)
    (hstickyPower : stickyLoss ≤ sigma / (2 + sigma))
    (hpowerUpper : sigma / (2 + sigma) ≤ 1 - stickyLoss)
    (hdeltaBound : 0 < deltaBound)
    (hdeltaBoundOne : deltaBound < 1) :
    ∃ schedule : Proposition63RichStickyKernelScheduleData sigma stickyLoss,
      ∃ stickyBound : ℝ,
        0 < stickyBound ∧ stickyBound ≤ deltaBound ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ stickyBound →
          ∀ initialInputLoss initialNormalizationLoss : ℝ,
            ∀ initialSource : PureWZ2ExtremalConfiguration
              sigma initialInputLoss delta,
            ∀ initialNormalized : PureWZ2CroppedCriticalNormalizationData
              (outputLoss := initialNormalizationLoss) initialSource 0,
            ∀ localLoss localIncidence : ℝ,
            ∀ localL : NNReal,
            ∀ localShading : WZ1PaperTubeShading
              initialNormalized.croppedFamily,
            ∀ localGrains : Proposition63InitialWeakLocalGrainData
              (incidence := localIncidence) localShading sigma
              (Kakeya.realRpowENN delta (-localLoss)) localL,
            ∀ prepared : Proposition63InitialLocalGrainReentryData
              (reentryLoss := schedule.sourceLoss) initialNormalized
              localShading localGrains,
              prepared.reentryNormalizationLoss =
                  schedule.normalizationLoss →
              (∀ index point,
                point ∈ initialNormalized.frame ''
                    initialNormalized.ordinaryRefined.carrier index →
                  |point (2 : Fin 3)| ≤ 1 / 8) →
              ∃ power : Proposition63PowerScale delta sigma,
                ∃ sticky : PureWZ2ReentrantPropStickyData
                    (sigma := sigma) (outputLoss := stickyLoss)
                    prepared.normalization.croppedRefined power.requested
                    0 61,
                  delta ≤ deltaBound ∧
                  Nonempty (Proposition63InitialWeakLocalGrainData
                    (incidence := localIncidence)
                    prepared.normalization.croppedRefined sigma
                    (Kakeya.realRpowENN delta (-localLoss)) localL) := by
  rcases proposition63_rich_sticky_kernel sigma critical stickyLoss
      hstickyLoss hstickyLossOne with ⟨schedule⟩
  let stickyBound : ℝ := min deltaBound schedule.delta₀
  have stickyBound_pos : 0 < stickyBound := by
    exact lt_min hdeltaBound schedule.delta₀_pos
  have stickyBound_le_external : stickyBound ≤ deltaBound :=
    min_le_left _ _
  have stickyBound_le_schedule : stickyBound ≤ schedule.delta₀ :=
    min_le_right _ _
  refine ⟨schedule, stickyBound, stickyBound_pos,
    stickyBound_le_external, ?_⟩
  intro delta delta_pos delta_le initialInputLoss initialNormalizationLoss
    initialSource initialNormalized localLoss localIncidence localL
    localShading localGrains prepared hnormalizationLoss initialAxialWindow
  have delta_lt_one : delta < 1 :=
    (delta_le.trans stickyBound_le_external).trans_lt hdeltaBoundOne
  rcases proposition63_power_scale delta_pos delta_lt_one
      critical.sigma_pos critical.sigma_lt_one with ⟨power⟩
  have window := power.first_sticky_window delta_pos delta_lt_one.le
    hstickyPower hpowerUpper
  rcases proposition63InitialLocalGrainReentry_richSticky prepared schedule
      rfl hnormalizationLoss (delta_le.trans stickyBound_le_schedule)
      initialAxialWindow power.requested window.1 window.2 with
    ⟨sticky, localGrainData⟩
  exact ⟨power, sticky, delta_le.trans stickyBound_le_external,
    localGrainData⟩

/-- The first sticky output supplies its own Property-(P) input.  The source
top-level CWA is transferred first to the selected fine family and then to
the actual coarse family of the same frozen Section-6 cover.  Boundary-cell
pruning is performed only after that Property-(P) refinement has been
chosen, so the exact requested scale is never replaced by an aligned one. -/
theorem proposition63_first_propertyP_safe_pullback
    {delta sigma stickyLoss tau epsilon₁ epsilon₃ densityLoss kappa : ℝ}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (base : PureWZ2GrainBaseConfig sigma stickyLoss delta)
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      base.shading rho logExponent)
    (retainedFactor : ENNReal)
    (hdeltaSmall24 : delta ≤ 1 / 24)
    (hrhoSmall24 : rho.1 ≤ 1 / 24)
    (hrhoSmall10000 : rho.1 ≤ 1 / 10000)
    (hcoverScale : 6 * delta ≤ rho.1)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * stickyLoss)
    (hstickyLoss : 0 < stickyLoss)
    (hsmall : Kakeya.realRpowENN rho.1 stickyLoss < 1 / 4)
    (hpackingAbsorb :
      (12 * ((2 * 4 * 601 ^ 3 * 12001 ^ 3 + 1 : ℕ) : ENNReal)) *
          ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN rho.1 (-sigma + 4 * stickyLoss))
    (hepsilon₁ : 0 < epsilon₁)
    (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (htau : 0 < tau)
    (hrhoTau : rho.1 ≤ tau)
    (htauLarge : rho.1 * Real.sqrt 3 ≤ tau)
    (htauSq : tau ^ 2 ≤ 4 * rho.1)
    (htauOne : tau ≤ 1)
    (hcell :
      Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
        Kakeya.realRpowENN rho.1 3)
    (hkappa : 0 < kappa)
    (hkappaOne : kappa ≤ 1)
    (hkappaRho : rho.1 ≤ kappa)
    (hkappaProperty : Real.rpow rho.1 epsilon₃ ≤ kappa)
    (hcloseAbsorb :
      (sticky.selected.family.enncard *
          (((Kakeya.realRpowENN delta stickyLoss)⁻¹ *
              ((wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
                (55296 * Kakeya.deltaTubeVolume 1))) *
            Kakeya.realRpowENN delta (-stickyLoss))) *
          ENNReal.ofReal (10000 * kappa ^ 2) * sticky.coarse.enncard <
        Kakeya.realRpowENN rho.1 densityLoss * sticky.coarse.enncard)
    (hboundary :
      (stickyCoarseMultiplicityCap sticky *
          stickyFiberMultiplicityCap sticky) *
          ENNReal.ofReal (1000 * delta / rho.1) <
        sticky.refined.mass)
    (hretained : ∀ propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃,
      retainedFactor *
            (propertyThreeFinePullbackShading
              sticky.cover sticky.refined propP.propertyThree).mass +
          (stickyCoarseMultiplicityCap sticky *
            stickyFiberMultiplicityCap sticky) *
            ENNReal.ofReal (1000 * delta / rho.1) ≤
        (propertyThreeFinePullbackShading
          sticky.cover sticky.refined propP.propertyThree).mass) :
    ∃ propP : PureWZ2PropertyPData
        (sigma := sigma)
        (coarseShading := sticky.croppedCoarseShading)
        (tau := tau) epsilon₁ epsilon₃,
      Nonempty (Proposition63SafePullbackData sticky propP
        base.extremal.delta_pos
        (retainedFactor *
          (propertyThreeFinePullbackShading
            sticky.cover sticky.refined propP.propertyThree).mass)) := by
  let selectedC : ENNReal :=
    ((Kakeya.realRpowENN delta stickyLoss)⁻¹ *
        ((wz2PaperPureRefinementFraction delta logExponent)⁻¹ *
          (55296 * Kakeya.deltaTubeVolume 1))) *
      Kakeya.realRpowENN delta (-stickyLoss)
  have hselectedCWA : WZ2PaperConvexWolffBound
      sticky.selected.family selectedC := by
    exact sticky.selected_top_level_cwa base.extremal base.line_class
      hdeltaSmall24 (Kakeya.realRpowENN delta (-stickyLoss))
      base.top_level_cwa
  have hcoarseCWA : WZ2PaperConvexWolffBound sticky.coarse
      (sticky.selected.family.enncard * selectedC) :=
    sticky.coarse_top_level_cwa_crude base.extremal.delta_pos
      hcoverScale selectedC hselectedCWA
  rcases propertyP_refinement_of_cwa sticky.coarse_extremal
      sticky.cover.coarse_line_class hcoarseCWA hdensityLoss hstickyLoss
      hsmall hrhoSmall24 hrhoSmall10000 hpackingAbsorb hepsilon₁
      hepsilon₃ hepsilonSum htau hrhoTau htauLarge htauSq htauOne
      hcell hkappa hkappaOne hkappaRho hkappaProperty (by
        simpa [selectedC] using hcloseAbsorb) with ⟨propP⟩
  refine ⟨propP, proposition63_safe_pullback sticky propP
    base.extremal.delta_pos rho.2.1 rho.2.2
    (retainedFactor *
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree).mass)
    hboundary ?_⟩
  exact hretained propP

/-- The complete first half of the paper construction, ending immediately
before Lemma 4.3.  Every field is attached to the same first sticky output:
Property (P), the boundary-safe pullback, finite planiness, the mass-maximal
complete metric fibre, the common-slice restriction, and the selected
horizontal chart. -/
structure Proposition63FirstChartData
    {delta sigma stickyLoss localLoss commonSliceLoss
      chartLoss tau epsilon₁ epsilon₃ coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (Delta : ℝ) (retainedFactor : ENNReal) where
  delta_pos : 0 < delta
  initial : PropertyThreeSelectedInitialLocalData
    (sigma := sigma) (outputLoss := localLoss)
    (coefficient := coefficient) sticky.refined
  rebalanced : Proposition63InitialRebalancedData
    sticky.balanced initial delta_pos
  metricFiber : Proposition63MetricFiberInputData
    (stickyLoss := stickyLoss) (localLoss := localLoss)
    (coefficient := coefficient)
    (hdelta := delta_pos) rebalanced
    sticky.coarse_extremal.delta_pos
  public_unit_ball :
    metricFiber.frozenRescaled.rescalingCertificate.publicFamily.IsInUnitBall
  sliceDensity : ENNReal
  commonSlice : Proposition63CommonSliceRescaledData
    (Delta := Delta) (targetLoss := commonSliceLoss)
    metricFiber sliceDensity
  Delta_pos : 0 < Delta
  Delta_small : Delta ≤ 1 / 200
  delta_le_Delta_sq : delta ≤ Delta ^ 2
  delta_div_Delta_small : delta / Delta ≤ 1 / 4
  chartSelection : Proposition63ChartSelectionData commonSlice
    Delta_pos Delta_small delta_le_Delta_sq delta_div_Delta_small
  chartRescaled : Proposition63ChartRescaledData chartSelection chartLoss

/-- Execute the quantitative part of the first Proposition 6.2 stage after
Property (P) and the exact-scale boundary-safe pullback have been fixed.  The
only assumptions below are the scalar inequalities consumed by the named
paper lemmas. -/
theorem proposition63_first_chart_of_safe_pullback
    {delta sigma stickyLoss localLoss commonSliceLoss
      chartLoss tau epsilon₁ epsilon₃ coefficient densityLoss kappa eta : ℝ}
    {priorIncidence : ℝ} {priorL : NNReal}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent)
    (Delta : ℝ) (retainedFactor : ENNReal)
    (hdelta : 0 < delta)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (safe : Proposition63SafePullbackData sticky propP hdelta
      (retainedFactor *
        (propertyThreeFinePullbackShading
          sticky.cover sticky.refined propP.propertyThree).mass))
    (priorLocalGrains : Proposition63InitialWeakLocalGrainData
      (incidence := priorIncidence) sourceShading sigma
      (Kakeya.realRpowENN delta (-localLoss)) priorL)
    (sourceExtremal : WZ2PaperCroppedIsExtremal
      sigma stickyLoss family sourceShading)
    (hsourceLine : WZ1PaperIsLineClass family)
    (extremalMassLoss : ENNReal)
    (hextremalMassLossPos : 0 < extremalMassLoss)
    (hextremalMassLossTop : extremalMassLoss ≠ ⊤)
    (hsafeMass : extremalMassLoss⁻¹ * sourceShading.mass ≤ safe.shading.mass)
    (hstickyLocal : stickyLoss ≤ localLoss)
    (hextremalSlack : extremalMassLoss *
        Kakeya.realRpowENN delta localLoss ≤
      Kakeya.realRpowENN delta stickyLoss)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * localLoss)
    (hlocalLoss : 0 < localLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hsmall : Kakeya.realRpowENN delta localLoss < 1 / 4)
    (hfixedAbsorb :
      (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN delta (-sigma + 4 * localLoss))
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) (extendShading sticky.selected safe.shading)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * localLoss)),
        Nonempty (SparseRelativeBandCVPackage
          (extendShading sticky.selected safe.shading) prepared))
    (hdenseIncidence : eta ≤ rho.1 / 2)
    (hsparseIncidence : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa) (extendShading sticky.selected safe.shading)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * localLoss)),
      ∀ package : SparseRelativeBandCVPackage
        (extendShading sticky.selected safe.shading) prepared,
        package.tau / kappa ≤ rho.1 / 2)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hetaPositive : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hpriorL : priorL ≤ Real.toNNReal coefficient)
    (hpriorIncidence : priorIncidence ≤ rho.1 / 2)
    (hpriorIncidenceNonnegative : 0 ≤ priorIncidence)
    (hactualSmall : ∀
      (ambientExtremal : WZ2PaperCroppedIsExtremal sigma localLoss family
        (extendShading sticky.selected safe.shading)),
      ∀ coordinate, coordinate < 1 →
        (ambientExtremal.cwa_nearby_scales.chosenNearby
          (schedule.requested coordinate)).rho < 1 / 8)
    (hparentKappa : ∀
      (ambientExtremal : WZ2PaperCroppedIsExtremal sigma localLoss family
        (extendShading sticky.selected safe.shading)),
      ∀ coordinate, coordinate < 1 →
        8 * (ambientExtremal.cwa_nearby_scales.chosenNearby
          (schedule.requested coordinate)).rho < kappa)
    (hretainedFactorPos : 0 < retainedFactor)
    (hretainedFactorTop : retainedFactor ≠ ⊤)
    (hdeltaOne : delta < 1)
    (hL_pos : 0 < rho.1)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hsliceDensityAbsorb : ∀
      (initial : PropertyThreeSelectedInitialLocalData
        (sigma := sigma) (outputLoss := localLoss)
        (coefficient := coefficient) sticky.refined)
      (rebalanced : Proposition63InitialRebalancedData
        sticky.balanced initial hdelta)
      (input : Proposition63MetricFiberInputData
        (stickyLoss := stickyLoss) (localLoss := localLoss)
        (coefficient := coefficient) (hdelta := hdelta) rebalanced hL_pos),
      let sliceDensity :=
        proposition63CanonicalSliceDensity (Delta := Delta) input
      Kakeya.realRpowENN (delta / rho.1) commonSliceLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * sliceDensity ∧
      Kakeya.realRpowENN (delta / rho.1) chartLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * (sliceDensity / 2))
    (hcommonLoss : stickyLoss ≤ commonSliceLoss)
    (hcommonLossPos : 0 < commonSliceLoss)
    (hscaleSmall : delta / rho.1 ≤ 1 / 24)
    (hDelta : 0 < Delta)
    (hDeltaSmall : Delta ≤ 1 / 200)
    (hdeltaDelta : delta ≤ Delta ^ 2)
    (hdeltaRatio : delta / Delta ≤ 1 / 4)
    (hchartLoss : stickyLoss ≤ chartLoss)
    (hchartLossPos : 0 < chartLoss)
    (hpublicUnitBall : ∀
      (initial : PropertyThreeSelectedInitialLocalData
        (sigma := sigma) (outputLoss := localLoss)
        (coefficient := coefficient) sticky.refined)
      (rebalanced : Proposition63InitialRebalancedData
        sticky.balanced initial hdelta)
      (input : Proposition63MetricFiberInputData
        (stickyLoss := stickyLoss) (localLoss := localLoss)
        (coefficient := coefficient) rebalanced hL_pos),
        input.frozenRescaled.rescalingCertificate.publicFamily.IsInUnitBall) :
    Nonempty (Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := coefficient) sticky Delta
      retainedFactor) := by
  have hambientSub : PaperIsSubshading
      (extendShading sticky.selected safe.shading) sourceShading := by
    intro ambientIndex point hpoint
    by_cases himage : ∃ index, sticky.selected.embedding index = ambientIndex
    · rcases himage with ⟨index, rfl⟩
      rw [extendShading_carrier_mem] at hpoint
      exact sticky.subshading index (safe.sub_refined index hpoint)
    · rw [extendShading_carrier_empty himage] at hpoint
      exact False.elim hpoint
  have hambientMass : extremalMassLoss⁻¹ * sourceShading.mass ≤
      (extendShading sticky.selected safe.shading).mass := by
    simpa [extendShading_mass] using hsafeMass
  let safeExtremal : WZ2PaperCroppedIsExtremal sigma localLoss family
      (extendShading sticky.selected safe.shading) :=
    transfer_cropped_extremal_to_subshading extremalMassLoss
      hextremalMassLossPos hextremalMassLossTop sourceExtremal
      hambientSub hambientMass
      (Kakeya.Assouad.extendShading_cubical sticky.selected safe.cubical)
      hstickyLocal hextremalSlack hdelta sourceExtremal.delta_le_one
      hlocalLoss
  rcases finite_planiness_of_extremal_with_mass_pos safeExtremal
      hsourceLine schedule
      hdensityLoss hlocalLoss
      hdeltaSmall hsmall hfixedAbsorb hsparsePackage hdenseIncidence
      hsparseIncidence hkappaNonnegative hkappaPositive hkappaHalf
      hetaPositive hetaHalf hcoefficient (hactualSmall safeExtremal)
      (hparentKappa safeExtremal) with
    ⟨ambientPlaniness, hambientPlaninessMass⟩
  let planiness := ambientPlaniness.restrictZeroExtension sticky.selected
  have hplaninessMass : 0 < planiness.data.refinement.shading.mass := by
    rw [show planiness.data.refinement.shading.mass =
        ambientPlaniness.data.refinement.shading.mass by
      exact ambientPlaniness.data.refinement.restrictZeroExtension_mass
        sticky.selected]
    exact hambientPlaninessMass
  let rebasedBounded := safe.rebasePlaniness retainedFactor
    hretainedFactorPos hretainedFactorTop planiness
  let priorSelected := priorLocalGrains.restrictSubfamily sticky.selected
  have hfinalPrior : PaperIsSubshading
      rebasedBounded.data.refinement.shading
      (restrictPaperShading sticky.selected sourceShading) := by
    intro index point hpoint
    exact sticky.subshading index <|
      safe.sub_refined index <|
        planiness.data.refinement.subshading index hpoint
  let commonIncidence : ℝ := max priorIncidence rebasedBounded.data.incidence
  have hpriorIncidence' : priorIncidence ≤ commonIncidence := le_max_left _ _
  have hplaninessIncidence : rebasedBounded.data.incidence ≤
      commonIncidence := le_max_right _ _
  have hcommonIncidence : 0 ≤ commonIncidence :=
    hpriorIncidenceNonnegative.trans hpriorIncidence'
  let pullbackInitial :=
    PropertyThreeSelectedInitialLocalData.ofPriorLocalGrains
      rebasedBounded.data hplaninessMass priorSelected hfinalPrior hpriorL
      commonIncidence hpriorIncidence' hplaninessIncidence hcommonIncidence
  let initial := pullbackInitial.onStickyRefined sticky propP hdelta
  have hinitialIncidence : initial.incidence ≤ rho.1 / 2 := by
    change commonIncidence ≤ rho.1 / 2
    rw [max_le_iff]
    exact ⟨hpriorIncidence, rebasedBounded.incidence_le⟩
  let ambientDensity : ENNReal :=
    proposition63CanonicalAmbientDensity initial
  have hsourceDensity' :
      ambientDensity * sticky.selected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        initial.planiness.refinement.shading.mass := by
    exact (proposition63CanonicalAmbientDensity_spec initial hdelta
      sticky.selected_nonempty).le
  let firstStage : Proposition63FirstStageData
      (localLoss := localLoss) (coefficient := coefficient)
      sticky ambientDensity :=
    { delta_pos := hdelta
      initial := initial
      incidence_le_parent_half := hinitialIncidence
      source_density := hsourceDensity' }
  rcases firstStage.metricFiberInput with ⟨rebalanced, hmetricFiber⟩
  rcases hmetricFiber with ⟨metricFiber⟩
  let sliceDensity : ENNReal :=
    proposition63CanonicalSliceDensity (Delta := Delta) metricFiber
  have haggregate := proposition63CanonicalSliceDensity_spec
    (Delta := Delta) metricFiber
  rcases hsliceDensityAbsorb initial rebalanced metricFiber with
    ⟨hcommonDensityAbsorb, hchartDensityAbsorb⟩
  rcases proposition63_common_slice_rescaled metricFiber hdeltaSmall hDelta
      sliceDensity haggregate
      hcommonLoss hcommonLossPos rho.2.2 hscaleSmall
      hcommonDensityAbsorb with ⟨commonSlice⟩
  rcases proposition63_select_chart commonSlice hDelta hDeltaSmall
      hdeltaDelta hdeltaRatio with ⟨chartSelection⟩
  rcases proposition63_chart_rescaled chartSelection rho.2.2 hscaleSmall
      hchartLoss hchartLossPos hchartDensityAbsorb with ⟨chartRescaled⟩
  exact ⟨{
    delta_pos := hdelta
    initial := initial
    rebalanced := rebalanced
    metricFiber := metricFiber
    public_unit_ball := hpublicUnitBall initial rebalanced metricFiber
    sliceDensity := sliceDensity
    commonSlice := commonSlice
    Delta_pos := hDelta
    Delta_small := hDeltaSmall
    delta_le_Delta_sq := hdeltaDelta
    delta_div_Delta_small := hdeltaRatio
    chartSelection := chartSelection
    chartRescaled := chartRescaled
  }⟩

/-- Add the two structural steps immediately following the first chart
selection in `wz2_63.tex`: extend the discrete slope, then apply the dyadic
Lemma 4.3 refinement to that very chart-normalized shading. -/
structure Proposition63ThroughLemma43Data
    {delta sigma stickyLoss localLoss commonSliceLoss chartLoss
      lemma43Loss tau epsilon₁ epsilon₃ coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {Delta : ℝ} {retainedFactor : ENNReal}
    (first : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := coefficient) sticky Delta
      retainedFactor) where
  rho_eq_Delta : rho.1 = Delta
  slopes : first.chartSelection.Proposition63SlopeData
  lemma43 : Proposition63Lemma43Data
    (sigma := sigma) (sourceLoss := chartLoss)
    (targetLoss := lemma43Loss)
    (first.chartSelection.normalizedShading first.chartRescaled)
    (Delta / 2)
  normalizedCWA : ENNReal
  normalized_top_level_cwa : WZ2PaperConvexWolffBound
    (first.chartSelection.normalizedFamily first.chartRescaled)
    normalizedCWA

/-- The chart and dyadic Lemma 4.3 composition.  In particular, Lemma 4.3
is applied only after the exact-power metric-fibre and common-slice stages. -/
theorem proposition63_through_lemma43
    {delta sigma stickyLoss localLoss commonSliceLoss chartLoss
      lemma43Loss tau epsilon₁ epsilon₃ coefficient densityLoss
      tauExponent kappa43 tau43 : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      sourceShading rho logExponent}
    {Delta : ℝ} {retainedFactor : ENNReal}
    (first : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := coefficient) sticky Delta
      retainedFactor)
    (hrhoDelta : rho.1 = Delta)
    {C : ENNReal}
    (hline : WZ1PaperIsLineClass
      (first.chartSelection.normalizedFamily first.chartRescaled))
    (hsourceCWA : WZ2PaperConvexWolffBound
      (first.chartSelection.normalizedFamily first.chartRescaled) C)
    (hCV : ∀ (E : Set Point3), MeasurableSet E →
      E ⊆ (first.chartSelection.normalizedShading
        first.chartRescaled).union → ∀ (L : ENNReal),
        (∀ point ∈ E, L ≤
          (paperShadingTrilinearMultiplicity
            (first.chartSelection.normalizedShading
              first.chartRescaled) point) ^ (1 / 2 : ℝ)) →
        L * MeasureTheory.volume E ≤
          C *
            (ENNReal.ofReal ((delta / rho.1) ^ 2) *
              (first.chartSelection.normalizedFamily
                first.chartRescaled).enncard) ^ (3 / 2 : ℝ))
    (hdensityLoss : densityLoss = 2 - sigma + 3 * chartLoss)
    (hdeltaSmall : delta / rho.1 ≤ 1 / 24)
    (hbandDensityAbsorb :
      (2 * (((Nat.log 2
          (first.chartSelection.normalizedFamily
            first.chartRescaled).card + 1 : ℕ) : ENNReal))) *
        Kakeya.realRpowENN (delta / rho.1) chartLoss ≤ 1)
    (hfixedAbsorb :
      (144 : ENNReal) * ENNReal.ofReal Real.pi ≤
        Kakeya.realRpowENN (delta / rho.1) (-sigma + 4 * chartLoss))
    (hcardinality :
      ((first.chartSelection.normalizedFamily first.chartRescaled).card : ℝ) ≤
        (99 : ℝ) ^ 6 *
          Real.rpow (delta / rho.1) (-6 - chartLoss))
    (hlogAbsorb :
      2 * (Real.log
          ((99 : ℝ) ^ 6 *
            Real.rpow (delta / rho.1) (-6 - chartLoss)) /
            Real.log 2 + 1) ≤
        Real.rpow (delta / rho.1)
          ((chartLoss - lemma43Loss) / 2))
    (hlemma43FixedAbsorb :
      (49 : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho.1)
          ((chartLoss - lemma43Loss) / 2))
    (hchartLoss : 0 < chartLoss)
    (hchartLemma43 : chartLoss ≤ lemma43Loss)
    (hlemma43Loss : 0 < lemma43Loss)
    (hkappa43 : 0 < kappa43)
    (htau43 : 0 < tau43)
    (htau43Power : ENNReal.ofReal tau43 =
      Kakeya.realRpowENN (delta / rho.1) tauExponent)
    (hdenseIncidence : kappa43 ≤ Delta / 2)
    (hsparseIncidence : tau43 / kappa43 ≤ Delta / 2)
    (hpowerSmall :
      (8192 : ENNReal) *
          (((Nat.log 2
            (first.chartSelection.normalizedFamily
              first.chartRescaled).card + 1 : ℕ) : ENNReal)) ^ 2 *
          C ^ 2 ≤
        Kakeya.realRpowENN (delta / rho.1)
          (tauExponent - sigma + 5 * chartLoss)) :
    Nonempty (Proposition63ThroughLemma43Data
      (lemma43Loss := lemma43Loss) first) := by
  rcases first.chartSelection.slope_extension hrhoDelta with ⟨slopes⟩
  have htransportedExtremal :=
    first.chartSelection.normalizedExtremal first.chartRescaled
  rcases proposition63_dyadic_lemma43_weak_plane_map
      htransportedExtremal hline hdensityLoss hdeltaSmall
      hbandDensityAbsorb hfixedAbsorb hCV hcardinality hlogAbsorb
      hlemma43FixedAbsorb hchartLoss hchartLemma43 hlemma43Loss
      hkappa43 htau43 htau43Power hdenseIncidence hsparseIncidence
      hpowerSmall with ⟨lemma43⟩
  exact ⟨{
    rho_eq_Delta := hrhoDelta
    slopes := slopes
    lemma43 := lemma43
    normalizedCWA := C
    normalized_top_level_cwa := hsourceCWA
  }⟩

/- Apply the second Proposition 6.2 and Lemma 4.4 to the actual Lemma 4.3
refinement.  Node 3 exposes `inputLoss` and its scale threshold before the
caller supplies the ordinary trace source and normalization, so the loss
quantifiers cannot be accidentally swapped.  The requested scale below is
the exact `Delta` from the first power-scale identity. -/
/-
theorem proposition63_second_sticky_lemma44
    {normalizationExponent logExponent : ℕ}
    (hStickyAt : PureWZ2CroppedPropStickyAt
      normalizationExponent logExponent)
    {sigma delta : ℝ} (critical : PureWZ2CriticalPackage sigma)
    (power : Proposition63PowerScale delta sigma)
    (stickyLoss lemma44Loss : ℝ)
    (hstickyLoss : 0 < stickyLoss)
    (hstickyHalf : stickyLoss ≤ sigma / 2)
    (hsigmaHalf : sigma / 2 ≤ 1 - stickyLoss)
    (hstickyLemma44 : stickyLoss ≤ lemma44Loss)
    (hlemma44Loss : 0 < lemma44Loss) :
    ∃ sourceLoss normalizationLoss deltaBound : ℝ,
      0 < sourceLoss ∧ 0 < normalizationLoss ∧
      sourceLoss ≤ normalizationLoss / 2 ∧
      normalizationLoss < stickyLoss ∧
      0 < deltaBound ∧ deltaBound ≤ 1 ∧
      ∀ ordinarySource :
          PureWZ2ExtremalConfiguration sigma inputLoss power.h,
        ∀ normalized : PureWZ2CroppedCriticalNormalizationData
            (outputLoss := inputLoss) ordinarySource normalizationExponent,
          ∀ lemma43SourceLoss : ℝ,
            ∀ lemma43Source : WZ1PaperTubeShading normalized.croppedFamily,
            ∀ lemma43 : Proposition63Lemma43Data
              (sigma := sigma) (sourceLoss := lemma43SourceLoss)
              (targetLoss := inputLoss) lemma43Source
              ((power.secondRequested critical.sigma_pos
                critical.sigma_lt_one).1 / 2),
                  normalized.croppedRefined = lemma43.shading →
                  power.h ≤ deltaBound →
                  (∀ sticky : PureWZ2PropStickyData
                    (sigma := sigma) (outputLoss := stickyLoss)
                    lemma43.shading
                    (power.secondRequested critical.sigma_pos
                      critical.sigma_lt_one) logExponent,
                    (Kakeya.realRpowENN
                        (power.secondRequested critical.sigma_pos
                          critical.sigma_lt_one).1
                        (2 - sigma - stickyLoss) *
                      sticky.coarse.enncard) *
                        Kakeya.realRpowENN
                          (power.secondRequested critical.sigma_pos
                            critical.sigma_lt_one).1 lemma44Loss ≤
                      Kakeya.realRpowENN
                        (power.secondRequested critical.sigma_pos
                          critical.sigma_lt_one).1 stickyLoss) →
                  ∃ sticky : PureWZ2PropStickyData
                      (sigma := sigma) (outputLoss := stickyLoss)
                      lemma43.shading
                      (power.secondRequested critical.sigma_pos
                        critical.sigma_lt_one) logExponent,
                    Nonempty (Proposition63Lemma44Data
                      lemma43 sticky lemma44Loss) := by
  rcases hStickyAt sigma critical stickyLoss hstickyLoss with
    ⟨inputLoss, deltaBound, hinputLoss, hdeltaBound,
      hdeltaBoundOne, hSticky⟩
  refine ⟨inputLoss, deltaBound, hinputLoss, hdeltaBound,
    hdeltaBoundOne, ?_⟩
  intro ordinarySource normalized lemma43SourceLoss lemma43Source lemma43
    hnormalized hpowerBound hrestore
  have hwindow := power.second_sticky_window
    (stickyLoss := stickyLoss)
    hstickyHalf hsigmaHalf
  rcases hSticky power.h power.h_pos hpowerBound ordinarySource normalized
      (power.secondRequested critical.sigma_pos critical.sigma_lt_one)
      hwindow.1 hwindow.2 with ⟨sticky⟩
  rw [hnormalized] at sticky
  exact ⟨sticky, proposition63_paper_lemma44_coarse_pair lemma43 sticky
    hstickyLemma44 hlemma44Loss (hrestore sticky)⟩
-/

/-! ## The second paper stage: Lemmas 4.4, 4.7, and 4.12 -/

/- The numerical and finite-schedule input to Lemma 4.7, stored only after
Lemma 4.4 has fixed the coarse family and its plane map. -/
structure Proposition63Lemma47Certificate
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    (lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss)
    (outputLoss coefficient ratio : ℝ) where
  C : ENNReal
  top_level_cwa : WZ2PaperConvexWolffBound sticky.coarse C
  N : ℕ
  schedule : Proposition63FiniteLipschitzSchedule
    rho.1 coefficient ratio N
  kappa : ℕ → ℝ
  densityPower : ℕ → ENNReal
  densityLoss : ℝ
  densityLoss_eq : densityLoss = 2 - sigma + 3 * lemma44Loss
  lemma44Loss_pos : 0 < lemma44Loss
  source_small : Kakeya.realRpowENN rho.1 lemma44Loss < 1 / 4
  rho_small : rho.1 ≤ 1 / 10000
  directionK : ℕ → ℕ
  directionK_one : ∀ coordinate, coordinate < N →
    1 ≤ directionK coordinate
  kappa_eq : ∀ coordinate, coordinate < N →
    kappa coordinate = (directionK coordinate : ℝ) * rho.1
  directionK_scale : ∀ coordinate, coordinate < N →
    (directionK coordinate : ℝ) * rho.1 ≤ 1 / 2
  density_eq : ∀ coordinate, coordinate < N →
    densityPower coordinate =
      Kakeya.realRpowENN rho.1 densityLoss
  packing_absorb : ∀ coordinate, coordinate < N →
    (24 * ((proposition63DirectionalPointPackingConstant *
        directionK coordinate ^ 2 : ℕ) : ENNReal)) *
      ENNReal.ofReal Real.pi ≤
      Kakeya.realRpowENN rho.1 (-sigma + 4 * lemma44Loss)
  actual_small : ∀ coordinate, coordinate < N →
    ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
      (schedule.requested coordinate)).rho < 1 / 8
  parent_kappa : ∀ coordinate, coordinate < N →
    8 * ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
      (schedule.requested coordinate)).rho < kappa coordinate
  coefficient_pos : 0 < coefficient
  loss_le : lemma44Loss ≤ outputLoss
  outputLoss_pos : 0 < outputLoss
  top_absorb : C ≤ Kakeya.realRpowENN rho.1 (-outputLoss)
  restore : proposition63Lemma43MassLoss
        (∏ coordinate ∈ Finset.range N, densityPower coordinate ^ 2)
        (2 * (∏ coordinate ∈ Finset.range N,
            27 * (2 *
              (wz1OrientationCapCount
                (10 *
                    (rho.1 +
                      4 *
                        ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
                          (schedule.requested coordinate)).rho) /
                      (kappa coordinate -
                        8 *
                          ((lemma44.coarse_extremal.cwa_nearby_scales).chosenNearby
                            (schedule.requested coordinate)).rho))
                (schedule.variationScale coordinate) : ENNReal))) * 27) *
        Kakeya.realRpowENN rho.1 outputLoss ≤
      Kakeya.realRpowENN rho.1 lemma44Loss

/-- Apply Lemma 4.7 from its paper-order certificate.  The returned plane
map is definitionally the restriction of the Lemma 4.4 map. -/
theorem Proposition63Lemma47Certificate.run
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      outputLoss coefficient ratio : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    (certificate : Proposition63Lemma47Certificate
      lemma44 outputLoss coefficient ratio) :
    Nonempty (Proposition63Lemma47Data
      lemma44 outputLoss coefficient) := by
  exact proposition63_paper_lemma47_from_finite_schedule
    lemma44 certificate.top_level_cwa certificate.schedule
    certificate.kappa certificate.densityPower certificate.densityLoss
    certificate.densityLoss_eq certificate.lemma44Loss_pos
    certificate.source_small certificate.rho_small
    certificate.directionK certificate.directionK_one
    certificate.kappa_eq certificate.directionK_scale
    certificate.density_eq certificate.packing_absorb
    certificate.actual_small certificate.parent_kappa
    certificate.coefficient_pos certificate.loss_le
    certificate.outputLoss_pos certificate.top_absorb certificate.restore

/-- The quantitative Property-(P) and Cordoba input to Lemma 4.12, stored
after Lemma 4.7 so its shading and the inherited plane map are fixed. -/
structure Proposition63Lemma412Certificate
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      lemma47Loss coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    (lemma47 : Proposition63Lemma47Data
      lemma44 lemma47Loss coefficient)
    (outputLoss : ℝ) where
  parameters : CanonicalCoarsePropertyPParameters
    (sigma := sigma) (loss := lemma47Loss) lemma47.shading
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  loss_le : lemma47Loss ≤ outputLoss
  outputLoss_pos : 0 < outputLoss
  slack : (2 : ENNReal) *
      Kakeya.realRpowENN rho.1 outputLoss ≤
    Kakeya.realRpowENN rho.1 lemma47Loss
  rho_small : rho.1 ≤ 1 / 1000
  W0 : ℝ
  Vmin : ℝ
  Vtotal : ℝ
  W0_eq : W0 = 40 * rho.1
  W0_pos : 0 < W0
  Vmin_eq : Vmin =
    Real.rpow rho.1
        (1 + 7 * parameters.epsilon₁ + parameters.epsilon₃) *
      parameters.tau ^ 2 / 200
  Vmin_pos : 0 < Vmin
  Vtotal_pos : 0 < Vtotal
  volume_le : MeasureTheory.volume lemma47.shading.union ≤
    ENNReal.ofReal Vtotal
  sourceConstant : ENNReal
  source_one : 1 ≤ sourceConstant
  source_ne_top : sourceConstant ≠ ⊤
  critical_arithmetic :
    let criticalScale := 48 * rho.1 ^ 2
    ENNReal.ofReal
      ((Vtotal / Vmin) *
        (2 * (2 * W0) / criticalScale + 2)) ≤ sourceConstant
  small_cost :
    let criticalScale := 48 * rho.1 ^ 2
    10 * ((10 * sourceConstant) *
        ENNReal.ofReal (10 * criticalScale / rho.1)) ≤
      Kakeya.realRpowENN rho.1 (-outputLoss)
  large_endpoint :
    let criticalScale := 48 * rho.1 ^ 2
    3 * (2 / Real.sqrt criticalScale) ^ sigma ≤
      rho.1 ^ (-outputLoss)

/-- Apply Lemma 4.12 from its paper-order certificate, preserving the same
Lemma 4.4 plane map already used by Lemma 4.7. -/
theorem Proposition63Lemma412Certificate.run
    {delta sigma lemma43SourceLoss lemma43Loss stickyLoss lemma44Loss
      lemma47Loss outputLoss coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      lemma43.shading rho logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    {lemma47 : Proposition63Lemma47Data
      lemma44 lemma47Loss coefficient}
    (certificate : Proposition63Lemma412Certificate lemma47 outputLoss) :
    Nonempty (Proposition63Lemma412Data lemma47 outputLoss) := by
  exact proposition63_paper_lemma412_same_plane_map lemma47
    certificate.parameters certificate.sigma_pos certificate.sigma_lt_one
    certificate.loss_le certificate.outputLoss_pos certificate.slack
    certificate.rho_small certificate.W0 certificate.Vmin
    certificate.Vtotal certificate.W0_eq certificate.W0_pos
    certificate.Vmin_eq certificate.Vmin_pos certificate.Vtotal_pos
    certificate.volume_le certificate.sourceConstant
    certificate.source_one certificate.source_ne_top
    certificate.critical_arithmetic certificate.small_cost
    certificate.large_endpoint

/-- Dependent output of the second half of the paper construction.  The
types enforce that Lemmas 4.7 and 4.12 use the exact plane map selected by
Lemma 4.4; no replacement plane map can enter this record. -/
structure Proposition63ThroughLemma412Data
    {delta sigma lemma43SourceLoss lemma43Loss inputLoss
      normalizationLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) source (rho.1 / 2))
    (ordinary : Kakeya.Streamlined.TubeShading family)
    {normalizationExponent logExponent : ℕ}
    (prepared : Proposition63RegularizedReentryData
      lemma43 ordinary inputLoss normalizationLoss normalizationExponent)
    (stickyLoss lemma44Loss lemma47Loss preGrainLoss coefficient : ℝ) where
  sticky : PureWZ2PropStickyData
    (sigma := sigma) (outputLoss := stickyLoss)
    prepared.restrictedLemma43.shading rho logExponent
  lemma44 : Proposition63Lemma44Data
    prepared.restrictedLemma43 sticky lemma44Loss
  lemma47 : Proposition63Lemma47Data lemma44 lemma47Loss coefficient
  lemma412 : Proposition63Lemma412OutputData lemma47 preGrainLoss

/-- Compatibility wrapper for the former externally-certified Lemma 4.7
route.  The active paper-order wrapper below uses the internally generated
finite schedule instead. -/
theorem proposition63_rich_second_stage_through_lemma412_with_certificate
    {delta sigma lemma43SourceLoss inputLoss normalizationLoss stickyLoss
      lemma44Loss lemma47Loss preGrainLoss coefficient ratio : ℝ}
    {normalizationExponent : ℕ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := inputLoss) source (rho.1 / 2))
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (prepared : Proposition63RegularizedReentryData
      lemma43 ordinary inputLoss normalizationLoss normalizationExponent)
    (schedule : Proposition63RichStickyKernelScheduleData sigma stickyLoss)
    (reentryLoss_eq : inputLoss = schedule.sourceLoss)
    (reentryNormalizationLoss_eq :
      normalizationLoss = schedule.normalizationLoss)
    (delta_le_schedule : delta ≤ schedule.delta₀)
    (rho_lower : Real.rpow delta (1 - stickyLoss) ≤ rho.1)
    (rho_upper : rho.1 ≤ Real.rpow delta stickyLoss)
    (hstickyLemma44 : 2 * stickyLoss ≤ lemma44Loss)
    (hlemma44Loss : 0 < lemma44Loss)
    (lemma47Certificate : ∀
      (rich : Proposition63RichTerminalStickyData
        (sigma := sigma) (outputLoss := stickyLoss)
        prepared.restrictedLemma43.shading
        (prepared.normalization.toPropStickyReentryData
          prepared.target_loss_pos prepared.normalization_loss_pos) rho),
      ∀ lemma44 : Proposition63Lemma44Data
        prepared.restrictedLemma43 rich.data lemma44Loss,
        Nonempty (Proposition63Lemma47Certificate
          lemma44 lemma47Loss coefficient ratio))
    (lemma412Certificate : ∀
      (rich : Proposition63RichTerminalStickyData
        (sigma := sigma) (outputLoss := stickyLoss)
        prepared.restrictedLemma43.shading
        (prepared.normalization.toPropStickyReentryData
          prepared.target_loss_pos prepared.normalization_loss_pos) rho),
      ∀ lemma44 : Proposition63Lemma44Data
        prepared.restrictedLemma43 rich.data lemma44Loss,
      ∀ lemma47 : Proposition63Lemma47Data
        lemma44 lemma47Loss coefficient,
        Nonempty (Proposition63Lemma412Certificate
          lemma47 preGrainLoss)) :
    Nonempty (Proposition63ThroughLemma412Data
      (logExponent := 61) lemma43 ordinary prepared
      stickyLoss lemma44Loss lemma47Loss preGrainLoss coefficient) := by
  have produce := schedule.runTerminal delta lemma43.extremal.delta_pos
    delta_le_schedule
  rw [← reentryLoss_eq, ← reentryNormalizationLoss_eq] at produce
  rcases produce prepared.normalization.croppedFamily
      prepared.normalization.croppedRefined
      (prepared.normalization.toPropStickyReentryData
        prepared.target_loss_pos prepared.normalization_loss_pos)
      rho rho_lower rho_upper with ⟨rich⟩
  have rich' : Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      prepared.restrictedLemma43.shading
      (prepared.normalization.toPropStickyReentryData
        prepared.target_loss_pos prepared.normalization_loss_pos) rho := by
    simpa only [
      Proposition63RegularizedReentryData.normalization_croppedFamily,
      Proposition63RegularizedReentryData.normalization_croppedRefined]
      using rich
  rcases proposition63_paper_lemma44_coarse_pair_of_terminal
      (terminalLoss := rich'.terminalLoss)
      prepared.restrictedLemma43
      (prepared.normalization.toPropStickyReentryData
        prepared.target_loss_pos prepared.normalization_loss_pos)
      rich' hstickyLemma44 hlemma44Loss
      with ⟨lemma44⟩
  rcases lemma47Certificate rich' lemma44 with ⟨certificate47⟩
  rcases certificate47.run with ⟨lemma47⟩
  rcases lemma412Certificate rich' lemma44 lemma47 with
    ⟨certificate412⟩
  rcases certificate412.run with ⟨lemma412⟩
  exact ⟨{
    sticky := rich'.data
    lemma44 := lemma44
    lemma47 := lemma47
    lemma412 := lemma412.toOutput
  }⟩

/-- Execute the active paper-order second stage using the loss hierarchy's
backward-selected finite Lemma 4.7 schedule.  No global-product Lemma 4.7
certificate is accepted: the same rich output provides Lemma 4.4 and the
ordinary coarse re-entry consumed by the forward finite iteration. -/
theorem proposition63_rich_second_stage_through_lemma412
    {delta sigma lemma43SourceLoss inputLoss normalizationLoss
      terminalOutputLoss : ℝ}
    {normalizationExponent : ℕ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := inputLoss) source (rho.1 / 2))
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (prepared : Proposition63RegularizedReentryData
      lemma43 ordinary inputLoss normalizationLoss normalizationExponent)
    (hierarchy : Proposition63TerminalLossHierarchy sigma terminalOutputLoss)
    (schedule : Proposition63RichStickyKernelScheduleData
      sigma hierarchy.stickyLoss)
    (reentryLoss_eq : inputLoss = schedule.sourceLoss)
    (reentryNormalizationLoss_eq :
      normalizationLoss = schedule.normalizationLoss)
    (delta_le_schedule : delta ≤ schedule.delta₀)
    (rho_le_lemma47 : rho.1 ≤ hierarchy.lemma47Schedule.delta₀)
    (rho_lower : Real.rpow delta (1 - hierarchy.stickyLoss) ≤ rho.1)
    (rho_upper : rho.1 ≤ Real.rpow delta hierarchy.stickyLoss)
    (initialAxialWindow : ∀ index point,
      point ∈ prepared.normalization.frame ''
          prepared.normalization.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (lemma412Certificate : ∀
      (rich : Proposition63RichTerminalStickyData
        (sigma := sigma) (outputLoss := hierarchy.stickyLoss)
        prepared.restrictedLemma43.shading
        (prepared.normalization.toPropStickyReentryData
          prepared.target_loss_pos prepared.normalization_loss_pos) rho),
      ∀ lemma44 : Proposition63Lemma44Data
        prepared.restrictedLemma43 rich.data hierarchy.lemma44Loss,
      ∀ lemma47 : Proposition63Lemma47Data lemma44
        hierarchy.lemma47Loss
        (Real.rpow rho.1 (-hierarchy.lemma47Loss)),
        Nonempty (Proposition63Lemma412Certificate
          lemma47 hierarchy.preGrainLoss)) :
    Nonempty (Proposition63ThroughLemma412Data
      (logExponent := 61) lemma43 ordinary prepared
      hierarchy.stickyLoss hierarchy.lemma44Loss hierarchy.lemma47Loss
      hierarchy.preGrainLoss
      (Real.rpow rho.1 (-hierarchy.lemma47Loss))) := by
  have produce := schedule.runTerminal delta lemma43.extremal.delta_pos
    delta_le_schedule
  rw [← reentryLoss_eq, ← reentryNormalizationLoss_eq] at produce
  rcases produce prepared.normalization.croppedFamily
      prepared.normalization.croppedRefined
      (prepared.normalization.toPropStickyReentryData
        prepared.target_loss_pos prepared.normalization_loss_pos)
      rho rho_lower rho_upper with ⟨rich⟩
  have rich' : Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := hierarchy.stickyLoss)
      prepared.restrictedLemma43.shading
      (prepared.normalization.toPropStickyReentryData
        prepared.target_loss_pos prepared.normalization_loss_pos) rho := by
    simpa only [
      Proposition63RegularizedReentryData.normalization_croppedFamily,
      Proposition63RegularizedReentryData.normalization_croppedRefined]
      using rich
  have lemma44LossPos : 0 < hierarchy.lemma44Loss :=
    hierarchy.sticky_pos.trans hierarchy.sticky_lt_lemma44
  rcases proposition63_paper_lemma44_coarse_pair_of_terminal
      (terminalLoss := rich'.terminalLoss) prepared.restrictedLemma43
      (prepared.normalization.toPropStickyReentryData
        prepared.target_loss_pos prepared.normalization_loss_pos)
      rich' hierarchy.two_sticky_le_lemma44 lemma44LossPos with ⟨lemma44⟩
  rcases hierarchy.runLemma47 rich' lemma44 rho_le_lemma47
      initialAxialWindow with ⟨lemma47⟩
  rcases lemma412Certificate rich' lemma44 lemma47 with
    ⟨certificate412⟩
  rcases certificate412.run with ⟨lemma412⟩
  exact ⟨{
    sticky := rich'.data
    lemma44 := lemma44
    lemma47 := lemma47
    lemma412 := lemma412.toOutput
  }⟩

/- The historical direct second-stage wrapper below predates Node 3's
dual-loss kernel.  It is not used by the active Node 4 assembly.

/-- Execute the second Proposition 6.2, then Lemmas 4.4, 4.7, and 4.12 in
the literal order of `wz2_63.tex`. -/
theorem proposition63_second_stage_through_lemma412
    {sigma stickyLoss lemma44Loss lemma47Loss preGrainLoss coefficient
      ratio : ℝ}
    {normalizationExponent logExponent : ℕ}
    (critical : PureWZ2CriticalPackage sigma)
    (hStickyAt :
      PureWZ2CroppedPropStickyAt normalizationExponent logExponent)
    (hstickyLoss : 0 < stickyLoss)
    (hstickyLemma44 : stickyLoss ≤ lemma44Loss)
    (hlemma44Loss : 0 < lemma44Loss) :
    ∃ inputLoss deltaBound : ℝ,
      0 < inputLoss ∧ 0 < deltaBound ∧ deltaBound ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaBound →
        ∀ rho : WZ2PaperRequestedScale delta,
          Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
          rho.1 ≤ Real.rpow delta stickyLoss →
          ∀ lemma43SourceLoss : ℝ,
            ∀ family : Kakeya.Streamlined.TubeFamily delta,
              ∀ lemma43Source : WZ1PaperTubeShading family,
                ∀ lemma43 : Proposition63Lemma43Data
                  (sigma := sigma) (sourceLoss := lemma43SourceLoss)
                  (targetLoss := sourceLoss) lemma43Source (rho.1 / 2),
                  ∀ ordinary : Kakeya.Streamlined.TubeShading family,
                    ∀ prepared : Proposition63RegularizedReentryData
                      lemma43 ordinary sourceLoss normalizationLoss
                        normalizationExponent,
                    (∀ sticky : PureWZ2PropStickyData
                      (sigma := sigma) (outputLoss := stickyLoss)
                      prepared.restrictedLemma43.shading rho logExponent,
                      (Kakeya.realRpowENN rho.1
                          (2 - sigma - stickyLoss) *
                        sticky.coarse.enncard) *
                          Kakeya.realRpowENN rho.1 lemma44Loss ≤
                        Kakeya.realRpowENN rho.1 stickyLoss) →
                    (∀ sticky : PureWZ2PropStickyData
                        (sigma := sigma) (outputLoss := stickyLoss)
                        prepared.restrictedLemma43.shading rho logExponent,
                      ∀ lemma44 : Proposition63Lemma44Data
                        prepared.restrictedLemma43 sticky lemma44Loss,
                        Nonempty (Proposition63Lemma47Certificate
                          lemma44 lemma47Loss coefficient ratio)) →
                    (∀ sticky : PureWZ2PropStickyData
                        (sigma := sigma) (outputLoss := stickyLoss)
                        prepared.restrictedLemma43.shading rho logExponent,
                      ∀ lemma44 : Proposition63Lemma44Data
                        prepared.restrictedLemma43 sticky lemma44Loss,
                      ∀ lemma47 : Proposition63Lemma47Data
                        lemma44 lemma47Loss coefficient,
                        Nonempty (Proposition63Lemma412Certificate
                          lemma47 preGrainLoss)) →
                    Nonempty (Proposition63ThroughLemma412Data
                      (logExponent := logExponent)
                      lemma43 ordinary prepared stickyLoss lemma44Loss
                        lemma47Loss preGrainLoss coefficient) := by
  rcases proposition63_paper_lemma44_of_regularized_reentry critical
      hStickyAt hstickyLoss hstickyLemma44 hlemma44Loss with
    ⟨sourceLoss, normalizationLoss, deltaBound, hsourceLoss,
      hnormalizationLoss, hlossGap, hnormalizationSticky, hdeltaBound,
      hdeltaBoundOne, hlemma44⟩
  refine ⟨sourceLoss, normalizationLoss, deltaBound, hsourceLoss,
    hnormalizationLoss, hlossGap, hnormalizationSticky, hdeltaBound,
    hdeltaBoundOne, ?_⟩
  intro delta hdelta hdeltaLe rho hrhoLower hrhoUpper
    lemma43SourceLoss family lemma43Source lemma43 ordinary prepared
    hrestore hlemma47Certificate hlemma412Certificate
  rcases hlemma44 delta hdelta hdeltaLe rho hrhoLower hrhoUpper
      lemma43SourceLoss family lemma43Source lemma43 ordinary prepared
      hrestore with ⟨sticky, ⟨lemma44⟩⟩
  rcases hlemma47Certificate sticky lemma44 with ⟨certificate47⟩
  rcases certificate47.run with ⟨lemma47⟩
  rcases hlemma412Certificate sticky lemma44 lemma47 with
    ⟨certificate412⟩
  rcases certificate412.run with ⟨lemma412⟩
  exact ⟨{
    sticky := sticky
    lemma44 := lemma44
    lemma47 := lemma47
    lemma412 := lemma412.toOutput
  }⟩
-/

/-- Reattach the coarse global-slice estimate to the genuine regularized
second-stage family.  The source of the second Lemma 4.3 is a selected
positive-trace subfamily, so its points are mapped back through the stored
subfamily embedding before the first normalized slab estimate is used. -/
theorem Proposition63ThroughLemma412Data.preGrain
    {delta Delta sigma sticky1Loss localLoss commonSliceLoss chartLoss
      lemma43SourceLoss lemma43Loss inputLoss normalizationLoss tau epsilon₁ epsilon₃
      coefficient retainedLoss
      sticky2Loss lemma44Loss lemma47Loss preGrainLoss coefficient47 : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {firstScale : WZ2PaperRequestedScale delta}
    {firstLogExponent normalizationExponent secondLogExponent : ℕ}
    {firstSticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sticky1Loss)
      sourceShading firstScale firstLogExponent}
    {retainedFactor : ENNReal}
    (first : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := coefficient)
      firstSticky Delta retainedFactor)
    (slopes : first.chartSelection.Proposition63SlopeData)
    {secondScale : WZ2PaperRequestedScale (delta / firstScale.1)}
    {secondFamily : Kakeya.Streamlined.TubeFamily (delta / firstScale.1)}
    {lemma43Source : WZ1PaperTubeShading secondFamily}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) lemma43Source (secondScale.1 / 2)}
    (ordinary : Kakeya.Streamlined.TubeShading secondFamily)
    (prepared : Proposition63RegularizedReentryData
      lemma43 ordinary inputLoss normalizationLoss normalizationExponent)
    (second : Proposition63ThroughLemma412Data
      (sigma := sigma) (inputLoss := inputLoss)
      (normalizationLoss := normalizationLoss)
      (rho := secondScale) (normalizationExponent := normalizationExponent)
      (logExponent := secondLogExponent)
      lemma43 ordinary prepared sticky2Loss lemma44Loss
        lemma47Loss preGrainLoss coefficient47)
    (hsourceUnion : prepared.restrictedLemma43.shading.union ⊆
      (first.chartSelection.normalizedShading first.chartRescaled).union)
    (hsecondDelta : secondScale.1 = Delta)
    (hrhoDelta : firstScale.1 = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hglobalCost : Proposition63ChartSelectionData.proposition63CoarseGlobalADConstant
        delta firstScale.1 Delta localLoss coefficient ≤
      Kakeya.realRpowENN secondScale.1 (-preGrainLoss)) :
    Nonempty (PureWZ2GeneralPreGrainData second.lemma412.shading sigma
      preGrainLoss (Real.toNNReal coefficient47)
      (252000 * Real.toNNReal coefficient) 1) := by
  apply first.chartSelection.proposition63_lemma412_pregrain_of_source_union
    first.chartRescaled slopes second.lemma412 hsourceUnion
      hsecondDelta hrhoDelta hsigma hsigmaOne hglobalCost

/-- Exact-source specialization of `preGrain`.  The first chart-normalized
shading is definitionally the source of `lemma43`; regularized re-entry only
selects a subfamily and then a dense subshading.  Consequently the source-union
inclusion is internal provenance, not an additional runtime hypothesis. -/
theorem Proposition63ThroughLemma412Data.preGrainOfExactSource
    {delta Delta sigma sticky1Loss localLoss commonSliceLoss chartLoss
      lemma43SourceLoss lemma43Loss inputLoss normalizationLoss tau epsilon₁ epsilon₃ coefficient
      retainedLoss sticky2Loss lemma44Loss lemma47Loss preGrainLoss
      coefficient47 : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {firstScale : WZ2PaperRequestedScale delta}
    {firstLogExponent normalizationExponent secondLogExponent : ℕ}
    {firstSticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sticky1Loss)
      sourceShading firstScale firstLogExponent}
    {retainedFactor : ENNReal}
    (first : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := coefficient)
      firstSticky Delta retainedFactor)
    (slopes : first.chartSelection.Proposition63SlopeData)
    {secondScale : WZ2PaperRequestedScale (delta / firstScale.1)}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss)
      (first.chartSelection.normalizedShading first.chartRescaled)
      (secondScale.1 / 2))
    (ordinary : Kakeya.Streamlined.TubeShading
      (first.chartSelection.normalizedFamily first.chartRescaled))
    (prepared : Proposition63RegularizedReentryData
      lemma43 ordinary inputLoss normalizationLoss normalizationExponent)
    (second : Proposition63ThroughLemma412Data
      (sigma := sigma) (inputLoss := inputLoss)
      (normalizationLoss := normalizationLoss)
      (rho := secondScale) (normalizationExponent := normalizationExponent)
      (logExponent := secondLogExponent)
      lemma43 ordinary prepared sticky2Loss lemma44Loss lemma47Loss
        preGrainLoss coefficient47)
    (hsecondDelta : secondScale.1 = Delta)
    (hrhoDelta : firstScale.1 = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hglobalCost : Proposition63ChartSelectionData.proposition63CoarseGlobalADConstant
        delta firstScale.1 Delta localLoss coefficient ≤
      Kakeya.realRpowENN secondScale.1 (-preGrainLoss)) :
    Nonempty (PureWZ2GeneralPreGrainData second.lemma412.shading sigma
      preGrainLoss (Real.toNNReal coefficient47)
      (252000 * Real.toNNReal coefficient) 1) := by
  apply Proposition63ThroughLemma412Data.preGrain
    (retainedLoss := retainedLoss) (lemma43 := lemma43)
    first slopes ordinary prepared second
    prepared.restrictedLemma43_union_subset_source
    hsecondDelta hrhoDelta hsigma hsigmaOne hglobalCost

end Kakeya.Assouad.PureWZ2

end
