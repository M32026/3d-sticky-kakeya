import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichJointHeightClosureSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.RichEndpointScalarSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyMixedNumericSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64P7ScaleSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64SelectedSourceFrostmanSchedule

/-!
# Production schedule for the direct-rich endpoint

The terminal paper-order loss is chosen before the direct-rich endpoint loss.
The ordinary prefix is then selected backwards from that endpoint, and every
runtime cutoff is finally intersected.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2C2RichEndpointClosureSchedule
    (capability : PureWZ2PropStickyCapability)
    (sigma outputLoss targetDelta₀ C Ctotal : ℝ) where
  mild : PureWZ2Proposition64MildRescalingScalarSchedule
    outputLoss targetDelta₀ C Ctotal
  terminalFinalLoss : ℝ := mild.epsilon₂ / (8 * mild.levelCount)
  terminalFinalLoss_eq :
    terminalFinalLoss = mild.epsilon₂ / (8 * mild.levelCount)
  terminalFinalLoss_pos : 0 < terminalFinalLoss
  terminal : PureWZ2ReentrantTerminalPaperOrderSchedule
    capability sigma terminalFinalLoss
  ordinary : PureWZ2C2OrdinaryGlobalSchedule
    capability sigma outputLoss targetDelta₀ C Ctotal
  mild_eq : ordinary.mild = mild
  endpointLoss_le_terminalSticky :
    ordinary.endpointOutputLoss ≤ terminal.kernel.terminal.stickyLoss
  endpointLoss_twice_le_terminalSticky :
    2 * ordinary.endpointOutputLoss ≤
      terminal.kernel.terminal.stickyLoss
  endpointLoss_le_terminalSource :
    ordinary.endpointOutputLoss ≤ terminal.sourceLossCeiling
  exactCoreAbsorption : PureWZ2RichEndpointExactCoreAbsorption
  quantitativeMassAbsorption :
    PureWZ2RichEndpointQuantitativeMassAbsorption
      terminal.sourceLossCeiling terminal.localMassLoss
        terminal.kernel.terminal.workingLoss
  mixedNumeric : PureWZ2MixedHierarchyNumericSchedule
    ordinary.mild.levelCount sigma terminalFinalLoss
      ordinary.mild.epsilon₂ ordinary.mild.workLoss
  slabDensityLoss : ℝ := 5 * ordinary.mild.epsilon₂
  slabDensityLoss_eq :
    slabDensityLoss = 5 * ordinary.mild.epsilon₂
  rescalingLoss : ℝ := 6 * ordinary.mild.epsilon₂
  rescalingLoss_eq : rescalingLoss = 6 * ordinary.mild.epsilon₂
  jointDensity : PureWZ2Proposition64JointDensitySchedule
    ordinary.mild.levelCount slabDensityLoss rescalingLoss targetDelta₀
  selectedSourceFrostman :
    PureWZ2Proposition64SelectedSourceFrostmanSchedule
      ordinary.mild.levelCount ordinary.mild.epsilon₂ slabDensityLoss
        (outputLoss / 2)
  p7Scale : PureWZ2Proposition64P7ScaleSchedule outputLoss
  p7Rounding : p7Scale.RoundingCutoff
  p7Volume :
    PureWZ2Proposition64P7ScaleSchedule.VolumeCutoff
      sigma outputLoss ordinary.mild.epsilon₂
  p7Terminal :
    PureWZ2Proposition64P7ScaleSchedule.TerminalCutoff
      (outputLoss / 2) p7Scale.nearbyLoss outputLoss
  p7ScalePowerLoss_lt_nearby :
    48 * ordinary.mild.epsilon₂ < p7Scale.nearbyLoss
  totalLoss : ℝ := ordinary.ordinaryEndpointLoss + rescalingLoss
  totalLoss_eq : totalLoss = ordinary.ordinaryEndpointLoss + rescalingLoss
  totalLoss_le_eight_epsilon₂ :
    totalLoss ≤ 8 * ordinary.mild.epsilon₂
  totalLoss_le_totalMargin :
    totalLoss ≤ Ctotal * ordinary.mild.epsilon₂
  totalLoss_le_outputMargin :
    totalLoss ≤ (1 - C * ordinary.mild.epsilon₂) * outputLoss
  commonDelta₀ : ℝ :=
    min (pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀) <|
      min (1 / 144 : ℝ) <| min ordinary.commonDelta₀ <|
      min terminal.delta₀ <| min exactCoreAbsorption.delta₀ <|
        min quantitativeMassAbsorption.delta₀ <|
          min mixedNumeric.delta₀ <| min jointDensity.sourceDelta₀
            (min selectedSourceFrostman.delta₀
              (min p7Rounding.delta₀
                (min p7Volume.delta₀ p7Terminal.delta₀)))
  commonDelta₀_eq : commonDelta₀ =
    min (pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀)
      (min (1 / 144 : ℝ) (min ordinary.commonDelta₀
        (min terminal.delta₀ (min exactCoreAbsorption.delta₀
          (min quantitativeMassAbsorption.delta₀
            (min mixedNumeric.delta₀ (min jointDensity.sourceDelta₀
              (min selectedSourceFrostman.delta₀
                (min p7Rounding.delta₀
                  (min p7Volume.delta₀ p7Terminal.delta₀))))))))))
  commonDelta₀_pos : 0 < commonDelta₀
  commonDelta₀_le_lemma35 : commonDelta₀ ≤
    pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀
  commonDelta₀_le_endpointSquare : commonDelta₀ ≤ 1 / 144
  commonDelta₀_le_ordinary : commonDelta₀ ≤ ordinary.commonDelta₀
  commonDelta₀_le_terminal : commonDelta₀ ≤ terminal.delta₀
  commonDelta₀_le_exactCore : commonDelta₀ ≤ exactCoreAbsorption.delta₀
  commonDelta₀_le_quantitativeMass :
    commonDelta₀ ≤ quantitativeMassAbsorption.delta₀
  commonDelta₀_le_mixedNumeric : commonDelta₀ ≤ mixedNumeric.delta₀
  commonDelta₀_le_jointDensity : commonDelta₀ ≤ jointDensity.sourceDelta₀
  commonDelta₀_le_selectedSourceFrostman :
    commonDelta₀ ≤ selectedSourceFrostman.delta₀
  commonDelta₀_le_p7Rounding : commonDelta₀ ≤ p7Rounding.delta₀
  commonDelta₀_le_p7Volume : commonDelta₀ ≤ p7Volume.delta₀
  commonDelta₀_le_p7Terminal : commonDelta₀ ≤ p7Terminal.delta₀

theorem exists_pureWZ2C2RichEndpointClosureSchedule
    (capability : PureWZ2PropStickyCapability)
    {sigma outputLoss targetDelta₀ C Ctotal : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (houtput : 0 < outputLoss)
    (htarget : 0 < targetDelta₀)
    (hC : 0 < C)
    (hCtotal : 64 ≤ Ctotal) :
    Nonempty (PureWZ2C2RichEndpointClosureSchedule
      capability sigma outputLoss targetDelta₀ C Ctotal) := by
  rcases exists_pureWZ2Proposition64MildRescalingScalarSchedule
      houtput htarget hC (by linarith) with ⟨mild⟩
  let terminalFinalLoss := mild.epsilon₂ / (8 * mild.levelCount)
  have hterminalFinal : 0 < terminalFinalLoss := by
    dsimp only [terminalFinalLoss]
    have hNpos : (0 : ℝ) < (mild.levelCount : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega) mild.levelCount_ge_two)
    exact div_pos mild.epsilon₂_pos (mul_pos (by norm_num) hNpos)
  rcases pureWZ2_reentrantTerminal_paperOrderSchedule capability critical
      critical.sigma_pos critical.sigma_lt_one hterminalFinal with ⟨terminal⟩
  have hterminalStickyPos : 0 < terminal.kernel.terminal.stickyLoss := by
    calc
      0 < terminal.sourceLossCeiling := terminal.sourceLossCeiling_pos
      _ ≤ terminal.kernel.sourceLossCeiling :=
        terminal.sourceLossCeiling_kernel
      _ ≤ terminal.kernel.terminal.sourceLossCeiling :=
        terminal.kernel.sourceLossCeiling_terminal
      _ < terminal.kernel.terminal.stickyLoss :=
        terminal.kernel.terminal.sourceLossCeiling_lt_stickyLoss
  rcases pureWZ2C2_ordinaryGlobalScheduleWithEndpointBound capability critical
      mild houtput htarget hC (by linarith)
      (endpointBound := min (terminal.kernel.terminal.stickyLoss / 2)
        terminal.sourceLossCeiling)
      (show 0 < min (terminal.kernel.terminal.stickyLoss / 2)
          terminal.sourceLossCeiling by
        exact lt_min
          (div_pos hterminalStickyPos (by norm_num))
          terminal.sourceLossCeiling_pos) with
    ⟨ordinary, hordinaryMild, hordinaryBound⟩
  rcases pureWZ2_richEndpointExactCore_absorption with
    ⟨exactCoreAbsorption⟩
  have hendpointHalf : ordinary.endpointOutputLoss ≤
      terminal.kernel.terminal.stickyLoss / 2 :=
    ordinary.endpointOutputLoss_le_bound.trans <| by
      rw [hordinaryBound]
      exact min_le_left _ _
  have hendpointSource : ordinary.endpointOutputLoss ≤
      terminal.sourceLossCeiling :=
    ordinary.endpointOutputLoss_le_bound.trans <| by
      rw [hordinaryBound]
      exact min_le_right _ _
  have hquantitativeGap : terminal.sourceLossCeiling +
      terminal.localMassLoss < terminal.kernel.terminal.workingLoss := by
    have hsourceSticky : terminal.sourceLossCeiling <
        terminal.kernel.terminal.stickyLoss :=
      terminal.sourceLossCeiling_kernel.trans
        terminal.kernel.sourceLossCeiling_terminal |>.trans_lt
          terminal.kernel.terminal.sourceLossCeiling_lt_stickyLoss
    linarith [terminal.localMassLoss_lt_gap]
  rcases pureWZ2_richEndpointQuantitativeMass_absorption
      terminal.sourceLossCeiling terminal.localMassLoss
      terminal.kernel.terminal.workingLoss hquantitativeGap with
    ⟨quantitativeMassAbsorption⟩
  have hNfour : 4 ≤ ordinary.mild.levelCount := by
    rw [hordinaryMild]
    exact mild.levelCount_ge_four
  have hterminalLevelZero : terminalFinalLoss ≤
      ordinary.mild.epsilon₂ /
        (4 * (ordinary.mild.levelCount : ℝ)) := by
    rw [hordinaryMild]
    dsimp only [terminalFinalLoss]
    have hNpos : (0 : ℝ) < (mild.levelCount : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega) mild.levelCount_ge_two)
    have hdenom : (0 : ℝ) < 8 * mild.levelCount := by positivity
    have hdenom' : (0 : ℝ) < 4 * mild.levelCount := by positivity
    exact (div_le_div_iff_of_pos_left mild.epsilon₂_pos hdenom hdenom').2
      (by nlinarith)
  have hepsilonUpper : ordinary.mild.epsilon₂ ≤
      1 / (ordinary.mild.levelCount : ℝ) := by
    rw [hordinaryMild, mild.epsilon₂_eq]
  rcases pureWZ2_mixed_hierarchy_numeric_schedule (sigma := sigma) hNfour
      hterminalFinal
      ordinary.mild.epsilon₂_pos ordinary.mild.workLoss_eq.ge hepsilonUpper
      hterminalLevelZero with ⟨mixedNumeric⟩
  let slabDensityLoss := 5 * ordinary.mild.epsilon₂
  let rescalingLoss := 6 * ordinary.mild.epsilon₂
  have hslabDensity : 0 < slabDensityLoss := by
    dsimp only [slabDensityLoss]
    exact mul_pos (by norm_num) ordinary.mild.epsilon₂_pos
  have hlossGap : slabDensityLoss < rescalingLoss := by
    dsimp only [slabDensityLoss, rescalingLoss]
    linarith [ordinary.mild.epsilon₂_pos]
  rcases exists_pureWZ2Proposition64JointDensitySchedule
      ordinary.mild.levelCount_ge_two hslabDensity hlossGap htarget with
    ⟨jointDensity⟩
  rcases exists_pureWZ2Proposition64SelectedSourceFrostmanSchedule
      (show 0 < ordinary.mild.levelCount by
        omega) ordinary.mild.epsilon₂_pos ordinary.mild.epsilon₂_eq
      (show slabDensityLoss = 5 * ordinary.mild.epsilon₂ by rfl)
      (by
        rw [hordinaryMild]
        exact mild.ten_epsilon₂_lt_half_output) with
    ⟨selectedSourceFrostman⟩
  let p7Scale :=
    PureWZ2Proposition64P7ScaleSchedule.canonical houtput
  rcases p7Scale.exists_roundingCutoff with ⟨p7Rounding⟩
  have hvolumeGap : 4 * ordinary.mild.epsilon₂ < outputLoss := by
    rw [hordinaryMild]
    linarith [mild.epsilon₂_pos, mild.ten_epsilon₂_lt_half_output]
  rcases PureWZ2Proposition64P7ScaleSchedule.exists_volumeCutoff
      (sigma := sigma) houtput ordinary.mild.epsilon₂_pos hvolumeGap with
    ⟨p7Volume⟩
  rcases PureWZ2Proposition64P7ScaleSchedule.exists_terminalCutoff
      (show outputLoss / 2 < outputLoss by linarith)
      p7Scale.nearbyLoss_lt_output with
    ⟨p7Terminal⟩
  have hp7ScalePowerLoss :
      48 * ordinary.mild.epsilon₂ < p7Scale.nearbyLoss := by
    have htotal :
        64 * ordinary.mild.epsilon₂ ≤
          (1 - C * ordinary.mild.epsilon₂) * outputLoss := by
      rw [hordinaryMild]
      exact (mul_le_mul_of_nonneg_right hCtotal mild.epsilon₂_pos.le).trans
        mild.total_loss_margin
    have hrescaling : 0 < C * ordinary.mild.epsilon₂ :=
      mul_pos hC ordinary.mild.epsilon₂_pos
    rw [p7Scale.nearbyLoss_eq]
    nlinarith [houtput]
  let totalLoss := ordinary.ordinaryEndpointLoss + rescalingLoss
  have htotalEight : totalLoss ≤ 8 * ordinary.mild.epsilon₂ := by
    dsimp only [totalLoss, rescalingLoss]
    linarith [ordinary.ordinaryEndpointLoss_le_two_epsilon₂]
  have htotalMargin : totalLoss ≤ Ctotal * ordinary.mild.epsilon₂ :=
    htotalEight.trans <|
      mul_le_mul_of_nonneg_right (show (8 : ℝ) ≤ Ctotal by linarith)
        ordinary.mild.epsilon₂_pos.le
  have htotalOutput : totalLoss ≤
      (1 - C * ordinary.mild.epsilon₂) * outputLoss :=
    htotalMargin.trans <| by
      rw [hordinaryMild]
      exact mild.total_loss_margin
  let commonDelta₀ :=
    min (pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀) <|
      min (1 / 144 : ℝ) <| min ordinary.commonDelta₀ <|
    min terminal.delta₀ <| min exactCoreAbsorption.delta₀ <|
      min quantitativeMassAbsorption.delta₀ <|
          min mixedNumeric.delta₀ <| min jointDensity.sourceDelta₀
            (min selectedSourceFrostman.delta₀
              (min p7Rounding.delta₀
                (min p7Volume.delta₀ p7Terminal.delta₀)))
  exact ⟨{
    mild := mild
    terminalFinalLoss := terminalFinalLoss
    terminalFinalLoss_eq := rfl
    terminalFinalLoss_pos := hterminalFinal
    terminal := terminal
    ordinary := ordinary
    mild_eq := hordinaryMild
    endpointLoss_le_terminalSticky := hendpointHalf.trans <|
      div_le_self hterminalStickyPos.le (by norm_num)
    endpointLoss_twice_le_terminalSticky := by linarith
    endpointLoss_le_terminalSource := hendpointSource
    exactCoreAbsorption := exactCoreAbsorption
    quantitativeMassAbsorption := quantitativeMassAbsorption
    mixedNumeric := mixedNumeric
    slabDensityLoss := slabDensityLoss
    slabDensityLoss_eq := rfl
    rescalingLoss := rescalingLoss
    rescalingLoss_eq := rfl
    jointDensity := jointDensity
    selectedSourceFrostman := selectedSourceFrostman
    p7Scale := p7Scale
    p7Rounding := p7Rounding
    p7Volume := p7Volume
    p7Terminal := p7Terminal
    p7ScalePowerLoss_lt_nearby := hp7ScalePowerLoss
    totalLoss := totalLoss
    totalLoss_eq := rfl
    totalLoss_le_eight_epsilon₂ := htotalEight
    totalLoss_le_totalMargin := htotalMargin
    totalLoss_le_outputMargin := htotalOutput
    commonDelta₀ := commonDelta₀
    commonDelta₀_eq := rfl
    commonDelta₀_pos :=
      lt_min (pureWZ2Proposition64Lemma35SourceCeiling_pos htarget) <|
        lt_min (by norm_num) <| lt_min ordinary.commonDelta₀_pos <|
          lt_min terminal.delta₀_pos <|
            lt_min exactCoreAbsorption.delta₀_pos <|
              lt_min quantitativeMassAbsorption.delta₀_pos <|
                lt_min mixedNumeric.delta₀_pos <|
                  lt_min jointDensity.sourceDelta₀_pos <|
                    lt_min selectedSourceFrostman.delta₀_pos
                      (lt_min p7Rounding.delta₀_pos
                        (lt_min p7Volume.delta₀_pos p7Terminal.delta₀_pos))
    commonDelta₀_le_lemma35 := min_le_left _ _
    commonDelta₀_le_endpointSquare :=
      (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_ordinary :=
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_terminal :=
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_exactCore := (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_quantitativeMass := (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_mixedNumeric := (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_jointDensity := (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans <|
                (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_selectedSourceFrostman := (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans <|
                (min_le_right _ _).trans <|
                  (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_p7Rounding := (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans <|
                (min_le_right _ _).trans <|
                  (min_le_right _ _).trans <|
                    (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_p7Volume := (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans <|
                (min_le_right _ _).trans <|
                  (min_le_right _ _).trans <|
                    (min_le_right _ _).trans <|
                      (min_le_right _ _).trans (min_le_left _ _)
    commonDelta₀_le_p7Terminal := (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans <|
                (min_le_right _ _).trans <|
                  (min_le_right _ _).trans <|
                    (min_le_right _ _).trans <|
                      (min_le_right _ _).trans (min_le_right _ _) }⟩

end Kakeya.Assouad

end
