import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectCommonYSourceAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCWAScalarClosure
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalFinalDensityScalar
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalFinalDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalTopLevelAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalGlobalCeilingBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalFinalVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalLossGaps
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationTerminalAssembly

/-!
# Final assembly for the actual direct half-offset terminal

This is the TeX 682--686 and 407--408 assembly boundary.  Every public field
is attached to the same literal fixed-lambda terminal, the same local-packing
cleanup, and the same final jointly selected family and shading.
-/

noncomputable section

namespace Kakeya.Assouad

open PureWZ2DirectCommonYSourceAssembly
open PureWZ2DirectCommonYSourceAssembly.TerminalGeometry
open PureWZ2DirectCommonYSourceAssembly.TerminalPlaneData
open PureWZ2DirectCommonYSourceAssembly.TerminalGeometry.PureWZ2ExternalWeightRegularizationData
open PureWZ2DirectCommonYSourceAssembly.TerminalGeometry.PureWZ2ExternalWeightRegularizationData.DirectHalfOffsetTerminalCWAScheduleData

/-- The actual fixed-lambda terminal route proves the frozen large-slope
statement from the certified fixed-scale Proposition 6.2 construction. -/
theorem pureWZ2_direct_halfOffset_large_slope :
    PureWZ2LargeSlopeStatement := by
  intro hsubunit hcritical hsticky hgrains hc2grains
  have hC2 : PureWZ2C2GrainsFromCriticalStatement :=
    hc2grains hsubunit hcritical hsticky hgrains
  rcases Prop62PaperAudit.V4.Prop62V4DirectNode6FixedScaleCertified.fixedScaleStatement with
    ⟨logExponent, certifiedProvider⟩
  intro sigma critical outputLoss outputDeltaBound houtputLoss houtputDeltaBound
  rcases exists_pureWZ2FinalQuotientLossSchedule
      critical.sigma_pos critical.sigma_lt_one houtputLoss with
    ⟨schedule⟩
  have houtputNonneg : 0 ≤ outputLoss := houtputLoss.le
  have hnearbyNonneg : 0 ≤ schedule.nearbyLoss := schedule.nearby_loss_pos.le
  rcases exists_delta_for_cleanup_source_regularization_fixed_schedule
        schedule.epsilon schedule.epsilon_pos with
    ⟨cleanupScale, hcleanupScale, hcleanupScaleOne, hcleanup⟩
  rcases exists_delta_for_actual_requested_cwa_budgets
        schedule.epsilon schedule.nearbyLoss
        (pureWZ2FixedScheduleLevelCount schedule.epsilon)
        schedule.epsilon_pos hnearbyNonneg
        schedule.directHalfOffsetTerminal_cwa_gap with
    ⟨cwaScale, hcwaScale, hcwaScaleOne, hcwa⟩
  rcases exists_delta_for_actualLocalPacking_final_density_budget
        outputLoss schedule.epsilon_pos (by linarith)
        schedule.directHalfOffsetTerminal_density_gap with
    ⟨densityScale, hdensityScale, hdensityScaleOne, hdensity⟩
  rcases exists_delta_for_cubicalShading_global_ad_uniform_at_outputLoss
        schedule.nearbyLoss schedule.epsilon_pos hnearbyNonneg
        schedule.directHalfOffsetTerminal_global_gap with
    ⟨globalScale, hglobalScale, hglobalScaleOne, hglobal⟩
  rcases exists_delta_for_localGrainData_at_outputLoss_uniform
        schedule.epsilon outputLoss schedule.epsilon_pos houtputNonneg
        schedule.directHalfOffsetTerminal_local_gap with
    ⟨localScale, hlocalScale, hlocalScaleOne, hlocal⟩
  rcases exists_delta_for_directHalfOffsetFinalVolume_source_power_absorption
        schedule.epsilon sigma schedule.nearbyLoss outputLoss
        schedule.epsilon_pos critical.sigma_lt_one
        (by linarith [schedule.nearby_loss_le_output])
        (schedule.directHalfOffsetTerminal_volume_gap critical.sigma_pos.le) with
    ⟨volumeScale, hvolumeScale, hvolumeScaleOne, hvolume⟩
  rcases exists_delta_for_directHalfOffsetTerminal_top_level_absorption
        schedule.nearbyLoss outputLoss schedule.directHalfOffsetTerminal_top_level_gap with
    ⟨topScale, htopScale, htopScaleOne, htop⟩
  rcases exists_delta_for_halfOffsetLineClassTargetDelta_half_power_upper with
    ⟨radiusScale, hradiusScale, hradiusScaleOne, hradius⟩
  let analyticScale := min cleanupScale <| min cwaScale <|
    min densityScale <| min globalScale <| min localScale <|
      min volumeScale <| min topScale radiusScale
  have hanalyticScale : 0 < analyticScale := by
    dsimp only [analyticScale]
    positivity
  let targetCap := min 1 outputDeltaBound
  have htargetCap : 0 < targetCap := lt_min (by norm_num) houtputDeltaBound
  let sourceBound := min analyticScale (targetCap ^ 2)
  have hsourceBound : 0 < sourceBound := by
    dsimp only [sourceBound]
    exact lt_min hanalyticScale (sq_pos_of_pos htargetCap)
  rcases pureWZ2_direct_commonY_source_assembly hC2 certifiedProvider
      sigma critical schedule.epsilon sourceBound
      schedule.epsilon_pos schedule.epsilon_le_sixty_fourth hsourceBound with
    ⟨delta, hdelta, hdeltaBound, ⟨commonSource⟩⟩
  have hdeltaAnalytic : delta ≤ analyticScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaTargetSquare : delta ≤ targetCap ^ 2 :=
    hdeltaBound.trans (min_le_right _ _)
  rcases le_min_iff.mp hdeltaAnalytic with ⟨hdeltaCleanup, hrest₁⟩
  rcases le_min_iff.mp hrest₁ with ⟨hdeltaCWA, hrest₂⟩
  rcases le_min_iff.mp hrest₂ with ⟨hdeltaDensity, hrest₃⟩
  rcases le_min_iff.mp hrest₃ with ⟨hdeltaGlobal, hrest₄⟩
  rcases le_min_iff.mp hrest₄ with ⟨hdeltaLocal, hrest₅⟩
  rcases le_min_iff.mp hrest₅ with ⟨hdeltaVolume, hrest₆⟩
  rcases le_min_iff.mp hrest₆ with ⟨hdeltaTop, hdeltaRadius⟩
  rcases commonSource.toTerminalGeometry with ⟨terminal⟩
  rcases commonSource.toHalfOffsetTerminalSaturationPlaneMapCore terminal with
    ⟨planeCore⟩
  let planeData : commonSource.TerminalPlaneData :=
    { geometry := terminal, core := planeCore }
  rcases toLocalDistinctCleanup (commonSource := commonSource) terminal with
    ⟨cleanup⟩
  rcases hcleanup commonSource hdelta hdeltaCleanup terminal cleanup with
    ⟨regularization, hregularizedTwo⟩
  have hsourceOne : 1 ≤ Kakeya.realRpowENN delta
      (-commonSource.halfOffsetAssembly.technicalLoss) := by
    rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hdelta
      commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one
      (by linarith [commonSource.halfOffsetAssembly.technicalLoss_nonneg])
  have hambientLeOutput : Kakeya.realRpowENN delta
        (-commonSource.halfOffsetAssembly.technicalLoss) ≤
      regularization.outputConstant :=
    regularization.ambientConstant_le_outputConstant hsourceOne (by simp [pow_two])
  have hepsilonLevels : ENNReal.ofReal (1 / delta) ≤
      Kakeya.realRpowENN delta (-schedule.epsilon) ^
        pureWZ2FixedScheduleLevelCount schedule.epsilon :=
    pureWZ2FixedScheduleLevelCount_covers_inv hdelta
      commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one
      schedule.epsilon_pos
  have hepsilonSource : Kakeya.realRpowENN delta (-schedule.epsilon) ≤
      Kakeya.realRpowENN delta
        (-commonSource.halfOffsetAssembly.technicalLoss) :=
    realRpowENN_antitone hdelta
      commonSource.halfOffsetAssembly.cfg.extremal.delta_le_one
      (neg_le_neg commonSource.epsilon_le_halfOffsetAssembly_technicalLoss)
  have hlevels : ENNReal.ofReal (1 / delta) ≤
      regularization.outputConstant ^
        pureWZ2FixedScheduleLevelCount schedule.epsilon :=
    hepsilonLevels.trans <| pow_le_pow_left'
      (hepsilonSource.trans hambientLeOutput) _
  have hsourceSquare : regularization.outputConstant *
      regularization.outputConstant ≤ regularization.outputConstant ^ 2 := by
    exact le_of_eq (pow_two regularization.outputConstant).symm
  rcases directHalfOffsetTerminal_cwa_schedule_of_geometry
      (commonSource := commonSource)
      (sourceScheduleConstant := regularization.outputConstant ^ 2)
      (parentLevelCount := pureWZ2FixedScheduleLevelCount schedule.epsilon)
      regularization hregularizedTwo hlevels hsourceSquare with
    ⟨scheduleData, hlineFactor⟩
  have hcwaBudgets := hcwa commonSource
    commonSource.halfOffsetAssembly.technicalLoss rfl
    commonSource.halfOffsetAssembly.technicalLoss_le_two_epsilon
    hdelta hdeltaCWA terminal cleanup regularization scheduleData hlineFactor
  have htargetFinite : WZ2PaperFiniteErrorConstant
      (Kakeya.realRpowENN terminal.targetDelta (-schedule.nearbyLoss)) := by
    constructor
    · rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        commonSource.halfOffsetLineClassTargetDelta_pos
        (commonSource.halfOffsetLineClassTargetDelta_small.le.trans (by norm_num))
        (by linarith [schedule.nearby_loss_pos])
    · simp [Kakeya.realRpowENN]
  rcases scheduleData.toRequestedCWAData htargetFinite
      hcwaBudgets.1 hcwaBudgets.2 with
    ⟨requested⟩
  have hdensityBudget := hdensity commonSource
    commonSource.halfOffsetAssembly.technicalLoss_le_two_epsilon
    hdelta hdeltaDensity terminal cleanup regularization
  have hambientGlobal := hglobal commonSource
    commonSource.halfOffsetAssembly.technicalLoss_le_two_epsilon
    critical.sigma_pos critical.sigma_lt_one hdelta hdeltaGlobal terminal
  have hvolumeBudget := hvolume commonSource hdelta hdeltaVolume terminal
  rcases hlocal commonSource critical.sigma_pos critical.sigma_lt_one
      hdelta hdeltaLocal planeData with
    ⟨ambientLocal⟩
  have htopBudget := htop commonSource hdelta hdeltaTop terminal
  have hnearbyLeOutput : Kakeya.realRpowENN terminal.targetDelta
        (-schedule.nearbyLoss) ≤
      Kakeya.realRpowENN terminal.targetDelta (-outputLoss) :=
    realRpowENN_antitone commonSource.halfOffsetLineClassTargetDelta_pos
      (commonSource.halfOffsetLineClassTargetDelta_small.le.trans (by norm_num))
      (by linarith [schedule.nearby_loss_le_output])
  have houtputOne : 1 ≤ Kakeya.realRpowENN terminal.targetDelta (-outputLoss) := by
    rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      commonSource.halfOffsetLineClassTargetDelta_pos
      (commonSource.halfOffsetLineClassTargetDelta_small.le.trans (by norm_num))
      (by linarith)
  have houtputTop : Kakeya.realRpowENN terminal.targetDelta (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hfinalVolume := requested.finalShading_volume_upper outputLoss
    critical.sigma_pos critical.sigma_lt_one
    (by simp [Kakeya.realRpowENN]) hambientGlobal hvolumeBudget
  have hfinalProjection := requested.finalShading_projection_upper outputLoss
    critical.sigma_pos critical.sigma_lt_one
    (by simp [Kakeya.realRpowENN]) hambientGlobal hvolumeBudget
  let terminalData : PureWZ2HorizontalTerminalData
      (sigma := sigma) (nearbyLoss := schedule.nearbyLoss)
      (outputLoss := outputLoss)
      (safePublicSlope commonSource terminal)
      requested.finalTarget requested.finalShading :=
    { slope_nonsingular :=
        safePublicSlope_nonsingular commonSource terminal
      delta_pos := commonSource.halfOffsetLineClassTargetDelta_pos
      delta_le_one :=
        commonSource.halfOffsetLineClassTargetDelta_small.le.trans (by norm_num)
      output_loss_pos := houtputLoss
      nearby_loss_pos := schedule.nearby_loss_pos
      nearby_loss_le_one := schedule.nearby_loss_le_one
      nearby_loss_le_output := schedule.nearby_loss_le_output
      nonempty := requested.finalTarget_nonempty
      line_class := requested.finalTarget_line_class
      cubical := requested.finalShading_cubical
      nearby_cwa := requested.toNearbyCWA
      carrier_subset := requested.finalTarget_ordinary_carrier_subset_paper
      top_level_absorption := htopBudget
      dense := requested.finalShading_dense_of_selectedWeightLevel_budget
        outputLoss hdensityBudget
      volume_upper := hfinalVolume
      projection_upper := hfinalProjection
      global_ad := fun z hz =>
        (requested.finalShading_global_ad
          (safePublicSlope commonSource terminal) hambientGlobal z hz).weaken_constant
            hnearbyLeOutput houtputOne houtputTop
      local_grains := requested.finalLocalGrains ambientLocal }
  have htargetHalf := hradius commonSource hdelta hdeltaRadius
  have hsqrtDelta : Real.sqrt delta ≤ targetCap := by
    apply (Real.sqrt_le_iff).2
    exact ⟨le_of_lt htargetCap, hdeltaTargetSquare⟩
  have htargetOutput : terminal.targetDelta ≤ outputDeltaBound := by
    calc
      terminal.targetDelta ≤ Real.rpow delta (1 / 2) := htargetHalf
      _ = Real.sqrt delta := (Real.sqrt_eq_rpow delta).symm
      _ ≤ targetCap := hsqrtDelta
      _ ≤ outputDeltaBound := min_le_right _ _
  exact ⟨terminal.targetDelta,
    commonSource.halfOffsetLineClassTargetDelta_pos,
    htargetOutput, ⟨terminalData.toLargeSlopeConfiguration⟩⟩

end Kakeya.Assouad

end
