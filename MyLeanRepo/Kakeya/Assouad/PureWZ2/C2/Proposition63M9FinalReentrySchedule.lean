import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ReentryTraceFloorSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9FinalScaleCutoff
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9NestedSchedule

/-!
# Pre-runtime scalar schedule for the M9 final re-entry

This module freezes only family-free scalar data for the future final
re-entry normalization.  It does not inspect a runtime source family, target
family, shading cardinality, or quotient target.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

/-- The concrete runtime statement returned by the existing production M9
power-tail cutoff, with the cutoff parameter factored out for reuse as a
stored certificate. -/
def Proposition63M9FinalReentryPowerTailRunner
    (sourceLoss scaleLoss outputLoss outputExponent : ℝ)
    (levelCount : ℕ) (delta₀ : ℝ) : Prop :=
  ∀ {sourceDelta sigma : ℝ}, 0 < sourceDelta → sourceDelta ≤ delta₀ →
    ∀ {Lplane Lslope : NNReal}
      {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
      (sourceShading : WZ1PaperTubeShading sourceFamily)
      (sourceExtremal : WZ2PaperCroppedIsExtremal
        sigma sourceLoss sourceFamily sourceShading)
      (sourceLine : WZ1PaperIsLineClass sourceFamily)
      (sourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily)
      (sourceMidpoint : ∀ index,
        ‖wz2PaperTubeMidpoint (sourceFamily.tube index)‖ ≤ 3)
      (preGrain : PureWZ2GeneralPreGrainData sourceShading sigma sourceLoss
        Lplane Lslope 1),
      (Lplane : ℝ) ≤ proposition63M9PowerScale sourceDelta scaleLoss →
      (Lslope : ℝ) ≤ proposition63M9PowerScale sourceDelta scaleLoss →
      0 < sigma → sigma < 1 →
      ∃ hscale : 1 ≤ proposition63M9PowerScale sourceDelta scaleLoss,
      ∃ hscaleDeltaSmall :
          proposition63M9PowerScale sourceDelta scaleLoss * sourceDelta ≤
            1 / 1000,
      ∃ sourceData : Proposition63M9MildRescalingSourceData sourceShading
          sourceExtremal sourceLine sourceDistinct sourceMidpoint preGrain
          hscale hscaleDeltaSmall levelCount
          (Kakeya.realRpowENN sourceDelta (-outputExponent)),
      ∃ sourceSchedule : WZ2PaperPureFiniteNearbyScheduleData
          (fine := sourceData.selected.family)
          (Kakeya.realRpowENN sourceDelta (-outputExponent))
          (Kakeya.realRpowENN sourceDelta (-(8 * sourceLoss))) levelCount,
        ∀ targetData : Proposition63M9MildRescalingQuotientTargetData
            sourceData sourceSchedule,
          Nonempty (Proposition63M9RobustQuotientTailCertificates
            (outputLoss := outputLoss) targetData)

/-- Family-free scalar schedule for the final M9 re-entry normalization.

The final hierarchy loss is `outputLoss`.  The M9 tail is first run at
`grainLoss`, then the re-entry source loss is `ordinaryLoss`, with
`grainLoss < ordinaryLoss < outputLoss / 2`.  The actual production M9
parameter is not chosen independently: it is the nested schedule's
`outer.preGrainLoss`. -/
structure Proposition63M9FinalReentryLossSchedule
    (sigma outputLoss : ℝ)
    (critical : PureWZ2CriticalPackage sigma) where
  traceFloorLoss : ℝ
  traceFloorLoss_eq : traceFloorLoss = outputLoss / 8
  traceFloorLoss_pos : 0 < traceFloorLoss
  traceSchedule :
    PureWZ2ReentryTraceFloorSchedule sigma traceFloorLoss traceFloorLoss
  grainLoss : ℝ
  grainLoss_eq :
    grainLoss =
      min (outputLoss / 8) (traceSchedule.traceSourceCeiling / 4)
  ordinaryLoss : ℝ
  ordinaryLoss_eq : ordinaryLoss = 2 * grainLoss
  grainLoss_pos : 0 < grainLoss
  ordinaryLoss_pos : 0 < ordinaryLoss
  grainLoss_lt_ordinaryLoss : grainLoss < ordinaryLoss
  ordinaryLoss_lt_half_output : ordinaryLoss < outputLoss / 2
  ordinaryLoss_le_traceSource :
    ordinaryLoss ≤ traceSchedule.traceSourceCeiling
  nested : Proposition63M9NestedScheduleData sigma grainLoss critical
  p : ℝ
  p_eq : p = nested.outer.preGrainLoss
  p_pos : 0 < p
  p_lt_one : p < 1
  m9SourceLoss : ℝ
  m9SourceLoss_eq : m9SourceLoss = 4 * p
  m9OutputExponent : ℝ
  m9OutputExponent_eq : m9OutputExponent = 16 * p
  m9_source_gap :
    3 * m9SourceLoss + 3 * p < m9OutputExponent
  m9_tail_gap :
    18 * m9SourceLoss + 12 * p < grainLoss
  robustSchedule :
    Proposition63M9RobustTailScheduleData m9SourceLoss 1 1
  powerTailCutoff : ℝ
  powerTailCutoff_pos : 0 < powerTailCutoff
  powerTailCutoff_le_one : powerTailCutoff ≤ 1
  powerTail_run :
    Proposition63M9FinalReentryPowerTailRunner
      (4 * nested.outer.preGrainLoss) nested.outer.preGrainLoss grainLoss
      (16 * nested.outer.preGrainLoss)
      robustSchedule.levelCount powerTailCutoff
  finalScaleCutoff : ℝ
  finalScaleCutoff_pos : 0 < finalScaleCutoff
  finalScaleCutoff_le_one : finalScaleCutoff ≤ 1
  finalScale_le_traceCutoff :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ finalScaleCutoff →
      proposition63M9PowerScale delta p * delta ≤ traceSchedule.delta₀
  denseCropCutoff : ℝ
  denseCropCutoff_pos : 0 < denseCropCutoff
  denseCropCutoff_le_one : denseCropCutoff ≤ 1
  dense_crop_absorption :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ denseCropCutoff →
      Kakeya.realRpowENN delta traceSchedule.densityLoss ≤
        (73 / 100 : ENNReal) *
          Kakeya.realRpowENN delta ordinaryLoss
  finalScale_le_denseCropCutoff :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ finalScaleCutoff →
      proposition63M9PowerScale delta p * delta ≤ denseCropCutoff
  delta₀ : ℝ
  delta₀_eq :
    delta₀ =
      min traceSchedule.delta₀
        (min robustSchedule.delta₀
          (min powerTailCutoff (min finalScaleCutoff denseCropCutoff)))
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1

namespace Proposition63M9FinalReentryLossSchedule

variable {sigma outputLoss : ℝ} {critical : PureWZ2CriticalPackage sigma}
    (schedule : Proposition63M9FinalReentryLossSchedule
      sigma outputLoss critical)

theorem delta₀_le_trace : schedule.delta₀ ≤ schedule.traceSchedule.delta₀ := by
  rw [schedule.delta₀_eq]
  exact min_le_left _ _

theorem delta₀_le_robust : schedule.delta₀ ≤ schedule.robustSchedule.delta₀ := by
  rw [schedule.delta₀_eq]
  exact (min_le_right _ _).trans <| min_le_left _ _

theorem delta₀_le_powerTail :
    schedule.delta₀ ≤ schedule.powerTailCutoff := by
  rw [schedule.delta₀_eq]
  exact (min_le_right _ _).trans <|
    (min_le_right _ _).trans (min_le_left _ _)

theorem delta₀_le_finalScale :
    schedule.delta₀ ≤ schedule.finalScaleCutoff := by
  rw [schedule.delta₀_eq]
  exact (min_le_right _ _).trans <|
    (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)

theorem delta₀_le_denseCrop :
    schedule.delta₀ ≤ schedule.denseCropCutoff := by
  rw [schedule.delta₀_eq]
  exact (min_le_right _ _).trans <|
    (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_right _ _)

theorem targetDelta_le_traceCutoff
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaSmall : delta ≤ schedule.delta₀) :
    proposition63M9PowerScale delta schedule.p * delta ≤
      schedule.traceSchedule.delta₀ :=
  schedule.finalScale_le_traceCutoff hdelta
    (hdeltaSmall.trans schedule.delta₀_le_finalScale)

theorem trace_absorption_for_ordinaryLoss
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ schedule.traceSchedule.delta₀) :
    (Kakeya.realRpowENN delta
        (-(schedule.traceSchedule.criticalFloor.structuralLoss -
          schedule.traceSchedule.densityLoss)))⁻¹ ≤
      (100 : ENNReal)⁻¹ *
        (Kakeya.realRpowENN delta schedule.ordinaryLoss / 2) :=
  schedule.traceSchedule.trace_absorption delta hdelta hdeltaSmall
    schedule.ordinaryLoss schedule.ordinaryLoss_pos.le
    schedule.ordinaryLoss_le_traceSource

end Proposition63M9FinalReentryLossSchedule

/-- Construct the complete family-free final re-entry schedule.  The only
assumptions are the critical package and a small public output-loss budget;
all choices are made before any runtime family or cardinality is known. -/
theorem exists_proposition63_m9_final_reentry_loss_schedule
    {sigma outputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (houtputLoss : 0 < outputLoss)
    (houtputLoss_le_one : outputLoss ≤ 1) :
    Nonempty (Proposition63M9FinalReentryLossSchedule
      sigma outputLoss critical) := by
  let traceFloorLoss : ℝ := outputLoss / 8
  have traceFloorLoss_pos : 0 < traceFloorLoss := by
    dsimp only [traceFloorLoss]
    positivity
  rcases critical.reentryTraceFloorSchedule
      (floorLoss := traceFloorLoss)
      (structuralBudget := traceFloorLoss)
      traceFloorLoss_pos traceFloorLoss_pos le_rfl with
    ⟨traceSchedule⟩
  let grainLoss : ℝ :=
    min (outputLoss / 8) (traceSchedule.traceSourceCeiling / 4)
  let ordinaryLoss : ℝ := 2 * grainLoss
  have grainLoss_pos : 0 < grainLoss := by
    dsimp only [grainLoss]
    exact lt_min (by positivity)
      (div_pos traceSchedule.traceSourceCeiling_pos (by norm_num))
  have ordinaryLoss_pos : 0 < ordinaryLoss := by
    dsimp only [ordinaryLoss]
    positivity
  have grainLoss_lt_ordinaryLoss : grainLoss < ordinaryLoss := by
    dsimp only [ordinaryLoss]
    linarith [grainLoss_pos]
  have ordinaryLoss_lt_half_output :
      ordinaryLoss < outputLoss / 2 := by
    have hgrain : grainLoss ≤ outputLoss / 8 := by
      dsimp only [grainLoss]
      exact min_le_left _ _
    dsimp only [ordinaryLoss]
    linarith [houtputLoss]
  have ordinaryLoss_le_traceSource :
      ordinaryLoss ≤ traceSchedule.traceSourceCeiling := by
    have hgrain : grainLoss ≤ traceSchedule.traceSourceCeiling / 4 := by
      dsimp only [grainLoss]
      exact min_le_right _ _
    dsimp only [ordinaryLoss]
    linarith [traceSchedule.traceSourceCeiling_pos]
  have grainLoss_le_one : grainLoss ≤ 1 := by
    have hgrain : grainLoss ≤ outputLoss / 8 := by
      dsimp only [grainLoss]
      exact min_le_left _ _
    linarith
  rcases proposition63_m9_nested_schedule critical grainLoss_pos with
    ⟨nested⟩
  let p : ℝ := nested.outer.preGrainLoss
  have p_pos : 0 < p := by
    dsimp only [p]
    exact nested.outer.preGrain_pos
  have p_lt_one : p < 1 := by
    dsimp only [p]
    exact nested.outer.preGrain_lt_output.trans_le grainLoss_le_one
  have m9SourceLoss_pos : 0 < 4 * p := by
    positivity
  have tailArithmetic :=
    proposition63_m9_production_power_tail_losses
      p_pos nested.outer.eightyFour_preGrain_lt_output
  rcases proposition63_m9_robust_tail_schedule
      (4 * p) m9SourceLoss_pos 1 1 with
    ⟨robustSchedule⟩
  rcases exists_proposition63_m9_power_source_and_robust_tail_cutoff
      (4 * p) p grainLoss (16 * p) robustSchedule.levelCount
      m9SourceLoss_pos p_pos.le p_lt_one robustSchedule.levelCount_loss
      (by ring) tailArithmetic.1 grainLoss_le_one tailArithmetic.2.1 with
    ⟨powerTailCutoff, powerTailCutoff_pos, powerTailCutoff_le_one,
      powerTail_run⟩
  have ordinaryLoss_lt_densityLoss :
      ordinaryLoss < traceSchedule.densityLoss := by
    have hgrain : grainLoss ≤ traceSchedule.traceSourceCeiling / 4 := by
      dsimp only [grainLoss]
      exact min_le_right _ _
    rw [traceSchedule.traceSourceCeiling_eq] at hgrain
    rw [traceSchedule.densityLoss_eq]
    dsimp only [ordinaryLoss]
    linarith [traceSchedule.criticalFloor.structuralLoss_pos]
  let denseCropGap :=
    traceSchedule.densityLoss - ordinaryLoss
  have denseCropGap_pos : 0 < denseCropGap := by
    dsimp only [denseCropGap]
    linarith
  rcases exists_delta_realRpowENN_bound
      (2 : ENNReal) (by norm_num) denseCropGap_pos with
    ⟨denseCropCutoff, denseCropCutoff_pos, denseCropCutoff_le_one,
      denseCropBound⟩
  have denseCropAbsorption :
      ∀ {delta : ℝ}, 0 < delta → delta ≤ denseCropCutoff →
        Kakeya.realRpowENN delta traceSchedule.densityLoss ≤
          (73 / 100 : ENNReal) *
            Kakeya.realRpowENN delta ordinaryLoss := by
    intro delta deltaPos deltaLe
    have coefficientBound :
        (2 : ENNReal) ≤
          Kakeya.realRpowENN delta (-denseCropGap) :=
      denseCropBound delta deltaPos deltaLe
    have twiceDense :
        (2 : ENNReal) *
            Kakeya.realRpowENN delta traceSchedule.densityLoss ≤
          Kakeya.realRpowENN delta ordinaryLoss := by
      calc
        (2 : ENNReal) *
              Kakeya.realRpowENN delta traceSchedule.densityLoss ≤
            Kakeya.realRpowENN delta (-denseCropGap) *
              Kakeya.realRpowENN delta traceSchedule.densityLoss := by
          gcongr
        _ = Kakeya.realRpowENN delta ordinaryLoss := by
          rw [← realRpowENN_add deltaPos]
          congr 2
          dsimp only [denseCropGap]
          ring
    have halfLe : (1 / 2 : ENNReal) ≤ 73 / 100 := by
      exact (ENNReal.toReal_le_toReal
        (ENNReal.div_ne_top (by norm_num) (by norm_num))
        (ENNReal.div_ne_top (by norm_num) (by norm_num))).mp (by norm_num)
    calc
      Kakeya.realRpowENN delta traceSchedule.densityLoss =
          (1 / 2 : ENNReal) *
            ((2 : ENNReal) *
              Kakeya.realRpowENN delta traceSchedule.densityLoss) := by
        have halfTwo : (1 / 2 : ENNReal) * 2 = 1 := by
          calc
            (1 / 2 : ENNReal) * 2 = 2 * 2⁻¹ := by
              rw [ENNReal.div_eq_inv_mul]
              ring
            _ = 1 :=
              ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        rw [← mul_assoc, halfTwo, one_mul]
      _ ≤ (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta ordinaryLoss := by
        gcongr
      _ ≤ (73 / 100 : ENNReal) *
          Kakeya.realRpowENN delta ordinaryLoss := by
        simpa [mul_comm] using
          mul_le_mul_left halfLe
            (Kakeya.realRpowENN delta ordinaryLoss)
  have targetCutoff_pos :
      0 < min traceSchedule.delta₀ denseCropCutoff :=
    lt_min traceSchedule.delta₀_pos denseCropCutoff_pos
  rcases exists_proposition63_m9_final_scale_cutoff p_lt_one
      targetCutoff_pos with
    ⟨finalScaleCutoff, finalScaleCutoff_pos, finalScaleCutoff_le_one,
      finalScale_le_targetCutoff⟩
  have finalScale_le_traceCutoff :
      ∀ {delta : ℝ}, 0 < delta → delta ≤ finalScaleCutoff →
        proposition63M9PowerScale delta p * delta ≤ traceSchedule.delta₀ :=
    fun {_} deltaPos deltaLe =>
      (finalScale_le_targetCutoff deltaPos deltaLe).trans (min_le_left _ _)
  have finalScale_le_denseCropCutoff :
      ∀ {delta : ℝ}, 0 < delta → delta ≤ finalScaleCutoff →
        proposition63M9PowerScale delta p * delta ≤ denseCropCutoff :=
    fun {_} deltaPos deltaLe =>
      (finalScale_le_targetCutoff deltaPos deltaLe).trans (min_le_right _ _)
  let delta₀ : ℝ :=
    min traceSchedule.delta₀
      (min robustSchedule.delta₀
        (min powerTailCutoff (min finalScaleCutoff denseCropCutoff)))
  have delta₀_pos : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min traceSchedule.delta₀_pos <|
      lt_min robustSchedule.delta₀_pos <|
        lt_min powerTailCutoff_pos <|
          lt_min finalScaleCutoff_pos denseCropCutoff_pos
  have delta₀_le_one : delta₀ ≤ 1 := by
    dsimp only [delta₀]
    exact (min_le_left _ _).trans traceSchedule.delta₀_le_one
  exact ⟨{
    traceFloorLoss := traceFloorLoss
    traceFloorLoss_eq := rfl
    traceFloorLoss_pos := traceFloorLoss_pos
    traceSchedule := traceSchedule
    grainLoss := grainLoss
    grainLoss_eq := rfl
    ordinaryLoss := ordinaryLoss
    ordinaryLoss_eq := rfl
    grainLoss_pos := grainLoss_pos
    ordinaryLoss_pos := ordinaryLoss_pos
    grainLoss_lt_ordinaryLoss := grainLoss_lt_ordinaryLoss
    ordinaryLoss_lt_half_output := ordinaryLoss_lt_half_output
    ordinaryLoss_le_traceSource := ordinaryLoss_le_traceSource
    nested := nested
    p := p
    p_eq := rfl
    p_pos := p_pos
    p_lt_one := p_lt_one
    m9SourceLoss := 4 * p
    m9SourceLoss_eq := rfl
    m9OutputExponent := 16 * p
    m9OutputExponent_eq := rfl
    m9_source_gap := tailArithmetic.1
    m9_tail_gap := tailArithmetic.2.1
    robustSchedule := robustSchedule
    powerTailCutoff := powerTailCutoff
    powerTailCutoff_pos := powerTailCutoff_pos
    powerTailCutoff_le_one := powerTailCutoff_le_one
    powerTail_run := powerTail_run
    finalScaleCutoff := finalScaleCutoff
    finalScaleCutoff_pos := finalScaleCutoff_pos
    finalScaleCutoff_le_one := finalScaleCutoff_le_one
    finalScale_le_traceCutoff := finalScale_le_traceCutoff
    denseCropCutoff := denseCropCutoff
    denseCropCutoff_pos := denseCropCutoff_pos
    denseCropCutoff_le_one := denseCropCutoff_le_one
    dense_crop_absorption := denseCropAbsorption
    finalScale_le_denseCropCutoff := finalScale_le_denseCropCutoff
    delta₀ := delta₀
    delta₀_eq := rfl
    delta₀_pos := delta₀_pos
    delta₀_le_one := delta₀_le_one
  }⟩

end Kakeya.Assouad.PureWZ2

end
