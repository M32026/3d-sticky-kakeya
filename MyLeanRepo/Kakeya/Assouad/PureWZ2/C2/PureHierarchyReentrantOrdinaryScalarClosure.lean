import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantOrdinarySchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyNearbyCWASchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers

/-!
# Uniform scalar closure for one refreshed ordinary hierarchy step

All exponents and the small-scale threshold are selected before the runtime
source.  The only source-dependent input used below is the density lower bound
already stored in its exact re-entry record.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2HierarchyReentrantOrdinaryScalarClosure
    {sigma outputLoss structuralBudget : ℝ}
    (schedule : PureWZ2ReentryTraceFloorSchedule
      sigma outputLoss structuralBudget) where
  grainLoss : ℝ := schedule.densityLoss / 8
  grainLoss_eq : grainLoss = schedule.densityLoss / 8
  inputEta : ℝ := schedule.densityLoss / 2
  inputEta_eq : inputEta = schedule.densityLoss / 2
  outputEta : ℝ := 3 * schedule.densityLoss / 4
  outputEta_eq : outputEta = 3 * schedule.densityLoss / 4
  sourceLossCeiling : ℝ
  sourceLossCeiling_eq : sourceLossCeiling = grainLoss
  sourceLossCeiling_pos : 0 < sourceLossCeiling
  sourceLossCeiling_le_grain : sourceLossCeiling ≤ grainLoss
  cwaSchedule : PureWZ2HierarchyNearbyCWASchedule sourceLossCeiling
    schedule.densityLoss inputEta outputEta
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_schedule : delta₀ ≤ schedule.delta₀
  delta₀_le_cwa : delta₀ ≤ cwaSchedule.delta₀
  runtime :
    ∀ inputLoss : ℝ,
      0 < inputLoss → inputLoss ≤ sourceLossCeiling →
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ {normalizationExponent : ℕ},
          ∀ current : PureWZ2ReentrantGrainSource
              sigma inputLoss delta normalizationExponent,
            PureWZ2HierarchyReentrantOrdinaryScalarReceipt
              (grainLoss := grainLoss) (outputEta := outputEta)
              (inputEta := inputEta) current
              (Kakeya.realRpowENN delta inputEta) schedule
              sourceLossCeiling

/-- Choose the complete non-CWA scalar ledger before the runtime source. -/
theorem pureWZ2_reentrantOrdinary_scalarClosure
    {sigma outputLoss structuralBudget : ℝ}
    (schedule : PureWZ2ReentryTraceFloorSchedule
      sigma outputLoss structuralBudget)
    (structuralBudget_le_half : structuralBudget ≤ outputLoss / 2) :
    Nonempty (PureWZ2HierarchyReentrantOrdinaryScalarClosure schedule) := by
  let grainLoss := schedule.densityLoss / 8
  let inputEta := schedule.densityLoss / 2
  let outputEta := 3 * schedule.densityLoss / 4
  let sourceLossCeiling := schedule.densityLoss / 8
  have grainLoss_pos : 0 < grainLoss := by
    dsimp only [grainLoss]
    linarith [schedule.densityLoss_pos]
  have inputEta_pos : 0 < inputEta := by
    dsimp only [inputEta]
    linarith [schedule.densityLoss_pos]
  have outputEta_pos : 0 < outputEta := by
    dsimp only [outputEta]
    linarith [schedule.densityLoss_pos]
  have separationGap : 0 < outputEta - inputEta := by
    dsimp only [outputEta, inputEta]
    linarith [schedule.densityLoss_pos]
  have sourceLossCeiling_pos : 0 < sourceLossCeiling := by
    dsimp only [sourceLossCeiling, grainLoss]
    linarith [schedule.densityLoss_pos]
  have sourceLossCeiling_lt_density :
      sourceLossCeiling < schedule.densityLoss := by
    dsimp only [sourceLossCeiling, grainLoss]
    linarith [schedule.densityLoss_pos]
  have restrictionGap :
      0 < schedule.densityLoss - inputEta - 2 * sourceLossCeiling := by
    dsimp only [inputEta, sourceLossCeiling, grainLoss]
    linarith [schedule.densityLoss_pos]
  rcases exists_pureWZ2HierarchyNearbyCWASchedule
      schedule.densityLoss_pos sourceLossCeiling_lt_density
      restrictionGap separationGap with ⟨cwaSchedule⟩
  rcases Subunit.exists_delta₀_mul_pow_le_one
      2 (by norm_num) (outputEta - inputEta) separationGap with
    ⟨separationDelta₀, separationDelta₀_pos, separationDelta₀_one,
      separationAbsorption⟩
  have densityGap : 0 < schedule.densityLoss - outputEta := by
    dsimp only [outputEta]
    linarith [schedule.densityLoss_pos]
  rcases pure_wz2_exists_delta₀_constant_rpow_le_one
      (constant := 13824) (gap := schedule.densityLoss - outputEta)
      (by norm_num) densityGap with
    ⟨densityDelta₀, densityDelta₀_pos, densityDelta₀_one,
      densityAbsorption⟩
  let sourceEnvelope := sourceLossCeiling / 2 + grainLoss
  have inputGap : 0 < inputEta - sourceEnvelope := by
    dsimp only [inputEta, sourceEnvelope, sourceLossCeiling, grainLoss]
    linarith [schedule.densityLoss_pos]
  rcases pure_wz2_exists_delta₀_constant_rpow_le_one
      (constant := 200) (gap := inputEta - sourceEnvelope)
      (by norm_num) inputGap with
    ⟨inputDelta₀, inputDelta₀_pos, inputDelta₀_one, inputAbsorption⟩
  let delta₀ := min schedule.delta₀
    (min cwaSchedule.delta₀
      (min separationDelta₀ (min densityDelta₀ inputDelta₀)))
  have delta₀_pos : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min schedule.delta₀_pos <|
      lt_min cwaSchedule.delta₀_pos <|
        lt_min separationDelta₀_pos <|
          lt_min densityDelta₀_pos inputDelta₀_pos
  refine ⟨{
    grainLoss := grainLoss
    grainLoss_eq := rfl
    inputEta := inputEta
    inputEta_eq := rfl
    outputEta := outputEta
    outputEta_eq := rfl
    sourceLossCeiling := sourceLossCeiling
    sourceLossCeiling_eq := rfl
    sourceLossCeiling_pos := sourceLossCeiling_pos
    sourceLossCeiling_le_grain := le_rfl
    cwaSchedule := cwaSchedule
    delta₀ := delta₀
    delta₀_pos := delta₀_pos
    delta₀_le_one := (min_le_left _ _).trans schedule.delta₀_le_one
    delta₀_le_schedule := min_le_left _ _
    delta₀_le_cwa := (min_le_right _ _).trans (min_le_left _ _)
    runtime := ?_
  }⟩
  intro runtimeLoss runtimeLoss_pos runtimeLoss_le delta delta_pos delta_le
    normalizationExponent current
  have delta_one : delta ≤ 1 :=
    delta_le.trans ((min_le_left _ _).trans schedule.delta₀_le_one)
  have delta_separation : delta ≤ separationDelta₀ :=
    delta_le.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have delta_density : delta ≤ densityDelta₀ :=
    delta_le.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have delta_input : delta ≤ inputDelta₀ :=
    delta_le.trans <| (min_le_right _ _).trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  have delta_cwa : delta ≤ cwaSchedule.delta₀ :=
    delta_le.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have cwaAbsorption := cwaSchedule.absorb delta_pos delta_cwa
    (pureWZ2HierarchyReentrantOrdinary_card_log_bound current)
  have ordinaryLoss_le_envelope :
      current.ordinaryLoss + grainLoss ≤ sourceEnvelope := by
    have ordinaryLoss_le : current.ordinaryLoss ≤ sourceLossCeiling / 2 :=
      current.reentry.sourceLoss_le_half.trans <| by
        gcongr
    dsimp only [sourceEnvelope]
    linarith
  have exponentGap :
      inputEta - sourceEnvelope ≤
        inputEta - (current.ordinaryLoss + grainLoss) := by
    linarith
  have inputAbsorptionActual :
      ENNReal.ofReal (200 : ℝ) * Kakeya.realRpowENN delta
          (inputEta - (current.ordinaryLoss + grainLoss)) ≤ 1 := by
    exact (mul_le_mul_left'
      (pure_wz2_rpowENN_antitone delta_pos delta_one exponentGap)
      (ENNReal.ofReal (200 : ℝ))).trans
        (inputAbsorption delta delta_pos delta_input)
  have inputPower : Kakeya.realRpowENN delta inputEta ≤
      ENNReal.ofReal (200 : ℝ)⁻¹ *
        Kakeya.realRpowENN delta (current.ordinaryLoss + grainLoss) :=
    pure_wz2_density_power_from_absorption delta_pos (by norm_num)
      inputAbsorptionActual
  have inputDensity : Kakeya.realRpowENN delta inputEta ≤
      (100 : ENNReal)⁻¹ * current.reentry.geometry.ordinaryDensity *
        Kakeya.realRpowENN delta grainLoss := by
    calc
      Kakeya.realRpowENN delta inputEta ≤
          ENNReal.ofReal (200 : ℝ)⁻¹ *
            Kakeya.realRpowENN delta
              (current.ordinaryLoss + grainLoss) := inputPower
      _ = (100 : ENNReal)⁻¹ *
            (Kakeya.realRpowENN delta current.ordinaryLoss / 2) *
              Kakeya.realRpowENN delta grainLoss := by
        rw [realRpowENN_add delta_pos]
        have hconstant : ENNReal.ofReal (200 : ℝ)⁻¹ =
            (100 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹ := by
          rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 200)]
          rw [show ENNReal.ofReal (200 : ℝ) = (200 : ENNReal) by norm_num]
          rw [show (200 : ENNReal) = (100 : ENNReal) * 2 by norm_num]
          exact ENNReal.mul_inv (by norm_num) (by norm_num)
        rw [hconstant]
        simp only [div_eq_mul_inv]
        ring
      _ ≤ (100 : ENNReal)⁻¹ *
            current.reentry.geometry.ordinaryDensity *
              Kakeya.realRpowENN delta grainLoss := by
        gcongr
        exact current.reentry.ordinary_density_budget
  have grainPowerOne : Kakeya.realRpowENN delta grainLoss ≤ 1 :=
    (pure_wz2_rpowENN_antitone delta_pos delta_one grainLoss_pos.le).trans_eq
      (by simp [Kakeya.realRpowENN])
  have croppedMass : Kakeya.realRpowENN delta inputEta ≤
      (100 : ENNReal)⁻¹ * current.reentry.geometry.ordinaryDensity := by
    exact inputDensity.trans <| by
      calc
        (100 : ENNReal)⁻¹ * current.reentry.geometry.ordinaryDensity *
              Kakeya.realRpowENN delta grainLoss ≤
            (100 : ENNReal)⁻¹ * current.reentry.geometry.ordinaryDensity * 1 := by
          gcongr
        _ = (100 : ENNReal)⁻¹ *
            current.reentry.geometry.ordinaryDensity := by simp
  have separationReal :
      2 * Real.rpow delta (outputEta - inputEta) ≤ 1 :=
    separationAbsorption delta delta_pos delta_separation
  have densityAbsorptionActual :
      (13824 : ENNReal) * Kakeya.realRpowENN delta
          schedule.densityLoss ≤
        Kakeya.realRpowENN delta outputEta := by
    have absorbed := densityAbsorption delta delta_pos delta_density
    have split : Kakeya.realRpowENN delta schedule.densityLoss =
        Kakeya.realRpowENN delta (schedule.densityLoss - outputEta) *
          Kakeya.realRpowENN delta outputEta := by
      calc
        Kakeya.realRpowENN delta schedule.densityLoss =
            Kakeya.realRpowENN delta
              ((schedule.densityLoss - outputEta) + outputEta) := by
          congr 1
          ring
        _ = Kakeya.realRpowENN delta (schedule.densityLoss - outputEta) *
              Kakeya.realRpowENN delta outputEta :=
          realRpowENN_add delta_pos _ _
    calc
      (13824 : ENNReal) *
            Kakeya.realRpowENN delta schedule.densityLoss =
          (ENNReal.ofReal (13824 : ℝ) *
              Kakeya.realRpowENN delta
                (schedule.densityLoss - outputEta)) *
            Kakeya.realRpowENN delta outputEta := by
        rw [split]
        norm_num
        ring
      _ ≤ 1 * Kakeya.realRpowENN delta outputEta := by gcongr
      _ = Kakeya.realRpowENN delta outputEta := by simp
  have outputGrain : outputEta + grainLoss ≤ outputLoss := by
    dsimp only [outputEta, grainLoss]
    have densityLoss_le_output : schedule.densityLoss ≤ outputLoss :=
      schedule.densityLoss_le_floor
    linarith
  have topLevelAbsorption :
      ((Kakeya.realRpowENN delta outputEta)⁻¹ * 1) *
          Kakeya.realRpowENN delta (-grainLoss) ≤
        Kakeya.realRpowENN delta (-outputLoss) := by
    rw [mul_one, pure_wz2_realRpowENN_inv delta_pos,
      ← realRpowENN_add delta_pos]
    exact pure_wz2_rpowENN_antitone delta_pos delta_one (by linarith)
  exact
    { input_loss_le := runtimeLoss_le.trans (by rfl)
      delta_le_schedule := delta_le.trans (min_le_left _ _)
      densitySeparation :=
        pure_wz2_pruning_power_bound delta_pos separationReal
      inputDensityAbsorption := inputDensity
      croppedMassAbsorption := croppedMass
      input_loss_le_cwa := runtimeLoss_le
      cwa_epsilon_pos := by
        exact sub_pos.mpr sourceLossCeiling_lt_density
      cwaRestrictionAbsorption := cwaAbsorption.1
      cwaCardinalityAbsorption := cwaAbsorption.2
      grainLoss_le_density := by
        dsimp only [grainLoss]
        linarith [schedule.densityLoss_pos]
      densityLoss_le_half := by
        rw [schedule.densityLoss_eq]
        linarith [schedule.criticalFloor.structuralLoss_pos,
          schedule.criticalFloor.structuralLoss_le,
          structuralBudget_le_half]
      outputEta_le_structural := by
        dsimp only [outputEta]
        rw [schedule.densityLoss_eq]
        linarith [schedule.criticalFloor.structuralLoss_pos]
      densityAbsorption := densityAbsorptionActual
      topLevelAbsorption := topLevelAbsorption }

end Kakeya.Assouad

end
