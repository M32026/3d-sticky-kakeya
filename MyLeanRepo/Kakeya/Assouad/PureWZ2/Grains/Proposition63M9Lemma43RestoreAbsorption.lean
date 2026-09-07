import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScalePlaneMap

/-!
# Proposition 6.3 M9: family-independent Lemma 4.3 restore absorption

The cutoff in this file is chosen before the runtime extremal family.  The
runtime specialization uses only the universal cropped-family logarithmic
envelope.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open scoped ENNReal

/-- A pre-runtime cutoff absorbing the exact `1 / 16` Lemma 4.3 restoration
loss for every subsequently chosen cropped extremal family. -/
structure Proposition63M9Lemma43RestoreAbsorptionData
    (sourceLoss outputLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  restore : ∀ {delta sigma inputLoss normalizationLoss : ℝ}
      {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
      {normalizationExponent : ℕ}
      (normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent),
      delta ≤ delta₀ →
        proposition63Lemma43MassLoss (1 / 16)
              (((Nat.log 2 normalized.croppedFamily.card + 1 : ℕ) : ENNReal)) *
            Kakeya.realRpowENN delta outputLoss ≤
          Kakeya.realRpowENN delta sourceLoss

/-- Choose the Lemma 4.3 restoration cutoff before any runtime family. -/
theorem proposition63_m9_lemma43_restore_absorption
    (sourceLoss outputLoss : ℝ) (hgap : sourceLoss < outputLoss) :
    Nonempty (Proposition63M9Lemma43RestoreAbsorptionData
      sourceLoss outputLoss) := by
  let gap : ℝ := outputLoss - sourceLoss
  have gapPos : 0 < gap := by
    dsimp only [gap]
    linarith
  rcases exists_delta_realRpowENN_bound (2 : ENNReal) (by norm_num) gapPos with
    ⟨oneDelta, oneDeltaPos, oneDeltaOne, oneAbsorb⟩
  rcases exists_delta_C_pow_log_absorbed_ennreal
      (32 : ENNReal) (by norm_num) proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos
      (show 0 < (1 : ℕ) by norm_num) with
    ⟨ratioDelta, ratioDeltaPos, ratioDeltaOne, ratioAbsorb⟩
  let delta₀ : ℝ := min oneDelta (min ratioDelta (1 / 100000))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min oneDeltaPos <|
      lt_min ratioDeltaPos (by norm_num)
    delta₀_le_one := (min_le_left _ _).trans oneDeltaOne
    delta₀_le_tiny := (min_le_right _ _).trans (min_le_right _ _)
    restore := ?_
  }⟩
  intro delta sigma inputLoss normalizationLoss source normalizationExponent
    normalized deltaLe
  have deltaPos : 0 < delta := normalized.final_extremal.delta_pos
  have deltaOne : delta ≤ 1 := normalized.final_extremal.delta_le_one
  have deltaTiny : delta ≤ 1 / 100000 :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_right _ _)
  have deltaLeOneAbsorb : delta ≤ oneDelta :=
    deltaLe.trans (min_le_left _ _)
  have deltaLeRatioAbsorb : delta ≤ ratioDelta :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  let cardLog : ENNReal :=
    ((Nat.log 2 normalized.croppedFamily.card + 1 : ℕ) : ENNReal)
  have cardLogLe : cardLog ≤ proposition63OneScaleLogEnvelope delta := by
    have cardLogMono : Nat.log 2 normalized.croppedFamily.card + 1 ≤
        Nat.log 2 (2 * normalized.croppedFamily.card) + 1 :=
      Nat.add_le_add_right (Nat.log_mono_right <|
        Nat.le_mul_of_pos_left _ (by norm_num)) 1
    have cardLogCast : cardLog ≤
        ((Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ℕ) :
          ENNReal) := by
      dsimp only [cardLog]
      exact_mod_cast cardLogMono
    exact cardLogCast.trans <| by
      simpa only [Nat.cast_add, Nat.cast_one] using
        proposition63_cropped_cardLog_le_oneScaleEnvelope normalized deltaTiny
  have oneBound :
      2 * Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta sourceLoss := by
    calc
      2 * Kakeya.realRpowENN delta outputLoss ≤
          Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta outputLoss :=
        mul_le_mul_right' (oneAbsorb delta deltaPos deltaLeOneAbsorb) _
      _ = Kakeya.realRpowENN delta sourceLoss := by
        rw [← realRpowENN_add deltaPos]
        congr 1
        dsimp only [gap]
        ring
  have envelopeAbsorb :
      32 * proposition63OneScaleLogEnvelope delta ≤
        Kakeya.realRpowENN delta (-gap) := by
    simpa [proposition63OneScaleLogEnvelope] using
      ratioAbsorb delta deltaPos deltaLeRatioAbsorb
  have ratioBound :
      2 * cardLog * Kakeya.realRpowENN delta outputLoss ≤
        (1 / 16 : ENNReal) * Kakeya.realRpowENN delta sourceLoss := by
    calc
      2 * cardLog * Kakeya.realRpowENN delta outputLoss ≤
          2 * proposition63OneScaleLogEnvelope delta *
            Kakeya.realRpowENN delta outputLoss := by gcongr
      _ = (1 / 16 : ENNReal) *
          ((32 * proposition63OneScaleLogEnvelope delta) *
            Kakeya.realRpowENN delta outputLoss) := by
        simp only [← mul_assoc]
        rw [show (1 / 16 : ENNReal) * 32 = 2 by
          simp only [one_div]
          calc
            (16 : ENNReal)⁻¹ * 32 =
                (16 : ENNReal)⁻¹ * (16 * 2) := by congr 1 <;> norm_num
            _ = ((16 : ENNReal)⁻¹ * 16) * 2 :=
              (mul_assoc _ _ _).symm
            _ = 1 * 2 := by
              rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
            _ = 2 := one_mul 2]
      _ ≤ (1 / 16 : ENNReal) *
          (Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta outputLoss) := by gcongr
      _ = (1 / 16 : ENNReal) * Kakeya.realRpowENN delta sourceLoss := by
        rw [← realRpowENN_add deltaPos]
        congr 2
        dsimp only [gap]
        ring
  simpa only [cardLog] using
    proposition63Lemma43MassLoss_slack_of_two_bounds
      (left := (1 / 16 : ENNReal)) (right := cardLog)
      (by norm_num) (by norm_num) oneBound ratioBound

end Kakeya.Assouad.PureWZ2
