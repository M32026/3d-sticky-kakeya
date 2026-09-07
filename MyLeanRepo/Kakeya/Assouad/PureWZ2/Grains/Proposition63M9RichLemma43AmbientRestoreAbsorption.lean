import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9Lemma43RestoreAbsorption

/-!
# Proposition 6.3 M9: ambient rich Lemma 4.3 restore absorption

This file freezes the family-independent cutoff which pays both the rich
terminal's 61-log mass retention and the actual dyadic-band logarithm in the
pointwise Lemma 4.3 output.  The two losses are kept in the same left factor
used by the ambient zero-extension; neither may be omitted or paid twice.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open scoped ENNReal

/-- A pre-runtime cutoff absorbing the complete ambient rich Lemma 4.3 mass
loss.  Its logarithmic order is `61 + 1`: the rich terminal contributes the
first 61 powers and the actual multiplicity band contributes the final
selected-family cardinality logarithm. -/
structure Proposition63M9RichLemma43AmbientRestoreAbsorptionData
    (sourceLoss targetLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  restore : ∀ {delta sigma inputLoss normalizationLoss : ℝ}
      {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
      {normalizationExponent : ℕ}
      (normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent)
      (selected : Kakeya.Streamlined.TubeSubfamily
        normalized.croppedFamily),
      delta ≤ delta₀ →
        proposition63Lemma43MassLoss
            (wz2PaperPureRefinementFraction delta 61 * (1 / 16))
            (((Nat.log 2 selected.family.card + 1 : ℕ) : ENNReal)) *
          Kakeya.realRpowENN delta targetLoss ≤
        Kakeya.realRpowENN delta sourceLoss

/-- Choose the complete ambient restore cutoff before the runtime family. -/
theorem proposition63_m9_rich_lemma43_ambient_restore_absorption
    (sourceLoss targetLoss : ℝ) (hgap : sourceLoss < targetLoss) :
    Nonempty (Proposition63M9RichLemma43AmbientRestoreAbsorptionData
      sourceLoss targetLoss) := by
  let gap : ℝ := targetLoss - sourceLoss
  have gapPos : 0 < gap := by
    dsimp only [gap]
    linarith
  rcases exists_delta_C_pow_log_absorbed_ennreal
      (32 : ENNReal) (by norm_num) proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos
      (show 0 < (62 : ℕ) by norm_num) with
    ⟨logDelta, logDeltaPos, logDeltaOne, logAbsorb⟩
  rcases exists_delta_realRpowENN_bound
      (2 : ENNReal) (by norm_num) gapPos with
    ⟨twoDelta, twoDeltaPos, twoDeltaOne, twoAbsorb⟩
  let delta₀ : ℝ := min logDelta (min twoDelta (1 / 100000))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min logDeltaPos <|
      lt_min twoDeltaPos (by norm_num)
    delta₀_le_one := (min_le_left _ _).trans logDeltaOne
    delta₀_le_tiny := (min_le_right _ _).trans (min_le_right _ _)
    restore := ?_
  }⟩
  intro delta sigma inputLoss normalizationLoss source normalizationExponent
    normalized selected deltaLe
  have deltaPos : 0 < delta := normalized.final_extremal.delta_pos
  have deltaLeLog : delta ≤ logDelta :=
    deltaLe.trans (min_le_left _ _)
  have deltaLeTwo : delta ≤ twoDelta :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have deltaSmall : delta ≤ 1 / 100000 :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_right _ _)
  have deltaOne : delta ≤ 1 := deltaLeLog.trans logDeltaOne
  have deltaLtOne : delta < 1 := deltaSmall.trans_lt (by norm_num)
  let envelope := proposition63OneScaleLogEnvelope delta
  let cardLog : ENNReal :=
    ((Nat.log 2 selected.family.card + 1 : ℕ) : ENNReal)
  let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  let fraction := wz2PaperPureRefinementFraction delta 61
  let left : ENNReal := fraction * (1 / 16)
  have selectedCard : selected.family.card ≤
      normalized.croppedFamily.card := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      selected.embedding selected.embedding.injective
  have cardLogLe : cardLog ≤ envelope := by
    have logNat : Nat.log 2 selected.family.card + 1 ≤
        Nat.log 2 (2 * normalized.croppedFamily.card) + 1 :=
      Nat.add_le_add_right (Nat.log_mono_right <|
        selectedCard.trans <| Nat.le_mul_of_pos_left _ (by norm_num)) 1
    have logENN : cardLog ≤
        ((Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ℕ) :
          ENNReal) := by
      dsimp only [cardLog]
      exact_mod_cast logNat
    exact logENN.trans <| by
      simpa only [envelope, Nat.cast_add, Nat.cast_one] using
        proposition63_cropped_cardLog_le_oneScaleEnvelope normalized
          deltaSmall
  have logTermLe : logTerm ≤ envelope := by
    dsimp only [logTerm, envelope, proposition63OneScaleLogEnvelope]
    apply ENNReal.ofReal_mono
    have logNonnegative : 0 ≤ Real.log delta⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ deltaPos).mpr deltaOne)
    rw [show 1 / delta = delta⁻¹ by simp]
    have coefficientOne : 1 ≤ proposition63OneScaleLogCoefficient :=
      (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
    calc
      Real.log delta⁻¹ ≤ 1 + Real.log delta⁻¹ := by linarith
      _ ≤ proposition63OneScaleLogCoefficient *
          (1 + Real.log delta⁻¹) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr coefficientOne)
          (show 0 ≤ 1 + Real.log delta⁻¹ by linarith)]
  have cardLogPos : 0 < cardLog := by
    dsimp only [cardLog]
    exact_mod_cast Nat.zero_lt_succ (Nat.log 2 selected.family.card)
  have cardLogTop : cardLog ≠ ⊤ := by simp [cardLog]
  have logTermPos : 0 < logTerm := by
    exact ENNReal.ofReal_pos.mpr <|
      Real.log_pos (one_lt_one_div deltaPos deltaLtOne)
  have logTermTop : logTerm ≠ ⊤ := by simp [logTerm]
  have fractionBounds :=
    pure_refinement_fraction_pos_ne_top deltaPos deltaLtOne 61
  have leftPos : 0 < left := by
    dsimp only [left]
    exact ENNReal.mul_pos fractionBounds.1.ne' (by norm_num)
  have leftTop : left ≠ ⊤ := by
    dsimp only [left]
    exact ENNReal.mul_ne_top fractionBounds.2 (by norm_num)
  have oneBound :
      2 * Kakeya.realRpowENN delta targetLoss ≤
        Kakeya.realRpowENN delta sourceLoss := by
    calc
      2 * Kakeya.realRpowENN delta targetLoss ≤
          Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta targetLoss := by
        gcongr
        exact twoAbsorb delta deltaPos deltaLeTwo
      _ = Kakeya.realRpowENN delta sourceLoss := by
        rw [← realRpowENN_add deltaPos]
        congr 1
        dsimp only [gap]
        ring
  have logarithmicAbsorption :
      (32 : ENNReal) * envelope ^ 62 ≤
        Kakeya.realRpowENN delta (-gap) := by
    simpa only [envelope, proposition63OneScaleLogEnvelope] using
      logAbsorb delta deltaPos deltaLeLog
  have logProduct : cardLog * logTerm ^ 61 ≤ envelope ^ 62 := by
    calc
      cardLog * logTerm ^ 61 ≤ envelope * envelope ^ 61 := by gcongr
      _ = envelope ^ 62 := by
        conv_rhs => rw [show 62 = 61 + 1 by norm_num, pow_succ]
        ac_rfl
  have ratioMultiplied :
      (2 * Kakeya.realRpowENN delta targetLoss) *
          (cardLog * logTerm ^ 61) ≤
        (1 / 16 : ENNReal) * Kakeya.realRpowENN delta sourceLoss := by
    calc
      (2 * Kakeya.realRpowENN delta targetLoss) *
            (cardLog * logTerm ^ 61) ≤
          2 * Kakeya.realRpowENN delta targetLoss * envelope ^ 62 :=
        by gcongr
      _ = (1 / 16 : ENNReal) *
          ((32 * envelope ^ 62) *
            Kakeya.realRpowENN delta targetLoss) := by
        have hcoefficient : (1 / 16 : ENNReal) * 32 = 2 := by
          simp only [one_div]
          calc
            (16 : ENNReal)⁻¹ * 32 =
                (16 : ENNReal)⁻¹ * (16 * 2) := by
              congr 1
              norm_num
            _ = ((16 : ENNReal)⁻¹ * 16) * 2 :=
              (mul_assoc _ _ _).symm
            _ = 1 * 2 := by
              rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
            _ = 2 := one_mul 2
        rw [← hcoefficient]
        ac_rfl
      _ ≤ (1 / 16 : ENNReal) *
          (Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta targetLoss) := by gcongr
      _ = (1 / 16 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss := by
        rw [← realRpowENN_add deltaPos]
        congr 2
        dsimp only [gap]
        ring
  have denominatorPos : 0 < logTerm ^ 61 :=
    ENNReal.pow_pos logTermPos 61
  have denominatorTop : logTerm ^ 61 ≠ ⊤ :=
    ENNReal.pow_ne_top logTermTop
  have ratioBound :
      2 * cardLog * Kakeya.realRpowENN delta targetLoss ≤
        left * Kakeya.realRpowENN delta sourceLoss := by
    have leftRewrite : left =
        (1 / 16 : ENNReal) * (logTerm ^ 61)⁻¹ := by
      dsimp only [left, fraction, logTerm]
      rw [wz2PaperPureRefinementFraction, ← ENNReal.inv_pow]
      ring
    rw [leftRewrite]
    rw [show (1 / 16 : ENNReal) * (logTerm ^ 61)⁻¹ *
          Kakeya.realRpowENN delta sourceLoss =
        ((1 / 16 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss) / (logTerm ^ 61) by
      simp only [div_eq_mul_inv]
      ring]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl denominatorPos.ne') (Or.inl denominatorTop)).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using ratioMultiplied
  simpa only [left, cardLog, fraction] using
    proposition63Lemma43MassLoss_slack_of_two_bounds
      leftPos leftTop oneBound ratioBound

end Kakeya.Assouad.PureWZ2

end
