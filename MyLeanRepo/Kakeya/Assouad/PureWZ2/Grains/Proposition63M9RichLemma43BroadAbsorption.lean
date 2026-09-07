import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RichLemma43Preparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustLemma43Scales
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SparseRelativeBandBroadAbsorption

/-!
# Proposition 6.3 M9: rich-terminal broad-set absorption

The first rich terminal does not make its refined shading extremal.  Its
ambient mass floor therefore carries the genuine 61-log terminal retention.
Since the broad-set monomial uses that mass floor twice, the uniform cutoff
below pays 122 powers from the terminal and two further powers from the actual
dyadic-band logarithm.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set
open scoped ENNReal

/-- Family-independent power budget for the rich-terminal broad deletion. -/
structure Proposition63M9RichLemma43BroadCutoffData
    (sigma sourceLoss normalizationLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  broad_power_budget : ∀ {delta inputLoss : ℝ}
      {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
      {normalizationExponent : ℕ}
      (normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent)
      (selected : Kakeya.Streamlined.TubeSubfamily
        normalized.croppedFamily),
      delta ≤ delta₀ →
        (8192 : ENNReal) *
            (((Nat.log 2 selected.family.card + 1 : ℕ) : ENNReal)) ^ 2 *
            Kakeya.realRpowENN delta (-normalizationLoss) ^ 2 ≤
          wz2PaperPureRefinementFraction delta 61 ^ 2 *
            Kakeya.realRpowENN delta
              (3 * sigma / 4 - sigma + 5 * sourceLoss)

/-- Freeze the 124-log broad-set budget before the runtime family. -/
theorem proposition63_m9_rich_lemma43_broad_cutoff
    (sigma sourceLoss normalizationLoss : ℝ)
    (hgap : 5 * sourceLoss + 2 * normalizationLoss < sigma / 4) :
    Nonempty (Proposition63M9RichLemma43BroadCutoffData
      sigma sourceLoss normalizationLoss) := by
  let gap : ℝ := sigma / 4 - 5 * sourceLoss - 2 * normalizationLoss
  have gapPos : 0 < gap := by
    dsimp only [gap]
    linarith
  rcases exists_delta_C_pow_log_absorbed_ennreal
      (8192 : ENNReal) (by norm_num) proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos
      (show 0 < (124 : ℕ) by norm_num) with
    ⟨logDelta, logDeltaPos, logDeltaOne, logAbsorb⟩
  let delta₀ : ℝ := min logDelta (1 / 100000)
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := lt_min logDeltaPos (by norm_num)
    delta₀_le_one := (min_le_left _ _).trans logDeltaOne
    delta₀_le_tiny := min_le_right _ _
    broad_power_budget := ?_ }⟩
  intro delta inputLoss source normalizationExponent normalized selected deltaLe
  have deltaPos : 0 < delta := normalized.final_extremal.delta_pos
  have deltaLeLog : delta ≤ logDelta := deltaLe.trans (min_le_left _ _)
  have deltaSmall : delta ≤ 1 / 100000 :=
    deltaLe.trans (min_le_right _ _)
  have deltaOne : delta ≤ 1 := deltaLeLog.trans logDeltaOne
  have deltaLtOne : delta < 1 := deltaSmall.trans_lt (by norm_num)
  let envelope := proposition63OneScaleLogEnvelope delta
  let cardLog : ENNReal :=
    ((Nat.log 2 selected.family.card + 1 : ℕ) : ENNReal)
  let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  let fraction := wz2PaperPureRefinementFraction delta 61
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
    nlinarith [mul_nonneg (sub_nonneg.mpr coefficientOne)
      (show 0 ≤ 1 + Real.log delta⁻¹ by linarith)]
  have logTermPos : 0 < logTerm := by
    exact ENNReal.ofReal_pos.mpr <|
      Real.log_pos (one_lt_one_div deltaPos deltaLtOne)
  have logTermTop : logTerm ≠ ⊤ := by simp [logTerm]
  have denominatorPos : 0 < logTerm ^ 122 :=
    ENNReal.pow_pos logTermPos 122
  have denominatorTop : logTerm ^ 122 ≠ ⊤ :=
    ENNReal.pow_ne_top logTermTop
  have logarithmicAbsorption :
      (8192 : ENNReal) * envelope ^ 124 ≤
        Kakeya.realRpowENN delta (-gap) := by
    simpa only [envelope, proposition63OneScaleLogEnvelope] using
      logAbsorb delta deltaPos deltaLeLog
  have logProduct : cardLog ^ 2 * logTerm ^ 122 ≤ envelope ^ 124 := by
    calc
      cardLog ^ 2 * logTerm ^ 122 ≤ envelope ^ 2 * envelope ^ 122 := by
        gcongr
      _ = envelope ^ 124 := by rw [← pow_add]
  have multiplied :
      ((8192 : ENNReal) * cardLog ^ 2 *
          Kakeya.realRpowENN delta (-normalizationLoss) ^ 2) *
          logTerm ^ 122 ≤
        Kakeya.realRpowENN delta
          (3 * sigma / 4 - sigma + 5 * sourceLoss) := by
    have normalizationSquare :
        Kakeya.realRpowENN delta (-normalizationLoss) ^ 2 =
          Kakeya.realRpowENN delta (-2 * normalizationLoss) := by
      rw [pow_two, ← Kakeya.Assouad.realRpowENN_add deltaPos]
      congr 1
      ring
    calc
      ((8192 : ENNReal) * cardLog ^ 2 *
            Kakeya.realRpowENN delta (-normalizationLoss) ^ 2) *
            logTerm ^ 122 =
          (8192 * (cardLog ^ 2 * logTerm ^ 122)) *
            Kakeya.realRpowENN delta (-normalizationLoss) ^ 2 := by ring
      _ ≤ (8192 * envelope ^ 124) *
            Kakeya.realRpowENN delta (-normalizationLoss) ^ 2 := by gcongr
      _ ≤ Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta (-normalizationLoss) ^ 2 := by gcongr
      _ = Kakeya.realRpowENN delta
          (3 * sigma / 4 - sigma + 5 * sourceLoss) := by
        rw [normalizationSquare, ← Kakeya.Assouad.realRpowENN_add deltaPos]
        congr 1
        dsimp only [gap]
        ring
  have fractionSquare : fraction ^ 2 = (logTerm ^ 122)⁻¹ := by
    dsimp only [fraction, logTerm, wz2PaperPureRefinementFraction]
    calc
      ((ENNReal.ofReal (Real.log (1 / delta)))⁻¹ ^ 61) ^ 2 =
          (ENNReal.ofReal (Real.log (1 / delta)))⁻¹ ^ (61 * 2) := by
        rw [pow_mul]
      _ = (ENNReal.ofReal (Real.log (1 / delta)) ^ 122)⁻¹ := by
        rw [ENNReal.inv_pow]
  rw [fractionSquare]
  rw [show (logTerm ^ 122)⁻¹ *
        Kakeya.realRpowENN delta
            (3 * sigma / 4 - sigma + 5 * sourceLoss) =
      Kakeya.realRpowENN delta
          (3 * sigma / 4 - sigma + 5 * sourceLoss) /
        (logTerm ^ 122) by
          simp only [div_eq_mul_inv]
          ac_rfl]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl denominatorPos.ne') (Or.inl denominatorTop)).2
  simpa only [cardLog, mul_assoc, mul_comm, mul_left_comm] using multiplied

/-- The broad-set monomial estimate with an explicit ambient mass factor. -/
theorem sparse_relative_band_power_monomial_budget_with_ambient_factor
    {delta sigma loss tauExponent : ℝ}
    {bandCount coefficient fraction familyCard : ENNReal}
    (hdelta : 0 < delta)
    (hsmall :
      (8192 : ENNReal) * bandCount ^ 2 * coefficient ^ 2 ≤
        fraction ^ 2 * Kakeya.realRpowENN delta
          (tauExponent - sigma + 5 * loss)) :
    (8192 : ENNReal) * bandCount ^ 2 * coefficient ^ 2 *
        (ENNReal.ofReal (delta ^ 2) * familyCard) ^ 3 ≤
      Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
        Kakeya.realRpowENN delta tauExponent *
        (fraction * Kakeya.realRpowENN delta (loss + 2)) ^ 2 *
        familyCard ^ 3 := by
  have hdeltaTwo : ENNReal.ofReal (delta ^ 2) =
      Kakeya.realRpowENN delta 2 := by
    simp [Kakeya.realRpowENN]
  have htubeCube : Kakeya.realRpowENN delta 2 ^ 3 =
      Kakeya.realRpowENN delta 6 := by
    calc
      Kakeya.realRpowENN delta 2 ^ 3 =
          Kakeya.realRpowENN delta 2 * Kakeya.realRpowENN delta 2 *
            Kakeya.realRpowENN delta 2 := by ring
      _ = Kakeya.realRpowENN delta (2 + 2 + 2) := by
        rw [← Kakeya.Assouad.realRpowENN_add hdelta,
          ← Kakeya.Assouad.realRpowENN_add hdelta]
      _ = Kakeya.realRpowENN delta 6 := by norm_num
  have ambientSquare :
      (fraction * Kakeya.realRpowENN delta (loss + 2)) ^ 2 =
        fraction ^ 2 * Kakeya.realRpowENN delta (2 * (loss + 2)) := by
    rw [mul_pow]
    congr 1
    calc
      Kakeya.realRpowENN delta (loss + 2) ^ 2 =
          Kakeya.realRpowENN delta (loss + 2) *
            Kakeya.realRpowENN delta (loss + 2) := by ring
      _ = Kakeya.realRpowENN delta ((loss + 2) + (loss + 2)) := by
        rw [← Kakeya.Assouad.realRpowENN_add hdelta]
      _ = Kakeya.realRpowENN delta (2 * (loss + 2)) := by
        congr 1
        ring
  rw [hdeltaTwo]
  calc
    (8192 : ENNReal) * bandCount ^ 2 * coefficient ^ 2 *
          (Kakeya.realRpowENN delta 2 * familyCard) ^ 3 =
        ((8192 : ENNReal) * bandCount ^ 2 * coefficient ^ 2) *
          Kakeya.realRpowENN delta 6 * familyCard ^ 3 := by
      rw [mul_pow, htubeCube]
      ring
    _ ≤ (fraction ^ 2 * Kakeya.realRpowENN delta
          (tauExponent - sigma + 5 * loss)) *
        Kakeya.realRpowENN delta 6 * familyCard ^ 3 := by gcongr
    _ = Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
        Kakeya.realRpowENN delta tauExponent *
        (fraction * Kakeya.realRpowENN delta (loss + 2)) ^ 2 *
        familyCard ^ 3 := by
      rw [ambientSquare]
      have powerIdentity :
          Kakeya.realRpowENN delta (tauExponent - sigma + 5 * loss) *
              Kakeya.realRpowENN delta 6 =
            Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
              Kakeya.realRpowENN delta tauExponent *
              Kakeya.realRpowENN delta (2 * (loss + 2)) := by
        calc
          Kakeya.realRpowENN delta (tauExponent - sigma + 5 * loss) *
              Kakeya.realRpowENN delta 6 =
            Kakeya.realRpowENN delta
              (tauExponent - sigma + 5 * loss + 6) :=
                (Kakeya.Assouad.realRpowENN_add hdelta
                  (tauExponent - sigma + 5 * loss) 6).symm
          _ = Kakeya.realRpowENN delta
              ((2 - sigma + 3 * loss + tauExponent) +
                2 * (loss + 2)) := by
            congr 1
            ring
          _ = Kakeya.realRpowENN delta
                (2 - sigma + 3 * loss + tauExponent) *
              Kakeya.realRpowENN delta (2 * (loss + 2)) :=
                Kakeya.Assouad.realRpowENN_add hdelta _ _
          _ = (Kakeya.realRpowENN delta (2 - sigma + 3 * loss) *
                Kakeya.realRpowENN delta tauExponent) *
              Kakeya.realRpowENN delta (2 * (loss + 2)) := by
                rw [Kakeya.Assouad.realRpowENN_add hdelta]
      rw [show fraction ^ 2 *
            Kakeya.realRpowENN delta (tauExponent - sigma + 5 * loss) *
            Kakeya.realRpowENN delta 6 * familyCard ^ 3 =
          fraction ^ 2 *
            (Kakeya.realRpowENN delta (tauExponent - sigma + 5 * loss) *
              Kakeya.realRpowENN delta 6) * familyCard ^ 3 by ring,
        powerIdentity]
      ring

/-- Convert the rich-terminal mass receipt and the 124-log cutoff into the
exact broad-deletion inequality on the actual selected dyadic band. -/
theorem Proposition63M9RichLemma43Preparation.broad_absorb
    {delta sigma outputLoss sourceLoss normalizationLoss densityLoss theta : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (rich : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (prepared : Proposition63M9RichLemma43Preparation
      (densityLoss := densityLoss) rich)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * outputLoss)
    (hnormalizationOutput : normalizationLoss ≤ outputLoss)
    (hthetaPower : ENNReal.ofReal theta =
      Kakeya.realRpowENN delta (3 * sigma / 4))
    (cutoff : Proposition63M9RichLemma43BroadCutoffData
      sigma outputLoss normalizationLoss)
    (hdeltaCutoff : delta ≤ cutoff.delta₀) :
    let m := 2 ^ prepared.prepared.band.level
    let Q : ℕ := m ^ 3 / 4
    (2 : ENNReal) * (2 * m : ℕ) *
        Kakeya.realRpowENN delta (-normalizationLoss) *
        (ENNReal.ofReal (delta ^ 2) *
          rich.data.selected.family.enncard) ^ (3 / 2 : ℝ) ≤
      (((Q : ENNReal) * ENNReal.ofReal theta) ^ (1 / 2 : ℝ)) *
        prepared.prepared.band.band.mass := by
  let m : ℕ := 2 ^ prepared.prepared.band.level
  let Q : ℕ := m ^ 3 / 4
  let bandCount : ENNReal :=
    ((Nat.log 2 rich.data.selected.family.card + 1 : ℕ) : ENNReal)
  let fraction := wz2PaperPureRefinementFraction delta 61
  have bandCountZero : bandCount ≠ 0 := by
    dsimp only [bandCount]
    exact_mod_cast (Nat.zero_lt_succ
      (Nat.log 2 rich.data.selected.family.card)).ne'
  have bandCountTop : bandCount ≠ ⊤ := by simp [bandCount]
  have multiplicityUpper : (prepared.prepared.m0 : ENNReal) ≤
      2 * (m : ENNReal) := by
    exact_mod_cast prepared.m0_lt_twice_bandMultiplicity.le
  have densityBound :
      Kakeya.realRpowENN delta densityLoss *
          rich.data.selected.family.enncard ≤ 2 * (m : ENNReal) :=
    prepared.prepared.density_lower.trans multiplicityUpper
  have qBound : (1 / 16 : ENNReal) * (m : ENNReal) ^ 3 ≤ (Q : ENNReal) := by
    have hmTwo : 2 ≤ m := prepared.hm24.trans' (by norm_num)
    have cube : 4 ≤ m ^ 3 := by
      calc
        4 ≤ 2 ^ 3 := by norm_num
        _ ≤ m ^ 3 := Nat.pow_le_pow_left hmTwo 3
    have qNat : m ^ 3 ≤ 16 * Q := by
      dsimp only [Q]
      omega
    rw [show (1 / 16 : ENNReal) * (m : ENNReal) ^ 3 =
      (m : ENNReal) ^ 3 / 16 by simp [div_eq_mul_inv, mul_comm]]
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    have qCast : (m : ENNReal) ^ 3 ≤ (16 * Q : ℕ) := by
      exact_mod_cast qNat
    simpa [Nat.cast_mul, mul_comm] using qCast
  have sourceCardinality :
      Kakeya.realRpowENN delta (normalizationLoss + 2) *
          rich.data.selected.family.enncard ≤ croppedShading.mass := by
    exact selected_cardinality_cancellation reentry.cropped_extremal
      reentry.geometry.line_class rich.data.selected
        (hdeltaCutoff.trans cutoff.delta₀_le_tiny |>.trans (by norm_num))
  have sourcePower : Kakeya.realRpowENN delta (outputLoss + 2) ≤
      Kakeya.realRpowENN delta (normalizationLoss + 2) := by
    exact pure_wz2_rpowENN_antitone reentry.cropped_extremal.delta_pos
      reentry.cropped_extremal.delta_le_one
      (by linarith [hnormalizationOutput])
  have ambientMass :
      (fraction * Kakeya.realRpowENN delta (outputLoss + 2)) *
          rich.data.selected.family.enncard ≤ rich.data.refined.mass := by
    calc
      (fraction * Kakeya.realRpowENN delta (outputLoss + 2)) *
            rich.data.selected.family.enncard =
          fraction * (Kakeya.realRpowENN delta (outputLoss + 2) *
            rich.data.selected.family.enncard) := by ring
      _ ≤ fraction * (Kakeya.realRpowENN delta (normalizationLoss + 2) *
            rich.data.selected.family.enncard) := by gcongr
      _ ≤ fraction * croppedShading.mass := by gcongr
      _ ≤ rich.data.refined.mass := rich.total_mass_retention
  have bandRetention : (1 / 4 : ENNReal) * rich.data.refined.mass ≤
      bandCount * prepared.prepared.band.band.mass := by
    have raw := prepared.prepared.band.band_mass_retention
    have highBound : prepared.prepared.high.mass ≤
        bandCount * prepared.prepared.band.band.mass := by
      change prepared.prepared.high.mass / bandCount ≤
        prepared.prepared.band.band.mass at raw
      rw [ENNReal.div_le_iff bandCountZero bandCountTop] at raw
      simpa [bandCount, mul_comm] using raw
    calc
      (1 / 4 : ENNReal) * rich.data.refined.mass ≤
          rich.data.refined.mass := by
        simpa only [one_mul, mul_comm] using
          mul_le_mul_right (by norm_num : (1 / 4 : ENNReal) ≤ 1)
            rich.data.refined.mass
      _ = prepared.prepared.high.mass := by rw [prepared.high_eq]
      _ ≤ bandCount * prepared.prepared.band.band.mass := highBound
  have powerSmall := cutoff.broad_power_budget
    reentry.toNormalizationData rich.data.selected hdeltaCutoff
  have monomial := sparse_relative_band_power_monomial_budget_with_ambient_factor
    (delta := delta) (sigma := sigma) (loss := outputLoss)
    (tauExponent := 3 * sigma / 4) (bandCount := bandCount)
    (coefficient := Kakeya.realRpowENN delta (-normalizationLoss))
    (fraction := fraction)
    (familyCard := rich.data.selected.family.enncard)
    reentry.cropped_extremal.delta_pos (by simpa [bandCount, fraction] using powerSmall)
  have result := sparse_relative_band_absorption_of_monomial_budget
    bandCountZero bandCountTop
    (by simpa [m, hdensityLoss] using densityBound) qBound ambientMass
    bandRetention (by simpa [hthetaPower] using monomial)
  rw [hthetaPower]
  convert result using 1
  · norm_num [m, Q, bandCount, fraction, Nat.cast_mul]
    ring

end Kakeya.Assouad.PureWZ2

end
