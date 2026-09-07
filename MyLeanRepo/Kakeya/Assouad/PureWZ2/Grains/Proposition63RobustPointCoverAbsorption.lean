import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExtremalOneScaleFullGrain

/-!
# Family-free restoration for robust point covers

The robust localization retains a fixed fraction, one dyadic logarithm, and
the rich terminal's fixed logarithmic refinement fraction.  This module
absorbs that entire loss before the runtime selected family is known.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- Pre-runtime boundary absorption for an inner ordered pair.  The positive
power comes from the genuine pair window `delta^(1-scaleLoss) ≤ tau`; no
three-dimensional cover count is used. -/
structure Proposition63RobustBoundaryAbsorptionData
    (scaleLoss normalizationLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  grid_le : ∀ {delta tau : ℝ}, 0 < delta → delta ≤ delta₀ →
    0 < tau → Real.rpow delta (1 - scaleLoss) ≤ 3 * tau →
      delta ≤ gridSide (tau / 2)
  periodic : ∀ {delta tau : ℝ}, 0 < delta → delta ≤ delta₀ →
    0 < tau → Real.rpow delta (1 - scaleLoss) ≤ 3 * tau →
      50 * delta ≤ gridSide (tau / 2)
  absorb : ∀ {delta tau : ℝ}, 0 < delta → delta ≤ delta₀ →
    0 < tau → Real.rpow delta (1 - scaleLoss) ≤ 3 * tau →
    (24000000 : ENNReal) *
          (Kakeya.realRpowENN delta (-normalizationLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal (Real.sqrt (delta / gridSide (tau / 2))) ≤
      (1 / 10 : ENNReal) * wz2PaperPureRefinementFraction delta 61 *
        Kakeya.realRpowENN delta (normalizationLoss + 2)

/-- Choose the fixed-grid boundary threshold before the runtime scale. -/
theorem proposition63_robust_boundary_absorption
    (scaleLoss normalizationLoss : ℝ)
    (hnormalization : 0 < normalizationLoss)
    (hgap : 2 * normalizationLoss < scaleLoss / 2) :
    Nonempty (Proposition63RobustBoundaryAbsorptionData
      scaleLoss normalizationLoss) := by
  let gain : ℝ := scaleLoss / 2
  let gap : ℝ := gain - 2 * normalizationLoss
  have gapPos : 0 < gap := by
    dsimp only [gap, gain]
    linarith
  let fixed : ENNReal :=
    30 * 24000000 * (wz2PaperBoundaryGeometryConstant + 1)
  have fixedTop : fixed ≠ ⊤ := by
    dsimp only [fixed, wz2PaperBoundaryGeometryConstant]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by norm_num))
      (ENNReal.add_ne_top.mpr
        ⟨ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top,
          by norm_num⟩)
  rcases exists_delta_C_pow_log_absorbed_ennreal fixed fixedTop
      proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos
      (show 0 < (61 : ℕ) by norm_num) with
    ⟨logDelta, logDeltaPos, logDeltaOne, logAbsorb⟩
  have scaleLossPos : 0 < scaleLoss := by linarith
  rcases exists_delta_rpow_le_single scaleLoss (1 / 300) scaleLossPos
      (by norm_num) (by norm_num) with
    ⟨gridDelta, gridDeltaPos, gridDeltaOne, gridAbsorb⟩
  let delta₀ : ℝ :=
    min logDelta (min gridDelta (min (1 / 100000) (Real.exp (-1))))
  have ratioPower : ∀ {delta tau : ℝ}, 0 < delta → 0 < tau →
      Real.rpow delta (1 - scaleLoss) ≤ 3 * tau →
      delta / tau ≤ 3 * Real.rpow delta scaleLoss := by
    intro delta tau deltaPos tauPos tauLower
    have tauLowerThird : Real.rpow delta (1 - scaleLoss) / 3 ≤ tau := by
      linarith
    have quotient : delta / Real.rpow delta (1 - scaleLoss) =
        Real.rpow delta scaleLoss := by
      have raw := Real.rpow_sub deltaPos 1 (1 - scaleLoss)
      rw [Real.rpow_one] at raw
      exact raw.symm.trans <| by congr 1 <;> ring
    calc
      delta / tau ≤ delta / (Real.rpow delta (1 - scaleLoss) / 3) :=
        div_le_div_of_nonneg_left deltaPos.le
          (div_pos (Real.rpow_pos_of_pos deltaPos _) (by norm_num))
          tauLowerThird
      _ = 3 * (delta / Real.rpow delta (1 - scaleLoss)) := by
        field_simp [(Real.rpow_pos_of_pos deltaPos _).ne']
      _ = 3 * Real.rpow delta scaleLoss :=
        congrArg (fun value : ℝ => 3 * value) quotient
  have tauLarge : ∀ {delta tau : ℝ}, 0 < delta → delta ≤ delta₀ →
      0 < tau → Real.rpow delta (1 - scaleLoss) ≤ 3 * tau →
      100 * delta ≤ tau := by
    intro delta tau deltaPos deltaLe tauPos tauLower
    have deltaLeGrid : delta ≤ gridDelta :=
      deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
    have quotientBound : delta / tau ≤ 1 / 100 :=
      (ratioPower deltaPos tauPos tauLower).trans <|
        calc
          3 * Real.rpow delta scaleLoss ≤ 3 * (1 / 300 : ℝ) :=
            mul_le_mul_of_nonneg_left
              (gridAbsorb delta deltaPos deltaLeGrid) (by norm_num)
          _ = 1 / 100 := by norm_num
    have divided := (div_le_iff₀ tauPos).mp quotientBound
    nlinarith
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := by dsimp only [delta₀]; positivity
    delta₀_le_one := (min_le_left _ _).trans logDeltaOne
    delta₀_le_tiny := (min_le_right _ _).trans <|
      (min_le_right _ _).trans (min_le_left _ _)
    grid_le := by
      intro delta tau deltaPos deltaLe tauPos tauLower
      have large := tauLarge deltaPos deltaLe tauPos tauLower
      have sqrtThreeLeTwo : Real.sqrt 3 ≤ 2 := by
        rw [Real.sqrt_le_iff]
        norm_num
      unfold gridSide
      rw [show 2 * (tau / 2) / Real.sqrt 3 = tau / Real.sqrt 3 by ring]
      rw [le_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
      calc
        delta * Real.sqrt 3 ≤ delta * 2 := by gcongr
        _ ≤ tau := by linarith
    periodic := by
      intro delta tau deltaPos deltaLe tauPos tauLower
      have large := tauLarge deltaPos deltaLe tauPos tauLower
      have sqrtThreeLeTwo : Real.sqrt 3 ≤ 2 := by
        rw [Real.sqrt_le_iff]
        norm_num
      unfold gridSide
      rw [show 2 * (tau / 2) / Real.sqrt 3 = tau / Real.sqrt 3 by ring]
      rw [le_div_iff₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3))]
      calc
        50 * delta * Real.sqrt 3 ≤ 100 * delta := by nlinarith
        _ ≤ tau := large
    absorb := ?_
  }⟩
  intro delta tau deltaPos deltaLe tauPos tauLower
  have deltaLeLog : delta ≤ logDelta := deltaLe.trans (min_le_left _ _)
  have deltaOne : delta ≤ 1 := deltaLeLog.trans logDeltaOne
  have deltaLtOne : delta < 1 :=
    deltaLe.trans_lt <| (min_le_right _ _).trans_lt <|
      (min_le_right _ _).trans_lt <| (min_le_right _ _).trans_lt
          (Real.exp_lt_one_iff.mpr (by norm_num))
  let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  let envelope := proposition63OneScaleLogEnvelope delta
  have logTermPos : 0 < logTerm := by
    exact ENNReal.ofReal_pos.mpr <|
      Real.log_pos (one_lt_one_div deltaPos deltaLtOne)
  have logTermTop : logTerm ≠ ⊤ := by simp [logTerm]
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
  have logarithmicAbsorption : fixed * envelope ^ 61 ≤
      Kakeya.realRpowENN delta (-gap) := by
    simpa only [fixed, envelope, proposition63OneScaleLogEnvelope] using
      logAbsorb delta deltaPos deltaLeLog
  have tauPower : delta / tau ≤ 3 * Real.rpow delta scaleLoss :=
    ratioPower deltaPos tauPos tauLower
  have sideEq : gridSide (tau / 2) = tau / Real.sqrt 3 := by
    unfold gridSide
    ring
  have ratioBound : delta / gridSide (tau / 2) ≤
      6 * Real.rpow delta scaleLoss := by
    rw [sideEq]
    have sqrtThreeLeTwo : Real.sqrt 3 ≤ 2 := by
      rw [Real.sqrt_le_iff]
      norm_num
    have ratioEq : delta / (tau / Real.sqrt 3) =
        Real.sqrt 3 * (delta / tau) := by
      field_simp [tauPos.ne', (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)).ne']
    rw [ratioEq]
    exact (mul_le_mul_of_nonneg_left tauPower (Real.sqrt_nonneg 3)).trans <|
      calc
        Real.sqrt 3 * (3 * Real.rpow delta scaleLoss) ≤
            2 * (3 * Real.rpow delta scaleLoss) := by
          exact mul_le_mul_of_nonneg_right sqrtThreeLeTwo
            (mul_nonneg (by norm_num)
              (Real.rpow_nonneg deltaPos.le _))
        _ = 6 * Real.rpow delta scaleLoss := by ring
  have rootBoundReal : Real.sqrt (delta / gridSide (tau / 2)) ≤
      3 * Real.rpow delta gain := by
    have ratioNonnegative : 0 ≤ delta / gridSide (tau / 2) := by
      unfold gridSide
      positivity
    have powerPos : 0 < Real.rpow delta scaleLoss :=
      Real.rpow_pos_of_pos deltaPos _
    have sqrtBound := Real.sqrt_le_sqrt ratioBound
    have powerSqrt : Real.sqrt (Real.rpow delta scaleLoss) =
        Real.rpow delta gain := by
      rw [Real.sqrt_eq_rpow]
      calc
        Real.rpow (Real.rpow delta scaleLoss) (1 / 2 : ℝ) =
            Real.rpow delta (scaleLoss * (1 / 2 : ℝ)) :=
          (Real.rpow_mul deltaPos.le _ _).symm
        _ = Real.rpow delta gain := by
          congr 1
          dsimp only [gain]
          ring
    have sqrtSixPower : Real.sqrt (6 * Real.rpow delta scaleLoss) ≤
        3 * Real.sqrt (Real.rpow delta scaleLoss) := by
      have leftNonnegative := Real.sqrt_nonneg
        (6 * Real.rpow delta scaleLoss)
      have rightNonnegative : 0 ≤
          3 * Real.sqrt (Real.rpow delta scaleLoss) := by positivity
      have leftSquare :
          Real.sqrt (6 * Real.rpow delta scaleLoss) ^ 2 =
            6 * Real.rpow delta scaleLoss := by
        rw [Real.sq_sqrt]
        positivity
      have rightSquare :
          (3 * Real.sqrt (Real.rpow delta scaleLoss)) ^ 2 =
            9 * Real.rpow delta scaleLoss := by
        rw [mul_pow, Real.sq_sqrt powerPos.le]
        ring
      nlinarith
    exact sqrtBound.trans <| by
      rw [powerSqrt] at sqrtSixPower
      exact sqrtSixPower
  have rootBound :
      ENNReal.ofReal (Real.sqrt (delta / gridSide (tau / 2))) ≤
        3 * Kakeya.realRpowENN delta gain := by
    calc
      ENNReal.ofReal (Real.sqrt (delta / gridSide (tau / 2))) ≤
          ENNReal.ofReal (3 * Real.rpow delta gain) :=
        ENNReal.ofReal_mono rootBoundReal
      _ = 3 * Kakeya.realRpowENN delta gain := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num [Kakeya.realRpowENN]
  have oneLeNegative : (1 : ENNReal) ≤
      Kakeya.realRpowENN delta (-normalizationLoss) := by
    rw [Kakeya.realRpowENN, ← ENNReal.ofReal_one]
    apply ENNReal.ofReal_mono
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      deltaPos deltaOne (by linarith)
  have bracketBound :
      Kakeya.realRpowENN delta (-normalizationLoss) *
            wz2PaperBoundaryGeometryConstant + 1 ≤
        Kakeya.realRpowENN delta (-normalizationLoss) *
          (wz2PaperBoundaryGeometryConstant + 1) := by
    calc
      _ ≤ Kakeya.realRpowENN delta (-normalizationLoss) *
              wz2PaperBoundaryGeometryConstant +
            Kakeya.realRpowENN delta (-normalizationLoss) := by gcongr
      _ = _ := by ring
  have rawBound :
      (24000000 : ENNReal) *
          (Kakeya.realRpowENN delta (-normalizationLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal (Real.sqrt (delta / gridSide (tau / 2))) ≤
        (3 * 24000000 * (wz2PaperBoundaryGeometryConstant + 1)) *
          Kakeya.realRpowENN delta
            (-normalizationLoss + 2 + gain) := by
    calc
      _ ≤ (24000000 : ENNReal) *
          (Kakeya.realRpowENN delta (-normalizationLoss) *
            (wz2PaperBoundaryGeometryConstant + 1)) *
          Kakeya.realRpowENN delta 2 *
          (3 * Kakeya.realRpowENN delta gain) := by gcongr
      _ = (3 * 24000000 * (wz2PaperBoundaryGeometryConstant + 1)) *
          Kakeya.realRpowENN delta
            (-normalizationLoss + 2 + gain) := by
        have powers : Kakeya.realRpowENN delta (-normalizationLoss) *
              Kakeya.realRpowENN delta 2 *
              Kakeya.realRpowENN delta gain =
            Kakeya.realRpowENN delta
              (-normalizationLoss + 2 + gain) := by
          rw [← realRpowENN_add deltaPos, ← realRpowENN_add deltaPos]
        rw [show (24000000 : ENNReal) *
              (Kakeya.realRpowENN delta (-normalizationLoss) *
                (wz2PaperBoundaryGeometryConstant + 1)) *
              Kakeya.realRpowENN delta 2 *
              (3 * Kakeya.realRpowENN delta gain) =
            (3 * 24000000 * (wz2PaperBoundaryGeometryConstant + 1)) *
              (Kakeya.realRpowENN delta (-normalizationLoss) *
                Kakeya.realRpowENN delta 2 *
                Kakeya.realRpowENN delta gain) by ring]
        rw [powers]
  have multiplied :
      ((3 * 24000000 *
          (wz2PaperBoundaryGeometryConstant + 1)) *
        Kakeya.realRpowENN delta
          (-normalizationLoss + 2 + gain)) * logTerm ^ 61 ≤
        (1 / 10 : ENNReal) *
          Kakeya.realRpowENN delta (normalizationLoss + 2) := by
    have exponentIdentity : -gap +
        (-normalizationLoss + 2 + gain) = normalizationLoss + 2 := by
      dsimp only [gap]
      ring
    calc
      _ = (1 / 10 : ENNReal) *
          (fixed * logTerm ^ 61) *
            Kakeya.realRpowENN delta
              (-normalizationLoss + 2 + gain) := by
        dsimp only [fixed]
        have constantEq :
            (3 * 24000000 : ENNReal) =
              (1 / 10 : ENNReal) * (30 * 24000000) := by
          have leftTop : (3 * 24000000 : ENNReal) ≠ ⊤ := by norm_num
          have rightTop :
              (1 / 10 : ENNReal) * (30 * 24000000) ≠ ⊤ :=
            ENNReal.mul_ne_top
              (ENNReal.div_ne_top (by norm_num) (by norm_num))
              (by norm_num)
          rw [← ENNReal.toReal_eq_toReal_iff' leftTop rightTop]
          norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
        rw [show ((3 * 24000000 : ENNReal) *
              (wz2PaperBoundaryGeometryConstant + 1)) *
              Kakeya.realRpowENN delta
                (-normalizationLoss + 2 + gain) * logTerm ^ 61 =
            (3 * 24000000 : ENNReal) *
              ((wz2PaperBoundaryGeometryConstant + 1) *
                logTerm ^ 61 * Kakeya.realRpowENN delta
                  (-normalizationLoss + 2 + gain)) by ring]
        rw [constantEq]
        ring
      _ ≤ (1 / 10 : ENNReal) *
          (fixed * envelope ^ 61) *
            Kakeya.realRpowENN delta
              (-normalizationLoss + 2 + gain) := by gcongr
      _ ≤ (1 / 10 : ENNReal) *
          Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta
              (-normalizationLoss + 2 + gain) := by gcongr
      _ = (1 / 10 : ENNReal) *
          Kakeya.realRpowENN delta (normalizationLoss + 2) := by
        rw [show (1 / 10 : ENNReal) *
            Kakeya.realRpowENN delta (-gap) *
              Kakeya.realRpowENN delta
                (-normalizationLoss + 2 + gain) =
            (1 / 10 : ENNReal) *
              (Kakeya.realRpowENN delta (-gap) *
                Kakeya.realRpowENN delta
                  (-normalizationLoss + 2 + gain)) by ring]
        rw [← realRpowENN_add deltaPos, exponentIdentity]
  rw [show (1 / 10 : ENNReal) *
      wz2PaperPureRefinementFraction delta 61 *
        Kakeya.realRpowENN delta (normalizationLoss + 2) =
      ((1 / 10 : ENNReal) *
        Kakeya.realRpowENN delta (normalizationLoss + 2)) /
          logTerm ^ 61 by
    dsimp only [logTerm]
    rw [wz2PaperPureRefinementFraction, ← ENNReal.inv_pow]
    simp only [div_eq_mul_inv]
    ring]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (pow_ne_zero 61 logTermPos.ne'))
    (Or.inl (ENNReal.pow_ne_top logTermTop))).2
  exact (mul_le_mul_right' rawBound (logTerm ^ 61)).trans multiplied

/-- A pre-runtime small-scale receipt for restoring a robust point cover.
`logExponent = 0` is the target-ambient first cover; `logExponent = 61` is
the local second cover. -/
structure Proposition63RobustPointCoverRestorationAbsorptionData
    (sourceLoss outputLoss : ℝ) (logExponent : ℕ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  delta₀_le_tiny : delta₀ ≤ 1 / 100000
  absorb : ∀ {delta sigma inputLoss actualSourceLoss : ℝ}
      {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
      {normalizationExponent : ℕ},
      ∀ (normalized : PureWZ2CroppedCriticalNormalizationData
          (outputLoss := actualSourceLoss) source normalizationExponent),
        ∀ selected : Kakeya.Streamlined.TubeSubfamily
            normalized.croppedFamily,
          0 < delta → delta ≤ delta₀ →
            proposition63Lemma43MassLoss
                ((81 / 400 : ENNReal) *
                  (((Nat.log 2 selected.family.card + 1 : ℕ) :
                    ENNReal))⁻¹ *
                  wz2PaperPureRefinementFraction delta logExponent) 1 *
                Kakeya.realRpowENN delta outputLoss ≤
              Kakeya.realRpowENN delta sourceLoss

/-- Choose the robust-cover restoration threshold before the runtime family.
The strict loss gap absorbs one selected-family logarithm and the fixed
normalization logarithm. -/
theorem proposition63_robust_point_cover_restoration_absorption
    (sourceLoss outputLoss : ℝ) (logExponent : ℕ)
    (hgap : sourceLoss < outputLoss) :
    Nonempty (Proposition63RobustPointCoverRestorationAbsorptionData
      sourceLoss outputLoss logExponent) := by
  let gap : ℝ := outputLoss - sourceLoss
  have gapPos : 0 < gap := by simpa only [gap] using sub_pos.mpr hgap
  let fixed : ENNReal := 10
  have fixedTop : fixed ≠ ⊤ := by simp [fixed]
  have exponentPos : 0 < logExponent + 1 := by omega
  rcases exists_delta_C_pow_log_absorbed_ennreal fixed fixedTop
      proposition63OneScaleLogCoefficient
      proposition63OneScaleLogCoefficient_nonneg gapPos exponentPos with
    ⟨logDelta, logDeltaPos, logDeltaOne, logAbsorb⟩
  rcases exists_delta_realRpowENN_bound (2 : ENNReal) (by norm_num) gapPos with
    ⟨twoDelta, twoDeltaPos, twoDeltaOne, twoAbsorb⟩
  let delta₀ : ℝ := min logDelta (min twoDelta (1 / 100000))
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := by dsimp only [delta₀]; positivity
    delta₀_le_one := (min_le_left _ _).trans logDeltaOne
    delta₀_le_tiny := (min_le_right _ _).trans (min_le_right _ _)
    absorb := ?_
  }⟩
  intro delta sigma inputLoss actualSourceLoss source normalizationExponent
    normalized selected deltaPos deltaLe
  have deltaLeLog : delta ≤ logDelta :=
    deltaLe.trans (min_le_left _ _)
  have deltaLeTwo : delta ≤ twoDelta :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
  have deltaSmall : delta ≤ 1 / 100000 :=
    deltaLe.trans <| (min_le_right _ _).trans (min_le_right _ _)
  have deltaOne : delta ≤ 1 := deltaLeLog.trans logDeltaOne
  have deltaLtOne : delta < 1 := deltaSmall.trans_lt (by norm_num)
  let envelope := proposition63OneScaleLogEnvelope delta
  let logFactor : ENNReal :=
    ((Nat.log 2 selected.family.card + 1 : ℕ) : ENNReal)
  let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  let fraction := wz2PaperPureRefinementFraction delta logExponent
  let left : ENNReal := (81 / 400 : ENNReal) * logFactor⁻¹ * fraction
  have selectedCard : selected.family.card ≤
      normalized.croppedFamily.card := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      selected.embedding selected.embedding.injective
  have selectedLog : logFactor ≤ envelope := by
    have logNat : Nat.log 2 selected.family.card + 1 ≤
        Nat.log 2 (2 * normalized.croppedFamily.card) + 1 :=
      Nat.add_le_add_right (Nat.log_mono_right <|
        selectedCard.trans <| Nat.le_mul_of_pos_left _ (by norm_num)) 1
    have logENN' :
        ((Nat.log 2 selected.family.card + 1 : ℕ) : ENNReal) ≤
        ((Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ℕ) :
          ENNReal) := by
      exact_mod_cast logNat
    have logENN : logFactor ≤
        ((Nat.log 2 (2 * normalized.croppedFamily.card) + 1 : ℕ) :
          ENNReal) := by
      simpa only [logFactor] using logENN'
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
  have logFactorPos : 0 < logFactor := by
    dsimp only [logFactor]
    exact_mod_cast Nat.zero_lt_succ (Nat.log 2 selected.family.card)
  have logFactorTop : logFactor ≠ ⊤ := by simp [logFactor]
  have fractionBounds := pure_refinement_fraction_pos_ne_top
    deltaPos deltaLtOne logExponent
  have leftPos : 0 < left := by
    dsimp only [left]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (by norm_num : (81 / 400 : ENNReal) ≠ 0)
        (ENNReal.inv_ne_zero.mpr logFactorTop)).ne'
      fractionBounds.1.ne'
  have leftTop : left ≠ ⊤ := by
    dsimp only [left]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.div_ne_top (by norm_num) (by norm_num))
        (ENNReal.inv_ne_top.mpr logFactorPos.ne'))
      fractionBounds.2
  have oneBound :
      2 * Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta sourceLoss := by
    calc
      2 * Kakeya.realRpowENN delta outputLoss ≤
          Kakeya.realRpowENN delta (-gap) *
            Kakeya.realRpowENN delta outputLoss := by
        exact mul_le_mul_right' (twoAbsorb delta deltaPos deltaLeTwo) _
      _ = Kakeya.realRpowENN delta sourceLoss := by
        rw [← realRpowENN_add deltaPos]
        congr 1
        dsimp only [gap]
        ring_nf
  have logarithmicAbsorption :
      fixed * envelope ^ (logExponent + 1) ≤
        Kakeya.realRpowENN delta (-gap) := by
    simpa only [fixed, envelope, proposition63OneScaleLogEnvelope] using
      logAbsorb delta deltaPos deltaLeLog
  have ratioMultiplied :
      (2 * Kakeya.realRpowENN delta outputLoss) *
          (logFactor * logTerm ^ logExponent) ≤
        (81 / 400 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss := by
    have logProduct : logFactor * logTerm ^ logExponent ≤
        envelope ^ (logExponent + 1) := by
      calc
        logFactor * logTerm ^ logExponent ≤
            envelope * envelope ^ logExponent := by gcongr
        _ = envelope ^ (logExponent + 1) := by
          rw [pow_succ']
    have scaledAbsorption :
        2 * envelope ^ (logExponent + 1) ≤
          (81 / 400 : ENNReal) * Kakeya.realRpowENN delta (-gap) := by
      calc
        2 * envelope ^ (logExponent + 1) ≤
            ((81 / 400 : ENNReal) * 10) *
              envelope ^ (logExponent + 1) := by
          apply mul_le_mul_right'
          have rightTop : (81 / 400 : ENNReal) * 10 ≠ ⊤ :=
            ENNReal.mul_ne_top
              (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by norm_num)
          rw [← ENNReal.toReal_le_toReal (by norm_num) rightTop]
          norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
        _ = (81 / 400 : ENNReal) *
            (fixed * envelope ^ (logExponent + 1)) := by
          dsimp only [fixed]
          ring
        _ ≤ (81 / 400 : ENNReal) *
            Kakeya.realRpowENN delta (-gap) := by gcongr
    calc
      (2 * Kakeya.realRpowENN delta outputLoss) *
            (logFactor * logTerm ^ logExponent) ≤
          2 * Kakeya.realRpowENN delta outputLoss *
            envelope ^ (logExponent + 1) :=
        mul_le_mul_left' logProduct _
      _ = (2 * envelope ^ (logExponent + 1)) *
          Kakeya.realRpowENN delta outputLoss := by ring
      _ ≤ ((81 / 400 : ENNReal) *
            Kakeya.realRpowENN delta (-gap)) *
          Kakeya.realRpowENN delta outputLoss :=
        mul_le_mul_right' scaledAbsorption _
      _ = (81 / 400 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss := by
        rw [show ((81 / 400 : ENNReal) *
            Kakeya.realRpowENN delta (-gap)) *
              Kakeya.realRpowENN delta outputLoss =
            (81 / 400 : ENNReal) *
              (Kakeya.realRpowENN delta (-gap) *
                Kakeya.realRpowENN delta outputLoss) by ring]
        rw [← realRpowENN_add deltaPos]
        congr 1
        dsimp only [gap]
        ring
  have ratioBound :
      2 * (1 : ENNReal) * Kakeya.realRpowENN delta outputLoss ≤
        left * Kakeya.realRpowENN delta sourceLoss := by
    have logTermPos : 0 < logTerm := by
      exact ENNReal.ofReal_pos.mpr <|
        Real.log_pos (one_lt_one_div deltaPos deltaLtOne)
    have logTermTop : logTerm ≠ ⊤ := by simp [logTerm]
    have denominatorPos : 0 < logFactor * logTerm ^ logExponent := by
      exact ENNReal.mul_pos logFactorPos.ne'
        (pow_ne_zero _ logTermPos.ne')
    have denominatorTop : logFactor * logTerm ^ logExponent ≠ ⊤ :=
      ENNReal.mul_ne_top logFactorTop (ENNReal.pow_ne_top logTermTop)
    have leftRewrite : left =
        (81 / 400 : ENNReal) *
          (logFactor * logTerm ^ logExponent)⁻¹ := by
      dsimp only [left, fraction, logTerm]
      rw [wz2PaperPureRefinementFraction, ← ENNReal.inv_pow]
      rw [ENNReal.mul_inv (Or.inl logFactorPos.ne')
        (Or.inl logFactorTop)]
      ring
    rw [leftRewrite]
    rw [show (81 / 400 : ENNReal) *
        (logFactor * logTerm ^ logExponent)⁻¹ *
          Kakeya.realRpowENN delta sourceLoss =
        ((81 / 400 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss) /
            (logFactor * logTerm ^ logExponent) by
      simp only [div_eq_mul_inv]
      ring]
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl denominatorPos.ne') (Or.inl denominatorTop)).2
    simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using
      ratioMultiplied
  simpa only [left] using
    proposition63Lemma43MassLoss_slack_of_two_bounds
      leftPos leftTop oneBound ratioBound

/-- Specialize the family-free receipt to the first robust cover, which is
restored on the target terminal's ambient zero-extension. -/
theorem Proposition63RobustPointCoverRestorationAbsorptionData.absorbTargetAmbient
    {sourceLoss outputLoss delta sigma inputLoss actualSourceLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (data : Proposition63RobustPointCoverRestorationAbsorptionData
      sourceLoss outputLoss 0)
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := actualSourceLoss) source normalizationExponent)
    (selected : Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily)
    (hdelta : delta ≤ data.delta₀) :
    proposition63Lemma43MassLoss
        ((81 / 400 : ENNReal) *
          (((Nat.log 2 selected.family.card + 1 : ℕ) : ENNReal))⁻¹) 1 *
        Kakeya.realRpowENN delta outputLoss ≤
      Kakeya.realRpowENN delta sourceLoss := by
  simpa [wz2PaperPureRefinementFraction] using
    data.absorb normalized selected
      normalized.final_extremal.delta_pos hdelta

/-- Specialize the family-free receipt to the local square-root robust cover,
including the rich terminal's fixed 61-log refinement fraction. -/
theorem Proposition63RobustPointCoverRestorationAbsorptionData.absorbLocal
    {sourceLoss outputLoss delta sigma inputLoss actualSourceLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (data : Proposition63RobustPointCoverRestorationAbsorptionData
      sourceLoss outputLoss 61)
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := actualSourceLoss) source normalizationExponent)
    (selected : Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily)
    (hdelta : delta ≤ data.delta₀) :
    proposition63Lemma43MassLoss
        ((81 / 400 : ENNReal) *
          (((Nat.log 2 selected.family.card + 1 : ℕ) : ENNReal))⁻¹ *
          wz2PaperPureRefinementFraction delta 61) 1 *
        Kakeya.realRpowENN delta outputLoss ≤
      Kakeya.realRpowENN delta sourceLoss :=
  data.absorb normalized selected
    normalized.final_extremal.delta_pos hdelta

/-- Run the fourth rich call and the second robust localization with every
runtime-family quantity discharged from preselected scalar receipts. -/
theorem Proposition63LiftedPointCoverData.toNestedAnalyticViaFourthRobustOfAbsorptions
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss firstLoss tauScale densityLoss reentryLoss
      reentryNormalizationLoss weightLoss sqrtStickyLoss secondLoss epsilon₁
      epsilon₃ : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {incidenceBound : ℝ}
    (currentMap : PaperWZ1WeakPlaneMapData
      (extendShading outer.data.selected outer.data.refined) incidenceBound)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient currentMap.planeMap)
    (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := delta)
      (spatialRadius := tauScale) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined)
      currentMap.planeMap tauConstant)
    (absorption : Proposition63CurrentReentryAbsorptionData
      outerSourceLoss outerNormalizationLoss densityLoss firstLoss weightLoss
      reentryLoss
      (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaAbsorption : delta ≤ absorption.delta₀)
    (houterNormalizationLoss : 0 < outerNormalizationLoss)
    (htwoNormalization : 2 * outerNormalizationLoss ≤ reentryLoss)
    (hfirstReentry : firstLoss ≤ reentryLoss)
    (hfirstLoss : 0 < firstLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (richSchedule : Proposition63RichThreeCallScheduleData
      sigma sqrtStickyLoss)
    (hreentryLoss : reentryLoss = richSchedule.third.sourceLoss)
    (hthirdNormalization :
      reentryNormalizationLoss = richSchedule.third.normalizationLoss)
    (hdeltaThird : delta ≤ richSchedule.third.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtLower : Real.rpow delta (1 - sqrtStickyLoss) ≤ sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤ Real.rpow delta sqrtStickyLoss)
    (hsqrtOne : sqrtRequested.1 ≤ 1)
    (boundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      sqrtStickyLoss reentryNormalizationLoss)
    (hdeltaBoundary : delta ≤ boundaryAbsorption.delta₀)
    (gridAbsorption : Proposition63RobustGridPruningAbsorptionData
      reentryNormalizationLoss epsilon₁)
    (hdeltaGridAbsorption : delta ≤ gridAbsorption.delta₀)
    (crossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent outerLoss reentryNormalizationLoss weightLoss 4
        (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaCrossAbsorption : delta ≤ crossAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : sqrtRequested.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              reentryNormalizationLoss sqrtStickyLoss
              sqrtRequested.1 sqrtRequested.1 /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                sqrtRequested.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta sqrtRequested.1
              incidenceBound coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN
          (sqrtRequested.1 / delta) (1 - sigma))
    (hnormalizationSecond : reentryNormalizationLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (restoreAbsorption :
      Proposition63RobustPointCoverRestorationAbsorptionData
        reentryNormalizationLoss secondLoss 61)
    (hdeltaRestore : delta ≤ restoreAbsorption.delta₀) :
    Nonempty (Proposition63NestedPointCoverAnalyticData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (queryScale := delta) (tauScale := tauScale)
      (sqrtScale := sqrtRequested.1) outerReentry.toNormalizationData
      currentMap.planeMap tauConstant
      (C * Kakeya.realRpowENN
        (sqrtRequested.1 / delta) (1 - sigma))) := by
  have firstSubNormalized : PaperIsSubshading first.state.shading
      outerReentry.toNormalizationData.croppedRefined := by
    exact fun index point hpoint =>
      extendShading_subshading outer.data.selected outer.data.subshading index <|
        first.state.subshading index hpoint
  rcases first.nextReentryAndThirdRichOfAbsorption
      outerReentry.toNormalizationData firstSubNormalized absorption
      hdeltaAbsorption houterNormalizationLoss htwoNormalization
      hfirstReentry hfirstLoss hreentryNormalizationLoss hreentryHalf
      richSchedule hreentryLoss hthirdNormalization hdeltaThird sqrtRequested
      hsqrtLower hsqrtUpper with
    ⟨reentry, ⟨target⟩, hweight, hweightUpper, hlevel, hnormalization⟩
  let firstMap : PaperWZ1WeakPlaneMapData first.state.shading incidenceBound :=
    paperWeakPlaneMapRestrict currentMap first.state.subshading
  let normalizedMap : PaperWZ1WeakPlaneMapData
      reentry.normalization.croppedRefined incidenceBound :=
    reentry.normalizedPlaneMap firstMap
  let targetMap : PaperWZ1WeakPlaneMapData
      target.data.refined incidenceBound :=
    target.terminalPlaneMap normalizedMap
  have htargetReentryLoss : 0 < reentryLoss := by
    rw [hreentryLoss]
    exact richSchedule.third.sourceLoss_pos
  have receipts :=
    Proposition63RichTerminalStickyData.robustTauRuntimeReceipts_of_absorptions
      outer reentry htargetReentryLoss target hnormalization gridAbsorption
      crossAbsorption hdeltaGridAbsorption hdeltaCrossAbsorption hrobustScale
      hweight hweightUpper hlevel
      (reentry.reentry_extremal.delta_pos.trans_le
        sqrtRequested.2.1) hsqrtOne hrobustSmall
  rcases receipts with ⟨hgridError, hcrossCall⟩
  have htargetPos : 0 < sqrtRequested.1 :=
    reentry.reentry_extremal.delta_pos.trans_le sqrtRequested.2.1
  have hsqrtLowerThree : Real.rpow delta (1 - sqrtStickyLoss) ≤
      3 * sqrtRequested.1 :=
    hsqrtLower.trans <| by nlinarith [htargetPos]
  have hdeltaGrid := boundaryAbsorption.grid_le
    reentry.reentry_extremal.delta_pos hdeltaBoundary htargetPos
      hsqrtLowerThree
  have hperiodic := boundaryAbsorption.periodic
    reentry.reentry_extremal.delta_pos hdeltaBoundary htargetPos
      hsqrtLowerThree
  have hboundaryScalarActual := boundaryAbsorption.absorb
    reentry.reentry_extremal.delta_pos hdeltaBoundary htargetPos
      hsqrtLowerThree
  have hboundaryActual := target.boundaryCWA_of_scalar htargetReentryLoss
    (hdeltaSmall.trans (by norm_num)) <| by
      simpa only [hnormalization] using hboundaryScalarActual
  have harithmeticActual :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              reentry.reentryNormalizationLoss sqrtStickyLoss
              sqrtRequested.1 sqrtRequested.1 /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                sqrtRequested.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta sqrtRequested.1
              incidenceBound coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN
          (sqrtRequested.1 / delta) (1 - sigma) := by
    simpa only [hnormalization] using harithmetic
  have hrestoreActual : proposition63Lemma43MassLoss
        ((81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹ *
          wz2PaperPureRefinementFraction delta 61) 1 *
        Kakeya.realRpowENN delta secondLoss ≤
      Kakeya.realRpowENN delta reentry.reentryNormalizationLoss := by
    exact (restoreAbsorption.absorbLocal reentry.normalization
      target.data.selected hdeltaRestore
      ).trans_eq (congrArg (Kakeya.realRpowENN delta) hnormalization.symm)
  rcases proposition63_robust_tau_local_point_cover_data_of_cwa outer reentry
      first.state.subshading htargetReentryLoss target currentMap.planeMap
      incidenceBound targetMap.unit hplaneLipschitz targetMap.incidence
      sqrtRequested.2.1 hdeltaGrid htargetPos hsqrtOne hperiodic
      hboundaryActual hgridError hrobustSmall hcrossCall hkappa
      htargetSmall hdeltaSmall (by linarith [htargetPos]) hsqrtSq hsigma
      hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog hlog
      haxis C harithmeticActual (hdeltaSmall.trans_lt (by norm_num))
      (hnormalization.trans_le hnormalizationSecond) hsecondLoss
      hrestoreActual with
    ⟨second, _hfactor, hsecondSubset⟩
  exact Proposition63NestedPointCoverAnalyticData.ofLiftedPointCovers
    outerReentry.toNormalizationData
    (extendShading outer.data.selected outer.data.refined) currentMap.planeMap
    tauConstant
    (C * Kakeya.realRpowENN (sqrtRequested.1 / delta) (1 - sigma))
    first reentry sqrtRequested rfl target.data second hsecondSubset

/-- Attach constant multiplicity and fresh whole-cell balancing immediately
after the fourth-call robust localization.  This is the final M3 transition
from a first restored cover to concrete nested point-cover data. -/
theorem Proposition63LiftedPointCoverData.toNestedPointCoverViaFourthRobustOfAbsorptions
    {delta sigma robustExponent outerLoss outerSourceLoss
      outerNormalizationLoss firstLoss tauScale densityLoss reentryLoss
      reentryNormalizationLoss weightLoss sqrtStickyLoss secondLoss epsilon₁
      epsilon₃ middleLoss finalLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {incidenceBound : ℝ}
    (currentMap : PaperWZ1WeakPlaneMapData
      (extendShading outer.data.selected outer.data.refined) incidenceBound)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient currentMap.planeMap)
    (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := delta)
      (spatialRadius := tauScale) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined)
      currentMap.planeMap tauConstant)
    (absorption : Proposition63CurrentReentryAbsorptionData
      outerSourceLoss outerNormalizationLoss densityLoss firstLoss weightLoss
      reentryLoss
      (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaAbsorption : delta ≤ absorption.delta₀)
    (houterNormalizationLoss : 0 < outerNormalizationLoss)
    (htwoNormalization : 2 * outerNormalizationLoss ≤ reentryLoss)
    (hfirstReentry : firstLoss ≤ reentryLoss)
    (hfirstLoss : 0 < firstLoss)
    (hreentryNormalizationLoss : 0 < reentryNormalizationLoss)
    (hreentryHalf : reentryLoss ≤ reentryNormalizationLoss / 2)
    (richSchedule : Proposition63RichThreeCallScheduleData
      sigma sqrtStickyLoss)
    (hreentryLoss : reentryLoss = richSchedule.third.sourceLoss)
    (hthirdNormalization :
      reentryNormalizationLoss = richSchedule.third.normalizationLoss)
    (hdeltaThird : delta ≤ richSchedule.third.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtLower : Real.rpow delta (1 - sqrtStickyLoss) ≤ sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤ Real.rpow delta sqrtStickyLoss)
    (hsqrtOne : sqrtRequested.1 ≤ 1)
    (boundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      sqrtStickyLoss reentryNormalizationLoss)
    (hdeltaBoundary : delta ≤ boundaryAbsorption.delta₀)
    (gridAbsorption : Proposition63RobustGridPruningAbsorptionData
      reentryNormalizationLoss epsilon₁)
    (hdeltaGridAbsorption : delta ≤ gridAbsorption.delta₀)
    (crossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent outerLoss reentryNormalizationLoss weightLoss 4
        (proposition63CanonicalNearbyLevelCount outerNormalizationLoss))
    (hdeltaCrossAbsorption : delta ≤ crossAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : sqrtRequested.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              reentryNormalizationLoss sqrtStickyLoss
              sqrtRequested.1 sqrtRequested.1 /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                sqrtRequested.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta sqrtRequested.1
              incidenceBound coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN
          (sqrtRequested.1 / delta) (1 - sigma))
    (hnormalizationSecond : reentryNormalizationLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (restoreAbsorption :
      Proposition63RobustPointCoverRestorationAbsorptionData
        reentryNormalizationLoss secondLoss 61)
    (hdeltaRestore : delta ≤ restoreAbsorption.delta₀)
    (hsecondMiddle : secondLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (multiplicityAbsorption : Proposition63FullGrainLogAbsorptionData
      secondLoss middleLoss)
    (hdeltaMultiplicity : delta ≤ multiplicityAbsorption.delta₀)
    (hbalancingBoundary :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / sqrtRequested.1)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (balancingAbsorption : Proposition63FullGrainBalancingAbsorptionData
      middleLoss finalLoss)
    (hdeltaBalancing : delta ≤ balancingAbsorption.delta₀) :
    Nonempty (Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := delta)
      (tauScale := tauScale) (sqrtScale := sqrtRequested.1)
      outerReentry.toNormalizationData currentMap.planeMap tauConstant
      (C * Kakeya.realRpowENN
        (sqrtRequested.1 / delta) (1 - sigma))) := by
  rcases first.toNestedAnalyticViaFourthRobustOfAbsorptions outer currentMap
      hplaneLipschitz tauConstant absorption hdeltaAbsorption
      houterNormalizationLoss htwoNormalization hfirstReentry hfirstLoss
      hreentryNormalizationLoss hreentryHalf richSchedule hreentryLoss
      hthirdNormalization hdeltaThird sqrtRequested hsqrtLower hsqrtUpper
      hsqrtOne boundaryAbsorption hdeltaBoundary gridAbsorption
      hdeltaGridAbsorption crossAbsorption hdeltaCrossAbsorption
      hrobustScale hrobustSmall hkappa htargetSmall hdeltaSmall hsqrtSq
      hsigma hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog
      hlog haxis C harithmetic hnormalizationSecond hsecondLoss
      restoreAbsorption hdeltaRestore with
    ⟨analytic⟩
  have cardLogLe :
      ((Nat.log 2 analytic.reentry.normalization.croppedFamily.card + 1 :
          ℕ) : ENNReal) ≤ proposition63OneScaleLogEnvelope delta := by
    have raw := proposition63_cropped_cardLog_le_oneScaleEnvelope
      analytic.reentry.normalization
      (hdeltaMultiplicity.trans multiplicityAbsorption.delta₀_le_tiny)
    exact le_trans (by
      exact_mod_cast Nat.add_le_add_right
        (Nat.log_mono_right <| Nat.le_mul_of_pos_left _ (by norm_num)) 1) raw
  have multiplicitySlack :
      (((Nat.log 2 analytic.reentry.normalization.croppedFamily.card + 1 :
          ℕ) : ENNReal) * Kakeya.realRpowENN delta middleLoss) ≤
        Kakeya.realRpowENN delta secondLoss :=
    (mul_le_mul_right' cardLogLe _).trans <|
      multiplicityAbsorption.absorbEnvelope
        analytic.reentry.reentry_extremal.delta_pos hdeltaMultiplicity
  have htargetPos : 0 < sqrtRequested.1 :=
    analytic.reentry.reentry_extremal.delta_pos.trans_le sqrtRequested.2.1
  have hperiodicGrid := boundaryAbsorption.periodic
    analytic.reentry.reentry_extremal.delta_pos hdeltaBoundary htargetPos <|
      hsqrtLower.trans (by nlinarith [htargetPos])
  have hgridSideLeTarget :
      gridSide (sqrtRequested.1 / 2) ≤ sqrtRequested.1 := by
    have sqrtThreeGeOne : 1 ≤ Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    unfold gridSide
    rw [show 2 * (sqrtRequested.1 / 2) / Real.sqrt 3 =
        sqrtRequested.1 / Real.sqrt 3 by ring]
    exact div_le_self htargetPos.le sqrtThreeGeOne
  have hperiodicScale : 50 * delta ≤ sqrtRequested.1 :=
    hperiodicGrid.trans hgridSideLeTarget
  rcases analytic.prepareFreshBalancedCells hsecondMiddle hmiddleLoss
      multiplicitySlack (hdeltaSmall.trans (by norm_num)) hperiodicScale
      (outerReentry.toNormalizationData.final_extremal.delta_pos.trans_le
        sqrtRequested.2.1) hsqrtOne hbalancingBoundary hmiddleFinal
      hfinalLoss (balancingAbsorption.absorb
        analytic.reentry.reentry_extremal.delta_pos hdeltaBalancing) with
    ⟨result, _hcurrent, _hfirstFactor, _hweight, _hlevel, _hsecondFactor,
      _hpreparation⟩
  exact ⟨result⟩

/-- Consume the middle payload of a four-call schedule and execute its fourth
rich call, second robust localization, and fresh whole-cell balancing.  The
third terminal is reused definitionally as the second robust outer witness. -/
theorem Proposition63FirstRobustTargetAmbientData.completeFourCallPointCover
    {delta sigma robustExponent outerSourceLoss outerNormalizationLoss tau
      firstLoss firstWeightLoss densityLoss nextWeightLoss outputLoss secondLoss epsilon₁
      epsilon₃ middleLoss finalLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent firstLevelCount : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {firstRobustScale targetScale : WZ2PaperRequestedScale delta}
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := schedule.secondOutputLoss) sourceShading outerReentry
      firstRobustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := schedule.third.sourceLoss)
      outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined))
    (target : Proposition63RichTerminalStickyData
      (outputLoss := schedule.thirdOutputLoss)
      targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        schedule.third.sourceLoss_pos
        targetReentry.reentry_normalization_loss_pos) targetScale)
    {incidenceBound : ℝ}
    (targetMap : PaperWZ1WeakPlaneMapData target.data.refined incidenceBound)
    {firstConstant : ENNReal}
    (data : Proposition63FirstRobustTargetAmbientData
      (targetNormalizationLoss := schedule.third.normalizationLoss)
      (tau := tau) (firstLoss := firstLoss)
      (weightLoss := firstWeightLoss)
      firstRobustScale outer
      targetReentry schedule.third.sourceLoss_pos targetScale target
      firstLevelCount
      targetMap.planeMap firstConstant)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient targetMap.planeMap)
    (reentryAbsorption : Proposition63CurrentReentryAbsorptionData
      schedule.third.sourceLoss schedule.third.normalizationLoss densityLoss
      firstLoss nextWeightLoss schedule.fourth.sourceLoss
      (proposition63CanonicalNearbyLevelCount
        schedule.third.normalizationLoss))
    (hdeltaReentry : delta ≤ reentryAbsorption.delta₀)
    (hfirstReentry : firstLoss ≤ schedule.fourth.sourceLoss)
    (hfirstLoss : 0 < firstLoss)
    (hdeltaFourth : delta ≤ schedule.fourth.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale delta)
    (hsqrtLower : Real.rpow delta (1 - outputLoss) ≤ sqrtRequested.1)
    (hsqrtUpper : sqrtRequested.1 ≤ Real.rpow delta outputLoss)
    (hsqrtOne : sqrtRequested.1 ≤ 1)
    (boundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      outputLoss schedule.fourth.normalizationLoss)
    (hdeltaBoundary : delta ≤ boundaryAbsorption.delta₀)
    (gridAbsorption : Proposition63RobustGridPruningAbsorptionData
      schedule.fourth.normalizationLoss epsilon₁)
    (hdeltaGrid : delta ≤ gridAbsorption.delta₀)
    (crossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent schedule.thirdOutputLoss
        schedule.fourth.normalizationLoss nextWeightLoss 4
        (proposition63CanonicalNearbyLevelCount
          schedule.third.normalizationLoss))
    (hdeltaCross : delta ≤ crossAbsorption.delta₀)
    (htargetScale : targetScale.1 = Real.rpow delta robustExponent)
    (htargetSmall : targetScale.1 ≤ 1 / 10000)
    (hkappa : Real.rpow delta epsilon₃ ≤ targetScale.1)
    (hsqrtSmall : sqrtRequested.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              schedule.fourth.normalizationLoss outputLoss
              sqrtRequested.1 sqrtRequested.1 /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                sqrtRequested.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta sqrtRequested.1
              incidenceBound coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN
          (sqrtRequested.1 / delta) (1 - sigma))
    (hnormalizationSecond :
      schedule.fourth.normalizationLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (restoreAbsorption :
      Proposition63RobustPointCoverRestorationAbsorptionData
        schedule.fourth.normalizationLoss secondLoss 61)
    (hdeltaRestore : delta ≤ restoreAbsorption.delta₀)
    (hsecondMiddle : secondLoss ≤ middleLoss)
    (hmiddleLoss : 0 < middleLoss)
    (multiplicityAbsorption : Proposition63FullGrainLogAbsorptionData
      secondLoss middleLoss)
    (hdeltaMultiplicity : delta ≤ multiplicityAbsorption.delta₀)
    (hbalancingBoundary :
      2 * 24000000 *
          (Kakeya.realRpowENN delta (-middleLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          ENNReal.ofReal (Real.sqrt (delta / sqrtRequested.1)) <
        Kakeya.realRpowENN delta middleLoss)
    (hmiddleFinal : middleLoss ≤ finalLoss)
    (hfinalLoss : 0 < finalLoss)
    (balancingAbsorption : Proposition63FullGrainBalancingAbsorptionData
      middleLoss finalLoss)
    (hdeltaBalancing : delta ≤ balancingAbsorption.delta₀) :
    Nonempty (Proposition63NestedPointCoverData
      (firstLoss := firstLoss) (reentryLoss := schedule.fourth.sourceLoss)
      (sqrtStickyLoss := outputLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (queryScale := delta) (tauScale := tau)
      (sqrtScale := sqrtRequested.1) targetReentry.normalization
      targetMap.planeMap firstConstant
      (C * Kakeya.realRpowENN
        (sqrtRequested.1 / delta) (1 - sigma))) := by
  let ambientTargetMap : PaperWZ1WeakPlaneMapData
      (extendShading target.data.selected target.data.refined)
      incidenceBound := target.ambientTerminalPlaneMap targetMap
  have hambientLipschitz :
      LipschitzWith coefficient ambientTargetMap.planeMap := by
    change LipschitzWith coefficient targetMap.planeMap
    exact hplaneLipschitz
  have htwoNormalization :
      2 * targetReentry.reentryNormalizationLoss ≤
        schedule.fourth.sourceLoss := by
    rw [data.target_normalization_loss]
    have hthirdNormalization := schedule.third.normalizationLoss_lt_output
    have hthirdOutput := schedule.thirdOutputLoss_eq
    have hfourthSource := schedule.thirdOutputLoss_lt_fourthSource
    linarith
  have reentryPackage :
      ∃ actual : Proposition63CurrentReentryAbsorptionData
          schedule.third.sourceLoss targetReentry.reentryNormalizationLoss
          densityLoss firstLoss nextWeightLoss schedule.fourth.sourceLoss
          (proposition63CanonicalNearbyLevelCount
            targetReentry.reentryNormalizationLoss),
        delta ≤ actual.delta₀ := by
    rw [data.target_normalization_loss]
    exact ⟨reentryAbsorption, hdeltaReentry⟩
  rcases reentryPackage with ⟨reentryAbsorptionActual, hdeltaReentryActual⟩
  have crossPackage :
      ∃ actual : Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
          robustExponent schedule.thirdOutputLoss
          schedule.fourth.normalizationLoss nextWeightLoss 4
          (proposition63CanonicalNearbyLevelCount
            targetReentry.reentryNormalizationLoss),
        delta ≤ actual.delta₀ := by
    rw [data.target_normalization_loss]
    exact ⟨crossAbsorption, hdeltaCross⟩
  rcases crossPackage with ⟨crossAbsorptionActual, hdeltaCrossActual⟩
  exact data.first.toNestedPointCoverViaFourthRobustOfAbsorptions target
    ambientTargetMap hambientLipschitz firstConstant reentryAbsorptionActual
    hdeltaReentryActual targetReentry.reentry_normalization_loss_pos
    htwoNormalization hfirstReentry hfirstLoss
    schedule.fourth.normalizationLoss_pos schedule.fourth.sourceLoss_le_half
    schedule.lastThree rfl rfl hdeltaFourth sqrtRequested hsqrtLower
    hsqrtUpper hsqrtOne boundaryAbsorption hdeltaBoundary gridAbsorption
    hdeltaGrid crossAbsorptionActual hdeltaCrossActual htargetScale
    htargetSmall hkappa
    hsqrtSmall hdeltaSmall hsqrtSq hsigma hsigmaOne hepsilon₁ hepsilon₃
    hepsilonSum logScale hdeltaLog hlog haxis C harithmetic
    hnormalizationSecond hsecondLoss restoreAbsorption hdeltaRestore
    hsecondMiddle hmiddleLoss multiplicityAbsorption hdeltaMultiplicity
    hbalancingBoundary hmiddleFinal hfinalLoss balancingAbsorption
    hdeltaBalancing

/-- Add the actual second and third rich terminals to the M3 payload.  The
first robust cover is produced only after both runtime calls have been made,
and it is restored on the third terminal's exact ambient zero-extension. -/
theorem proposition63_first_robust_target_ambient_runtime_of_absorptions
    {delta sigma initialInputLoss normalizationLoss firstReentryLoss
      densityLoss weightLoss outerExtremalLoss outerLoss targetLoss
      robustExponent tau epsilon₁ epsilon₃ parentLoss firstLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource 0}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (firstReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := firstReentryLoss) initialNormalized current)
    (firstSchedule : Proposition63RichStickyKernelScheduleData sigma outerLoss)
    (hfirstReentryLoss : firstReentryLoss = firstSchedule.sourceLoss)
    (hfirstNormalizationLoss :
      firstReentry.reentryNormalizationLoss =
        firstSchedule.normalizationLoss)
    (hdeltaFirst : delta ≤ firstSchedule.delta₀)
    (robustScale : WZ2PaperRequestedScale delta)
    (hrobustLower : Real.rpow delta (1 - outerLoss) ≤ robustScale.1)
    (hrobustUpper : robustScale.1 ≤ Real.rpow delta outerLoss)
    (secondSchedule : Proposition63RichStickyKernelScheduleData sigma targetLoss)
    (hdeltaSecond : delta ≤ secondSchedule.delta₀)
    (densityAbsorb : Kakeya.realRpowENN delta densityLoss ≤
      Kakeya.realRpowENN delta firstReentryLoss / 2)
    (targetNearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := firstReentry.normalization.croppedFamily)
      (Kakeya.realRpowENN delta
        (-firstReentry.reentryNormalizationLoss))
      (Kakeya.realRpowENN delta (-secondSchedule.sourceLoss))
      (proposition63CanonicalNearbyLevelCount
        firstReentry.reentryNormalizationLoss))
    (ambientTwo : (2 : ENNReal) < Kakeya.realRpowENN delta
      (-firstReentry.reentryNormalizationLoss))
    (hsourceOuter :
      firstReentry.reentryNormalizationLoss ≤ outerExtremalLoss)
    (houterExtremalLoss : 0 < outerExtremalLoss)
    (houterRetention :
      Kakeya.realRpowENN delta outerExtremalLoss ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta firstReentry.reentryNormalizationLoss)
    (houterTargetReentry : outerExtremalLoss ≤ secondSchedule.sourceLoss)
    (canonicalWeightAbsorb :
      proposition63CanonicalReentryWeight delta weightLoss ≤
        (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta densityLoss *
          Kakeya.realRpowENN delta (outerExtremalLoss + 2))
    (traceFixedAbsorb :
      (96 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta
            (secondSchedule.sourceLoss - weightLoss) ≤ 1)
    (paperFixedAbsorb :
      ((4 : ENNReal) * 55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta
            (secondSchedule.sourceLoss - weightLoss) ≤ 73 / 100)
    (regularizationAbsorb :
      let degreeConstant :=
        16 * (targetNearbySchedule.scaleCount : ENNReal) *
          (Nat.log 2
            (2 * firstReentry.normalization.croppedFamily.card) + 1 :
              ENNReal) ^ targetNearbySchedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2
            (2 * firstReentry.normalization.croppedFamily.card) + 1 :
              ENNReal) ^ (targetNearbySchedule.scaleCount + 1)
      max degreeConstant
          (((proposition63CanonicalReentryWeight delta weightLoss)⁻¹ *
              (Kakeya.realRpowENN delta
                  (-firstReentry.reentryNormalizationLoss) *
                (regularizationLoss *
                  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
                    Kakeya.realRpowENN delta 2)) *
                degreeConstant)) *
            Kakeya.realRpowENN delta
              (-firstReentry.reentryNormalizationLoss)) ≤
        Kakeya.realRpowENN delta (-secondSchedule.sourceLoss))
    (hdeltaSmall : delta ≤ 1 / 100000)
    (targetScale : WZ2PaperRequestedScale delta)
    (htargetLower : Real.rpow delta (1 - targetLoss) ≤ targetScale.1)
    (htargetUpper : targetScale.1 ≤ Real.rpow delta targetLoss)
    {incidenceBound : ℝ}
    (currentMap : PaperWZ1WeakPlaneMapData current incidenceBound)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient currentMap.planeMap)
    (gridAbsorption : Proposition63RobustGridPruningAbsorptionData
      secondSchedule.normalizationLoss epsilon₁)
    (crossAbsorption :
      Proposition63ScaledTwoRichTerminalScalarAbsorptionData sigma
        robustExponent outerLoss secondSchedule.normalizationLoss weightLoss
        4 (proposition63CanonicalNearbyLevelCount
          firstReentry.reentryNormalizationLoss))
    (hdeltaGridAbsorption : delta ≤ gridAbsorption.delta₀)
    (hdeltaCrossAbsorption : delta ≤ crossAbsorption.delta₀)
    (hrobustScale : robustScale.1 = Real.rpow delta robustExponent)
    (hdeltaTau : delta ≤ tau)
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (boundaryAbsorption : Proposition63RobustBoundaryAbsorptionData
      targetLoss secondSchedule.normalizationLoss)
    (hdeltaBoundary : delta ≤ boundaryAbsorption.delta₀)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (htargetTau : targetScale.1 ≤ 3 * tau)
    (htauSq : tau ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              secondSchedule.normalizationLoss targetLoss targetScale.1 tau /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                tau ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta tau incidenceBound
              coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN (tau / delta) (1 - sigma))
    (hnormalizationParent :
      secondSchedule.normalizationLoss ≤ parentLoss)
    (hparentRetention :
      Kakeya.realRpowENN delta parentLoss ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta secondSchedule.normalizationLoss)
    (hparentOutput : parentLoss ≤ firstLoss)
    (hfirstLoss : 0 < firstLoss)
    (restoreAbsorption :
      Proposition63RobustPointCoverRestorationAbsorptionData
        parentLoss firstLoss 0)
    (hdeltaRestore : delta ≤ restoreAbsorption.delta₀) :
    ∃ outer : Proposition63RichTerminalStickyData
        (outputLoss := outerLoss) firstReentry.normalization.croppedRefined
        (firstReentry.normalization.toPropStickyReentryData
          (by rw [hfirstReentryLoss]; exact firstSchedule.sourceLoss_pos)
          firstReentry.reentry_normalization_loss_pos) robustScale,
      ∃ targetReentry : Proposition63CurrentShadingReentryData
          (reentryLoss := secondSchedule.sourceLoss)
          firstReentry.normalization
          (extendShading outer.data.selected outer.data.refined),
        ∃ target : Proposition63RichTerminalStickyData
            (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
            (targetReentry.normalization.toPropStickyReentryData
              secondSchedule.sourceLoss_pos
              targetReentry.reentry_normalization_loss_pos) targetScale,
          ∃ targetMap : PaperWZ1WeakPlaneMapData target.data.refined
              incidenceBound,
            targetMap.planeMap = currentMap.planeMap ∧
              LipschitzWith coefficient targetMap.planeMap ∧
              Nonempty (Proposition63FirstRobustTargetAmbientData
                (targetNormalizationLoss := secondSchedule.normalizationLoss)
                (tau := tau) (firstLoss := firstLoss)
                (weightLoss := weightLoss) robustScale outer
                targetReentry secondSchedule.sourceLoss_pos targetScale target
                (proposition63CanonicalNearbyLevelCount
                  firstReentry.reentryNormalizationLoss) targetMap.planeMap
                (C * Kakeya.realRpowENN (tau / delta) (1 - sigma))) := by
  rcases proposition63_nested_two_rich_runtime firstReentry firstSchedule
      hfirstReentryLoss hfirstNormalizationLoss hdeltaFirst hrobustLower
      hrobustUpper secondSchedule hdeltaSecond densityAbsorb
      targetNearbySchedule ambientTwo hsourceOuter houterExtremalLoss
      houterRetention houterTargetReentry canonicalWeightAbsorb
      traceFixedAbsorb paperFixedAbsorb regularizationAbsorb
      (hdeltaSmall.trans (by norm_num)) htargetLower htargetUpper with
    ⟨outer, targetReentry, hweight, hweightUpper, hlevel,
      hnormalizationActual, ⟨target⟩⟩
  let firstNormalizedMap := firstReentry.normalizedPlaneMap currentMap
  let outerMap := outer.terminalPlaneMap firstNormalizedMap
  let outerAmbientMap := outer.ambientTerminalPlaneMap outerMap
  let targetNormalizedMap := targetReentry.normalizedPlaneMap outerAmbientMap
  let targetMap := target.terminalPlaneMap targetNormalizedMap
  have htargetLipschitz : LipschitzWith coefficient targetMap.planeMap := by
    change LipschitzWith coefficient currentMap.planeMap
    exact hplaneLipschitz
  have hrestoreActual := restoreAbsorption.absorbTargetAmbient
    targetReentry.normalization target.data.selected hdeltaRestore
  have htauLower : Real.rpow delta (1 - targetLoss) ≤ 3 * tau :=
    htargetLower.trans htargetTau
  have hdeltaGrid := boundaryAbsorption.grid_le
    targetReentry.reentry_extremal.delta_pos hdeltaBoundary htau
      htauLower
  have hperiodic := boundaryAbsorption.periodic
    targetReentry.reentry_extremal.delta_pos hdeltaBoundary htau
      htauLower
  have hboundaryScalarActual := boundaryAbsorption.absorb
    targetReentry.reentry_extremal.delta_pos hdeltaBoundary htau htauLower
  have hfirst := proposition63_first_robust_target_ambient_of_absorptions
    outer targetReentry secondSchedule.sourceLoss_pos target
    hnormalizationActual gridAbsorption crossAbsorption
    hdeltaGridAbsorption hdeltaCrossAbsorption hrobustScale hweight
    hweightUpper hlevel targetMap htargetLipschitz hdeltaTau hdeltaGrid htau
    htauOne hperiodic (by simpa only [hnormalizationActual] using
      hboundaryScalarActual) hrobustSmall hkappa htargetSmall
    (hdeltaSmall.trans (by norm_num)) htargetTau
    htauSq hsigma hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale
    hdeltaLog hlog haxis C (by simpa only [hnormalizationActual] using
      harithmetic) (by simpa only [hnormalizationActual] using
      hnormalizationParent) (by simpa only [hnormalizationActual] using
      hparentRetention) hparentOutput hfirstLoss hrestoreActual
  exact ⟨outer, targetReentry, target, targetMap, rfl,
    htargetLipschitz, hfirst⟩

end Kakeya.Assouad.PureWZ2

end
