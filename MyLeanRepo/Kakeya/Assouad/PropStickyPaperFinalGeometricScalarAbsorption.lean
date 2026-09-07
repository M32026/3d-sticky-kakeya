import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryCoefficient
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryLogCoefficient
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCropBoundaryNormalized

/-!
# Scalar absorption for final geometric balancing

The crossing and crop estimates below depend only on the physical logarithmic
envelope and the two normalized boundary constants.  They are independent of
the post-deletion regularization pipeline.
-/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_final_geometric_crossing_scalar_absorption
    (sourceLoss stableLoss : ℝ)
    (hSourcePos : 0 < sourceLoss)
    (hSourceBoundary : 16 * sourceLoss < stableLoss)
    (firstLevelCount secondLevelCount : ℕ) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta rho : ℝ},
        ∀ (hdelta : 0 < delta),
        delta ≤ delta₀ →
        0 < rho →
        rho ≤ 1 →
        Real.rpow delta (1 - stableLoss) ≤ rho →
        ∀ (firstLog secondLog fineLog firstLoss secondLoss
          topLevelConstant : ENNReal),
          firstLog ≤
              ENNReal.ofReal
                (wz2PaperBoundaryLogCoefficient *
                  (1 + Real.log delta⁻¹)) →
          secondLog ≤
              ENNReal.ofReal
                (wz2PaperBoundaryLogCoefficient *
                  (1 + Real.log delta⁻¹)) →
          fineLog ≤
              ENNReal.ofReal
                (wz2PaperBoundaryLogCoefficient *
                  (1 + Real.log delta⁻¹)) →
          firstLoss ≤
              8 * firstLog ^ (firstLevelCount + 2) →
          secondLoss ≤
              8 * secondLog ^ (secondLevelCount + 2) →
          topLevelConstant ≤
              Kakeya.realRpowENN delta (-4 * sourceLoss) →
          let fraction := wz1PaperRefinementFraction delta 20
          let bandFactor :=
            firstLoss * fraction⁻¹ * (secondLoss * fineLog)
          2 * bandFactor * 24000000 *
                (topLevelConstant * wz2PaperBoundaryGeometryConstant + 1) *
                ENNReal.ofReal (Real.sqrt (delta / rho)) <
            wz1PaperRefinementFraction delta 4 *
              ((1 / 2 : ENNReal) *
                Kakeya.realRpowENN delta sourceLoss) := by
  let exponent : ℕ :=
    firstLevelCount + secondLevelCount + 29
  let geometry : ENNReal := wz2PaperBoundaryGeometryConstant
  let fixed : ENNReal :=
    512 * 24000000 * (geometry + 1)
  have hGeometryTop : geometry ≠ ⊤ := by
    dsimp only [geometry, wz2PaperBoundaryGeometryConstant]
    exact ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
  have hFixedTop : fixed ≠ ⊤ := by
    dsimp only [fixed]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) (by norm_num))
      (ENNReal.add_ne_top.mpr ⟨hGeometryTop, by norm_num⟩)
  let logCoefficient : ℝ := wz2PaperBoundaryLogCoefficient
  have hLogCoefficient : 0 ≤ logCoefficient := by
    dsimp only [logCoefficient, wz2PaperBoundaryLogCoefficient]
    positivity
  have hStablePos : 0 < stableLoss := by
    linarith
  have hGap :
      0 < stableLoss / 2 - 5 * sourceLoss := by
    linarith
  have hExponentPos : 0 < exponent := by
    dsimp only [exponent]
    omega
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        fixed hFixedTop logCoefficient hLogCoefficient
        hGap hExponentPos
    with ⟨powerScale, hPowerScalePos, hPowerScaleOne, hPowerAbsorb⟩
  let delta₀ := min powerScale (1 / 2 : ℝ)
  refine
    ⟨delta₀, lt_min hPowerScalePos (by norm_num),
      (min_le_left _ _).trans hPowerScaleOne, ?_⟩
  intro delta rho hdelta hdeltaBound hrho hrhoOne hCallerLower
    firstLog secondLog fineLog firstLoss secondLoss topLevelConstant
    hFirstLog hSecondLog hFineLog hFirstLoss hSecondLoss hTopLevel
  have hdeltaPower : delta ≤ powerScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaHalf : delta ≤ 1 / 2 :=
    hdeltaBound.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 := by linarith
  have hdeltaStrict : delta < 1 := by linarith
  let logScale : ENNReal :=
    ENNReal.ofReal (Real.log delta⁻¹)
  let envelope : ENNReal :=
    ENNReal.ofReal
      (logCoefficient * (1 + Real.log delta⁻¹))
  let fraction := wz1PaperRefinementFraction delta 20
  let bandFactor :=
    firstLoss * fraction⁻¹ * (secondLoss * fineLog)
  have hLogRealPos : 0 < Real.log delta⁻¹ := by
    apply Real.log_pos
    exact (one_lt_inv₀ hdelta).mpr hdeltaStrict
  have hLogScaleZero : logScale ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hLogRealPos).ne'
  have hLogScaleTop : logScale ≠ ⊤ := by
    dsimp only [logScale]
    exact ENNReal.ofReal_ne_top
  have hLogEnvelope : logScale ≤ envelope := by
    dsimp only [logScale, envelope]
    apply ENNReal.ofReal_mono
    have hCoefficientOne :
        1 ≤ logCoefficient := by
      dsimp only [logCoefficient, wz2PaperBoundaryLogCoefficient]
      have hleft :
          1 ≤ 5 * Real.log 163 / Real.log 2 + 2 := by
        have hnonneg :
            0 ≤ 5 * Real.log 163 / Real.log 2 := by
          positivity
        linarith
      exact hleft.trans (le_max_left _ _)
    calc
      Real.log delta⁻¹ ≤ 1 + Real.log delta⁻¹ := by linarith
      _ ≤ logCoefficient * (1 + Real.log delta⁻¹) := by
        exact
          le_mul_of_one_le_left
            (by linarith [hLogRealPos]) hCoefficientOne
  have hFirstLog' : firstLog ≤ envelope := by
    simpa [envelope, logCoefficient] using hFirstLog
  have hSecondLog' : secondLog ≤ envelope := by
    simpa [envelope, logCoefficient] using hSecondLog
  have hFineLog' : fineLog ≤ envelope := by
    simpa [envelope, logCoefficient] using hFineLog
  have hFractionInv :
      fraction⁻¹ = logScale ^ 20 := by
    dsimp only [fraction, wz1PaperRefinementFraction, logScale]
    rw [ENNReal.inv_pow, inv_inv]
    congr 2
    congr 1
    field_simp [hdelta.ne']
  have hFirstLossEnvelope :
      firstLoss ≤ 8 * envelope ^ (firstLevelCount + 2) := by
    calc
      firstLoss ≤ 8 * firstLog ^ (firstLevelCount + 2) :=
        hFirstLoss
      _ ≤ 8 * envelope ^ (firstLevelCount + 2) := by
        gcongr
  have hSecondLossEnvelope :
      secondLoss ≤ 8 * envelope ^ (secondLevelCount + 2) := by
    calc
      secondLoss ≤ 8 * secondLog ^ (secondLevelCount + 2) :=
        hSecondLoss
      _ ≤ 8 * envelope ^ (secondLevelCount + 2) := by
        gcongr
  have hBandFactor :
      bandFactor ≤
        64 * envelope ^
          (firstLevelCount + secondLevelCount + 25) := by
    rw [show bandFactor =
        firstLoss * fraction⁻¹ * (secondLoss * fineLog) by rfl]
    rw [hFractionInv]
    calc
      firstLoss * logScale ^ 20 * (secondLoss * fineLog) ≤
          (8 * envelope ^ (firstLevelCount + 2)) *
            envelope ^ 20 *
              ((8 * envelope ^ (secondLevelCount + 2)) * envelope) := by
        gcongr
      _ =
          64 * envelope ^
            (firstLevelCount + secondLevelCount + 25) := by
        have hPower :
            envelope ^ (firstLevelCount + 2) *
                  envelope ^ 20 *
                  (envelope ^ (secondLevelCount + 2) * envelope) =
              envelope ^
                (firstLevelCount + secondLevelCount + 25) := by
          have hFirst :
              envelope ^ (firstLevelCount + 2) * envelope ^ 20 =
                envelope ^ ((firstLevelCount + 2) + 20) :=
            (pow_add envelope (firstLevelCount + 2) 20).symm
          have hSecond :
              envelope ^ (secondLevelCount + 2) * envelope =
                envelope ^ ((secondLevelCount + 2) + 1) := by
            simpa using (pow_succ envelope (secondLevelCount + 2)).symm
          have hCombined :
              envelope ^ ((firstLevelCount + 2) + 20) *
                    envelope ^ ((secondLevelCount + 2) + 1) =
                envelope ^
                  (((firstLevelCount + 2) + 20) +
                    ((secondLevelCount + 2) + 1)) :=
            (pow_add envelope
              ((firstLevelCount + 2) + 20)
              ((secondLevelCount + 2) + 1)).symm
          calc
            envelope ^ (firstLevelCount + 2) *
                  envelope ^ 20 *
                  (envelope ^ (secondLevelCount + 2) * envelope) =
                envelope ^
                  ((firstLevelCount + 2) + 20 +
                    ((secondLevelCount + 2) + 1)) := by
              rw [hFirst, hSecond]
              exact hCombined
            _ =
                envelope ^
                  (firstLevelCount + secondLevelCount + 25) := by
              congr 1
              omega
        rw [show
          (8 * envelope ^ (firstLevelCount + 2)) *
                envelope ^ 20 *
                ((8 * envelope ^ (secondLevelCount + 2)) * envelope) =
              64 *
                (envelope ^ (firstLevelCount + 2) *
                  envelope ^ 20 *
                  (envelope ^ (secondLevelCount + 2) * envelope)) by
            ring]
        rw [hPower]
  have hMiddleOne :
      (1 : ENNReal) ≤
        Kakeya.realRpowENN delta (-4 * sourceLoss) := by
    simpa only [neg_mul] using
      middleConstant_ge_one hdelta hdeltaOne
        (by positivity : 0 < 4 * sourceLoss)
  have hTopEnvelope :
      topLevelConstant * geometry + 1 ≤
        Kakeya.realRpowENN delta (-4 * sourceLoss) *
          (geometry + 1) := by
    calc
      topLevelConstant * geometry + 1 ≤
          Kakeya.realRpowENN delta (-4 * sourceLoss) * geometry + 1 := by
        gcongr
      _ ≤
          Kakeya.realRpowENN delta (-4 * sourceLoss) * geometry +
            Kakeya.realRpowENN delta (-4 * sourceLoss) := by
        gcongr
      _ =
          Kakeya.realRpowENN delta (-4 * sourceLoss) *
            (geometry + 1) := by ring
  have hRatio :
      delta / rho ≤ Real.rpow delta stableLoss := by
    rw [div_le_iff₀ hrho]
    calc
      delta =
          Real.rpow delta stableLoss *
            Real.rpow delta (1 - stableLoss) := by
        calc
          delta = Real.rpow delta (stableLoss + (1 - stableLoss)) := by
            rw [show stableLoss + (1 - stableLoss) = 1 by ring]
            exact (Real.rpow_one delta).symm
          _ =
              Real.rpow delta stableLoss *
                Real.rpow delta (1 - stableLoss) :=
            Real.rpow_add hdelta _ _
      _ ≤ Real.rpow delta stableLoss * rho := by
        exact mul_le_mul_of_nonneg_left hCallerLower
          (Real.rpow_nonneg hdelta.le _)
  have hRoot :
      ENNReal.ofReal (Real.sqrt (delta / rho)) ≤
        Kakeya.realRpowENN delta (stableLoss / 2) := by
    apply ENNReal.ofReal_mono
    calc
      Real.sqrt (delta / rho) ≤
          Real.sqrt (Real.rpow delta stableLoss) :=
        Real.sqrt_le_sqrt hRatio
      _ = Real.rpow delta (stableLoss / 2) := by
        calc
          Real.sqrt (Real.rpow delta stableLoss) =
              Real.rpow (Real.rpow delta stableLoss) (1 / 2) :=
            Real.sqrt_eq_rpow _
          _ = Real.rpow delta (stableLoss * (1 / 2)) :=
            (Real.rpow_mul hdelta.le _ _).symm
          _ = Real.rpow delta (stableLoss / 2) := by
            congr 1
            ring
  have hEnvelopePower :
      envelope ^ exponent =
        envelope ^ (firstLevelCount + secondLevelCount + 25) *
          envelope ^ 4 := by
    rw [← pow_add]
  have hPowerBound :
      fixed * envelope ^ exponent ≤
        Kakeya.realRpowENN delta
          (-(stableLoss / 2 - 5 * sourceLoss)) :=
    hPowerAbsorb delta hdelta hdeltaPower
  have hGapPower :
      Kakeya.realRpowENN delta
            (-(stableLoss / 2 - 5 * sourceLoss)) *
          Kakeya.realRpowENN delta (-4 * sourceLoss) *
          Kakeya.realRpowENN delta (stableLoss / 2) =
        Kakeya.realRpowENN delta sourceLoss := by
    rw [← realRpowENN_add hdelta, ← realRpowENN_add hdelta]
    congr 2
    ring
  have hQuarter :
      (1 / 4 : ENNReal) * 512 = 128 := by
    have hCancel :
        (4 : ENNReal)⁻¹ * 4 = 1 :=
      ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
    calc
      (1 / 4 : ENNReal) * 512 =
          (4 : ENNReal)⁻¹ * (4 * 128) := by
        rw [one_div]
        norm_num
      _ = ((4 : ENNReal)⁻¹ * 4) * 128 := by ring
      _ = 128 := by rw [hCancel, one_mul]
  have hScalar :
      (2 * bandFactor * 24000000 *
          (topLevelConstant * geometry + 1) *
          ENNReal.ofReal (Real.sqrt (delta / rho))) *
          logScale ^ 4 <
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss := by
    calc
      (2 * bandFactor * 24000000 *
          (topLevelConstant * geometry + 1) *
          ENNReal.ofReal (Real.sqrt (delta / rho))) *
          logScale ^ 4 ≤
        (128 * 24000000 * (geometry + 1)) *
          envelope ^ exponent *
          Kakeya.realRpowENN delta (-4 * sourceLoss) *
          Kakeya.realRpowENN delta (stableLoss / 2) := by
        calc
          _ ≤
              (2 *
                (64 * envelope ^
                  (firstLevelCount + secondLevelCount + 25)) *
                24000000 *
                (Kakeya.realRpowENN delta (-4 * sourceLoss) *
                  (geometry + 1)) *
                Kakeya.realRpowENN delta (stableLoss / 2)) *
                envelope ^ 4 := by
            gcongr
          _ =
              (128 * 24000000 * (geometry + 1)) *
                envelope ^ exponent *
                Kakeya.realRpowENN delta (-4 * sourceLoss) *
                Kakeya.realRpowENN delta (stableLoss / 2) := by
            rw [hEnvelopePower]
            ring
      _ =
          (1 / 4 : ENNReal) *
            (fixed * envelope ^ exponent) *
            Kakeya.realRpowENN delta (-4 * sourceLoss) *
            Kakeya.realRpowENN delta (stableLoss / 2) := by
        dsimp only [fixed]
        calc
          (128 * 24000000 * (geometry + 1)) *
                envelope ^ exponent *
                Kakeya.realRpowENN delta (-4 * sourceLoss) *
                Kakeya.realRpowENN delta (stableLoss / 2) =
              ((1 / 4 : ENNReal) * 512) *
                24000000 * (geometry + 1) * envelope ^ exponent *
                Kakeya.realRpowENN delta (-4 * sourceLoss) *
                Kakeya.realRpowENN delta (stableLoss / 2) := by
            rw [hQuarter]
          _ =
              (1 / 4 : ENNReal) *
                (512 * 24000000 * (geometry + 1) *
                  envelope ^ exponent) *
                Kakeya.realRpowENN delta (-4 * sourceLoss) *
                Kakeya.realRpowENN delta (stableLoss / 2) := by
            ring
      _ ≤
          (1 / 4 : ENNReal) *
            Kakeya.realRpowENN delta
              (-(stableLoss / 2 - 5 * sourceLoss)) *
            Kakeya.realRpowENN delta (-4 * sourceLoss) *
            Kakeya.realRpowENN delta (stableLoss / 2) := by
        gcongr
      _ =
          (1 / 4 : ENNReal) *
            Kakeya.realRpowENN delta sourceLoss := by
        calc
          (1 / 4 : ENNReal) *
                Kakeya.realRpowENN delta
                  (-(stableLoss / 2 - 5 * sourceLoss)) *
                Kakeya.realRpowENN delta (-4 * sourceLoss) *
                Kakeya.realRpowENN delta (stableLoss / 2) =
              (1 / 4 : ENNReal) *
                (Kakeya.realRpowENN delta
                    (-(stableLoss / 2 - 5 * sourceLoss)) *
                  Kakeya.realRpowENN delta (-4 * sourceLoss) *
                  Kakeya.realRpowENN delta (stableLoss / 2)) := by
            ring
          _ =
              (1 / 4 : ENNReal) *
                Kakeya.realRpowENN delta sourceLoss := by
            rw [hGapPower]
      _ <
          (1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta sourceLoss := by
        have hPowerZero :
            Kakeya.realRpowENN delta sourceLoss ≠ 0 := by
          simp [Kakeya.realRpowENN,
            Real.rpow_pos_of_pos hdelta]
        have hPowerTop :
            Kakeya.realRpowENN delta sourceLoss ≠ ⊤ := by
          simp [Kakeya.realRpowENN]
        have hQuarterHalf :
            (1 / 4 : ENNReal) < (1 / 2 : ENNReal) := by
          rw [one_div, one_div]
          exact ENNReal.inv_lt_inv' (by norm_num)
        exact
          (by
            simpa [mul_comm] using
              ENNReal.mul_lt_mul_right
                hPowerZero hPowerTop hQuarterHalf)
  have hFractionFour :
      wz1PaperRefinementFraction delta 4 =
        logScale⁻¹ ^ 4 := by
    dsimp only [wz1PaperRefinementFraction, logScale]
    congr 2
    congr 1
    field_simp [hdelta.ne']
  have hCancel :
      wz1PaperRefinementFraction delta 4 * logScale ^ 4 = 1 := by
    rw [hFractionFour, ← mul_pow,
      ENNReal.inv_mul_cancel hLogScaleZero hLogScaleTop]
    norm_num
  change
    2 * bandFactor * 24000000 *
          (topLevelConstant * geometry + 1) *
          ENNReal.ofReal (Real.sqrt (delta / rho)) <
      wz1PaperRefinementFraction delta 4 *
        ((1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss)
  calc
    2 * bandFactor * 24000000 *
          (topLevelConstant * geometry + 1) *
          ENNReal.ofReal (Real.sqrt (delta / rho)) =
        wz1PaperRefinementFraction delta 4 *
          ((2 * bandFactor * 24000000 *
            (topLevelConstant * geometry + 1) *
            ENNReal.ofReal (Real.sqrt (delta / rho))) *
            logScale ^ 4) := by
      calc
        _ = 1 *
            (2 * bandFactor * 24000000 *
              (topLevelConstant * geometry + 1) *
              ENNReal.ofReal (Real.sqrt (delta / rho))) := by simp
        _ =
            (wz1PaperRefinementFraction delta 4 * logScale ^ 4) *
              (2 * bandFactor * 24000000 *
                (topLevelConstant * geometry + 1) *
                ENNReal.ofReal (Real.sqrt (delta / rho))) := by
          rw [hCancel]
        _ =
            wz1PaperRefinementFraction delta 4 *
              ((2 * bandFactor * 24000000 *
                (topLevelConstant * geometry + 1) *
                ENNReal.ofReal (Real.sqrt (delta / rho))) *
                logScale ^ 4) := by ring
    _ <
        wz1PaperRefinementFraction delta 4 *
          ((1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta sourceLoss) := by
      exact
        ENNReal.mul_lt_mul_right
          (by
            rw [hFractionFour]
            exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr hLogScaleTop))
          (by
            rw [hFractionFour]
            exact ENNReal.pow_ne_top
              (ENNReal.inv_ne_top.mpr hLogScaleZero))
          hScalar

theorem wz2_paper_final_geometric_crop_scalar_absorption
    (sourceLoss outputLoss : ℝ)
    (hSourcePos : 0 < sourceLoss)
    (hSourceOutput : 16 * sourceLoss < outputLoss)
    (firstLevelCount secondLevelCount : ℕ) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta rho : ℝ},
        ∀ (hdelta : 0 < delta),
        delta ≤ delta₀ →
        0 < rho →
        rho ≤ 1 →
        rho ≤ Real.rpow delta outputLoss →
        ∀ (firstLog secondLog fineLog availableLog
          firstLoss secondLoss topLevelConstant : ENNReal),
          firstLog ≤
              ENNReal.ofReal
                (wz2PaperBoundaryLogCoefficient *
                  (1 + Real.log delta⁻¹)) →
          secondLog ≤
              ENNReal.ofReal
                (wz2PaperBoundaryLogCoefficient *
                  (1 + Real.log delta⁻¹)) →
          fineLog ≤
              ENNReal.ofReal
                (wz2PaperBoundaryLogCoefficient *
                  (1 + Real.log delta⁻¹)) →
          availableLog ≤
              ENNReal.ofReal
                (wz2PaperBoundaryLogCoefficient *
                  (1 + Real.log delta⁻¹)) →
          firstLoss ≤
              8 * firstLog ^ (firstLevelCount + 2) →
          secondLoss ≤
              8 * secondLog ^ (secondLevelCount + 2) →
          topLevelConstant ≤
              Kakeya.realRpowENN delta (-4 * sourceLoss) →
          let fraction := wz1PaperRefinementFraction delta 20
          let lossFactor :=
            firstLoss * fraction⁻¹ *
              (secondLoss * fineLog) * (8 * availableLog)
          2 * lossFactor * wz2PaperCropBoundaryMassConstant *
                (topLevelConstant + 1) *
                ENNReal.ofReal (Real.sqrt rho) <
            wz1PaperRefinementFraction delta 4 *
              ((1 / 2 : ENNReal) *
                Kakeya.realRpowENN delta sourceLoss) := by
  let exponent : ℕ :=
    firstLevelCount + secondLevelCount + 30
  let fixed : ENNReal :=
    8192 * wz2PaperCropBoundaryMassConstant
  have hFixedTop : fixed ≠ ⊤ := by
    dsimp only [fixed, wz2PaperCropBoundaryMassConstant]
    exact ENNReal.mul_ne_top (by norm_num) <|
      ENNReal.mul_ne_top (by norm_num) <|
        ENNReal.add_ne_top.mpr
          ⟨ENNReal.mul_ne_top (by norm_num)
              deltaTubeVolume_one_ne_top,
            by norm_num⟩
  let logCoefficient : ℝ := wz2PaperBoundaryLogCoefficient
  have hLogCoefficient : 0 ≤ logCoefficient := by
    dsimp only [logCoefficient, wz2PaperBoundaryLogCoefficient]
    positivity
  have hGap : 0 < outputLoss / 2 - 5 * sourceLoss := by
    linarith
  have hExponentPos : 0 < exponent := by
    dsimp only [exponent]
    omega
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        fixed hFixedTop logCoefficient hLogCoefficient
        hGap hExponentPos
    with ⟨powerScale, hPowerScalePos, hPowerScaleOne, hPowerAbsorb⟩
  let delta₀ := min powerScale (1 / 2 : ℝ)
  refine
    ⟨delta₀, lt_min hPowerScalePos (by norm_num),
      (min_le_left _ _).trans hPowerScaleOne, ?_⟩
  intro delta rho hdelta hdeltaBound hrho hrhoOne hRhoUpper
    firstLog secondLog fineLog availableLog firstLoss secondLoss
    topLevelConstant hFirstLog hSecondLog hFineLog hAvailableLog
    hFirstLoss hSecondLoss hTopLevel
  have hdeltaPower : delta ≤ powerScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaHalf : delta ≤ 1 / 2 :=
    hdeltaBound.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 := by linarith
  have hdeltaStrict : delta < 1 := by linarith
  let logScale : ENNReal :=
    ENNReal.ofReal (Real.log delta⁻¹)
  let envelope : ENNReal :=
    ENNReal.ofReal
      (logCoefficient * (1 + Real.log delta⁻¹))
  let fraction := wz1PaperRefinementFraction delta 20
  let lossFactor :=
    firstLoss * fraction⁻¹ *
      (secondLoss * fineLog) * (8 * availableLog)
  have hLogRealPos : 0 < Real.log delta⁻¹ := by
    apply Real.log_pos
    exact (one_lt_inv₀ hdelta).mpr hdeltaStrict
  have hLogScaleZero : logScale ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hLogRealPos).ne'
  have hLogScaleTop : logScale ≠ ⊤ := by
    dsimp only [logScale]
    exact ENNReal.ofReal_ne_top
  have hLogEnvelope : logScale ≤ envelope := by
    dsimp only [logScale, envelope]
    apply ENNReal.ofReal_mono
    have hCoefficientOne : 1 ≤ logCoefficient := by
      dsimp only [logCoefficient, wz2PaperBoundaryLogCoefficient]
      have hleft :
          1 ≤ 5 * Real.log 163 / Real.log 2 + 2 := by
        have hnonneg :
            0 ≤ 5 * Real.log 163 / Real.log 2 := by
          positivity
        linarith
      exact hleft.trans (le_max_left _ _)
    calc
      Real.log delta⁻¹ ≤ 1 + Real.log delta⁻¹ := by linarith
      _ ≤ logCoefficient * (1 + Real.log delta⁻¹) := by
        exact le_mul_of_one_le_left
          (by linarith [hLogRealPos]) hCoefficientOne
  have hFirstLog' : firstLog ≤ envelope := by
    simpa [envelope, logCoefficient] using hFirstLog
  have hSecondLog' : secondLog ≤ envelope := by
    simpa [envelope, logCoefficient] using hSecondLog
  have hFineLog' : fineLog ≤ envelope := by
    simpa [envelope, logCoefficient] using hFineLog
  have hAvailableLog' : availableLog ≤ envelope := by
    simpa [envelope, logCoefficient] using hAvailableLog
  have hFractionInv :
      fraction⁻¹ = logScale ^ 20 := by
    dsimp only [fraction, wz1PaperRefinementFraction, logScale]
    rw [ENNReal.inv_pow, inv_inv]
    congr 2
    congr 1
    field_simp [hdelta.ne']
  have hFirstLossEnvelope :
      firstLoss ≤ 8 * envelope ^ (firstLevelCount + 2) := by
    calc
      firstLoss ≤ 8 * firstLog ^ (firstLevelCount + 2) := hFirstLoss
      _ ≤ 8 * envelope ^ (firstLevelCount + 2) := by gcongr
  have hSecondLossEnvelope :
      secondLoss ≤ 8 * envelope ^ (secondLevelCount + 2) := by
    calc
      secondLoss ≤ 8 * secondLog ^ (secondLevelCount + 2) := hSecondLoss
      _ ≤ 8 * envelope ^ (secondLevelCount + 2) := by gcongr
  have hLossFactor :
      lossFactor ≤
        512 * envelope ^
          (firstLevelCount + secondLevelCount + 26) := by
    rw [show lossFactor =
        firstLoss * fraction⁻¹ *
          (secondLoss * fineLog) * (8 * availableLog) by rfl]
    rw [hFractionInv]
    calc
      firstLoss * logScale ^ 20 *
            (secondLoss * fineLog) * (8 * availableLog) ≤
          (8 * envelope ^ (firstLevelCount + 2)) *
            envelope ^ 20 *
            ((8 * envelope ^ (secondLevelCount + 2)) * envelope) *
            (8 * envelope) := by
        gcongr
      _ =
          512 * envelope ^
            (firstLevelCount + secondLevelCount + 26) := by
        have hPower :
            envelope ^ (firstLevelCount + 2) *
                  envelope ^ 20 *
                  (envelope ^ (secondLevelCount + 2) * envelope) *
                  envelope =
              envelope ^
                (firstLevelCount + secondLevelCount + 26) := by
          have hFirst :
              envelope ^ (firstLevelCount + 2) * envelope ^ 20 =
                envelope ^ ((firstLevelCount + 2) + 20) :=
            (pow_add envelope (firstLevelCount + 2) 20).symm
          have hSecond :
              envelope ^ (secondLevelCount + 2) * envelope =
                envelope ^ ((secondLevelCount + 2) + 1) := by
            simpa using (pow_succ envelope (secondLevelCount + 2)).symm
          calc
            envelope ^ (firstLevelCount + 2) *
                  envelope ^ 20 *
                  (envelope ^ (secondLevelCount + 2) * envelope) *
                  envelope =
                envelope ^ ((firstLevelCount + 2) + 20) *
                  envelope ^ ((secondLevelCount + 2) + 1) *
                  envelope := by
              rw [hFirst, hSecond]
            _ =
                envelope ^
                  (((firstLevelCount + 2) + 20) +
                    ((secondLevelCount + 2) + 1) + 1) := by
              rw [← pow_add]
              exact
                (pow_succ envelope
                  (((firstLevelCount + 2) + 20) +
                    ((secondLevelCount + 2) + 1))).symm
            _ =
                envelope ^
                  (firstLevelCount + secondLevelCount + 26) := by
              congr 1
              omega
        rw [show
          (8 * envelope ^ (firstLevelCount + 2)) *
                envelope ^ 20 *
                ((8 * envelope ^ (secondLevelCount + 2)) * envelope) *
                (8 * envelope) =
              512 *
                (envelope ^ (firstLevelCount + 2) *
                  envelope ^ 20 *
                  (envelope ^ (secondLevelCount + 2) * envelope) *
                  envelope) by ring]
        rw [hPower]
  have hMiddleOne :
      (1 : ENNReal) ≤
        Kakeya.realRpowENN delta (-4 * sourceLoss) := by
    simpa only [neg_mul] using
      middleConstant_ge_one hdelta hdeltaOne
        (by positivity : 0 < 4 * sourceLoss)
  have hTopEnvelope :
      topLevelConstant + 1 ≤
        Kakeya.realRpowENN delta (-4 * sourceLoss) * 2 := by
    calc
      topLevelConstant + 1 ≤
          Kakeya.realRpowENN delta (-4 * sourceLoss) + 1 := by
        gcongr
      _ ≤
          Kakeya.realRpowENN delta (-4 * sourceLoss) +
            Kakeya.realRpowENN delta (-4 * sourceLoss) := by
        gcongr
      _ = Kakeya.realRpowENN delta (-4 * sourceLoss) * 2 := by ring
  have hRoot :
      ENNReal.ofReal (Real.sqrt rho) ≤
        Kakeya.realRpowENN delta (outputLoss / 2) := by
    apply ENNReal.ofReal_mono
    calc
      Real.sqrt rho ≤
          Real.sqrt (Real.rpow delta outputLoss) :=
        Real.sqrt_le_sqrt hRhoUpper
      _ = Real.rpow delta (outputLoss / 2) := by
        calc
          Real.sqrt (Real.rpow delta outputLoss) =
              Real.rpow (Real.rpow delta outputLoss) (1 / 2) :=
            Real.sqrt_eq_rpow _
          _ = Real.rpow delta (outputLoss * (1 / 2)) :=
            (Real.rpow_mul hdelta.le _ _).symm
          _ = Real.rpow delta (outputLoss / 2) := by
            congr 1
            ring
  have hEnvelopePower :
      envelope ^ exponent =
        envelope ^ (firstLevelCount + secondLevelCount + 26) *
          envelope ^ 4 := by
    rw [← pow_add]
  have hPowerBound :
      fixed * envelope ^ exponent ≤
        Kakeya.realRpowENN delta
          (-(outputLoss / 2 - 5 * sourceLoss)) :=
    hPowerAbsorb delta hdelta hdeltaPower
  have hGapPower :
      Kakeya.realRpowENN delta
            (-(outputLoss / 2 - 5 * sourceLoss)) *
          Kakeya.realRpowENN delta (-4 * sourceLoss) *
          Kakeya.realRpowENN delta (outputLoss / 2) =
        Kakeya.realRpowENN delta sourceLoss := by
    rw [← realRpowENN_add hdelta, ← realRpowENN_add hdelta]
    congr 2
    ring
  have hScalarCore :
      (2 * lossFactor * wz2PaperCropBoundaryMassConstant *
          (topLevelConstant + 1) *
          ENNReal.ofReal (Real.sqrt rho)) * logScale ^ 4 <
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss := by
    calc
      _ ≤
          (2048 * wz2PaperCropBoundaryMassConstant) *
            envelope ^ exponent *
            Kakeya.realRpowENN delta (-4 * sourceLoss) *
            Kakeya.realRpowENN delta (outputLoss / 2) := by
        calc
          _ ≤
              (2 * (512 * envelope ^
                (firstLevelCount + secondLevelCount + 26)) *
                wz2PaperCropBoundaryMassConstant *
                (Kakeya.realRpowENN delta (-4 * sourceLoss) * 2) *
                Kakeya.realRpowENN delta (outputLoss / 2)) *
                envelope ^ 4 := by
            gcongr
          _ =
              (2048 * wz2PaperCropBoundaryMassConstant) *
                envelope ^ exponent *
                Kakeya.realRpowENN delta (-4 * sourceLoss) *
                Kakeya.realRpowENN delta (outputLoss / 2) := by
            rw [hEnvelopePower]
            ring
      _ =
          (1 / 4 : ENNReal) * (fixed * envelope ^ exponent) *
            Kakeya.realRpowENN delta (-4 * sourceLoss) *
            Kakeya.realRpowENN delta (outputLoss / 2) := by
        dsimp only [fixed]
        have hQuarter :
            (1 / 4 : ENNReal) * 8192 = 2048 := by
          have hCancel :
              (4 : ENNReal)⁻¹ * 4 = 1 :=
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
          calc
            (1 / 4 : ENNReal) * 8192 =
                (4 : ENNReal)⁻¹ * (4 * 2048) := by
              rw [one_div]
              norm_num
            _ = ((4 : ENNReal)⁻¹ * 4) * 2048 := by ring
            _ = 2048 := by rw [hCancel, one_mul]
        rw [← hQuarter]
        ring
      _ ≤
          (1 / 4 : ENNReal) *
            Kakeya.realRpowENN delta
              (-(outputLoss / 2 - 5 * sourceLoss)) *
            Kakeya.realRpowENN delta (-4 * sourceLoss) *
            Kakeya.realRpowENN delta (outputLoss / 2) := by
        gcongr
      _ =
          (1 / 4 : ENNReal) *
            Kakeya.realRpowENN delta sourceLoss := by
        calc
          (1 / 4 : ENNReal) *
                Kakeya.realRpowENN delta
                  (-(outputLoss / 2 - 5 * sourceLoss)) *
                Kakeya.realRpowENN delta (-4 * sourceLoss) *
                Kakeya.realRpowENN delta (outputLoss / 2) =
              (1 / 4 : ENNReal) *
                (Kakeya.realRpowENN delta
                    (-(outputLoss / 2 - 5 * sourceLoss)) *
                  Kakeya.realRpowENN delta (-4 * sourceLoss) *
                  Kakeya.realRpowENN delta (outputLoss / 2)) := by
            ring
          _ =
              (1 / 4 : ENNReal) *
                Kakeya.realRpowENN delta sourceLoss := by
            rw [hGapPower]
      _ <
          (1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta sourceLoss := by
        have hPowerZero :
            Kakeya.realRpowENN delta sourceLoss ≠ 0 := by
          simp [Kakeya.realRpowENN,
            Real.rpow_pos_of_pos hdelta]
        have hPowerTop :
            Kakeya.realRpowENN delta sourceLoss ≠ ⊤ := by
          simp [Kakeya.realRpowENN]
        have hQuarterHalf :
            (1 / 4 : ENNReal) < (1 / 2 : ENNReal) := by
          rw [one_div, one_div]
          exact ENNReal.inv_lt_inv' (by norm_num)
        simpa [mul_comm] using
          ENNReal.mul_lt_mul_right
            hPowerZero hPowerTop hQuarterHalf
  have hFractionFour :
      wz1PaperRefinementFraction delta 4 =
        logScale⁻¹ ^ 4 := by
    dsimp only [wz1PaperRefinementFraction, logScale]
    congr 2
    congr 1
    field_simp [hdelta.ne']
  have hFractionZero :
      wz1PaperRefinementFraction delta 4 ≠ 0 := by
    rw [hFractionFour]
    exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr hLogScaleTop)
  have hFractionTop :
      wz1PaperRefinementFraction delta 4 ≠ ⊤ := by
    rw [hFractionFour]
    exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr hLogScaleZero)
  have hCancel :
      wz1PaperRefinementFraction delta 4 * logScale ^ 4 = 1 := by
    rw [hFractionFour, ← mul_pow,
      ENNReal.inv_mul_cancel hLogScaleZero hLogScaleTop]
    norm_num
  change
    2 * lossFactor * wz2PaperCropBoundaryMassConstant *
          (topLevelConstant + 1) *
          ENNReal.ofReal (Real.sqrt rho) <
      wz1PaperRefinementFraction delta 4 *
        ((1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss)
  calc
    2 * lossFactor * wz2PaperCropBoundaryMassConstant *
          (topLevelConstant + 1) *
          ENNReal.ofReal (Real.sqrt rho) =
        wz1PaperRefinementFraction delta 4 *
          ((2 * lossFactor * wz2PaperCropBoundaryMassConstant *
            (topLevelConstant + 1) *
            ENNReal.ofReal (Real.sqrt rho)) * logScale ^ 4) := by
      calc
        2 * lossFactor * wz2PaperCropBoundaryMassConstant *
              (topLevelConstant + 1) *
              ENNReal.ofReal (Real.sqrt rho) =
            1 *
              (2 * lossFactor * wz2PaperCropBoundaryMassConstant *
                (topLevelConstant + 1) *
                ENNReal.ofReal (Real.sqrt rho)) := by simp
        _ =
            (wz1PaperRefinementFraction delta 4 * logScale ^ 4) *
              (2 * lossFactor * wz2PaperCropBoundaryMassConstant *
                (topLevelConstant + 1) *
                ENNReal.ofReal (Real.sqrt rho)) := by rw [hCancel]
        _ =
            wz1PaperRefinementFraction delta 4 *
              ((2 * lossFactor * wz2PaperCropBoundaryMassConstant *
                (topLevelConstant + 1) *
                ENNReal.ofReal (Real.sqrt rho)) * logScale ^ 4) := by
          ring
    _ <
        wz1PaperRefinementFraction delta 4 *
          ((1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta sourceLoss) :=
      ENNReal.mul_lt_mul_right
        hFractionZero hFractionTop hScalarCore

end Kakeya.Assouad

end
