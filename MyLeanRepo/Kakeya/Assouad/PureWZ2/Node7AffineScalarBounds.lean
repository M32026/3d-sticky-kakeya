import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7OrdinaryCWA
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryLogCoefficient
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalCleanupOutputPower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredStrictFiberBounds

/-!
# Runtime scalar bounds for the Node 7 affine normalization

This file records the direct numerical bounds needed after the synchronized
source selection.  The estimates use only fields already present in the
runtime Node 7 data.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set
open PureWZ2DirectCommonYSourceAssembly.TerminalGeometry
open PureWZ2DirectCommonYSourceAssembly.TerminalGeometry.PureWZ2ExternalWeightRegularizationData

namespace PureWZ2Node7AffineDiagonalPreparationData

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta}

/-- The selected-source top-level constant is already one of the losses
dominated by the first regularization output constant. -/
theorem selectedSourceTopLevelConstant_le_outputConstant
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.selectedSourceTopLevelConstant ≤
      data.sourceRegularization.regularized.outputConstant := by
  let C := commonSource.commonBand.band.sourceConstant
  let R := data.sourceRegularization.regularized.retentionConstant
  let W := pureWZ2PopularSourceNormalization
    (band := commonSource.commonBand.band)
  let G := data.sourceRegularization.regularized.degreeConstant
  have hsourceOne : (1 : ENNReal) ≤ C :=
    commonSource.commonBand.band.lemma31.data.cfg.extremal.cwa_nearby_scales.2.1.1
  have hlogOne : (1 : ENNReal) ≤
      (Nat.log 2
          (2 * commonSource.commonBand.band.lemma31.data.cfg.family.card) + 1 :
        ENNReal) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hscaleCountOne : (1 : ENNReal) ≤
      data.sourceRegularization.regularized.schedule.scaleCount := by
    exact_mod_cast
      data.sourceRegularization.regularized.schedule.scaleCount_pos
  have hdegreeOne : (1 : ENNReal) ≤
      data.sourceRegularization.regularized.degreeConstant := by
    rw [data.sourceRegularization.regularized.degreeConstant_eq]
    have hlogPow : (1 : ENNReal) ≤
        (Nat.log 2
          (2 * commonSource.commonBand.band.lemma31.data.cfg.family.card) + 1 :
          ENNReal) ^
            data.sourceRegularization.regularized.schedule.scaleCount :=
      one_le_pow₀ hlogOne
    calc
      (1 : ENNReal) ≤ 16 * 1 * 1 := by norm_num
      _ ≤ 16 *
          (data.sourceRegularization.regularized.schedule.scaleCount : ENNReal) *
          (Nat.log 2
              (2 * commonSource.commonBand.band.lemma31.data.cfg.family.card) + 1 :
            ENNReal) ^
              data.sourceRegularization.regularized.schedule.scaleCount := by
        gcongr
  have hsourceDegree : (1 : ENNReal) ≤ C * G := by
    simpa only [one_mul] using
      (mul_le_mul hsourceOne hdegreeOne (by norm_num) (by norm_num))
  have hratio : W⁻¹ * R * C ≤ W⁻¹ * (C * R * G) * C := by
    have hmul := mul_le_mul_left' hsourceDegree (W⁻¹ * R * C)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul
  unfold selectedSourceTopLevelConstant
  change W⁻¹ * R * C ≤ data.sourceRegularization.regularized.outputConstant
  apply hratio.trans
  rw [data.sourceRegularization.regularized.outputConstant_eq]
  unfold wz2PaperPureNearbyRestrictionConstant
  change W⁻¹ * (C * R * G) * C ≤
    max data.sourceRegularization.parameters.scheduleConstant
      (max C (max G (W⁻¹ * (C * R * G) * C)))
  exact (le_max_right G _).trans <|
    (le_max_right C _).trans (le_max_right _ _)

/-- Exact inverse-Jacobian factor of the Node 7 affine map. -/
theorem selectedAffineTopLevelLoss_inverse_det_eq
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    let scale := data.node7Scale.affineScale
    let equivalence := pureWZ2AffineDiagonalAffineEquivCentered
      scale.slopeData.frameSlope data.selected.center
      scale.slopeData.heightScale scale.slopeData.transverseScale 1
      (by linarith [scale.height_lower]) scale.transverse_pos.ne' one_ne_zero
    |LinearMap.det (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)| =
      scale.slopeData.rotatedSlopeScale⁻¹ := by
  dsimp only
  let scale := data.node7Scale.affineScale
  let equivalence := pureWZ2AffineDiagonalAffineEquivCentered
    scale.slopeData.frameSlope data.selected.center
    scale.slopeData.heightScale scale.slopeData.transverseScale 1
    (by linarith [scale.height_lower]) scale.transverse_pos.ne' one_ne_zero
  have hdet := pureWZ2AffineDiagonalAffineEquivCentered_abs_det_general
    scale.slopeData.frameSlope data.selected.center
    scale.slopeData.heightScale scale.slopeData.transverseScale 1
    (by linarith [scale.height_lower]) scale.transverse_pos (by norm_num)
  have hproduct : scale.slopeData.heightScale *
      scale.slopeData.transverseScale * 1 ^ 3 =
      scale.slopeData.rotatedSlopeScale := by
    rw [scale.slopeData.heightScale_eq,
      scale.slopeData.transverseScale_eq]
    field_simp [scale.slopeData.rotatedSlopeScale_pos.ne',
      scale.slopeData.normalizationConstant_pos.ne']
  have hdet' : |LinearMap.det
      (equivalence.linear : Point3 →ₗ[ℝ] Point3)| =
      scale.slopeData.rotatedSlopeScale := by
    simpa only [equivalence] using hdet.trans hproduct
  change |LinearMap.det (equivalence.symm.linear : Point3 →ₗ[ℝ] Point3)| = _
  have hsymm : equivalence.symm.linear = equivalence.linear.symm := rfl
  rw [hsymm, LinearEquiv.det_coe_symm, abs_inv, hdet']

/-- The affine carrier loss has four inverse powers of the normalized slope
scale, with an explicit absolute coefficient. -/
theorem selectedAffineTopLevelLoss_le_rotatedSlopeScale_inv_four
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.selectedAffineTopLevelLoss ≤
      (110592000000000 : ENNReal) *
        ENNReal.ofReal
          (data.affineScale.slopeData.rotatedSlopeScale⁻¹) ^ 4 := by
  let scale := data.node7Scale.affineScale
  let gamma := scale.slopeData.rotatedSlopeScale
  have hgamma : 0 < gamma := scale.slopeData.rotatedSlopeScale_pos
  have hheight : scale.slopeData.heightScale = 1000 / gamma := by
    rw [scale.slopeData.heightScale_eq, data.node7Scale.normalization_thousand]
  have hfactorNonneg : 0 ≤ 2 * (8 * scale.slopeData.heightScale) - 1 := by
    nlinarith [scale.height_lower]
  have hfactor :
      27 * (2 * (8 * scale.slopeData.heightScale) - 1) ^ 3 ≤
        110592000000000 * gamma⁻¹ ^ 3 := by
    rw [hheight] at hfactorNonneg ⊢
    have hgammaInv : 0 < gamma⁻¹ := inv_pos.mpr hgamma
    have hbasic : 2 * (8 * (1000 / gamma)) - 1 ≤
        16000 * gamma⁻¹ := by
      rw [div_eq_mul_inv]
      linarith
    nlinarith [pow_le_pow_left₀ hfactorNonneg hbasic 3]
  unfold selectedAffineTopLevelLoss
  dsimp only
  rw [data.selectedAffineTopLevelLoss_inverse_det_eq]
  calc
    ENNReal.ofReal
          (27 * (2 * (8 * scale.slopeData.heightScale) - 1) ^ 3) *
        ENNReal.ofReal gamma⁻¹ ≤
      ENNReal.ofReal (110592000000000 * gamma⁻¹ ^ 3) *
        ENNReal.ofReal gamma⁻¹ := by gcongr
    _ = (110592000000000 : ENNReal) *
        ENNReal.ofReal gamma⁻¹ ^ 4 := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (110592000000000 : ℝ))]
      rw [ENNReal.ofReal_pow (inv_nonneg.mpr hgamma.le)]
      norm_num
      ring

/-- Replacing the normalized slope scale by its structural lower bound costs
the factor `3^4`. -/
theorem selectedAffineTopLevelLoss_le_rho_inv_four
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.selectedAffineTopLevelLoss ≤
      (8957952000000000 : ENNReal) *
        ENNReal.ofReal data.affineScale.rho⁻¹ ^ 4 := by
  have hrho : 0 < data.affineScale.rho := data.affineScale.rho_pos
  have hgamma : 0 < data.affineScale.slopeData.rotatedSlopeScale :=
    data.affineScale.slopeData.rotatedSlopeScale_pos
  have hinv : data.affineScale.slopeData.rotatedSlopeScale⁻¹ ≤
      3 * data.affineScale.rho⁻¹ := by
    apply (inv_le_comm₀ hgamma (by positivity)).mpr
    have := data.affineScale.rotated_lower
    field_simp [hrho.ne'] at this ⊢
    nlinarith
  calc
    data.selectedAffineTopLevelLoss ≤
        (110592000000000 : ENNReal) *
          ENNReal.ofReal
            (data.affineScale.slopeData.rotatedSlopeScale⁻¹) ^ 4 :=
      data.selectedAffineTopLevelLoss_le_rotatedSlopeScale_inv_four
    _ ≤ (110592000000000 : ENNReal) *
        ENNReal.ofReal (3 * data.affineScale.rho⁻¹) ^ 4 := by gcongr
    _ = (8957952000000000 : ENNReal) *
        ENNReal.ofReal data.affineScale.rho⁻¹ ^ 4 := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
      ring

/-- The affine carrier loss costs at most four copies of the source power
used to define the Lemma-31 scale. -/
theorem selectedAffineTopLevelLoss_le_source_power
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource) :
    data.selectedAffineTopLevelLoss ≤
      (8957952000000000 : ENNReal) *
        Kakeya.realRpowENN delta (-4 * epsilon) := by
  have hrho := data.selectedAffineTopLevelLoss_le_rho_inv_four
  have hrhoEq : data.affineScale.rho = Real.rpow delta epsilon := by
    rw [data.affineScale.rho_eq, commonSource.commonBand.band_lemma31,
      commonSource.lemma31.data.rho_eq_power]
  rw [hrhoEq] at hrho
  have hdelta :=
    commonSource.commonBand.band.lemma31.data.cfg.extremal.delta_pos
  have hpow : ENNReal.ofReal (Real.rpow delta epsilon)⁻¹ ^ 4 =
      Kakeya.realRpowENN delta (-4 * epsilon) := by
    simp only [Kakeya.realRpowENN]
    let a := Real.rpow delta epsilon
    have hpos : 0 < a :=
      Real.rpow_pos_of_pos hdelta epsilon
    calc
      ENNReal.ofReal a⁻¹ ^ 4 = (ENNReal.ofReal a)⁻¹ ^ 4 := by
        rw [ENNReal.ofReal_inv_of_pos hpos]
      _ = (ENNReal.ofReal a ^ 4)⁻¹ := ENNReal.inv_pow.symm
      _ = (ENNReal.ofReal (a ^ 4))⁻¹ := by
        rw [ENNReal.ofReal_pow hpos.le]
      _ = ENNReal.ofReal ((a ^ 4)⁻¹) :=
        (ENNReal.ofReal_inv_of_pos (pow_pos hpos 4)).symm
      _ = ENNReal.ofReal (Real.rpow delta (-4 * epsilon)) := by
        congr 1
        dsimp only [a]
        rw [rpow_nat_pow hdelta epsilon 4]
        exact (Real.rpow_neg hdelta.le (4 * epsilon)).symm.trans <| by
          congr 1
          ring
  rwa [hpow] at hrho

/-- Exact small loss ledger for the selected-source CWA before logarithmic
absorption. -/
theorem selectedSource_loss_sum_le_three_epsilon
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)
    (hsigmaOne : sigma < 1) :
    commonSource.commonBand.band.massLoss +
        commonSource.commonBand.band.lemma31.data.targetLoss + epsilon ≤
      3 * epsilon := by
  rw [commonSource.commonBand.band_massLoss,
    commonSource.commonBand.common_loss,
    commonSource.commonBand.band_lemma31,
    commonSource.lemma31.data.targetLoss_eq,
    ← commonSource.lemma31.eta_eq,
    commonSource.lemma31_eta_eq]
  have hsigmaSq : sigma ^ 2 ≤ 1 := by
    have hsigmaPos := commonSource.lemma31.sigma_pos
    nlinarith [sq_nonneg (sigma - 1), sq_nonneg sigma]
  have hepsilon := commonSource.lemma31.epsilon_pos
  nlinarith [mul_le_mul_of_nonneg_left hsigmaSq hepsilon.le]

/-- Fixed coefficient for the first source regularization, with schedule
depth chosen solely from `sigma` and `epsilon`. -/
def node7SelectedSourceFixedCoefficient (sigma epsilon : ℝ) : ENNReal :=
  terminalCleanupOutputFixedCoefficient
    (pureWZ2FixedScheduleLevelCount (epsilon * sigma ^ 2 / 16000))

theorem node7SelectedSourceFixedCoefficient_ne_top
    (sigma epsilon : ℝ) :
    node7SelectedSourceFixedCoefficient sigma epsilon ≠ ⊤ := by
  exact terminalCleanupOutputFixedCoefficient_ne_top _

private theorem pureWZ2PopularSourceWeightRatioConstant_ne_top :
    pureWZ2PopularSourceWeightRatioConstant ≠ ⊤ := by
  have hfraction : 0 < pureWZ2PopularSourceFraction := by
    unfold pureWZ2PopularSourceFraction
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by norm_num)).ne' (by norm_num)
  have hpi : 0 < ENNReal.ofReal (Real.pi / 4) :=
    ENNReal.ofReal_pos.mpr (div_pos Real.pi_pos (by norm_num))
  unfold pureWZ2PopularSourceWeightRatioConstant
  exact ENNReal.mul_ne_top (by norm_num) <| ENNReal.inv_ne_top.mpr <|
    mul_ne_zero hfraction.ne' hpi.ne'

/-- The automatically regularized source CWA has only a fixed-depth
polylogarithmic cost beyond five copies of the tiny source exponent. -/
theorem exists_delta_for_selectedSourceTopLevelConstant
    (sigma epsilon : ℝ) (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon : 0 < epsilon) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {delta : ℝ}
        {commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta}
        (data : PureWZ2Node7AffineDiagonalPreparationData commonSource),
        0 < delta → delta ≤ delta₀ →
        data.selectedSourceTopLevelConstant ≤
          Kakeya.realRpowENN delta (-5 * epsilon) := by
  let targetLoss : ℝ := epsilon * sigma ^ 2 / 16000
  let levelCount := pureWZ2FixedScheduleLevelCount targetLoss
  let fixed := terminalCleanupOutputFixedCoefficient levelCount
  let absorptionCoefficient := fixed *
    (1 + pureWZ2PopularSourceWeightRatioConstant)
  have hboundaryNonneg :
      0 ≤ 2 * pureWZ2BoundedSourceCardLogConstant := by
    unfold pureWZ2BoundedSourceCardLogConstant
    apply mul_nonneg (by norm_num)
    exact le_max_of_le_right <| div_nonneg (by norm_num) <|
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  rcases exists_delta_boundary_log_square
      (2 * pureWZ2BoundedSourceCardLogConstant) hboundaryNonneg with
    ⟨boundaryScale, hboundaryScale, hboundaryScaleOne, hboundary⟩
  have hlogPower : 0 < 2 * (2 * levelCount + 3) := by omega
  rcases exists_delta_log_absorbed_ennreal absorptionCoefficient
      (ENNReal.mul_ne_top
        (terminalCleanupOutputFixedCoefficient_ne_top levelCount)
        (ENNReal.add_ne_top.mpr
          ⟨by norm_num, pureWZ2PopularSourceWeightRatioConstant_ne_top⟩))
      hepsilon hlogPower with
    ⟨logScale, hlogScale, hlogScaleOne, habsorb⟩
  refine ⟨min boundaryScale logScale, lt_min hboundaryScale hlogScale,
    (min_le_left _ _).trans hboundaryScaleOne, ?_⟩
  intro logExponent delta commonSource data hdelta hdeltaSmall
  have hdeltaBoundary : delta ≤ boundaryScale :=
    hdeltaSmall.trans (min_le_left _ _)
  have hdeltaLog : delta ≤ logScale :=
    hdeltaSmall.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 := hdeltaBoundary.trans hboundaryScaleOne
  have htargetLossEq :
      commonSource.commonBand.band.lemma31.data.targetLoss = targetLoss := by
    rw [commonSource.commonBand.band_lemma31,
      commonSource.lemma31.data.targetLoss_eq,
      ← commonSource.lemma31.eta_eq, commonSource.lemma31_eta_eq]
    dsimp only [targetLoss]
    ring
  have htargetLossLe : targetLoss ≤ epsilon := by
    dsimp only [targetLoss]
    have hsigmaSq : sigma ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg sigma, sq_nonneg (sigma - 1)]
    nlinarith [mul_le_mul_of_nonneg_left hsigmaSq hepsilon.le]
  let ambient := Kakeya.realRpowENN delta (-epsilon)
  let logBase := ENNReal.ofReal (Real.log (1 / delta))
  let logEnvelope := logBase ^ 2
  let ratio := (1 + pureWZ2PopularSourceWeightRatioConstant) *
    Kakeya.realRpowENN delta (-2 * epsilon)
  have hambientOne : (1 : ENNReal) ≤ ambient := by
    dsimp only [ambient]
    calc
      (1 : ENNReal) = Kakeya.realRpowENN delta 0 := by
        simp [Kakeya.realRpowENN]
      _ ≤ Kakeya.realRpowENN delta (-epsilon) :=
        realRpowENN_antitone (a := -epsilon) (b := 0)
          hdelta hdeltaOne (by linarith)
  have hsourceBound : commonSource.commonBand.band.sourceConstant ≤ ambient := by
    unfold PureWZ2Lemma32DerivativeBandAssembly.sourceConstant
    rw [htargetLossEq]
    exact realRpowENN_antitone hdelta hdeltaOne (by linarith)
  have hscheduleBound : data.sourceRegularization.parameters.scheduleConstant ≤
      ambient ^ 2 := by
    rw [data.sourceRegularization.parameters.scheduleConstant_eq]
    exact pow_le_pow_left' hsourceBound 2
  have hmassLoss : commonSource.commonBand.band.massLoss ≤ 2 * epsilon := by
    rw [commonSource.commonBand.band_massLoss,
      commonSource.commonBand.common_loss,
      commonSource.lemma31.data.targetLoss_eq,
      ← commonSource.lemma31.eta_eq, commonSource.lemma31_eta_eq]
    have hsigmaSq : sigma ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg sigma, sq_nonneg (sigma - 1)]
    nlinarith [mul_le_mul_of_nonneg_left hsigmaSq hepsilon.le]
  have hratioBound : pureWZ2PopularSourceWeightRatioConstant *
        Kakeya.realRpowENN delta (-commonSource.commonBand.band.massLoss) ≤
      ratio := by
    have hpower : Kakeya.realRpowENN delta
          (-commonSource.commonBand.band.massLoss) ≤
        Kakeya.realRpowENN delta (-2 * epsilon) :=
      realRpowENN_antitone hdelta hdeltaOne (by linarith)
    calc
      _ ≤ pureWZ2PopularSourceWeightRatioConstant *
          Kakeya.realRpowENN delta (-2 * epsilon) := by gcongr
      _ ≤ ratio := by
        dsimp only [ratio]
        exact mul_le_mul_right' (le_add_left le_rfl) _
  have hratioOne : (1 : ENNReal) ≤ ratio := by
    dsimp only [ratio]
    have hpower : (1 : ENNReal) ≤
        Kakeya.realRpowENN delta (-2 * epsilon) := by
      calc
        (1 : ENNReal) = Kakeya.realRpowENN delta 0 := by
          simp [Kakeya.realRpowENN]
        _ ≤ Kakeya.realRpowENN delta (-2 * epsilon) :=
          realRpowENN_antitone (a := -2 * epsilon) (b := 0)
            hdelta hdeltaOne (by linarith)
    have hraw : (1 : ENNReal) * 1 ≤
        (1 + pureWZ2PopularSourceWeightRatioConstant) *
          Kakeya.realRpowENN delta (-2 * epsilon) :=
      mul_le_mul (le_add_right le_rfl) hpower (by norm_num) (by norm_num)
    simpa only [one_mul] using hraw
  have hlogData := hboundary delta hdelta hdeltaBoundary
  have hlogIdentity : Real.log (1 / delta) = Real.log delta⁻¹ := by
    congr 1
    field_simp [hdelta.ne']
  have hlogOne : (1 : ENNReal) ≤ logEnvelope := by
    dsimp only [logEnvelope, logBase]
    apply one_le_pow₀
    exact ENNReal.one_le_ofReal.mpr (by
      rw [hlogIdentity]
      linarith [hlogData.1])
  have hrawAbsorption :
      ENNReal.ofReal
          ((2 * pureWZ2BoundedSourceCardLogConstant) *
            (1 + Real.log delta⁻¹)) ≤ logEnvelope := by
    dsimp only [logEnvelope, logBase]
    calc
      _ ≤ ENNReal.ofReal ((Real.log delta⁻¹) ^ 2) :=
        ENNReal.ofReal_mono hlogData.2
      _ = _ := by
        rw [hlogIdentity]
        exact ENNReal.ofReal_pow (by linarith [hlogData.1]) 2
  have houtput :=
    data.sourceRegularization.regularized.popular_outputConstant_le_logSquareEnvelope
      hsourceBound hscheduleBound hrawAbsorption hlogOne
  have hmaster :
      PureWZ2ExternalWeightRegularizationData.pureWZ2ExternalWeightRatioOutputEnvelope
          ambient (ambient ^ 2) ratio
          logEnvelope data.sourceRegularization.parameters.levelCount ≤
        fixed * ambient ^ 2 * ratio *
          logEnvelope ^ (2 * data.sourceRegularization.parameters.levelCount + 3) := by
    have h := externalWeightRatioOutputEnvelope_le_terminalCleanupMaster
          ambient ratio logEnvelope
            data.sourceRegularization.parameters.levelCount
          hambientOne hratioOne hlogOne
    have hlevelCountEq : data.sourceRegularization.parameters.levelCount =
        levelCount := by
      rw [data.sourceRegularization.levelCount_eq, htargetLossEq]
    simpa only [hlevelCountEq, fixed] using h
  have hlogAbsorb := habsorb delta hdelta hdeltaLog
  have hambientPow : ambient ^ 2 =
      Kakeya.realRpowENN delta (-2 * epsilon) := by
    dsimp only [ambient]
    rw [pow_two, ← realRpowENN_add hdelta]
    congr 1
    ring
  have houtput' : data.sourceRegularization.regularized.outputConstant ≤
      PureWZ2ExternalWeightRegularizationData.pureWZ2ExternalWeightRatioOutputEnvelope
        ambient (ambient ^ 2) ratio logEnvelope
          data.sourceRegularization.parameters.levelCount :=
    houtput.trans <| by
      unfold PureWZ2ExternalWeightRegularizationData.pureWZ2ExternalWeightRatioOutputEnvelope
      gcongr
  calc
    data.selectedSourceTopLevelConstant ≤
        data.sourceRegularization.regularized.outputConstant :=
      data.selectedSourceTopLevelConstant_le_outputConstant
    _ ≤ PureWZ2ExternalWeightRegularizationData.pureWZ2ExternalWeightRatioOutputEnvelope
          ambient (ambient ^ 2) ratio
          logEnvelope data.sourceRegularization.parameters.levelCount := houtput'
    _ ≤ fixed * ambient ^ 2 * ratio *
          logEnvelope ^ (2 * data.sourceRegularization.parameters.levelCount + 3) :=
      hmaster
    _ = absorptionCoefficient *
          Kakeya.realRpowENN delta (-4 * epsilon) *
          logEnvelope ^ (2 * data.sourceRegularization.parameters.levelCount + 3) := by
      rw [hambientPow]
      dsimp only [ratio, absorptionCoefficient]
      have hpower : Kakeya.realRpowENN delta (-2 * epsilon) *
          Kakeya.realRpowENN delta (-2 * epsilon) =
          Kakeya.realRpowENN delta (-4 * epsilon) := by
        calc
          _ = Kakeya.realRpowENN delta
              ((-2 * epsilon) + (-2 * epsilon)) :=
            (realRpowENN_add hdelta _ _).symm
          _ = _ := by congr 1 <;> ring
      rw [show fixed * Kakeya.realRpowENN delta (-2 * epsilon) *
            ((1 + pureWZ2PopularSourceWeightRatioConstant) *
              Kakeya.realRpowENN delta (-2 * epsilon)) =
          fixed * (1 + pureWZ2PopularSourceWeightRatioConstant) *
            (Kakeya.realRpowENN delta (-2 * epsilon) *
              Kakeya.realRpowENN delta (-2 * epsilon)) by ring, hpower]
    _ ≤ Kakeya.realRpowENN delta (-4 * epsilon) *
          Kakeya.realRpowENN delta (-epsilon) := by
      have hlogBaseLe : logBase ≤
          ENNReal.ofReal (1 + Real.log delta⁻¹) := by
        dsimp only [logBase]
        exact ENNReal.ofReal_mono (by linarith)
      have hlogEnvelopePower :
          logEnvelope ^
              (2 * data.sourceRegularization.parameters.levelCount + 3) ≤
            (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^
              (2 * (2 * levelCount + 3)) := by
        dsimp only [logEnvelope]
        rw [← pow_mul]
        rw [data.sourceRegularization.levelCount_eq, htargetLossEq]
        exact pow_le_pow_left' hlogBaseLe _
      have hinside : absorptionCoefficient *
            logEnvelope ^
              (2 * data.sourceRegularization.parameters.levelCount + 3) ≤
          Kakeya.realRpowENN delta (-epsilon) := by
        calc
          _ ≤ absorptionCoefficient *
              (ENNReal.ofReal (1 + Real.log delta⁻¹)) ^
                (2 * (2 * levelCount + 3)) :=
            mul_le_mul_left' hlogEnvelopePower _
          _ ≤ _ := hlogAbsorb
      calc
        _ = Kakeya.realRpowENN delta (-4 * epsilon) *
              (absorptionCoefficient * logEnvelope ^
                (2 * data.sourceRegularization.parameters.levelCount + 3)) := by ring
        _ ≤ Kakeya.realRpowENN delta (-4 * epsilon) *
              Kakeya.realRpowENN delta (-epsilon) := by gcongr
    _ = Kakeya.realRpowENN delta (-5 * epsilon) := by
      rw [← realRpowENN_add hdelta]
      congr 1
      ring

/-- The complete pre-cleanup CWA constant has only nine copies of the source
loss, up to one fixed affine coefficient. -/
theorem selectedTopLevelConstant_le_source_power
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (hsource : data.selectedSourceTopLevelConstant ≤
      Kakeya.realRpowENN delta (-5 * epsilon)) :
    data.selectedAffineTopLevelLoss * data.selectedSourceTopLevelConstant ≤
      (8957952000000000 : ENNReal) *
        Kakeya.realRpowENN delta (-9 * epsilon) := by
  have hdelta :=
    commonSource.commonBand.band.lemma31.data.cfg.extremal.delta_pos
  calc
    _ ≤ ((8957952000000000 : ENNReal) *
          Kakeya.realRpowENN delta (-4 * epsilon)) *
        Kakeya.realRpowENN delta (-5 * epsilon) := by
      exact mul_le_mul data.selectedAffineTopLevelLoss_le_source_power
        hsource bot_le bot_le
    _ = (8957952000000000 : ENNReal) *
        Kakeya.realRpowENN delta (-9 * epsilon) := by
      have hpow : Kakeya.realRpowENN delta (-4 * epsilon) *
          Kakeya.realRpowENN delta (-5 * epsilon) =
          Kakeya.realRpowENN delta (-9 * epsilon) := by
        rw [← realRpowENN_add hdelta]
        congr 1
        ring
      rw [show (8957952000000000 : ENNReal) *
            Kakeya.realRpowENN delta (-4 * epsilon) *
              Kakeya.realRpowENN delta (-5 * epsilon) =
          8957952000000000 *
            (Kakeya.realRpowENN delta (-4 * epsilon) *
              Kakeya.realRpowENN delta (-5 * epsilon)) by ring, hpow]

/-- The mass lower bound and the first selected-weight floor give the direct
runtime density of the final ordinary shading. -/
theorem ordinaryShading_dense_of_budget
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (density : ENNReal)
    (budget : density * Kakeya.deltaTubeVolume data.finalRadius ≤
      ENNReal.ofReal data.affineScale.slopeData.rotatedSlopeScale *
        data.sourceRegularization.regularized.selectedWeightLevel) :
    data.ordinaryShading.IsLambdaDense
      density := by
  rw [Kakeya.Streamlined.Shading.IsLambdaDense, tubeFamily_mass_eq_nominal]
  calc
    density * (data.ordinaryFamily.enncard *
        Kakeya.deltaTubeVolume data.finalRadius) =
      (density * Kakeya.deltaTubeVolume data.finalRadius) *
        data.ordinaryFamily.enncard := by ring
    _ ≤
      (ENNReal.ofReal data.affineScale.slopeData.rotatedSlopeScale *
          data.sourceRegularization.regularized.selectedWeightLevel) *
        data.ordinaryFamily.enncard := by gcongr
    _ ≤ data.ordinaryShading.mass := data.ordinaryShading_mass_lower

/-- A pre-runtime source cutoff which turns the explicit affine radius bound
into the clean power `delta^(1-2 epsilon)`. -/
theorem exists_delta_for_node7_finalRadius_power_upper
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hepsilonHalf : epsilon < 1 / 2) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        {commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta}
        (data : PureWZ2Node7AffineDiagonalPreparationData commonSource),
        0 < delta → delta ≤ delta₀ →
        data.finalRadius ≤ Real.rpow delta (1 - 2 * epsilon) := by
  rcases exists_delta_mul_rpow_le_rpow (60000 : ℝ) (by norm_num)
      (alpha := 1 - epsilon) (beta := 1 - 2 * epsilon)
      (by linarith) with
    ⟨delta₀, hdelta₀, hdelta₀One, habsorb⟩
  refine ⟨delta₀, hdelta₀, hdelta₀One, ?_⟩
  intro logExponent sigma delta commonSource data hdelta hdeltaSmall
  exact data.finalRadius_le_source_power.trans
    (habsorb delta hdelta hdeltaSmall)

/-- The absolute coefficient in the source-power density floor. -/
def node7DensityFloorCoefficient : ENNReal :=
  ((3 : ENNReal) * 50 * 4)⁻¹ *
    (pureWZ2PopularSourceFraction * ENNReal.ofReal (Real.pi / 4))

theorem node7DensityFloorCoefficient_pos :
    0 < node7DensityFloorCoefficient := by
  have hcube : 0 < ENNReal.ofReal (((1 / 8 : ℝ) ^ 3) / 27) :=
    ENNReal.ofReal_pos.mpr (by norm_num)
  have hhundred : 0 < (1 / 100 : ENNReal) := by norm_num
  have hfraction : 0 < pureWZ2PopularSourceFraction := by
    unfold pureWZ2PopularSourceFraction
    exact ENNReal.mul_pos hcube.ne' hhundred.ne'
  unfold node7DensityFloorCoefficient
  exact ENNReal.mul_pos
    (ENNReal.inv_pos.mpr (by norm_num : (3 * 50 * 4 : ENNReal) ≠ ⊤)).ne'
    (ENNReal.mul_pos hfraction.ne'
      (ENNReal.ofReal_pos.mpr
        (div_pos Real.pi_pos (by norm_num))).ne').ne'

theorem node7DensityFloorCoefficient_ne_top :
    node7DensityFloorCoefficient ≠ ⊤ := by
  unfold node7DensityFloorCoefficient pureWZ2PopularSourceFraction
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.mpr (by norm_num))
    (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
      ENNReal.ofReal_ne_top)

/-- The literal popular-box mass and the affine Jacobian retain the expected
`delta^(2+4 epsilon)` density numerator before target-radius comparison. -/
theorem node7_density_source_power_floor
    (data : PureWZ2Node7AffineDiagonalPreparationData commonSource)
    (hsigmaOne : sigma < 1) :
    node7DensityFloorCoefficient *
        Kakeya.realRpowENN delta (2 + 4 * epsilon) ≤
      ENNReal.ofReal data.affineScale.slopeData.rotatedSlopeScale *
        data.sourceRegularization.regularized.selectedWeightLevel := by
  have hdelta :=
    commonSource.commonBand.band.lemma31.data.cfg.extremal.delta_pos
  have hdeltaOne :=
    commonSource.commonBand.band.lemma31.data.cfg.extremal.delta_le_one
  have hrho : 0 < commonSource.lemma31.data.rho.1 :=
    hdelta.trans_le commonSource.lemma31.data.rho.2.1
  have hgamma := data.affineScale.rotated_lower
  have hweight :=
    data.sourceRegularization.regularized.popular_selectedWeightLevel_lower
      data.popular
  have hmassLoss := selectedSource_loss_sum_le_three_epsilon
    commonSource hsigmaOne
  have htargetLossNonneg :
      0 ≤ commonSource.commonBand.band.lemma31.data.targetLoss := by
    rw [commonSource.commonBand.band.lemma31.data.targetLoss_eq]
    positivity [commonSource.commonBand.band.lemma31.data.eta_pos]
  unfold pureWZ2PopularSourceNormalization at hweight
  have hgammaENN : ENNReal.ofReal (data.affineScale.rho / 3) ≤
      ENNReal.ofReal data.affineScale.slopeData.rotatedSlopeScale :=
    ENNReal.ofReal_mono hgamma
  have hpower : Kakeya.realRpowENN delta (2 + 4 * epsilon) ≤
      Kakeya.realRpowENN delta
        (commonSource.commonBand.band.massLoss + 2 + 2 * epsilon) :=
    realRpowENN_antitone hdelta hdeltaOne
      (by linarith [htargetLossNonneg])
  have hrhoENN : ENNReal.ofReal data.affineScale.rho =
      Kakeya.realRpowENN delta epsilon := by
    rw [data.affineScale.rho_eq, commonSource.commonBand.band_lemma31,
      commonSource.lemma31.data.rho_eq_power]
    rfl
  have hpowerSplit : Kakeya.realRpowENN delta
        (commonSource.commonBand.band.massLoss + 2 + 2 * epsilon) =
      Kakeya.realRpowENN delta
          (commonSource.commonBand.band.massLoss + 2) *
        Kakeya.realRpowENN delta epsilon *
        Kakeya.realRpowENN delta epsilon := by
    rw [← realRpowENN_add hdelta, ← realRpowENN_add hdelta]
    congr 1
    ring
  have hcoefficientIdentity :
      node7DensityFloorCoefficient *
          (Kakeya.realRpowENN delta
              (commonSource.commonBand.band.massLoss + 2) *
            Kakeya.realRpowENN delta epsilon *
            Kakeya.realRpowENN delta epsilon) =
        ENNReal.ofReal (data.affineScale.rho / 3) *
          (pureWZ2PopularSourceFraction * ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta
              (commonSource.commonBand.band.massLoss + 2) *
            ENNReal.ofReal data.affineScale.rho / 50 / 4) := by
    unfold node7DensityFloorCoefficient
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
      ENNReal.ofReal_ofNat, hrhoENN]
    simp only [ENNReal.div_eq_inv_mul]
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)),
      ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    ring
  calc
    node7DensityFloorCoefficient *
          Kakeya.realRpowENN delta (2 + 4 * epsilon) ≤
        node7DensityFloorCoefficient *
          Kakeya.realRpowENN delta
            (commonSource.commonBand.band.massLoss + 2 + 2 * epsilon) := by
      gcongr
    _ = ENNReal.ofReal (data.affineScale.rho / 3) *
          (pureWZ2PopularSourceFraction * ENNReal.ofReal (Real.pi / 4) *
            Kakeya.realRpowENN delta
              (commonSource.commonBand.band.massLoss + 2) *
            ENNReal.ofReal data.affineScale.rho / 50 / 4) := by
      rw [hpowerSplit]
      exact hcoefficientIdentity
    _ ≤ ENNReal.ofReal data.affineScale.slopeData.rotatedSlopeScale *
          (pureWZ2PopularSourceNormalization
            (band := commonSource.commonBand.band) / 4) := by
      unfold pureWZ2PopularSourceNormalization
      have hrhoEq : commonSource.commonBand.band.lemma31.data.rho.1 =
          data.affineScale.rho := data.affineScale.rho_eq.symm
      rw [hrhoEq]
      exact mul_le_mul_right' hgammaENN _
    _ ≤ ENNReal.ofReal data.affineScale.slopeData.rotatedSlopeScale *
          data.sourceRegularization.regularized.selectedWeightLevel := by
      exact mul_le_mul_left' hweight _

/-- Once the final radius has the clean source-power upper bound, one fixed
constant absorption turns the literal mass floor into the cleanup density. -/
theorem exists_delta_for_node7_density_budget
    (epsilon coreLoss : ℝ)
    (hepsilon : 0 < epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (hcore : 0 < coreLoss)
    (hgap : 2 + 4 * epsilon < (1 - 2 * epsilon) * (coreLoss + 2)) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {logExponent : ℕ} {sigma delta : ℝ}
        {commonSource : PureWZ2DirectCommonYSourceAssembly
          logExponent sigma epsilon delta}
        (data : PureWZ2Node7AffineDiagonalPreparationData commonSource),
        sigma < 1 → 0 < delta → delta ≤ delta₀ →
        Kakeya.realRpowENN data.finalRadius coreLoss *
            Kakeya.deltaTubeVolume data.finalRadius ≤
          ENNReal.ofReal data.affineScale.slopeData.rotatedSlopeScale *
            data.sourceRegularization.regularized.selectedWeightLevel := by
  rcases exists_delta_for_node7_finalRadius_power_upper epsilon hepsilon
      hepsilonHalf with ⟨radiusScale, hradiusScale, hradiusScaleOne, hradius⟩
  let coefficient : ENNReal := 12 * node7DensityFloorCoefficient⁻¹
  have hcoefficientTop : coefficient ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) <| ENNReal.inv_ne_top.mpr
      node7DensityFloorCoefficient_pos.ne'
  rcases exists_delta_constant_mul_power_le_power coefficient hcoefficientTop
      (2 + 4 * epsilon) ((1 - 2 * epsilon) * (coreLoss + 2)) hgap with
    ⟨absorbScale, habsorbScale, habsorbScaleOne, habsorb⟩
  refine ⟨min radiusScale absorbScale, lt_min hradiusScale habsorbScale,
    (min_le_left _ _).trans hradiusScaleOne, ?_⟩
  intro logExponent sigma delta commonSource data hsigmaOne hdelta hdeltaSmall
  have hdeltaRadius := hdeltaSmall.trans (min_le_left _ _)
  have hdeltaAbsorb := hdeltaSmall.trans (min_le_right _ _)
  have hfinalUpper := hradius data hdelta hdeltaRadius
  have hfinalOne : data.finalRadius ≤ 1 := hfinalUpper.trans <| by
    exact Real.rpow_le_one hdelta.le
      (hdeltaSmall.trans <| (min_le_left _ _).trans hradiusScaleOne)
      (by linarith)
  have hvolume := pure_wz2_deltaTubeVolume_upper_twelve
    data.finalRadius_pos hfinalOne
  have htargetPower := pure_wz2_target_power_upper hdelta
    data.finalRadius_pos.le hfinalUpper (by linarith : 0 ≤ coreLoss + 2)
  have habs := habsorb hdelta hdeltaAbsorb
  have hcoefficientZero : node7DensityFloorCoefficient ≠ 0 :=
    node7DensityFloorCoefficient_pos.ne'
  have hcoefficientFinite : node7DensityFloorCoefficient ≠ ⊤ :=
    node7DensityFloorCoefficient_ne_top
  have hsourceFloor := data.node7_density_source_power_floor hsigmaOne
  calc
    Kakeya.realRpowENN data.finalRadius coreLoss *
          Kakeya.deltaTubeVolume data.finalRadius ≤
        Kakeya.realRpowENN data.finalRadius coreLoss *
          (12 * Kakeya.realRpowENN data.finalRadius 2) := by gcongr
    _ = 12 * Kakeya.realRpowENN data.finalRadius (coreLoss + 2) := by
      have hpow : Kakeya.realRpowENN data.finalRadius coreLoss *
          Kakeya.realRpowENN data.finalRadius 2 =
          Kakeya.realRpowENN data.finalRadius (coreLoss + 2) :=
        (realRpowENN_add data.finalRadius_pos coreLoss 2).symm
      rw [show Kakeya.realRpowENN data.finalRadius coreLoss *
            (12 * Kakeya.realRpowENN data.finalRadius 2) =
          12 * (Kakeya.realRpowENN data.finalRadius coreLoss *
            Kakeya.realRpowENN data.finalRadius 2) by ring, hpow]
    _ ≤ 12 * Kakeya.realRpowENN delta
          ((1 - 2 * epsilon) * (coreLoss + 2)) := by gcongr
    _ ≤ node7DensityFloorCoefficient *
          Kakeya.realRpowENN delta (2 + 4 * epsilon) := by
      have hscaled := mul_le_mul_left' habs node7DensityFloorCoefficient
      have hcancel : node7DensityFloorCoefficient * coefficient = 12 := by
        dsimp only [coefficient]
        rw [show node7DensityFloorCoefficient *
              (12 * node7DensityFloorCoefficient⁻¹) =
            12 * (node7DensityFloorCoefficient *
              node7DensityFloorCoefficient⁻¹) by ring,
          ENNReal.mul_inv_cancel hcoefficientZero hcoefficientFinite, mul_one]
      rw [show node7DensityFloorCoefficient *
            (coefficient * Kakeya.realRpowENN delta
              ((1 - 2 * epsilon) * (coreLoss + 2))) =
          (node7DensityFloorCoefficient * coefficient) *
            Kakeya.realRpowENN delta
              ((1 - 2 * epsilon) * (coreLoss + 2)) by ring, hcancel] at hscaled
      exact hscaled
    _ ≤ _ := hsourceFloor

end PureWZ2Node7AffineDiagonalPreparationData

end Kakeya.Assouad

end
