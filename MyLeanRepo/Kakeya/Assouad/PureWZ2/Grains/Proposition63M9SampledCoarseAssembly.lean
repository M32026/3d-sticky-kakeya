import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9AxialRootRealization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SampledCoarseFiberRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Exact-family sampled-coarse assembly for Proposition 6.3

This file records the first genuinely sampled coarse family in the M9 route.
It separates the still-quantitative fiber-regularization and sampled-density
receipts from the dependent family wiring.  In particular, the selected
coarse family, its sampled shading, its plane map, and the preliminary M8
output are never reselected.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

/-- The canonical finite nearby schedule for the first sampled-coarse
regularization.  Both constants and the scale count are fixed before the
runtime family is selected. -/
theorem Proposition63M9AlignedSampledStickyData.sampledFiberNearbySchedule
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff) :
    Nonempty (WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)) := by
  have rhoPos : 0 < aligned.aligned.requested.1 :=
    aligned.sticky.data.coarse_extremal.delta_pos
  have rhoOne : aligned.aligned.requested.1 ≤ 1 :=
    aligned.scale_le_outerScaleCeiling.trans cutoff.outerScaleCeiling_le_one
  have rhoFiber : aligned.aligned.requested.1 ≤ cutoff.sampledFiberScale :=
    aligned.scale_le_outerScaleCeiling.trans
      cutoff.outerScaleCeiling_le_sampledFiber
  have ambientThree : (3 : ENNReal) ≤
      Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss) := by
    have h := cutoff.sampledFiber_ambient rhoPos rhoFiber
    simpa only [cutoff.preliminaryStickyLoss_eq] using h
  apply paper_pure_finite_nearby_schedule
    (proposition63CanonicalNearbyLevelCount
      cutoff.sampledM8RootLosses.stickyLoss) rhoPos rhoOne
  · exact (by norm_num : (2 : ENNReal) < 3).trans_le ambientThree
  · simp [Kakeya.realRpowENN]
  · exact proposition63CanonicalNearbyLevelCount_reaches rhoPos rhoOne
      cutoff.sampledM8RootLosses.stickyLoss_pos
  · rw [← realRpowENN_add rhoPos]
    apply realRpowENN_antitone rhoPos rhoOne
    rw [cutoff.sampledM8RootLosses.selectedLoss_eq]
    linarith [cutoff.sampledM8RootLosses.stickyLoss_pos]
  · exact aligned.sticky.data.coarse_extremal.cwa_nearby_scales

/-- The first sampled-fiber normalization is the uniform terminal fiber-mass
floor after paying exactly the dyadic cardinality-band loss. -/
noncomputable def Proposition63M9AlignedSampledStickyData.sampledFiberNormalizationWeight
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff) : ENNReal :=
  (Kakeya.realRpowENN aligned.aligned.requested.1
      cutoff.sampledM8RootLosses.stickyLoss *
    (aligned.rich.terminal.fiberFloor : ENNReal) *
    Kakeya.realRpowENN aligned.rootDelta 2) /
      sampledCoarseFiberBandLoss aligned.sticky.data.selected.family.card

/-- A common upper bound for every terminal complete-fiber shaded mass. -/
noncomputable def Proposition63M9AlignedSampledStickyData.sampledFiberWeightUpper
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff) : ENNReal :=
  ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
      Kakeya.realRpowENN aligned.rootDelta 2) *
    (2 * (aligned.rich.terminal.fiberFloor : ENNReal))

/-- The real-logarithmic fiber-band loss is dominated by the standard
natural logarithmic cardinality term used by the nearby-scale machinery. -/
theorem sampledCoarseFiberBandLoss_le_natLog
    {cardinality : ℕ} (cardinalityPos : 0 < cardinality) :
    sampledCoarseFiberBandLoss cardinality ≤
      (Nat.log 2 (2 * cardinality) : ENNReal) + 1 := by
  unfold sampledCoarseFiberBandLoss
  simp only [div_one]
  rw [← ENNReal.ofReal_natCast (Nat.log 2 (2 * cardinality)),
    ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_add (Nat.cast_nonneg _) (by norm_num)]
  apply ENNReal.ofReal_mono
  have floorUpper : Real.logb 2 (cardinality : ℝ) <
      (⌊Real.logb 2 (cardinality : ℝ)⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have floorEq : (⌊Real.logb 2 (cardinality : ℝ)⌋₊ : ℝ) =
      (Nat.log 2 cardinality : ℝ) := by
    exact_mod_cast Real.natFloor_logb_natCast 2 cardinality
  rw [floorEq] at floorUpper
  have logDouble : Nat.log 2 (2 * cardinality) =
      Nat.log 2 cardinality + 1 := by
    rw [show 2 * cardinality = cardinality * 2 by omega,
      Nat.log_mul_base (by omega) cardinalityPos.ne']
  rw [logDouble]
  norm_num only [Nat.cast_add, Nat.cast_one]
  linarith

/-- Specialize the family-free sampled-fiber cutoff to the exact aligned rich
output.  Both runtime logarithms are first bounded by the root family's fixed
envelope; the terminal fiber cardinality and fine-scale tube volume then
cancel exactly between the canonical lower and upper weights. -/
theorem Proposition63M9AlignedSampledStickyData.sampledFiber_absorb
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff)
    (nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)) :
    let degreeConstant :=
      16 * (nearbySchedule.scaleCount : ENNReal) *
        (Nat.log 2 (2 * aligned.sticky.data.coarse.card) + 1 : ENNReal) ^
          nearbySchedule.scaleCount
    let regularizationLoss :=
      (8 : ENNReal) *
        (Nat.log 2 (2 * aligned.sticky.data.coarse.card) + 1 : ENNReal) ^
          (nearbySchedule.scaleCount + 1)
    max degreeConstant
        ((aligned.sampledFiberNormalizationWeight⁻¹ *
            (Kakeya.realRpowENN aligned.aligned.requested.1
              (-cutoff.sampledM8RootLosses.stickyLoss) *
              (regularizationLoss * aligned.sampledFiberWeightUpper) *
              degreeConstant)) *
          Kakeya.realRpowENN aligned.aligned.requested.1
            (-cutoff.sampledM8RootLosses.stickyLoss)) ≤
      Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss) := by
  let b := cutoff.sampledM8RootLosses.stickyLoss
  let N := proposition63CanonicalNearbyLevelCount b
  let delta := aligned.rootDelta
  let rho := aligned.aligned.requested.1
  let envelope := proposition63M9SampledFiberLogEnvelope delta
  let fineLog :=
    sampledCoarseFiberBandLoss aligned.sticky.data.selected.family.card
  let coarseLog : ENNReal :=
    Nat.log 2 (2 * aligned.sticky.data.coarse.card) + 1
  let geometry : ENNReal :=
    (55296 : ENNReal) * Kakeya.deltaTubeVolume 1
  let fiberFloor : ENNReal := aligned.rich.terminal.fiberFloor
  let deltaPower := Kakeya.realRpowENN delta 2
  let positivePower := Kakeya.realRpowENN rho b
  let ambientPower := Kakeya.realRpowENN rho (-b)
  let degreeConstant : ENNReal :=
    16 * (nearbySchedule.scaleCount : ENNReal) *
      coarseLog ^ nearbySchedule.scaleCount
  let regularizationLoss : ENNReal :=
    8 * coarseLog ^ (nearbySchedule.scaleCount + 1)
  have deltaPos : 0 < delta := aligned.rootDelta_pos
  have rootLeAbsorption : delta ≤ cutoff.sampledFiberAbsorption.delta₀ :=
    aligned.rootDelta_le_scaleCeiling.trans
      cutoff.scaleCeiling_le_outerScaleCeiling |>.trans
        cutoff.outerScaleCeiling_le_sampledFiberAbsorption
  have deltaOne : delta ≤ 1 :=
    rootLeAbsorption.trans cutoff.sampledFiberAbsorption.delta₀_le_one
  have deltaTiny : delta ≤ 1 / 100000 :=
    rootLeAbsorption.trans cutoff.sampledFiberAbsorption.delta₀_le_tiny
  have rhoPos : 0 < rho := aligned.sticky.data.coarse_extremal.delta_pos
  have rhoOne : rho ≤ 1 := aligned.sticky.data.coarse_extremal.delta_le_one
  have rhoUpper : rho ≤ Real.rpow delta b := by
    simpa only [rho, delta, b] using aligned.aligned.upper_window
  have selectedCardLeRoot : aligned.sticky.data.selected.family.card ≤
      aligned.normalization.croppedFamily.card := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      aligned.sticky.data.selected.embedding
      aligned.sticky.data.selected.embedding.injective
  have coarseCardLeSelected : aligned.sticky.data.coarse.card ≤
      aligned.sticky.data.selected.family.card := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective
      aligned.sticky.data.cover.toPaperTubeCover.parent
      aligned.sticky.data.cover.toPaperTubeCover.parent_surjective
  have rootLogBound :
      (Nat.log 2 (2 * aligned.normalization.croppedFamily.card) + 1 :
          ENNReal) ≤ proposition63OneScaleLogEnvelope delta := by
    exact proposition63_cropped_cardLog_le_oneScaleEnvelope
      aligned.normalization deltaTiny
  have baseEnvelope : proposition63OneScaleLogEnvelope delta ≤ envelope := by
    dsimp only [envelope]
    unfold proposition63OneScaleLogEnvelope
      proposition63M9SampledFiberLogEnvelope
    have logNonnegative : 0 ≤ 1 + Real.log delta⁻¹ := by
      have inverseOne : (1 : ℝ) ≤ delta⁻¹ :=
        (one_le_inv₀ deltaPos).mpr deltaOne
      linarith [Real.log_nonneg inverseOne]
    exact ENNReal.ofReal_mono <|
      mul_le_mul_of_nonneg_right (le_max_left _ _) logNonnegative
  have fineNatLog :
      (Nat.log 2 (2 * aligned.sticky.data.selected.family.card) :
          ENNReal) + 1 ≤
        (Nat.log 2 (2 * aligned.normalization.croppedFamily.card) :
          ENNReal) + 1 := by
    exact_mod_cast Nat.add_le_add_right
      (Nat.log_mono_right (Nat.mul_le_mul_left 2 selectedCardLeRoot)) 1
  have coarseNatLog :
      (Nat.log 2 (2 * aligned.sticky.data.coarse.card) : ENNReal) + 1 ≤
        (Nat.log 2 (2 * aligned.normalization.croppedFamily.card) :
          ENNReal) + 1 := by
    exact_mod_cast Nat.add_le_add_right
      (Nat.log_mono_right
        (Nat.mul_le_mul_left 2 (coarseCardLeSelected.trans selectedCardLeRoot))) 1
  have fineLogLe : fineLog ≤ envelope :=
    (sampledCoarseFiberBandLoss_le_natLog
      aligned.sticky.data.selected_nonempty).trans <|
        fineNatLog.trans <| rootLogBound.trans baseEnvelope
  have coarseLogLe : coarseLog ≤ envelope := by
    exact coarseNatLog.trans <| rootLogBound.trans baseEnvelope
  have envelopeOne : (1 : ENNReal) ≤ envelope := by
    dsimp only [envelope, proposition63M9SampledFiberLogEnvelope]
    have inverseOne : (1 : ℝ) ≤ delta⁻¹ :=
      (one_le_inv₀ deltaPos).mpr deltaOne
    have logNonnegative : 0 ≤ Real.log delta⁻¹ :=
      Real.log_nonneg inverseOne
    have coefficientOne : 1 ≤ proposition63M9SampledFiberLogCoefficient :=
      (show (1 : ℝ) ≤ proposition63OneScaleLogCoefficient by
        exact (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)).trans
          (le_max_left _ _)
    rw [show (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) by norm_num]
    apply ENNReal.ofReal_mono
    nlinarith [mul_nonneg (sub_nonneg.mpr coefficientOne)
      (show 0 ≤ 1 + Real.log delta⁻¹ by linarith)]
  have scaleCountLe : nearbySchedule.scaleCount ≤ N + 1 := by
    simpa only [N, b] using nearbySchedule.scaleCount_le
  have scaleCountCastLe : (nearbySchedule.scaleCount : ENNReal) ≤
      ((N + 1 : ℕ) : ENNReal) := by
    exact_mod_cast scaleCountLe
  have degreeBound : degreeConstant ≤
      (16 : ENNReal) * ((N + 1 : ℕ) : ENNReal) *
        envelope ^ (N + 1) := by
    calc
      degreeConstant ≤
          (16 : ENNReal) * ((N + 1 : ℕ) : ENNReal) *
            envelope ^ nearbySchedule.scaleCount := by
        dsimp only [degreeConstant]
        gcongr
      _ ≤ (16 : ENNReal) * ((N + 1 : ℕ) : ENNReal) *
          envelope ^ (N + 1) := by
        gcongr
  have degreeRoot := cutoff.sampledFiberAbsorption.degree_absorb
    deltaPos rootLeAbsorption
  have degreeToRho : Kakeya.realRpowENN delta
        (-(8 * b * b)) ≤ Kakeya.realRpowENN rho (-(8 * b)) := by
    have raw := pure_wz2_target_negative_power_lower deltaPos rhoPos rhoUpper
      (show 0 ≤ 8 * b by
        exact mul_nonneg (by norm_num)
          cutoff.sampledM8RootLosses.stickyLoss_pos.le)
    convert raw using 1 <;> ring
  have degreeFinal : degreeConstant ≤
      Kakeya.realRpowENN rho (-(8 * b)) :=
    degreeBound.trans <| degreeRoot.trans degreeToRho
  have fineLogZero : fineLog ≠ 0 := by
    dsimp only [fineLog]
    have positive : 0 < ENNReal.ofReal
        (Real.logb 2
          ((aligned.sticky.data.selected.family.card : ℝ) / 1) + 1) := by
      apply ENNReal.ofReal_pos.mpr
      have cardOne : (1 : ℝ) ≤
          (aligned.sticky.data.selected.family.card : ℝ) / 1 := by
        norm_num
        exact_mod_cast aligned.sticky.data.selected_nonempty
      have logNonnegative : 0 ≤ Real.logb 2
          ((aligned.sticky.data.selected.family.card : ℝ) / 1) :=
        Real.logb_nonneg (by norm_num) cardOne
      linarith
    exact positive.ne'
  have fineLogTop : fineLog ≠ ⊤ := by
    simp [fineLog, sampledCoarseFiberBandLoss]
  have positivePowerZero : positivePower ≠ 0 := by
    dsimp only [positivePower]
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos rhoPos b)).ne'
  have positivePowerTop : positivePower ≠ ⊤ := ENNReal.ofReal_ne_top
  have fiberFloorZero : fiberFloor ≠ 0 := by
    dsimp only [fiberFloor]
    exact_mod_cast aligned.rich.terminal.fiberFloor_pos.ne'
  have fiberFloorTop : fiberFloor ≠ ⊤ := by
    dsimp only [fiberFloor]
    exact ENNReal.natCast_ne_top _
  have deltaPowerZero : deltaPower ≠ 0 := by
    dsimp only [deltaPower]
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos deltaPos 2)).ne'
  have deltaPowerTop : deltaPower ≠ ⊤ := ENNReal.ofReal_ne_top
  have powerTriple : positivePower⁻¹ * ambientPower * ambientPower =
      Kakeya.realRpowENN rho (-(3 * b)) := by
    dsimp only [positivePower, ambientPower]
    rw [pure_wz2_realRpowENN_inv rhoPos]
    rw [← realRpowENN_add rhoPos, ← realRpowENN_add rhoPos]
    congr 1
    ring
  have massExact :
      aligned.sampledFiberNormalizationWeight⁻¹ *
          (ambientPower *
            (regularizationLoss * aligned.sampledFiberWeightUpper) *
            degreeConstant) * ambientPower =
        ((256 : ENNReal) * geometry *
            (nearbySchedule.scaleCount : ENNReal)) *
          fineLog * coarseLog ^ (2 * nearbySchedule.scaleCount + 1) *
          Kakeya.realRpowENN rho (-(3 * b)) := by
    unfold Proposition63M9AlignedSampledStickyData.sampledFiberNormalizationWeight
      Proposition63M9AlignedSampledStickyData.sampledFiberWeightUpper
    change ((positivePower * fiberFloor * deltaPower / fineLog)⁻¹ *
        (ambientPower *
          ((8 * coarseLog ^ (nearbySchedule.scaleCount + 1)) *
            ((geometry * deltaPower) * (2 * fiberFloor))) *
          ((16 * (nearbySchedule.scaleCount : ENNReal)) *
            coarseLog ^ nearbySchedule.scaleCount)) * ambientPower) = _
    rw [ENNReal.inv_div (Or.inl fineLogTop) (Or.inl fineLogZero)]
    rw [ENNReal.div_eq_inv_mul]
    have positiveFiberZero : positivePower * fiberFloor ≠ 0 :=
      mul_ne_zero positivePowerZero fiberFloorZero
    have positiveFiberTop : positivePower * fiberFloor ≠ ⊤ :=
      ENNReal.mul_ne_top positivePowerTop fiberFloorTop
    rw [ENNReal.mul_inv (Or.inl positiveFiberZero) (Or.inl positiveFiberTop)]
    rw [ENNReal.mul_inv (Or.inl positivePowerZero) (Or.inl positivePowerTop)]
    have coarsePowerCombine :
        coarseLog ^ (nearbySchedule.scaleCount + 1) *
            coarseLog ^ nearbySchedule.scaleCount =
          coarseLog ^ (2 * nearbySchedule.scaleCount + 1) := by
      rw [← pow_add]
      congr 1
      omega
    calc
      _ = (deltaPower⁻¹ * deltaPower) *
          (fiberFloor⁻¹ * fiberFloor) *
          (((256 : ENNReal) * geometry *
              (nearbySchedule.scaleCount : ENNReal)) *
            fineLog *
              (coarseLog ^ (nearbySchedule.scaleCount + 1) *
                coarseLog ^ nearbySchedule.scaleCount) *
            (positivePower⁻¹ * ambientPower * ambientPower)) := by ring
      _ = ((256 : ENNReal) * geometry *
            (nearbySchedule.scaleCount : ENNReal)) *
          fineLog *
            (coarseLog ^ (nearbySchedule.scaleCount + 1) *
              coarseLog ^ nearbySchedule.scaleCount) *
          Kakeya.realRpowENN rho (-(3 * b)) := by
        rw [ENNReal.inv_mul_cancel deltaPowerZero deltaPowerTop,
          ENNReal.inv_mul_cancel fiberFloorZero fiberFloorTop, powerTriple]
        simp
      _ = _ := by
        rw [coarsePowerCombine]
  have polylogBound :
      ((256 : ENNReal) * geometry *
          (nearbySchedule.scaleCount : ENNReal)) *
        fineLog * coarseLog ^ (2 * nearbySchedule.scaleCount + 1) ≤
      ((256 : ENNReal) * geometry * ((N + 1 : ℕ) : ENNReal)) *
        envelope ^ (2 * N + 4) := by
    calc
      _ ≤ ((256 : ENNReal) * geometry * ((N + 1 : ℕ) : ENNReal)) *
          envelope * envelope ^ (2 * nearbySchedule.scaleCount + 1) := by
        gcongr
      _ = ((256 : ENNReal) * geometry * ((N + 1 : ℕ) : ENNReal)) *
          envelope ^ (2 * nearbySchedule.scaleCount + 2) := by
        rw [show 2 * nearbySchedule.scaleCount + 2 =
          (2 * nearbySchedule.scaleCount + 1) + 1 by omega, pow_succ]
        ring
      _ ≤ ((256 : ENNReal) * geometry * ((N + 1 : ℕ) : ENNReal)) *
          envelope ^ (2 * N + 4) := by
        exact mul_le_mul_left'
          (pow_le_pow_right' envelopeOne (by omega)) _
  have massRoot := cutoff.sampledFiberAbsorption.mass_absorb
    deltaPos rootLeAbsorption
  have massToRho : Kakeya.realRpowENN delta
        (-(5 * b * b)) ≤ Kakeya.realRpowENN rho (-(5 * b)) := by
    have raw := pure_wz2_target_negative_power_lower deltaPos rhoPos rhoUpper
      (show 0 ≤ 5 * b by
        exact mul_nonneg (by norm_num)
          cutoff.sampledM8RootLosses.stickyLoss_pos.le)
    convert raw using 1 <;> ring
  have massFinal :
      aligned.sampledFiberNormalizationWeight⁻¹ *
          (ambientPower *
            (regularizationLoss * aligned.sampledFiberWeightUpper) *
            degreeConstant) * ambientPower ≤
        Kakeya.realRpowENN rho (-(8 * b)) := by
    rw [massExact]
    calc
      (((256 : ENNReal) * geometry *
            (nearbySchedule.scaleCount : ENNReal)) *
          fineLog * coarseLog ^ (2 * nearbySchedule.scaleCount + 1)) *
            Kakeya.realRpowENN rho (-(3 * b)) ≤
        (((256 : ENNReal) * geometry * ((N + 1 : ℕ) : ENNReal)) *
          envelope ^ (2 * N + 4)) *
            Kakeya.realRpowENN rho (-(3 * b)) := by gcongr
      _ ≤ Kakeya.realRpowENN delta (-(5 * b * b)) *
          Kakeya.realRpowENN rho (-(3 * b)) := by gcongr
      _ ≤ Kakeya.realRpowENN rho (-(5 * b)) *
          Kakeya.realRpowENN rho (-(3 * b)) := by gcongr
      _ = Kakeya.realRpowENN rho (-(8 * b)) := by
        rw [← realRpowENN_add rhoPos]
        congr 1
        ring
  dsimp only
  apply max_le
  · simpa only [degreeConstant, coarseLog, b,
      cutoff.sampledM8RootLosses.selectedLoss_eq] using degreeFinal
  · simpa only [degreeConstant, regularizationLoss, ambientPower,
      coarseLog, b, cutoff.sampledM8RootLosses.selectedLoss_eq] using massFinal

/-- The canonical sampled-fiber normalization is positive and finite. -/
theorem Proposition63M9AlignedSampledStickyData.sampledFiberNormalizationWeight_finite
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff) :
    aligned.sampledFiberNormalizationWeight ≠ 0 ∧
      aligned.sampledFiberNormalizationWeight ≠ ⊤ := by
  have bandPos : 0 <
      sampledCoarseFiberBandLoss
        aligned.sticky.data.selected.family.card := by
    apply ENNReal.ofReal_pos.mpr
    have cardOne : (1 : ℝ) ≤
        (aligned.sticky.data.selected.family.card : ℝ) / 1 := by
      norm_num
      exact_mod_cast aligned.sticky.data.selected_nonempty
    have logNonnegative : 0 ≤ Real.logb 2
        ((aligned.sticky.data.selected.family.card : ℝ) / 1) :=
      Real.logb_nonneg (by norm_num) cardOne
    change 0 < Real.logb 2
      ((aligned.sticky.data.selected.family.card : ℝ) / 1) + 1
    linarith
  have bandTop : sampledCoarseFiberBandLoss
      aligned.sticky.data.selected.family.card ≠ ⊤ := by
    simp [sampledCoarseFiberBandLoss]
  have rhoPowerPos : 0 < Kakeya.realRpowENN
      aligned.aligned.requested.1
      cutoff.sampledM8RootLosses.stickyLoss := by
    simp [Kakeya.realRpowENN,
      Real.rpow_pos_of_pos aligned.sticky.data.coarse_extremal.delta_pos]
  have fiberFloorPos : 0 <
      (aligned.rich.terminal.fiberFloor : ENNReal) := by
    exact_mod_cast aligned.rich.terminal.fiberFloor_pos
  have deltaPowerPos : 0 <
      Kakeya.realRpowENN aligned.rootDelta 2 := by
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos aligned.rootDelta_pos 2)
  constructor
  · have numeratorPos : 0 <
        Kakeya.realRpowENN aligned.aligned.requested.1
            cutoff.sampledM8RootLosses.stickyLoss *
          (aligned.rich.terminal.fiberFloor : ENNReal) *
          Kakeya.realRpowENN aligned.rootDelta 2 :=
      by
        have firstPos : 0 < Kakeya.realRpowENN
            aligned.aligned.requested.1
              cutoff.sampledM8RootLosses.stickyLoss *
            (aligned.rich.terminal.fiberFloor : ENNReal) :=
          ENNReal.mul_pos rhoPowerPos.ne' fiberFloorPos.ne'
        exact ENNReal.mul_pos firstPos.ne' deltaPowerPos.ne'
    exact (ENNReal.div_pos numeratorPos.ne' bandTop).ne'
  · apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _))
        ENNReal.ofReal_ne_top
    · exact bandPos.ne'

/-- Summing the terminal lower bound over the exact Section 6 fibers gives
the global normalization inequality required by the dyadic band selector. -/
theorem Proposition63M9AlignedSampledStickyData.sampledFiber_mass_lower
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff) :
    sampledCoarseFiberBandLoss aligned.sticky.data.selected.family.card *
        (aligned.sampledFiberNormalizationWeight *
          aligned.sticky.data.coarse.enncard) ≤
      aligned.sticky.data.refined.mass := by
  let bandLoss :=
    sampledCoarseFiberBandLoss aligned.sticky.data.selected.family.card
  let fiberFloorMass :=
    Kakeya.realRpowENN aligned.aligned.requested.1
        cutoff.sampledM8RootLosses.stickyLoss *
      (aligned.rich.terminal.fiberFloor : ENNReal) *
      Kakeya.realRpowENN aligned.rootDelta 2
  have bandLossPos : 0 < bandLoss := by
    apply ENNReal.ofReal_pos.mpr
    have cardOne : (1 : ℝ) ≤
        (aligned.sticky.data.selected.family.card : ℝ) / 1 := by
      norm_num
      exact_mod_cast aligned.sticky.data.selected_nonempty
    have logNonnegative : 0 ≤ Real.logb 2
        ((aligned.sticky.data.selected.family.card : ℝ) / 1) :=
      Real.logb_nonneg (by norm_num) cardOne
    change 0 < Real.logb 2
      ((aligned.sticky.data.selected.family.card : ℝ) / 1) + 1
    linarith
  have bandLossZero : bandLoss ≠ 0 := bandLossPos.ne'
  have bandLossTop : bandLoss ≠ ⊤ := by
    simp [bandLoss, sampledCoarseFiberBandLoss]
  have summedLower :
      fiberFloorMass * aligned.sticky.data.coarse.enncard ≤
        aligned.sticky.data.refined.mass := by
    rw [← aligned.sticky.data.cover.sum_fiberShadedMass
      aligned.sticky.data.refined]
    calc
      fiberFloorMass * aligned.sticky.data.coarse.enncard =
          ∑ _parent : Fin aligned.sticky.data.coarse.card,
            fiberFloorMass := by
        simp [Kakeya.Streamlined.TubeFamily.enncard, mul_comm]
      _ ≤ ∑ parent : Fin aligned.sticky.data.coarse.card,
          aligned.sticky.data.cover.toPaperTubeCover.fiberShadedMass
            aligned.sticky.data.refined parent := by
        apply Finset.sum_le_sum
        intro parent _
        simpa only [fiberFloorMass,
          Proposition63M9AlignedSampledStickyData.sticky,
          Proposition63RichTerminalStickyData.toReentrant] using
            aligned.rich.terminal_fiber_mass_lower parent
  calc
    sampledCoarseFiberBandLoss aligned.sticky.data.selected.family.card *
          (aligned.sampledFiberNormalizationWeight *
            aligned.sticky.data.coarse.enncard) =
        fiberFloorMass * aligned.sticky.data.coarse.enncard := by
      change bandLoss * ((fiberFloorMass / bandLoss) *
        aligned.sticky.data.coarse.enncard) = _
      rw [← mul_assoc, ENNReal.mul_div_cancel bandLossZero bandLossTop]
    _ ≤ aligned.sticky.data.refined.mass := summedLower

/-- The terminal fiber-cardinality band and the paper tube-volume estimate
give a finite uniform upper bound for the same exact fibers. -/
theorem Proposition63M9AlignedSampledStickyData.sampledFiber_weight_upper
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff) :
    aligned.sampledFiberWeightUpper ≠ ⊤ ∧
      ∀ parent,
        aligned.sticky.data.cover.toPaperTubeCover.fiberShadedMass
          aligned.sticky.data.refined parent ≤
            aligned.sampledFiberWeightUpper := by
  constructor
  · simp only [Proposition63M9AlignedSampledStickyData.sampledFiberWeightUpper]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num)
          Kakeya.Assouad.deltaTubeVolume_one_ne_top)
        (by simp [Kakeya.realRpowENN]))
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.natCast_ne_top _))
  · intro parent
    let fiber := wz2PaperFullFiberSubfamily
      aligned.sticky.data.selected.family aligned.sticky.data.coarse parent
    have rootSmall : aligned.rootDelta ≤ 1 / 24 :=
      aligned.rootDelta_le_scaleCeiling.trans
        cutoff.scaleCeiling_le_outerScaleCeiling |>.trans
          cutoff.outerScaleCeiling_le_lemma412 |>.trans
            cutoff.lemma412Cutoff.rho_small
    have massUpper := wz2_paper_shading_mass_upper
      aligned.rootDelta_pos rootSmall
      (aligned.sticky.data.cover.fine_line_class.subfamily fiber)
      (restrictPaperShading fiber aligned.sticky.data.refined)
    change (restrictPaperShading
      (wz2PaperFullFiberSubfamily aligned.sticky.data.selected.family
        aligned.sticky.data.coarse parent)
      aligned.sticky.data.refined).mass ≤ _ at massUpper
    have massEq : (restrictPaperShading
        (wz2PaperFullFiberSubfamily aligned.sticky.data.selected.family
          aligned.sticky.data.coarse parent)
        aligned.sticky.data.refined).mass =
        aligned.sticky.data.cover.toPaperTubeCover.fiberShadedMass
          aligned.sticky.data.refined parent := by
      simpa only [wz2PaperFullFiberSubfamily] using
        completeFiberShading_mass_eq_fiberShadedMass
          aligned.sticky.data.cover aligned.sticky.data.refined parent
    rw [massEq] at massUpper
    have fiberCard : fiber.family.enncard =
        wz2PaperFullFiberCount aligned.sticky.data.selected.family
          aligned.sticky.data.coarse parent := by
      rfl
    calc
      aligned.sticky.data.cover.toPaperTubeCover.fiberShadedMass
            aligned.sticky.data.refined parent ≤
          ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN aligned.rootDelta 2) *
            wz2PaperFullFiberCount aligned.sticky.data.selected.family
              aligned.sticky.data.coarse parent := by
        simpa only [fiberCard] using massUpper
      _ ≤ ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN aligned.rootDelta 2) *
            (2 * (aligned.rich.terminal.fiberFloor : ENNReal)) := by
        gcongr
        exact (aligned.rich.terminal.fiber_cardinality parent).2.le
      _ = aligned.sampledFiberWeightUpper := rfl

/-- Quantitative inputs for complete-fiber mass regularization on the exact
coarse family returned by the first aligned sticky call. -/
structure Proposition63M9SampledFiberRegularizationInputs
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff) where
  normalizationWeight : ENNReal
  weightUpper : ENNReal
  nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
    (fine := aligned.sticky.data.coarse)
    (Kakeya.realRpowENN aligned.aligned.requested.1
      (-cutoff.sampledM8RootLosses.stickyLoss))
    (Kakeya.realRpowENN aligned.aligned.requested.1
      (-cutoff.sampledM8RootLosses.selectedLoss))
    (proposition63CanonicalNearbyLevelCount
      cutoff.sampledM8RootLosses.stickyLoss)
  normalizationWeight_ne_zero : normalizationWeight ≠ 0
  normalizationWeight_ne_top : normalizationWeight ≠ ⊤
  weightUpper_ne_top : weightUpper ≠ ⊤
  mass_lower :
    ENNReal.ofReal
        (Real.logb 2
          ((aligned.sticky.data.selected.family.card : ℝ) / 1) + 1) *
      (normalizationWeight * aligned.sticky.data.coarse.enncard) ≤
        aligned.sticky.data.refined.mass
  weight_upper : ∀ parent,
    aligned.sticky.data.cover.toPaperTubeCover.fiberShadedMass
      aligned.sticky.data.refined parent ≤ weightUpper
  absorb :
    let degreeConstant :=
      16 * (nearbySchedule.scaleCount : ENNReal) *
        (Nat.log 2 (2 * aligned.sticky.data.coarse.card) + 1 : ENNReal) ^
          nearbySchedule.scaleCount
    let regularizationLoss :=
      (8 : ENNReal) *
        (Nat.log 2 (2 * aligned.sticky.data.coarse.card) + 1 : ENNReal) ^
          (nearbySchedule.scaleCount + 1)
    max degreeConstant
        ((normalizationWeight⁻¹ *
            (Kakeya.realRpowENN aligned.aligned.requested.1
              (-cutoff.sampledM8RootLosses.stickyLoss) *
              (regularizationLoss * weightUpper) * degreeConstant)) *
          Kakeya.realRpowENN aligned.aligned.requested.1
            (-cutoff.sampledM8RootLosses.stickyLoss)) ≤
      Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss)

/-- Package the canonical terminal-fiber weights once the separate scalar
absorption for the frozen nearby schedule has been discharged. -/
noncomputable def Proposition63M9AlignedSampledStickyData.sampledFiberRegularizationInputsOfAbsorb
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff)
    (nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss))
    (absorb :
      let degreeConstant :=
        16 * (nearbySchedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * aligned.sticky.data.coarse.card) + 1 : ENNReal) ^
            nearbySchedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * aligned.sticky.data.coarse.card) + 1 : ENNReal) ^
            (nearbySchedule.scaleCount + 1)
      max degreeConstant
          ((aligned.sampledFiberNormalizationWeight⁻¹ *
              (Kakeya.realRpowENN aligned.aligned.requested.1
                (-cutoff.sampledM8RootLosses.stickyLoss) *
                (regularizationLoss * aligned.sampledFiberWeightUpper) *
                degreeConstant)) *
            Kakeya.realRpowENN aligned.aligned.requested.1
              (-cutoff.sampledM8RootLosses.stickyLoss)) ≤
        Kakeya.realRpowENN aligned.aligned.requested.1
          (-cutoff.sampledM8RootLosses.selectedLoss)) :
    Proposition63M9SampledFiberRegularizationInputs aligned := by
  refine {
    normalizationWeight := aligned.sampledFiberNormalizationWeight
    weightUpper := aligned.sampledFiberWeightUpper
    nearbySchedule := nearbySchedule
    normalizationWeight_ne_zero :=
      aligned.sampledFiberNormalizationWeight_finite.1
    normalizationWeight_ne_top :=
      aligned.sampledFiberNormalizationWeight_finite.2
    weightUpper_ne_top := aligned.sampledFiber_weight_upper.1
    mass_lower := ?_
    weight_upper := aligned.sampledFiber_weight_upper.2
    absorb := absorb
  }
  simpa only [sampledCoarseFiberBandLoss] using
    aligned.sampledFiber_mass_lower

/-- All complete-fiber regularization inputs at the first sampled coarse
scale, with the scalar absorption discharged by the pre-runtime cutoff. -/
noncomputable def Proposition63M9AlignedSampledStickyData.sampledFiberRegularizationInputs
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff)
    (nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)) :
    Proposition63M9SampledFiberRegularizationInputs aligned :=
  aligned.sampledFiberRegularizationInputsOfAbsorb nearbySchedule
    (aligned.sampledFiber_absorb nearbySchedule)

/-- Execute the first quantitative selection without changing the sticky
family, shading, cover, or requested scale carried by `aligned`. -/
theorem Proposition63M9AlignedSampledStickyData.regularizeSampledFibers
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff)
    (inputs : Proposition63M9SampledFiberRegularizationInputs aligned) :
    Nonempty (PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := inputs.normalizationWeight)
      (weightUpper := inputs.weightUpper) aligned.sticky.data
      inputs.nearbySchedule) := by
  exact pure_wz2_sticky_coarse_fiber_mass_regularization
    aligned.sticky.data inputs.nearbySchedule
    inputs.normalizationWeight_ne_zero inputs.normalizationWeight_ne_top
    inputs.weightUpper_ne_top inputs.mass_lower inputs.weight_upper
    (by
      have rhoPos : 0 < aligned.aligned.requested.1 :=
        aligned.sticky.data.coarse_extremal.delta_pos
      have rhoOne : aligned.aligned.requested.1 ≤ 1 :=
        aligned.sticky.data.coarse_extremal.delta_le_one
      have selectedPos : 0 < cutoff.sampledM8RootLosses.selectedLoss := by
        rw [cutoff.sampledM8RootLosses.selectedLoss_eq]
        linarith [cutoff.sampledM8RootLosses.stickyLoss_pos]
      have hreal : 1 ≤ Real.rpow aligned.aligned.requested.1
          (-cutoff.sampledM8RootLosses.selectedLoss) := by
        have hzero : Real.rpow aligned.aligned.requested.1 0 ≤
            Real.rpow aligned.aligned.requested.1
              (-cutoff.sampledM8RootLosses.selectedLoss) :=
          Real.rpow_le_rpow_of_exponent_ge rhoPos rhoOne (by linarith)
        simpa using hzero
      exact ⟨by simpa [Kakeya.realRpowENN] using
        ENNReal.ofReal_mono hreal, by simp [Kakeya.realRpowENN]⟩)
    inputs.absorb

/-- Execute the first complete-fiber regularization using only the canonical
nearby schedule witness; all scalar and mass receipts are supplied by the
pre-runtime cutoff and the exact rich terminal. -/
theorem Proposition63M9AlignedSampledStickyData.regularizeCanonicalSampledFibers
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff)
    (nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)) :
    Nonempty (PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := aligned.sampledFiberNormalizationWeight)
      (weightUpper := aligned.sampledFiberWeightUpper) aligned.sticky.data
      nearbySchedule) := by
  exact aligned.regularizeSampledFibers
    (aligned.sampledFiberRegularizationInputs nearbySchedule)

/-- The single mass-loss factor from the original root shading to the exact
complete-fiber shading selected by the sampled coarse regularizer. -/
noncomputable def Proposition63M9AlignedSampledStickyData.sampledFineMassLoss
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff)
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)}
    (regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := aligned.sampledFiberNormalizationWeight)
      (weightUpper := aligned.sampledFiberWeightUpper) aligned.sticky.data
      nearbySchedule) : ENNReal :=
  (wz2PaperPureRefinementFraction aligned.rootDelta 61)⁻¹ *
    (sampledCoarseFiberBandLoss aligned.sticky.data.selected.family.card *
      regularized.regularized.regularizationLoss)

/-- The exact two-stage retention from the root shading to the synchronized
complete-fiber shading. -/
theorem Proposition63M9AlignedSampledStickyData.sampledFineMassLoss_spec
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff)
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)}
    (regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := aligned.sampledFiberNormalizationWeight)
      (weightUpper := aligned.sampledFiberWeightUpper) aligned.sticky.data
      nearbySchedule) :
    0 < aligned.sampledFineMassLoss regularized ∧
      aligned.sampledFineMassLoss regularized ≠ ⊤ ∧
      (aligned.sampledFineMassLoss regularized)⁻¹ *
          aligned.normalization.croppedRefined.mass ≤
        regularized.restriction.selectedFineShading.mass := by
  have deltaLtOne : aligned.rootDelta < 1 :=
    aligned.rootDelta_le_scaleCeiling.trans
      cutoff.scaleCeiling_le_outerScaleCeiling |>.trans_lt
        (cutoff.outerScaleCeiling_le_lemma412.trans
          cutoff.lemma412Cutoff.rho_small |>.trans_lt (by norm_num))
  have retained := regularized.source_mass_retained
    aligned.rootDelta_pos deltaLtOne
  have fractionZero : wz2PaperPureRefinementFraction aligned.rootDelta 61 ≠ 0 :=
    wz1PaperRefinementFraction_ne_zero aligned.rootDelta_pos deltaLtOne 61
  have fractionTop : wz2PaperPureRefinementFraction aligned.rootDelta 61 ≠ ⊤ :=
    wz1PaperRefinementFraction_ne_top aligned.rootDelta_pos deltaLtOne 61
  have bandPos : 0 < sampledCoarseFiberBandLoss
      aligned.sticky.data.selected.family.card := by
    apply ENNReal.ofReal_pos.mpr
    have cardOne : (1 : ℝ) ≤
        (aligned.sticky.data.selected.family.card : ℝ) / 1 := by
      norm_num
      exact_mod_cast aligned.sticky.data.selected_nonempty
    have logNonnegative : 0 ≤ Real.logb 2
        ((aligned.sticky.data.selected.family.card : ℝ) / 1) :=
      Real.logb_nonneg (by norm_num) cardOne
    linarith
  have bandTop : sampledCoarseFiberBandLoss
      aligned.sticky.data.selected.family.card ≠ ⊤ := by
    simp [sampledCoarseFiberBandLoss]
  have regularizationPos : 0 < regularized.regularized.regularizationLoss := by
    rw [regularized.regularized.regularizationLoss_eq]
    positivity
  have regularizationTop : regularized.regularized.regularizationLoss ≠ ⊤ := by
    rw [regularized.regularized.regularizationLoss_eq]
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top (by simp))
  constructor
  · unfold Proposition63M9AlignedSampledStickyData.sampledFineMassLoss
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr fractionTop)
      (mul_ne_zero bandPos.ne' regularizationPos.ne')
  constructor
  · unfold Proposition63M9AlignedSampledStickyData.sampledFineMassLoss
    exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr fractionZero)
      (ENNReal.mul_ne_top bandTop regularizationTop)
  · simpa only
      [sampledCoarseFiberBandLoss,
       Proposition63M9AlignedSampledStickyData.sticky,
       Proposition63RichTerminalStickyData.toReentrant,
       Proposition63M9AlignedSampledStickyData.sampledFineMassLoss]
      using retained

/-- The complete root-to-regularized mass loss is absorbed by one sticky-loss
power at the root scale. -/
theorem Proposition63M9AlignedSampledStickyData.sampledFineMassLoss_le_power
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff)
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)}
    (regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := aligned.sampledFiberNormalizationWeight)
      (weightUpper := aligned.sampledFiberWeightUpper) aligned.sticky.data
      nearbySchedule) :
    aligned.sampledFineMassLoss regularized ≤
      Kakeya.realRpowENN aligned.rootDelta
        (-cutoff.sampledM8RootLosses.stickyLoss) := by
  let b := cutoff.sampledM8RootLosses.stickyLoss
  let N := proposition63CanonicalNearbyLevelCount b
  let delta := aligned.rootDelta
  let envelope := proposition63M9SampledFiberLogEnvelope delta
  let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
  let fineLog :=
    sampledCoarseFiberBandLoss aligned.sticky.data.selected.family.card
  let coarseLog : ENNReal :=
    Nat.log 2 (2 * aligned.sticky.data.coarse.card) + 1
  have deltaPos : 0 < delta := aligned.rootDelta_pos
  have rootLeAbsorption : delta ≤ cutoff.sampledFiberAbsorption.delta₀ :=
    aligned.rootDelta_le_scaleCeiling.trans
      cutoff.scaleCeiling_le_outerScaleCeiling |>.trans
        cutoff.outerScaleCeiling_le_sampledFiberAbsorption
  have deltaOne : delta ≤ 1 :=
    rootLeAbsorption.trans cutoff.sampledFiberAbsorption.delta₀_le_one
  have deltaTiny : delta ≤ 1 / 100000 :=
    rootLeAbsorption.trans cutoff.sampledFiberAbsorption.delta₀_le_tiny
  have selectedCardLeRoot : aligned.sticky.data.selected.family.card ≤
      aligned.normalization.croppedFamily.card := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      aligned.sticky.data.selected.embedding
      aligned.sticky.data.selected.embedding.injective
  have coarseCardLeSelected : aligned.sticky.data.coarse.card ≤
      aligned.sticky.data.selected.family.card := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective
      aligned.sticky.data.cover.toPaperTubeCover.parent
      aligned.sticky.data.cover.toPaperTubeCover.parent_surjective
  have rootLogBound :
      (Nat.log 2 (2 * aligned.normalization.croppedFamily.card) + 1 :
          ENNReal) ≤ proposition63OneScaleLogEnvelope delta :=
    proposition63_cropped_cardLog_le_oneScaleEnvelope
      aligned.normalization deltaTiny
  have baseEnvelope : proposition63OneScaleLogEnvelope delta ≤ envelope := by
    dsimp only [envelope]
    unfold proposition63OneScaleLogEnvelope
      proposition63M9SampledFiberLogEnvelope
    have logNonnegative : 0 ≤ 1 + Real.log delta⁻¹ := by
      have inverseOne : (1 : ℝ) ≤ delta⁻¹ :=
        (one_le_inv₀ deltaPos).mpr deltaOne
      linarith [Real.log_nonneg inverseOne]
    exact ENNReal.ofReal_mono <|
      mul_le_mul_of_nonneg_right (le_max_left _ _) logNonnegative
  have fineNatLog :
      (Nat.log 2 (2 * aligned.sticky.data.selected.family.card) :
          ENNReal) + 1 ≤
        (Nat.log 2 (2 * aligned.normalization.croppedFamily.card) :
          ENNReal) + 1 := by
    exact_mod_cast Nat.add_le_add_right
      (Nat.log_mono_right (Nat.mul_le_mul_left 2 selectedCardLeRoot)) 1
  have coarseNatLog :
      (Nat.log 2 (2 * aligned.sticky.data.coarse.card) : ENNReal) + 1 ≤
        (Nat.log 2 (2 * aligned.normalization.croppedFamily.card) :
          ENNReal) + 1 := by
    exact_mod_cast Nat.add_le_add_right
      (Nat.log_mono_right
        (Nat.mul_le_mul_left 2 (coarseCardLeSelected.trans selectedCardLeRoot))) 1
  have fineLogLe : fineLog ≤ envelope :=
    (sampledCoarseFiberBandLoss_le_natLog
      aligned.sticky.data.selected_nonempty).trans <|
        fineNatLog.trans <| rootLogBound.trans baseEnvelope
  have coarseLogLe : coarseLog ≤ envelope :=
    coarseNatLog.trans <| rootLogBound.trans baseEnvelope
  have logTermLe : logTerm ≤ envelope := by
    apply (show logTerm ≤ proposition63OneScaleLogEnvelope delta by
      dsimp only [logTerm, proposition63OneScaleLogEnvelope]
      have inverseOne : (1 : ℝ) ≤ delta⁻¹ :=
        (one_le_inv₀ deltaPos).mpr deltaOne
      have logNonnegative : 0 ≤ Real.log delta⁻¹ :=
        Real.log_nonneg inverseOne
      have coefficientOne : 1 ≤ proposition63OneScaleLogCoefficient :=
        (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)
      apply ENNReal.ofReal_mono
      rw [show 1 / delta = delta⁻¹ by simp]
      nlinarith [mul_nonneg (sub_nonneg.mpr coefficientOne)
        (show 0 ≤ 1 + Real.log delta⁻¹ by linarith)]) |>.trans
      baseEnvelope
  have envelopeOne : (1 : ENNReal) ≤ envelope := by
    dsimp only [envelope, proposition63M9SampledFiberLogEnvelope]
    have inverseOne : (1 : ℝ) ≤ delta⁻¹ :=
      (one_le_inv₀ deltaPos).mpr deltaOne
    have logNonnegative : 0 ≤ Real.log delta⁻¹ := Real.log_nonneg inverseOne
    have coefficientOne : 1 ≤ proposition63M9SampledFiberLogCoefficient :=
      (show (1 : ℝ) ≤ proposition63OneScaleLogCoefficient by
        exact (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _)).trans
          (le_max_left _ _)
    rw [show (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) by norm_num]
    apply ENNReal.ofReal_mono
    nlinarith [mul_nonneg (sub_nonneg.mpr coefficientOne)
      (show 0 ≤ 1 + Real.log delta⁻¹ by linarith)]
  have scaleCountLe : nearbySchedule.scaleCount ≤ N + 1 := by
    simpa only [N, b] using nearbySchedule.scaleCount_le
  have regularizationBound : regularized.regularized.regularizationLoss ≤
      8 * envelope ^ (N + 2) := by
    rw [regularized.regularized.regularizationLoss_eq]
    calc
      (8 : ENNReal) * coarseLog ^ (nearbySchedule.scaleCount + 1) ≤
          8 * envelope ^ (nearbySchedule.scaleCount + 1) := by gcongr
      _ ≤ 8 * envelope ^ (N + 2) := by
        exact mul_le_mul_left'
          (pow_le_pow_right' envelopeOne (by omega)) 8
  have massLossEnvelope : aligned.sampledFineMassLoss regularized ≤
      8 * envelope ^ (N + 64) := by
    unfold Proposition63M9AlignedSampledStickyData.sampledFineMassLoss
    rw [wz2PaperPureRefinementFraction, ← ENNReal.inv_pow, inv_inv]
    change logTerm ^ 61 *
      (fineLog * regularized.regularized.regularizationLoss) ≤ _
    calc
      _ ≤ envelope ^ 61 * (envelope * (8 * envelope ^ (N + 2))) := by
        gcongr
      _ = 8 * envelope ^ (N + 64) := by
        rw [show N + 64 = 61 + (1 + (N + 2)) by omega]
        rw [pow_add, pow_add]
        ring
  exact massLossEnvelope.trans <| by
    simpa only [delta, b] using
      cutoff.sampledFiberAbsorption.source_mass_absorb
        deltaPos rootLeAbsorption

/-- The absorbed root-to-regularized mass loss fits exactly between the
root normalization loss and the first planiness loss. -/
theorem Proposition63M9AlignedSampledStickyData.sampledFineMassLoss_slack
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    (aligned : Proposition63M9AlignedSampledStickyData cutoff)
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)}
    (regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := aligned.sampledFiberNormalizationWeight)
      (weightUpper := aligned.sampledFiberWeightUpper) aligned.sticky.data
      nearbySchedule) :
    aligned.sampledFineMassLoss regularized *
        Kakeya.realRpowENN aligned.rootDelta
          cutoff.sampledM8RootLosses.planinessLoss ≤
      Kakeya.realRpowENN aligned.rootDelta aligned.rootNormalizationLoss := by
  have deltaOne : aligned.rootDelta ≤ 1 :=
    aligned.rootDelta_le_scaleCeiling.trans
      cutoff.scaleCeiling_le_outerScaleCeiling |>.trans
        cutoff.outerScaleCeiling_le_one
  calc
    aligned.sampledFineMassLoss regularized *
          Kakeya.realRpowENN aligned.rootDelta
            cutoff.sampledM8RootLosses.planinessLoss ≤
        Kakeya.realRpowENN aligned.rootDelta
            (-cutoff.sampledM8RootLosses.stickyLoss) *
          Kakeya.realRpowENN aligned.rootDelta
            cutoff.sampledM8RootLosses.planinessLoss := by
      gcongr
      exact aligned.sampledFineMassLoss_le_power regularized
    _ = Kakeya.realRpowENN aligned.rootDelta
          cutoff.sampledM8RootLosses.stickyLoss := by
      rw [← realRpowENN_add aligned.rootDelta_pos,
        cutoff.sampledM8RootLosses.planinessLoss_eq]
      congr 1
      ring
    _ ≤ Kakeya.realRpowENN aligned.rootDelta aligned.rootNormalizationLoss :=
      pure_wz2_rpowENN_antitone aligned.rootDelta_pos deltaOne
        aligned.rootNormalizationLoss_lt_sticky.le

/-- The two quantitative receipts which turn an exact sampled residue into
the cropped extremizer consumed by the preliminary M8 terminal. -/
structure Proposition63M9SampledExtremalityInputs
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {aligned : Proposition63M9AlignedSampledStickyData cutoff}
    {normalizationWeight weightUpper : ENNReal}
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)}
    (regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) aligned.sticky.data nearbySchedule)
    {coefficient : ℝ} {K : ℕ}
    (sampled : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      aligned.rootDelta_pos K) where
  fiberCap : ENNReal
  fiberCap_ne_top : fiberCap ≠ ⊤
  fiberCap_bound : ∀ parent point,
    (regularized.restriction.restrictedCover.toPaperTubeCover
        |>.fiberPointMultiplicity
          sampled.coarseMap.residue.selected parent point : ENNReal) ≤
      fiberCap
  bodyBudget : sampled.coarseMap.selectionLoss fiberCap *
    (Kakeya.realRpowENN aligned.aligned.requested.1
        cutoff.sampledM8RootLosses.selectedLoss *
      (wz1PaperBodyFamily
        regularized.restriction.selectedCoarse.family).mass) ≤
    regularized.restriction.selectedFineShading.mass

/-- Restore cropped extremality immediately after honest coarse sampling. -/
theorem RegularizedAlignedSampledPlaninessData.m9SampledExtremal
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {aligned : Proposition63M9AlignedSampledStickyData cutoff}
    {normalizationWeight weightUpper : ENNReal}
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)}
    (regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) aligned.sticky.data nearbySchedule)
    {coefficient : ℝ} {K : ℕ}
    (sampled : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      aligned.rootDelta_pos K)
    (inputs : Proposition63M9SampledExtremalityInputs regularized sampled) :
    WZ2PaperCroppedIsExtremal sigma
      cutoff.sampledM8RootLosses.selectedLoss
      regularized.restriction.selectedCoarse.family
      sampled.coarseMap.sampled.selected := by
  apply sampled.sampled_extremal regularized aligned.rootDelta_pos
    inputs.fiberCap inputs.fiberCap_ne_top inputs.fiberCap_bound
  · rw [cutoff.sampledM8RootLosses.selectedLoss_eq]
    linarith [cutoff.sampledM8RootLosses.stickyLoss_pos]
  · rw [cutoff.sampledM8RootLosses.selectedLoss_eq]
    linarith [cutoff.sampledM8RootLosses.stickyLoss_pos]
  · exact le_rfl
  · exact inputs.bodyBudget

/-- Exact-family assembly boundary for the first sampled coarse M8 run.  The
selected extremality is restored before M8 is invoked, and the strict axial
certificate comes from the same aligned rich output. -/
theorem RegularizedAlignedSampledPlaninessData.runPreliminaryM8OfReceipts
    {sigma outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    (cutoff : Proposition63M9PreNode3CutoffData hierarchy)
    {aligned : Proposition63M9AlignedSampledStickyData cutoff}
    {normalizationWeight weightUpper : ENNReal}
    {nearbySchedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := aligned.sticky.data.coarse)
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.stickyLoss))
      (Kakeya.realRpowENN aligned.aligned.requested.1
        (-cutoff.sampledM8RootLosses.selectedLoss))
      (proposition63CanonicalNearbyLevelCount
        cutoff.sampledM8RootLosses.stickyLoss)}
    (regularized : PureWZ2StickyCoarseFiberMassRegularizationData
      (normalizationWeight := normalizationWeight)
      (weightUpper := weightUpper) aligned.sticky.data nearbySchedule)
    {coefficient : ℝ} {K : ℕ}
    (sampled : RegularizedAlignedSampledPlaninessData
      (coefficient := coefficient)
      (regularizedCompleteFiberCompatibleCover regularized)
      aligned.rootDelta_pos K)
    (extremality : Proposition63M9SampledExtremalityInputs regularized sampled)
    (hnormalizationWeightZero : normalizationWeight ≠ 0)
    (hnormalizationWeightTop : normalizationWeight ≠ ⊤)
    (hextensionAbsorb :
      ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1) *
          (regularized.regularized.regularizationLoss * weightUpper) *
            Kakeya.realRpowENN aligned.aligned.requested.1
              cutoff.sampledM8RootLosses.currentLoss ≤
        normalizationWeight *
          Kakeya.realRpowENN aligned.aligned.requested.1
            cutoff.sampledM8RootLosses.selectedLoss)
    (hsigmaOne : sigma < 1) :
    ∃ reentry : Proposition63CurrentShadingReentryData
        (reentryLoss := cutoff.sampledM8RootLosses.reentryLoss)
        (cutoff.sampledM8RootLosses.ambientReentry aligned.sticky
          |>.toNormalizationData)
        sampled.ambientShading,
      ∃ rootMap : Proposition63RootPlaneMapData
          (densityLoss := cutoff.sampledM8.gridLoss)
          (incidence := aligned.aligned.requested.1) reentry 1,
        Nonempty (Proposition63PreliminaryLocalGrainData
          (localLoss := cutoff.initial.localLoss)
          (reentryLoss := cutoff.preliminaryProducerLoss)
          rootMap.root.normalization) := by
  exact sampled.runPreliminaryM8 cutoff regularized aligned.rootDelta_pos
    (sampled.m9SampledExtremal regularized extremality)
    hnormalizationWeightZero hnormalizationWeightTop hextensionAbsorb
    aligned.coarseAxialEighth aligned.scale_le_outerScaleCeiling hsigmaOne

end Kakeya.Assouad.PureWZ2

end
