import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallInnerScheduleRun
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallInnerLossSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairSqrtScale

/-!
# A genuine frozen-choice producer for the Proposition 6.3 four-call schedule

The data below is fixed once, before the finite iterator reveals any shading.
Its only index-dependent hypothesis is a uniform family of scalar receipts,
quantified over every scale package constructed from the frozen grid.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- A square-root package whose output loss is the output selected backwards
for this index, rather than the terminal loss stored in the interval grid. -/
structure Proposition63FourCallFrozenChoiceSqrtScalePackage
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    (outputLoss : ℝ)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index) where
  sqrtRequested : WZ2PaperRequestedScale scales.rhoHat.1
  hsqrtLower : Real.rpow scales.rhoHat.1 (1 - outputLoss) ≤ sqrtRequested.1
  hsqrtUpper : sqrtRequested.1 ≤ Real.rpow scales.rhoHat.1 outputLoss
  hsqrtOne : sqrtRequested.1 ≤ 1
  hsqrtSmall : sqrtRequested.1 ≤ 1 / 12
  hsqrtSq : sqrtRequested.1 ^ 2 ≤ 4 * scales.rhoHat.1
  sqrtScale_eq : sqrtRequested.1 = Real.sqrt scales.rhoHat.1

/-- Construct the index-output square-root package.  This is the dependent
version of `sqrtScalePackage`, needed because a backward schedule has a
different output loss at each ordered pair. -/
noncomputable def Proposition63FourCallOrderedPairIndexScales.choiceSqrtScalePackage
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (outputLoss : ℝ) (_houtputLoss : 0 < outputLoss)
    (houtputLossHalf : outputLoss ≤ 1 / 2)
    (hrhoSmall : scales.rhoHat.1 ≤ 1 / 144) :
    Proposition63FourCallFrozenChoiceSqrtScalePackage outputLoss scales := by
  have hrhoPos : 0 < scales.rhoHat.1 :=
    (grid.scale_pos _
      (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
        scales.logicalR_le_rhoHat
  have hrhoNonneg : 0 ≤ scales.rhoHat.1 := hrhoPos.le
  have hrhoOne : scales.rhoHat.1 ≤ 1 := scales.rhoHat.property.2
  have hrhoLeSqrt : scales.rhoHat.1 ≤ Real.sqrt scales.rhoHat.1 := by
    nlinarith [Real.sqrt_nonneg scales.rhoHat.1, Real.sq_sqrt hrhoNonneg]
  have hsqrtOne : Real.sqrt scales.rhoHat.1 ≤ 1 := by
    nlinarith [Real.sqrt_nonneg scales.rhoHat.1, Real.sq_sqrt hrhoNonneg]
  let sqrtRequested : WZ2PaperRequestedScale scales.rhoHat.1 :=
    ⟨Real.sqrt scales.rhoHat.1, hrhoLeSqrt, hsqrtOne⟩
  refine {
    sqrtRequested := sqrtRequested
    hsqrtLower := ?_
    hsqrtUpper := ?_
    hsqrtOne := sqrtRequested.property.2
    hsqrtSmall := ?_
    hsqrtSq := ?_
    sqrtScale_eq := rfl
  }
  · change Real.rpow scales.rhoHat.1 (1 - outputLoss) ≤
      Real.sqrt scales.rhoHat.1
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne (by linarith)
  · change Real.sqrt scales.rhoHat.1 ≤ Real.rpow scales.rhoHat.1 outputLoss
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne houtputLossHalf
  · change Real.sqrt scales.rhoHat.1 ≤ 1 / 12
    nlinarith [Real.sqrt_nonneg scales.rhoHat.1, Real.sq_sqrt hrhoNonneg]
  · change (Real.sqrt scales.rhoHat.1) ^ 2 ≤ 4 * scales.rhoHat.1
    rw [Real.sq_sqrt hrhoNonneg]
    linarith

/-- The common robust/target scale is forced by the interval-pair lower
window.  It is chosen as `rhoHat^(1-discreteLoss)`, not as an arbitrary
requested scale. -/
structure Proposition63FourCallFrozenRobustScalePackage
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {outputLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index) where
  requested : WZ2PaperRequestedScale scales.rhoHat.1
  secondLower : Real.rpow scales.rhoHat.1
    (1 - seed.schedule.secondOutputLoss) ≤ requested.1
  secondUpper : requested.1 ≤
    Real.rpow scales.rhoHat.1 seed.schedule.secondOutputLoss
  thirdLower : Real.rpow scales.rhoHat.1
    (1 - seed.schedule.thirdOutputLoss) ≤ requested.1
  thirdUpper : requested.1 ≤
    Real.rpow scales.rhoHat.1 seed.schedule.thirdOutputLoss
  scale_eq : requested.1 = Real.rpow scales.rhoHat.1 seed.robustExponent
  kappa : Real.rpow scales.rhoHat.1 seed.epsilon₃ ≤ requested.1
  targetTau : requested.1 ≤ 3 * scales.tau

/-- Construct the common robust/target scale from the genuine seed exponent
and the ordered-pair window. -/
noncomputable def Proposition63FourCallOrderedPairIndexScales.choiceRobustScalePackage
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {outputLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (hdiscreteHalf : discreteLoss < 1 / 2) :
    Proposition63FourCallFrozenRobustScalePackage seed scales := by
  have hrhoPos : 0 < scales.rhoHat.1 :=
    (grid.scale_pos _
      (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
        scales.logicalR_le_rhoHat
  have hrhoOne : scales.rhoHat.1 ≤ 1 := scales.rhoHat.property.2
  have hangularDiscrete :
      seed.paperAngularExponent ≤ discreteLoss / 4 := by
    rw [seed.paperAngularExponent_eq]
    exact min_le_left _ _
  have hdiscreteNonneg : 0 ≤ discreteLoss := by
    linarith [seed.paperAngularExponent_pos, hangularDiscrete]
  have hsecondComplement :
      seed.schedule.secondOutputLoss ≤ 1 - discreteLoss := by
    linarith [seed.secondOutputLoss_le_discrete]
  have hthirdComplement :
      seed.schedule.thirdOutputLoss ≤ 1 - discreteLoss := by
    linarith [seed.thirdOutputLoss_le_discrete]
  let requested : WZ2PaperRequestedScale scales.rhoHat.1 := {
    val := Real.rpow scales.rhoHat.1 seed.robustExponent
    property := by
      constructor
      · calc
          scales.rhoHat.1 = Real.rpow scales.rhoHat.1 1 :=
            (Real.rpow_one scales.rhoHat.1).symm
          _ ≤ Real.rpow scales.rhoHat.1 seed.robustExponent :=
            Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne
              seed.robustExponent_le_one
      · exact Real.rpow_le_one hrhoPos.le hrhoOne seed.robustExponent_pos.le
  }
  refine {
    requested := requested
    secondLower := ?_
    secondUpper := ?_
    thirdLower := ?_
    thirdUpper := ?_
    scale_eq := rfl
    kappa := ?_
    targetTau := ?_
  }
  · change Real.rpow scales.rhoHat.1
      (1 - seed.schedule.secondOutputLoss) ≤
        Real.rpow scales.rhoHat.1 seed.robustExponent
    exact Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne (by
      rw [seed.robustExponent_eq]
      linarith [seed.secondOutputLoss_le_discrete])
  · change Real.rpow scales.rhoHat.1 seed.robustExponent ≤
      Real.rpow scales.rhoHat.1 seed.schedule.secondOutputLoss
    exact Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne (by
      rw [seed.robustExponent_eq]
      exact hsecondComplement)
  · change Real.rpow scales.rhoHat.1
      (1 - seed.schedule.thirdOutputLoss) ≤
        Real.rpow scales.rhoHat.1 seed.robustExponent
    exact Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne (by
      rw [seed.robustExponent_eq]
      linarith [seed.thirdOutputLoss_le_discrete])
  · change Real.rpow scales.rhoHat.1 seed.robustExponent ≤
      Real.rpow scales.rhoHat.1 seed.schedule.thirdOutputLoss
    exact Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne (by
      rw [seed.robustExponent_eq]
      exact hthirdComplement)
  · change Real.rpow scales.rhoHat.1 seed.epsilon₃ ≤
      Real.rpow scales.rhoHat.1 seed.robustExponent
    exact Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne
      seed.robustExponent_le_epsilon₃
  · change Real.rpow scales.rhoHat.1 seed.robustExponent ≤ 3 * scales.tau
    rw [seed.robustExponent_eq]
    have hlogicalPos : 0 <
        (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) :=
      grid.scale_pos _
        (scales.first_lt_second.le.trans scales.second_le_gridN)
    have hpowMono : Real.rpow scales.rhoHat.1 (1 - discreteLoss) ≤
        Real.rpow (2 *
          (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ))
          (1 - discreteLoss) :=
      Real.rpow_le_rpow hrhoPos.le scales.rhoHat_le_two_logicalR
        (by linarith [hdiscreteHalf])
    have hmulPow : Real.rpow (2 *
        (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ))
        (1 - discreteLoss) =
        Real.rpow 2 (1 - discreteLoss) *
          Real.rpow
            (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
            (1 - discreteLoss) :=
      Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num) hlogicalPos.le
    rw [hmulPow] at hpowMono
    have htwoPow : Real.rpow 2 (1 - discreteLoss) ≤ 2 := by
      calc
        Real.rpow 2 (1 - discreteLoss) ≤ Real.rpow 2 1 :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by linarith)
        _ = 2 := by simp
    calc
      Real.rpow scales.rhoHat.1 (1 - discreteLoss) ≤
          Real.rpow 2 (1 - discreteLoss) *
            Real.rpow
              (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
              (1 - discreteLoss) := hpowMono
      _ ≤ 2 * Real.rpow
          (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
          (1 - discreteLoss) := by
            exact mul_le_mul_of_nonneg_right htwoPow
              (Real.rpow_nonneg hlogicalPos.le _)
      _ ≤ 2 * scales.tau := by gcongr; exact scales.pair_lower_window
      _ ≤ 3 * scales.tau := by linarith [scales.tau_pos]

/-- The paper-faithful robust and interval-target requested scales.  The
robust scale uses the small angular exponent needed by the first cross call,
whereas the third call is run at the actual interval scale.  No kappa lower
bound is asserted for the target scale. -/
structure Proposition63FourCallPaperScalePackage
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {outputLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index) where
  robustRequested : WZ2PaperRequestedScale scales.rhoHat.1
  targetRequested : WZ2PaperRequestedScale scales.rhoHat.1
  robustLower : Real.rpow scales.rhoHat.1
    (1 - seed.schedule.secondOutputLoss) ≤ robustRequested.1
  robustUpper : robustRequested.1 ≤
    Real.rpow scales.rhoHat.1 seed.schedule.secondOutputLoss
  targetLower : Real.rpow scales.rhoHat.1
    (1 - seed.schedule.thirdOutputLoss) ≤ targetRequested.1
  targetUpper : targetRequested.1 ≤
    Real.rpow scales.rhoHat.1 seed.schedule.thirdOutputLoss
  robustScale_eq : robustRequested.1 =
    Real.rpow scales.rhoHat.1 seed.paperAngularExponent
  targetScale_eq : targetRequested.1 = max scales.tau
    (Real.rpow scales.rhoHat.1 (1 - seed.schedule.thirdOutputLoss))
  robustKappa : Real.rpow scales.rhoHat.1 seed.paperAngularExponent ≤
    robustRequested.1
  targetTau : targetRequested.1 ≤ 3 * scales.tau
  robustPos : 0 < robustRequested.1
  targetPos : 0 < targetRequested.1
  robustLeOne : robustRequested.1 ≤ 1
  targetLeOne : targetRequested.1 ≤ 1

/-- Construct the two paper scales without identifying their exponents. -/
noncomputable def Proposition63FourCallOrderedPairIndexScales.choicePaperScalePackage
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {outputLoss : ℝ}
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (hdiscreteHalf : discreteLoss < 1 / 2) :
    Proposition63FourCallPaperScalePackage seed scales := by
  have hrhoPos : 0 < scales.rhoHat.1 :=
    (grid.scale_pos _
      (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
        scales.logicalR_le_rhoHat
  have hrhoOne : scales.rhoHat.1 ≤ 1 := scales.rhoHat.property.2
  have hangularDiscrete :
      seed.paperAngularExponent ≤ discreteLoss / 4 := by
    rw [seed.paperAngularExponent_eq]
    exact min_le_left _ _
  have hdiscretePos : 0 < discreteLoss := by
    linarith [seed.paperAngularExponent_pos, hangularDiscrete]
  have hsecondOutputLtHalf :
      seed.schedule.secondOutputLoss < discreteLoss / 2 := by
    linarith [seed.secondOutputLoss_lt_paperAngular, hangularDiscrete]
  have hthirdComplement :
      seed.schedule.thirdOutputLoss ≤ 1 - discreteLoss := by
    linarith [seed.thirdOutputLoss_le_discrete]
  let robustRequested : WZ2PaperRequestedScale scales.rhoHat.1 := {
    val := Real.rpow scales.rhoHat.1 seed.paperAngularExponent
    property := by
      constructor
      · calc
          scales.rhoHat.1 = Real.rpow scales.rhoHat.1 1 :=
            (Real.rpow_one scales.rhoHat.1).symm
          _ ≤ Real.rpow scales.rhoHat.1 seed.paperAngularExponent :=
            Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne
              seed.paperAngularExponent_le_one
      · exact Real.rpow_le_one hrhoPos.le hrhoOne
          seed.paperAngularExponent_pos.le
  }
  have targetPowerLeOne :
      Real.rpow scales.rhoHat.1 (1 - seed.schedule.thirdOutputLoss) ≤ 1 :=
    Real.rpow_le_one hrhoPos.le hrhoOne (by
      linarith [seed.thirdOutputLoss_le_discrete, hdiscreteHalf])
  let targetRequested : WZ2PaperRequestedScale scales.rhoHat.1 := {
    val := max scales.tau
      (Real.rpow scales.rhoHat.1 (1 - seed.schedule.thirdOutputLoss))
    property := by
      constructor
      · exact scales.rhoHat_le_tau.trans (le_max_left _ _)
      · exact max_le scales.tau_le_one targetPowerLeOne
  }
  refine {
    robustRequested := robustRequested
    targetRequested := targetRequested
    robustLower := ?_
    robustUpper := ?_
    targetLower := ?_
    targetUpper := ?_
    robustScale_eq := rfl
    targetScale_eq := rfl
    robustKappa := ?_
    targetTau := ?_
    robustPos := Real.rpow_pos_of_pos hrhoPos _
    targetPos := scales.tau_pos.trans_le (le_max_left _ _)
    robustLeOne := robustRequested.property.2
    targetLeOne := targetRequested.property.2
  }
  · change Real.rpow scales.rhoHat.1
      (1 - seed.schedule.secondOutputLoss) ≤
        Real.rpow scales.rhoHat.1 seed.paperAngularExponent
    exact Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne (by
      linarith [hangularDiscrete, hsecondOutputLtHalf, hdiscreteHalf])
  · change Real.rpow scales.rhoHat.1 seed.paperAngularExponent ≤
      Real.rpow scales.rhoHat.1 seed.schedule.secondOutputLoss
    exact Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne
      seed.secondOutputLoss_lt_paperAngular.le
  · exact le_max_right _ _
  · calc
      max scales.tau
          (Real.rpow scales.rhoHat.1
            (1 - seed.schedule.thirdOutputLoss)) ≤
          Real.rpow scales.rhoHat.1 seed.schedule.thirdOutputLoss := by
        apply max_le
        · calc
            scales.tau ≤ Real.sqrt scales.rhoHat.1 :=
              scales.tau_le_sqrt_logicalR.trans
                (Real.sqrt_le_sqrt scales.logicalR_le_rhoHat)
            _ = Real.rpow scales.rhoHat.1 (1 / 2 : ℝ) :=
              Real.sqrt_eq_rpow _
            _ ≤ Real.rpow scales.rhoHat.1
                  seed.schedule.thirdOutputLoss :=
              Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne (by
                linarith [seed.thirdOutputLoss_le_discrete, hdiscreteHalf])
        · exact Real.rpow_le_rpow_of_exponent_ge hrhoPos hrhoOne (by
            linarith [seed.thirdOutputLoss_le_discrete, hdiscreteHalf])
      _ = Real.rpow scales.rhoHat.1 seed.schedule.thirdOutputLoss := rfl
  · exact le_rfl
  · apply max_le
    · linarith [scales.tau_pos]
    · have hlogicalPos : 0 <
          (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ) :=
        grid.scale_pos _
          (scales.first_lt_second.le.trans scales.second_le_gridN)
      have hpowMono : Real.rpow scales.rhoHat.1
          (1 - seed.schedule.thirdOutputLoss) ≤
          Real.rpow (2 *
            (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ))
            (1 - seed.schedule.thirdOutputLoss) :=
        Real.rpow_le_rpow hrhoPos.le scales.rhoHat_le_two_logicalR (by
          linarith [seed.thirdOutputLoss_le_discrete, hdiscreteHalf])
      have hmulPow : Real.rpow (2 *
          (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ))
          (1 - seed.schedule.thirdOutputLoss) =
          Real.rpow 2 (1 - seed.schedule.thirdOutputLoss) *
            Real.rpow
              (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
              (1 - seed.schedule.thirdOutputLoss) :=
        Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num) hlogicalPos.le
      rw [hmulPow] at hpowMono
      have htwoPow : Real.rpow 2
          (1 - seed.schedule.thirdOutputLoss) ≤ 2 := by
        calc
          Real.rpow 2 (1 - seed.schedule.thirdOutputLoss) ≤ Real.rpow 2 1 :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
              linarith [seed.schedule.thirdOutputLoss_pos])
          _ = 2 := by simp
      have hpairThird : Real.rpow
          (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
          (1 - seed.schedule.thirdOutputLoss) ≤ scales.tau :=
        by
          rw [scales.tau_eq]
          exact (grid.pair_window seed.schedule.thirdOutputLoss
            seed.schedule.thirdOutputLoss_pos seed.thirdOutputLoss_le_discrete
            index scales.index_lt).1
      calc
        Real.rpow scales.rhoHat.1
            (1 - seed.schedule.thirdOutputLoss) ≤
            Real.rpow 2 (1 - seed.schedule.thirdOutputLoss) *
              Real.rpow
                (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
                (1 - seed.schedule.thirdOutputLoss) := hpowMono
        _ ≤ 2 * Real.rpow
            (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ)
            (1 - seed.schedule.thirdOutputLoss) := by
              exact mul_le_mul_of_nonneg_right htwoPow
                (Real.rpow_nonneg hlogicalPos.le _)
        _ ≤ 2 * scales.tau := by gcongr
        _ ≤ 3 * scales.tau := by linarith [scales.tau_pos]

/-- The scalar receipts not already supplied by the grid, scale-smallness, and
square-root-scale constructors.  This contains no shading, mass ledger, or
geometric object selected during the iteration. -/
structure Proposition63FourCallFrozenScalarReceiptsAt
    {delta sigma inputLoss normalizationLoss rootDensityLoss outputLoss
      rhoDensityLoss firstStageDensityLoss secondReentryDensityLoss rhoWeightLoss
      firstStageWeightLoss
      currentWeightLoss outerExtremalLoss robustExponent epsilon₁ epsilon₃
      parentLoss firstLoss nextWeightLoss secondLoss middleLoss finalLoss
      incidence discreteLoss intervalLoss gridOutputLoss queryScale K : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (loss : ℕ → ℝ) (leftFactor rightFactor : ℕ → ENNReal)
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)
    (seed : Proposition63FourCallInnerLossSeed
      sigma outputLoss discreteLoss)
    (sourceCoefficient : NNReal) (index : ℕ)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (sqrtPackage : Proposition63FourCallFrozenChoiceSqrtScalePackage
      outputLoss scales)
    (robustScale : WZ2PaperRequestedScale scales.rhoHat.1) where
  hdeltaFirstCall : delta ≤ schedule.first.delta₀
  hcellError :
    ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
      (scales.rhoHat.1 * Real.sqrt 3) ≤ 1 / 2
  hrhoAbsorption : scales.rhoHat.1 ≤ seed.rhoAbsorption.delta₀
  hdeltaSecondCall : scales.rhoHat.1 ≤ schedule.second.delta₀
  hdeltaThirdCall : scales.rhoHat.1 ≤ schedule.third.delta₀
  hdeltaFirstStage : scales.rhoHat.1 ≤ seed.firstStageAbsorption.delta₀
  hsourceOuter : schedule.second.normalizationLoss ≤ outerExtremalLoss
  houterExtremalLoss : 0 < outerExtremalLoss
  hrhoOuterRetention :
    scales.rhoHat.1 ≤ seed.outerRetentionAbsorption.delta₀
  houterTargetReentry : outerExtremalLoss ≤ schedule.third.sourceLoss
  hdeltaFirstGrid : scales.rhoHat.1 ≤ seed.firstGridAbsorption.delta₀
  hdeltaFirstCross : scales.rhoHat.1 ≤ seed.firstCrossAbsorption.delta₀
  hdeltaFirstBoundary : scales.rhoHat.1 ≤ seed.firstBoundaryAbsorption.delta₀
  hrobustSmall : robustScale.1 ≤ 1 / 10000
  hsigma : 0 < sigma
  hsigmaOne : sigma < 1
  logScale : ℝ
  hdeltaLog : scales.rhoHat.1 ≤ logScale
  hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale → scale ≤ logScale →
    ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / scale ^ 3 →
      Real.rpow scale epsilon₁ *
        (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108
  haxis : 4 * (6 * scales.rhoHat.1) ^ 2 ≤ (3 / 4 : ℝ) *
    (Real.rpow scales.rhoHat.1 (1 - epsilon₃)) ^ 2
  firstConstant : ENNReal
  hfirstArithmetic : ENNReal.ofReal
    ((proposition63RobustTauTotalVolume scales.rhoHat.1 sigma
        schedule.third.normalizationLoss schedule.thirdOutputLoss
        robustScale.1 scales.tau /
      (Real.rpow scales.rhoHat.1 (1 + 7 * epsilon₁ + epsilon₃) *
        scales.tau ^ 2 / 200)) *
      (2 * proposition63DependentSlabWidth scales.rhoHat.1 scales.tau
        (proposition63DependentCoarseIncidence scales.rhoHat.1 incidence
          (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))
        (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)) /
          scales.rhoHat.1 + 2)) ≤
    firstConstant * Kakeya.realRpowENN (scales.tau / scales.rhoHat.1) (1 - sigma)
  hrhoParentRetention :
    scales.rhoHat.1 ≤ seed.parentRetentionAbsorption.delta₀
  hdeltaFirstRestore : scales.rhoHat.1 ≤ seed.firstRestoreAbsorption.delta₀
  hdeltaSecondReentry : scales.rhoHat.1 ≤ seed.secondReentryAbsorption.delta₀
  hdeltaFourth : scales.rhoHat.1 ≤ schedule.fourth.delta₀
  hdeltaSecondBoundary : scales.rhoHat.1 ≤ seed.secondBoundaryAbsorption.delta₀
  hdeltaSecondGrid : scales.rhoHat.1 ≤ seed.secondGridAbsorption.delta₀
  hdeltaSecondCross : scales.rhoHat.1 ≤ seed.secondCrossAbsorption.delta₀
  htargetRobustSmall : robustScale.1 ≤ 1 / 10000
  finalConstant : ENNReal
  hfinalArithmetic : ENNReal.ofReal
    ((proposition63RobustTauTotalVolume scales.rhoHat.1 sigma
        schedule.fourth.normalizationLoss outputLoss sqrtPackage.sqrtRequested.1
        sqrtPackage.sqrtRequested.1 /
      (Real.rpow scales.rhoHat.1 (1 + 7 * epsilon₁ + epsilon₃) *
        sqrtPackage.sqrtRequested.1 ^ 2 / 200)) *
      (2 * proposition63DependentSlabWidth scales.rhoHat.1
        sqrtPackage.sqrtRequested.1
        (proposition63DependentCoarseIncidence scales.rhoHat.1 incidence
          (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)))
        (4 * (lipschitzExtensionConstant Point3 * sourceCoefficient)) /
          scales.rhoHat.1 + 2)) ≤
    finalConstant * Kakeya.realRpowENN
      (sqrtPackage.sqrtRequested.1 / scales.rhoHat.1) (1 - sigma)
  hdeltaSecondRestore : scales.rhoHat.1 ≤ seed.secondRestoreAbsorption.delta₀
  hdeltaMultiplicity : scales.rhoHat.1 ≤ seed.multiplicityAbsorption.delta₀
  hrhoBalancingBoundary :
    scales.rhoHat.1 ≤ seed.balancingBoundaryAbsorption.delta₀
  hdeltaBalancing : scales.rhoHat.1 ≤ seed.balancingAbsorption.delta₀
  cellVolumeFloor : ℝ
  outputCandidateLoss : ℝ
  spatialScale : ℝ
  coarseCritical : scales.rhoHat.1 ≤ seed.critical.delta₀
  hcriticalTrace : scales.rhoHat.1 ≤ seed.traceAbsorption.delta₀
  cellVolumeFloor_pos : 0 < cellVolumeFloor
  cellBudget : ENNReal.ofReal cellVolumeFloor *
      Kakeya.realRpowENN sqrtPackage.sqrtRequested.1 (sigma - outputLoss) ≤
    Kakeya.realRpowENN scales.rhoHat.1 (sigma + seed.floorLoss) *
      Kakeya.realRpowENN sqrtPackage.sqrtRequested.1 3
  coverBudget : ℕ
  hcoverBudgetPos : 0 < coverBudget
  hcoverBudget : (512 : ENNReal) *
    ((2 * Nat.ceil (2 * (((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)) + 2 :
      ENNReal) * (finalConstant * Kakeya.realRpowENN
        (sqrtPackage.sqrtRequested.1 / scales.rhoHat.1) (1 - sigma))) ≤
    (coverBudget : ENNReal)
  hsqrtConstantFinite : finalConstant * Kakeya.realRpowENN
    (sqrtPackage.sqrtRequested.1 / scales.rhoHat.1) (1 - sigma) ≠ ⊤
  hdeltaAlignedAbsorption : delta ≤ seed.alignedAbsorption.delta₀
  intervalAbsorption : Proposition63NestedIntervalAbsorptionData
    (((4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)
    firstConstant seed.alignedAbsorption.internalLoss
  hdeltaIntervalAbsorption : delta ≤ intervalAbsorption.delta₀
  uniformLevel : ℕ
  hleftFactor : leftFactor index =
    proposition63FourCallFrozenActualLeftFactor
      root.normalization.croppedFamily delta scales.rhoHat.1 sigma
      schedule.firstOutputLoss currentWeightLoss 61
      (proposition63FourCallAncestorRetentionUpper
        root.normalization.croppedFamily scales.rhoHat.1 sigma
        schedule.firstOutputLoss schedule.second.normalizationLoss
        schedule.second.sourceLoss rhoWeightLoss firstStageWeightLoss)
      (proposition63FourCallFrozenLineCoverBase
        cellVolumeFloor sqrtPackage.sqrtRequested.1 coverBudget)
      (proposition63CanonicalReentryWeight scales.rhoHat.1 nextWeightLoss)
  hrightFactor : rightFactor index =
    proposition63UniformDependentRightFactor root.normalization.croppedFamily uniformLevel
  hcurrentLevel : proposition63CanonicalNearbyLevelCount normalizationLoss ≤ uniformLevel
  hpaperNestedLevel :
    proposition63CanonicalNearbyLevelCount schedule.second.normalizationLoss ≤
      uniformLevel
  hnestedLevel :
    proposition63CanonicalNearbyLevelCount schedule.third.normalizationLoss ≤ uniformLevel

/-- Global pre-iteration scalar data.  The final field is a single uniform
statement over all indices and all scale packages generated from the grid; it
does not preselect an index-local witness. -/
structure Proposition63FourCallFrozenChoiceGlobalData
    {delta sigma inputLoss incidence
      discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (K : ℝ)
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss
        (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source normalizationExponent
        backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (leftFactor rightFactor : ℕ → ENNReal)
    (sourceCoefficient : NNReal) where
  delta_pos : 0 < delta
  discreteLoss_pos : 0 < discreteLoss
  discreteLoss_lt_half : discreteLoss < 1 / 2
  query_small : 2 * Real.rpow queryScale (discreteLoss / 2) ≤ 1
  delta_le_query : delta ≤ queryScale
  sqrt_query_small : 2 * Real.sqrt queryScale ≤ 1
  outputLoss_le_half : gridOutputLoss ≤ 1 / 2
  coefficient_one : 1 ≤
    (((4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)
  amplified_query_small : Real.rpow queryScale (discreteLoss / 2) ≤
    1 / (16 * (((4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ))
  rho_small : ∀ index, index < (finiteIntervalOrderedPairs gridN).length →
    ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
      scales.rhoHat.1 ≤ 1 / 144
  firstOutputLoss_le_discrete : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      (backward.seed index hindex).schedule.firstOutputLoss ≤ discreteLoss
  firstOutputLoss_lt_discrete : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      (backward.seed index hindex).schedule.firstOutputLoss < discreteLoss
  firstOutput_gap_small : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Real.rpow delta (discreteLoss -
        (backward.seed index hindex).schedule.firstOutputLoss) ≤ 1 / 2
  hdeltaCurrentReentry : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      delta ≤ (proposition63_four_call_inner_current_reentry_schedule_at
        backward source root index hindex).density_absorb.delta₀
  scalar_receipts : ∀ index,
    ∀ hindex : index < (finiteIntervalOrderedPairs gridN).length,
    ∀ (scales : Proposition63FourCallOrderedPairIndexScales grid index)
      (sqrtPackage : Proposition63FourCallFrozenChoiceSqrtScalePackage
        (backward.loss (index + 1)) scales),
      Proposition63FourCallFrozenScalarReceiptsAt root grid backward.loss
        leftFactor rightFactor (K := K)
        (outputLoss := backward.loss (index + 1))
        (rhoDensityLoss := (backward.seed index hindex).rhoDensityLoss)
        (firstStageDensityLoss :=
          (backward.seed index hindex).firstStageDensityLoss)
        (secondReentryDensityLoss :=
          (backward.seed index hindex).secondReentryDensityLoss)
        (rhoWeightLoss := (backward.seed index hindex).rhoWeightLoss)
        (firstStageWeightLoss :=
          (backward.seed index hindex).firstStageWeightLoss)
        (currentWeightLoss := backward.currentWeightLoss index hindex)
        (outerExtremalLoss := (backward.seed index hindex).outerExtremalLoss)
        (robustExponent := (backward.seed index hindex).robustExponent)
        (epsilon₁ := (backward.seed index hindex).epsilon₁)
        (epsilon₃ := (backward.seed index hindex).epsilon₃)
        (parentLoss := (backward.seed index hindex).parentLoss)
        (firstLoss := (backward.seed index hindex).firstLoss)
        (nextWeightLoss := (backward.seed index hindex).nextWeightLoss)
        (secondLoss := (backward.seed index hindex).secondLoss)
        (middleLoss := (backward.seed index hindex).middleLoss)
        (finalLoss := (backward.seed index hindex).finalLoss)
        (incidence := incidence) (backward.seed index hindex).schedule
        (backward.seed index hindex)
        sourceCoefficient index scales sqrtPackage
        (scales.choiceRobustScalePackage (backward.seed index hindex)
          discreteLoss_lt_half).requested

/-- Construct every frozen choice from one global scalar package and the grid's
uniform smallness hypotheses.  In particular, the conclusion produces the
finite family; it does not receive that family as an argument. -/
theorem proposition63_four_call_frozen_choice_producer
    {delta sigma inputLoss incidence
      discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (K : ℝ)
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss
        (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source normalizationExponent
        backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (leftFactor rightFactor : ℕ → ENNReal)
    (sourceCoefficient : NNReal)
    (global : Proposition63FourCallFrozenChoiceGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient) :
    ∀ index, index < (finiteIntervalOrderedPairs gridN).length →
      Nonempty (Proposition63FourCallOrderedPairFrozenChoiceAt
        (incidence := incidence) root grid backward.loss
        leftFactor rightFactor
        sourceCoefficient index) := by
  intro index hindex
  let seed := backward.seed index hindex
  let schedule := seed.schedule
  let currentData := proposition63_four_call_inner_current_reentry_schedule_at
    backward source root index hindex
  have hdeltaCurrent := global.hdeltaCurrentReentry index hindex
  have ambientTwo := currentData.density_absorb.ambient_two
    global.delta_pos hdeltaCurrent
  let rootReentrySchedule := Classical.choice <| root.finiteNearbySchedule
    (by
      dsimp [Proposition63FourCallInnerBackwardLossSchedule.rootNormalizationLoss]
      exact div_pos backward.rootBudget_pos (by norm_num))
    ambientTwo currentData.two_normalization_le_reentry
  rcases grid.orderedPairIndexScales global.delta_pos global.discreteLoss_pos
      global.query_small global.delta_le_query global.sqrt_query_small hindex with
    ⟨scales⟩
  have hrhoLower := scales.output_rpow_le_rhoHat
    schedule.firstOutputLoss_pos (global.firstOutputLoss_le_discrete index hindex)
  have hrhoUpper := scales.rhoHat_le_output_rpow global.delta_pos
    (global.firstOutputLoss_lt_discrete index hindex)
    (global.firstOutput_gap_small index hindex)
  have hscaleSmall := scales.scale_smallness global.coefficient_one
    global.discreteLoss_pos.le global.amplified_query_small
  have hrhoPos : 0 < scales.rhoHat.1 :=
    (grid.scale_pos _
      (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
        scales.logicalR_le_rhoHat
  let sqrtPackage := scales.choiceSqrtScalePackage
    (backward.loss (index + 1))
    (backward.loss_pos (index + 1) (by omega))
    ((backward.loss_le_terminal (index + 1) (by omega)).trans
      global.outputLoss_le_half)
    (global.rho_small index hindex scales)
  let robustPackage := scales.choiceRobustScalePackage seed
    global.discreteLoss_lt_half
  let receipts := global.scalar_receipts index hindex scales sqrtPackage
  let frozen : Proposition63FourCallOrderedPairFrozenInputsAt
      (rhoDensityLoss := seed.rhoDensityLoss)
      (firstStageDensityLoss := seed.firstStageDensityLoss)
      (secondReentryDensityLoss := seed.secondReentryDensityLoss)
      (rhoWeightLoss := seed.rhoWeightLoss)
      (firstStageWeightLoss := seed.firstStageWeightLoss)
      (currentWeightLoss := backward.currentWeightLoss index hindex)
      (outerExtremalLoss := seed.outerExtremalLoss)
      (robustExponent := seed.robustExponent)
      (epsilon₁ := seed.epsilon₁) (epsilon₃ := seed.epsilon₃)
      (parentLoss := seed.parentLoss) (firstLoss := seed.firstLoss)
      (nextWeightLoss := seed.nextWeightLoss)
      (secondLoss := seed.secondLoss) (middleLoss := seed.middleLoss)
      (finalLoss := seed.finalLoss) (incidence := incidence)
      root grid backward.loss leftFactor rightFactor schedule
      rootReentrySchedule sourceCoefficient index := {
    scales := scales
    ambient_two := ambientTwo
    currentLoss_le_reentry := currentData.currentLoss_lt_reentry.le
    currentLoss_pos := currentData.currentLoss_pos
    reentryLoss_le_half := schedule.first.sourceLoss_le_half
    canonical_weight_absorb := currentData.density_absorb.canonical_weight_absorb
      global.delta_pos hdeltaCurrent
    trace_fixed_absorb := currentData.density_absorb.trace_fixed_absorb
      global.delta_pos hdeltaCurrent
    paper_fixed_absorb := currentData.density_absorb.paper_fixed_absorb
      global.delta_pos hdeltaCurrent
    regularization_absorb := currentData.density_absorb.regularization_absorb
      root.normalization rfl rootReentrySchedule rfl rfl global.delta_pos
        hdeltaCurrent
    delta_small := hdeltaCurrent.trans <|
      currentData.density_absorb.delta₀_le_tiny.trans (by norm_num)
    hdeltaFirstCall := receipts.hdeltaFirstCall
    hrhoLower := hrhoLower
    hrhoUpper := hrhoUpper
    hcellError := receipts.hcellError
    rhoAbsorption := seed.rhoAbsorption
    hrhoAbsorption := receipts.hrhoAbsorption
    hrhoSmall := (global.rho_small index hindex scales).trans (by norm_num)
    hdeltaSecondCall := receipts.hdeltaSecondCall
    robustScale := robustPackage.requested
    hrobustLower := robustPackage.secondLower
    hrobustUpper := robustPackage.secondUpper
    hdeltaThirdCall := receipts.hdeltaThirdCall
    firstStageAbsorption := seed.firstStageAbsorption
    hdeltaFirstStage := receipts.hdeltaFirstStage
    hsourceOuter := receipts.hsourceOuter
    houterExtremalLoss := receipts.houterExtremalLoss
    houterRetention := seed.outerRetentionAbsorption.absorb hrhoPos
      receipts.hrhoOuterRetention
    houterTargetReentry := receipts.houterTargetReentry
    targetScale := robustPackage.requested
    htargetLower := robustPackage.thirdLower
    htargetUpper := robustPackage.thirdUpper
    firstGridAbsorption := seed.firstGridAbsorption
    firstCrossAbsorption := seed.firstCrossAbsorption
    hdeltaFirstGrid := receipts.hdeltaFirstGrid
    hdeltaFirstCross := receipts.hdeltaFirstCross
    hrobustScale := robustPackage.scale_eq
    htargetScale := robustPackage.scale_eq
    firstBoundaryAbsorption := seed.firstBoundaryAbsorption
    hdeltaFirstBoundary := receipts.hdeltaFirstBoundary
    hrobustSmall := receipts.hrobustSmall
    hkappa := robustPackage.kappa
    htargetSmall := receipts.hrobustSmall.trans (by norm_num : (1 : ℝ) / 10000 ≤ 1 / 12)
    htargetTau := robustPackage.targetTau
    htauSq := hscaleSmall.2.2.2
    hsigma := receipts.hsigma
    hsigmaOne := receipts.hsigmaOne
    hepsilon₁ := seed.epsilon₁_pos
    hepsilon₃ := seed.epsilon₃_pos
    hepsilonSum := seed.epsilon_sum_lt_one
    logScale := receipts.logScale
    hdeltaLog := receipts.hdeltaLog
    hlog := receipts.hlog
    haxis := receipts.haxis
    firstConstant := receipts.firstConstant
    hfirstArithmetic := receipts.hfirstArithmetic
    hnormalizationParent := by
      rw [seed.parentLoss_eq, ← schedule.thirdOutputLoss_eq]
      exact schedule.third.normalizationLoss_lt_output.le
    hparentRetention := seed.parentRetentionAbsorption.absorb hrhoPos
      receipts.hrhoParentRetention
    hparentOutput := by
      rw [seed.parentLoss_eq, seed.firstLoss_eq]
      linarith [schedule.fourth.sourceLoss_pos]
    hfirstLoss := by
      rw [seed.firstLoss_eq]
      exact div_pos schedule.fourth.sourceLoss_pos (by norm_num)
    firstRestoreAbsorption := seed.firstRestoreAbsorption
    hdeltaFirstRestore := receipts.hdeltaFirstRestore
    secondReentryAbsorption := seed.secondReentryAbsorption
    hdeltaSecondReentry := receipts.hdeltaSecondReentry
    hfirstReentry := by
      rw [seed.firstLoss_eq]
      linarith [schedule.fourth.sourceLoss_pos]
    hdeltaFourth := receipts.hdeltaFourth
    sqrtRequested := sqrtPackage.sqrtRequested
    hsqrtLower := sqrtPackage.hsqrtLower
    hsqrtUpper := sqrtPackage.hsqrtUpper
    hsqrtOne := sqrtPackage.hsqrtOne
    secondBoundaryAbsorption := seed.secondBoundaryAbsorption
    hdeltaSecondBoundary := receipts.hdeltaSecondBoundary
    secondGridAbsorption := seed.secondGridAbsorption
    hdeltaSecondGrid := receipts.hdeltaSecondGrid
    secondCrossAbsorption := seed.secondCrossAbsorption
    hdeltaSecondCross := receipts.hdeltaSecondCross
    htargetRobustSmall := receipts.hrobustSmall
    htargetKappa := robustPackage.kappa
    hsqrtSmall := sqrtPackage.hsqrtSmall
    hsqrtSq := sqrtPackage.hsqrtSq
    finalConstant := receipts.finalConstant
    hfinalArithmetic := receipts.hfinalArithmetic
    hnormalizationSecond := by
      rw [seed.secondLoss_eq]
      have htrace := seed.traceGap
      rw [seed.finalLoss_eq, seed.middleLoss_eq, seed.secondLoss_eq] at htrace
      ring_nf at htrace ⊢
      linarith [schedule.fourth.sourceLoss_pos]
    hsecondLoss := by
      rw [seed.secondLoss_eq]
      exact div_pos (add_pos schedule.fourth.normalizationLoss_pos
        seed.critical.structuralLoss_pos) (by norm_num)
    secondRestoreAbsorption := seed.secondRestoreAbsorption
    hdeltaSecondRestore := receipts.hdeltaSecondRestore
    hsecondMiddle := by
      rw [seed.middleLoss_eq]
      have htrace := seed.traceGap
      rw [seed.finalLoss_eq, seed.middleLoss_eq, seed.secondLoss_eq] at htrace
      rw [seed.secondLoss_eq]
      ring_nf at htrace ⊢
      linarith [schedule.fourth.sourceLoss_pos]
    hmiddleLoss := by
      rw [seed.middleLoss_eq]
      have hsecond : 0 < seed.secondLoss := by
        rw [seed.secondLoss_eq]
        exact div_pos (add_pos schedule.fourth.normalizationLoss_pos
          seed.critical.structuralLoss_pos) (by norm_num)
      exact div_pos (add_pos hsecond seed.critical.structuralLoss_pos)
        (by norm_num)
    multiplicityAbsorption := seed.multiplicityAbsorption
    hdeltaMultiplicity := receipts.hdeltaMultiplicity
    hbalancingBoundary := seed.balancingBoundaryAbsorption.absorb hrhoPos
      receipts.hrhoBalancingBoundary sqrtPackage.sqrtRequested
        sqrtPackage.sqrtScale_eq
    hmiddleFinal := seed.middleLoss_lt_finalLoss.le
    hfinalLoss := (by
      have hmiddle : 0 < seed.middleLoss := by
        rw [seed.middleLoss_eq]
        have hsecond : 0 < seed.secondLoss := by
          rw [seed.secondLoss_eq]
          exact div_pos (add_pos schedule.fourth.normalizationLoss_pos
            seed.critical.structuralLoss_pos) (by norm_num)
        exact div_pos (add_pos hsecond seed.critical.structuralLoss_pos)
          (by norm_num)
      exact hmiddle.trans seed.middleLoss_lt_finalLoss)
    balancingAbsorption := seed.balancingAbsorption
    hdeltaBalancing := receipts.hdeltaBalancing
    floorLoss := seed.floorLoss
    structuralBudget := seed.structuralBudget
    cellVolumeFloor := receipts.cellVolumeFloor
    outputCandidateLoss := backward.outputCandidateLoss index
    spatialScale := receipts.spatialScale
    critical := seed.critical
    coarseCritical := receipts.coarseCritical
    finalStructural := seed.finalLoss_le_structural
    criticalTraceAbsorption := seed.traceAbsorption.absorb scales.rhoHat.1
      hrhoPos receipts.hcriticalTrace
    cellVolumeFloor_pos := receipts.cellVolumeFloor_pos
    cellBudget := receipts.cellBudget
    tau_le_sqrt := hscaleSmall.2.2.1
    sqrtScale_eq := sqrtPackage.sqrtScale_eq
    hcoefficientOne := global.coefficient_one
    coverBudget := receipts.coverBudget
    hcoverBudgetPos := receipts.hcoverBudgetPos
    hcoverBudget := receipts.hcoverBudget
    hsqrtConstantFinite := receipts.hsqrtConstantFinite
    hnormalErrorTau := hscaleSmall.1
    hhullTau := hscaleSmall.2.1
    hnextLoss := backward.output_candidate_eq index hindex
    alignedAbsorption := seed.alignedAbsorption
    hdeltaAlignedAbsorption := receipts.hdeltaAlignedAbsorption
    nestedIntervalAbsorption := receipts.intervalAbsorption
    hdeltaNestedInterval := receipts.hdeltaIntervalAbsorption
    uniformLevel := receipts.uniformLevel
    hleftFactor := receipts.hleftFactor
    hrightFactor := receipts.hrightFactor
    hcurrentLevel := receipts.hcurrentLevel
    hnestedLevel := receipts.hnestedLevel
    hfourRho := by
      have := global.rho_small index hindex scales
      linarith
  }
  exact ⟨{
    outputLoss := backward.loss (index + 1)
    rhoDensityLoss := seed.rhoDensityLoss
    firstStageDensityLoss := seed.firstStageDensityLoss
    secondReentryDensityLoss := seed.secondReentryDensityLoss
    rhoWeightLoss := seed.rhoWeightLoss
    firstStageWeightLoss := seed.firstStageWeightLoss
    currentWeightLoss := backward.currentWeightLoss index hindex
    outerExtremalLoss := seed.outerExtremalLoss
    robustExponent := seed.robustExponent
    epsilon₁ := seed.epsilon₁
    epsilon₃ := seed.epsilon₃
    parentLoss := seed.parentLoss
    firstLoss := seed.firstLoss
    nextWeightLoss := seed.nextWeightLoss
    secondLoss := seed.secondLoss
    middleLoss := seed.middleLoss
    finalLoss := seed.finalLoss
    schedule := schedule
    currentSchedule := rootReentrySchedule
    frozen := frozen
  }⟩

end Kakeya.Assouad.PureWZ2
