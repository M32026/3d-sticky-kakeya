import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallFrozenChoiceProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperSeedCutoff

/-!
# Paper-only pre-runtime data for the four-call schedule

The legacy frozen-choice package also stores a pair-local interval-absorption
cutoff.  That cutoff is deliberately absent here: the paper route controls its
normalized first constant by a separate uniform envelope chosen before
`delta`.  This file retains only the scalar receipts actually consumed by the
paper runtime.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The paper route computes its real left/right mass factors in
`Proposition63FourCallPaperScalarFamilyData`.  This constant function occupies
the two legacy phantom parameters that remain in the runtime ABI. -/
def proposition63FourCallPaperPlaceholderFactor (_index : ℕ) : ENNReal := 1

/-- The scalar part of the legacy frozen receipt that is genuinely consumed
by the paper runtime.  In particular, it contains no pair-local nested
interval cutoff, legacy mass factor, or legacy level choice. -/
structure Proposition63FourCallPaperScalarReceiptsAt
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale
      outputLoss : ℝ}
    {gridN index : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss)
    (sourceCoefficient : NNReal)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index) where
  hdeltaFirstCall : delta ≤ seed.schedule.first.delta₀
  hcellError :
    ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
      (scales.rhoHat.1 * Real.sqrt 3) ≤ 1 / 2
  hrhoAbsorption : scales.rhoHat.1 ≤ seed.rhoAbsorption.delta₀
  hdeltaSecondCall : scales.rhoHat.1 ≤ seed.schedule.second.delta₀
  hdeltaThirdCall : scales.rhoHat.1 ≤ seed.schedule.third.delta₀
  hdeltaFirstStage : scales.rhoHat.1 ≤ seed.firstStageAbsorption.delta₀
  hsourceOuter : seed.schedule.second.normalizationLoss ≤ seed.outerExtremalLoss
  houterExtremalLoss : 0 < seed.outerExtremalLoss
  hrhoOuterRetention : scales.rhoHat.1 ≤ seed.outerRetentionAbsorption.delta₀
  houterTargetReentry : seed.outerExtremalLoss ≤ seed.schedule.third.sourceLoss
  hdeltaFirstGrid : scales.rhoHat.1 ≤ seed.firstGridAbsorption.delta₀
  hdeltaFirstBoundary : scales.rhoHat.1 ≤ seed.firstBoundaryAbsorption.delta₀
  hsigma : 0 < sigma
  hsigmaOne : sigma < 1
  logScale : ℝ
  hdeltaLog : scales.rhoHat.1 ≤ logScale
  hlog : 0 < seed.epsilon₁ → ∀ scale : ℝ, 0 < scale → scale ≤ logScale →
    ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / scale ^ 3 →
      Real.rpow scale seed.epsilon₁ *
        (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108
  hrhoParentRetention :
    scales.rhoHat.1 ≤ seed.parentRetentionAbsorption.delta₀
  hdeltaFirstRestore : scales.rhoHat.1 ≤ seed.firstRestoreAbsorption.delta₀
  hdeltaFourth : scales.rhoHat.1 ≤ seed.schedule.fourth.delta₀
  hdeltaSecondGrid : scales.rhoHat.1 ≤ seed.secondGridAbsorption.delta₀
  hdeltaSecondRestore : scales.rhoHat.1 ≤ seed.secondRestoreAbsorption.delta₀
  hdeltaMultiplicity : scales.rhoHat.1 ≤ seed.multiplicityAbsorption.delta₀
  hrhoBalancingBoundary :
    scales.rhoHat.1 ≤ seed.balancingBoundaryAbsorption.delta₀
  hdeltaBalancing : scales.rhoHat.1 ≤ seed.balancingAbsorption.delta₀

/-- Global scalar and cutoff data for the paper route.  The phantom factor
parameters preserve the existing dependent runtime ABI while the data itself
is independent of all legacy interval and mass-factor receipts. -/
structure Proposition63FourCallPaperPreludeGlobalData
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (K : ℝ)
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
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
  firstOutput_gap_small : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Real.rpow delta (discreteLoss -
        (backward.seed index hindex).schedule.firstOutputLoss) ≤ 1 / 2

/-- The first output loss is below the inner-grid loss by the frozen schedule
hierarchy; it is not an additional cutoff hypothesis. -/
theorem Proposition63FourCallPaperPreludeGlobalData.firstOutputLoss_le_discrete
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ} {K : ℝ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {leftFactor rightFactor : ℕ → ENNReal} {sourceCoefficient : NNReal}
    (_global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient)
    (index : ℕ)
    (hindex : index < (finiteIntervalOrderedPairs gridN).length) :
    (backward.seed index hindex).schedule.firstOutputLoss ≤ discreteLoss := by
  let seed := backward.seed index hindex
  exact seed.schedule.firstOutputLoss_lt_secondSource.le.trans <|
    seed.schedule.second.sourceLoss_le_half.trans <|
      (half_le_self seed.schedule.second.normalizationLoss_pos.le).trans <|
        seed.schedule.second.normalizationLoss_lt_output.le.trans
          seed.secondOutputLoss_le_discrete

/-- Strict version of `firstOutputLoss_le_discrete`. -/
theorem Proposition63FourCallPaperPreludeGlobalData.firstOutputLoss_lt_discrete
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ} {K : ℝ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {leftFactor rightFactor : ℕ → ENNReal} {sourceCoefficient : NNReal}
    (_global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient)
    (index : ℕ)
    (hindex : index < (finiteIntervalOrderedPairs gridN).length) :
    (backward.seed index hindex).schedule.firstOutputLoss < discreteLoss := by
  let seed := backward.seed index hindex
  exact seed.schedule.firstOutputLoss_lt_secondSource.trans_le <|
    seed.schedule.second.sourceLoss_le_half.trans <|
      (half_le_self seed.schedule.second.normalizationLoss_pos.le).trans <|
        seed.schedule.second.normalizationLoss_lt_output.le.trans
          seed.secondOutputLoss_le_discrete

/-- Produce the exact paper runtime receipt from the paper cutoff.  This is
where the old receipt used to require a pair-local nested-interval cutoff; no
such premise occurs here. -/
noncomputable def Proposition63FourCallPaperPreludeGlobalData.scalar_receipts
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ} {K : ℝ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {leftFactor rightFactor : ℕ → ENNReal} {sourceCoefficient : NNReal}
    (global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient)
    (index : ℕ)
    (hindex : index < (finiteIntervalOrderedPairs gridN).length)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (_sqrtPackage : Proposition63FourCallFrozenChoiceSqrtScalePackage
      (backward.loss (index + 1)) scales)
    (cutoff : Proposition63FourCallPaperSeedCutoffData
      (backward.seed index hindex)
      ((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    (hrho : scales.rhoHat.1 ≤ cutoff.rhoCutoff) :
    Proposition63FourCallPaperScalarReceiptsAt grid
      (backward.seed index hindex) sourceCoefficient scales := by
  let seed := backward.seed index hindex
  have hrhoLegacy : scales.rhoHat.1 ≤ cutoff.legacy.rhoCutoff :=
    hrho.trans cutoff.rhoCutoff_le_legacy
  have rho_pos : 0 < scales.rhoHat.1 :=
    (grid.scale_pos _
      (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
      scales.logicalR_le_rhoHat
  have hscaleSmall := scales.scale_smallness global.coefficient_one
    global.discreteLoss_pos.le global.amplified_query_small
  exact {
    hdeltaFirstCall := scales.rhoHat.property.1.trans <|
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_first
    hcellError := by
      have hsqrtThree : Real.sqrt 3 ≤ 2 := by
        nlinarith [Real.sqrt_nonneg 3,
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      have hcoefficient : 0 ≤
          ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) :=
        by positivity
      have hsmall := hscaleSmall.1.trans scales.tau_le_one
      have hmul :
          ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
              (scales.rhoHat.1 * Real.sqrt 3) ≤
            ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
              (scales.rhoHat.1 * 2) := by gcongr
      push_cast at hsmall
      calc
        ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
              (scales.rhoHat.1 * Real.sqrt 3) ≤
            ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
              (scales.rhoHat.1 * 2) := hmul
        _ = (1 / 16 : ℝ) *
              (8 * (4 *
                ((lipschitzExtensionConstant Point3 * sourceCoefficient :
                  NNReal) : ℝ)) * scales.rhoHat.1) := by ring
        _ ≤ (1 / 16 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hsmall (by norm_num)
        _ ≤ 1 / 2 := by norm_num
    hrhoAbsorption :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_rhoAbsorption
    hdeltaSecondCall :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_second
    hdeltaThirdCall :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_third
    hdeltaFirstStage :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_firstStageAbsorption
    hsourceOuter := by
      rw [seed.outerExtremalLoss_eq]
      exact seed.schedule.second.normalizationLoss_lt_output.le.trans <| by
        rw [seed.schedule.secondOutputLoss_eq]
    houterExtremalLoss := by
      rw [seed.outerExtremalLoss_eq]
      exact div_pos seed.schedule.third.sourceLoss_pos (by norm_num)
    hrhoOuterRetention :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_outerRetentionAbsorption
    houterTargetReentry := by
      rw [seed.outerExtremalLoss_eq]
      linarith [seed.schedule.third.sourceLoss_pos]
    hdeltaFirstGrid :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_firstGridAbsorption
    hdeltaFirstBoundary :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_firstBoundaryAbsorption
    hsigma := by
      linarith [seed.paperAngularExponent_pos,
        seed.paperAngularExponent_lt_sigma]
    hsigmaOne := seed.sigma_lt_one
    logScale := cutoff.legacy.rhoCutoff
    hdeltaLog := hrhoLegacy
    hlog := by
      intro _ scale hscale hscaleCutoff k hk hkUpper
      exact cutoff.legacy.cordobaLog scale hscale hscaleCutoff k hk hkUpper
    hrhoParentRetention :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_parentRetentionAbsorption
    hdeltaFirstRestore :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_firstRestoreAbsorption
    hdeltaFourth :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_fourth
    hdeltaSecondGrid :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_secondGridAbsorption
    hdeltaSecondRestore :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_secondRestoreAbsorption
    hdeltaMultiplicity :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_multiplicityAbsorption
    hrhoBalancingBoundary :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_balancingBoundaryAbsorption
    hdeltaBalancing :=
      hrhoLegacy.trans cutoff.legacy.rhoCutoff_le_balancingAbsorption
  }

end Kakeya.Assouad.PureWZ2
