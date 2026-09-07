import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperMassBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallInnerMassSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPairScalarChoices
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallFirstScalarEnvelope

/-!
# Pre-runtime scalar family for the paper-ordered four-call step

All choices in this file are made from the root configuration, the backward
loss schedule, and the finite interval grid.  In particular, none of them can
mention the callback's current shading.  The square-root package is rebuilt at
the internal fourth loss, and the two paper scales, constants, cell floor,
cover budget, interval absorption, ancestry envelope, and three-level bound
are all retained explicitly at every index.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The paper-specific left factor.  Its numerical value keeps the legacy
ancestry budget; `proposition63_four_call_frozen_left_eq_paper_left` moves the
target first-cover lower bound from the nested product into the corrected
paper ancestry envelope without changing this scalar. -/
noncomputable def proposition63FourCallPaperLeftFactorAt
    {delta sigma inputLoss normalizationLoss densityLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent densityLoss)
    (rho outerLoss fineWeightLoss : ℝ)
    (legacyAncestorUpper lineCover nestedWeight : ENNReal) : ENNReal :=
  proposition63FourCallFrozenActualLeftFactor
    root.normalization.croppedFamily delta rho sigma outerLoss fineWeightLoss 61
    legacyAncestorUpper lineCover nestedWeight

/-- The paper-specific right factor uses one level dominating the current,
second-call, and third-call normalizations. -/
def proposition63FourCallPaperRightFactorAt
    {delta sigma inputLoss normalizationLoss densityLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (root : Proposition63RootNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent densityLoss)
    (uniformLevel : ℕ) : ENNReal :=
  proposition63UniformDependentRightFactor
    root.normalization.croppedFamily uniformLevel

/-- Every scalar selected for one paper-ordered pair. -/
structure Proposition63FourCallPaperScalarDataAt
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (sourceCoefficient : NNReal)
    (index : ℕ) (hindex : index < (finiteIntervalOrderedPairs gridN).length) where
  scales : Proposition63FourCallOrderedPairIndexScales grid index
  internalSqrt : Proposition63FourCallFrozenChoiceSqrtScalePackage
    (backward.seed index hindex).fourthKernel.internalLoss scales
  paperScale : Proposition63FourCallPaperScalePackage
    (backward.seed index hindex) scales
  firstConstant : Proposition63FourCallFirstConstantChoice scales.rhoHat.1
    scales.tau sigma (backward.seed index hindex).schedule.third.normalizationLoss
    (backward.seed index hindex).schedule.thirdOutputLoss
    paperScale.targetRequested.1 (backward.seed index hindex).epsilon₁
    (backward.seed index hindex).paperAngularExponent incidence
    ((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient))
  firstConstant_value : firstConstant.firstConstant *
      Kakeya.realRpowENN (scales.tau / scales.rhoHat.1) (1 - sigma) =
    proposition63FourCallFirstArithmeticRequirement scales.rhoHat.1 scales.tau
      sigma (backward.seed index hindex).schedule.third.normalizationLoss
      (backward.seed index hindex).schedule.thirdOutputLoss
      paperScale.targetRequested.1 (backward.seed index hindex).epsilon₁
      (backward.seed index hindex).paperAngularExponent incidence
      ((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient))
  finalConstant : Proposition63FourCallFinalConstantChoice scales.rhoHat.1 sigma
    (backward.seed index hindex).schedule.fourth.normalizationLoss
    (backward.seed index hindex).fourthKernel.internalLoss
    internalSqrt.sqrtRequested.1 (backward.seed index hindex).epsilon₁
    (backward.seed index hindex).paperAngularExponent incidence
    ((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient))
  finalConstant_value : finalConstant.finalConstant =
    proposition63FourCallFinalArithmeticRequirement scales.rhoHat.1 sigma
        (backward.seed index hindex).schedule.fourth.normalizationLoss
        (backward.seed index hindex).fourthKernel.internalLoss
        internalSqrt.sqrtRequested.1 (backward.seed index hindex).epsilon₁
        (backward.seed index hindex).paperAngularExponent incidence
        ((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient)) /
      Kakeya.realRpowENN
        (internalSqrt.sqrtRequested.1 / scales.rhoHat.1) (1 - sigma)
  finalConstant_sqrt : Proposition63FourCallFinalConstantChoice
    scales.rhoHat.1 sigma
    (backward.seed index hindex).schedule.fourth.normalizationLoss
    (backward.seed index hindex).fourthKernel.internalLoss
    (Real.sqrt scales.rhoHat.1) (backward.seed index hindex).epsilon₁
    (backward.seed index hindex).paperAngularExponent incidence
    ((4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient))
  finalConstant_sqrt_value : finalConstant_sqrt.finalConstant =
    finalConstant.finalConstant
  finalConstant_sqrt_finite : finalConstant.finalConstant *
    Kakeya.realRpowENN
      (Real.sqrt scales.rhoHat.1 / scales.rhoHat.1) (1 - sigma) ≠ ⊤
  cellFloor : Proposition63FourCallCellVolumeFloorChoice scales.rhoHat.1
    internalSqrt.sqrtRequested.1 sigma
    (backward.seed index hindex).fourthKernel.internalLoss
    (backward.seed index hindex).floorLoss
  coverBudget : Proposition63FourCallCoverBudgetChoice
    (proposition63FourCallCoverRequirement
      ((4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient))
      finalConstant.finalConstant scales.rhoHat.1
      internalSqrt.sqrtRequested.1 sigma)
  coverBudget_value : coverBudget.coverBudget =
    Nat.ceil
        (proposition63FourCallCoverRequirement
          ((4 : NNReal) *
            (lipschitzExtensionConstant Point3 * sourceCoefficient))
          finalConstant.finalConstant scales.rhoHat.1
          internalSqrt.sqrtRequested.1 sigma).toNNReal + 1
  coverBudget_sqrt_bound : (512 : ENNReal) *
      ((2 * Nat.ceil (2 *
          ((((4 : NNReal) *
            (lipschitzExtensionConstant Point3 * sourceCoefficient)) : NNReal) :
              ℝ)) + 2 : ENNReal) *
        (finalConstant.finalConstant * Kakeya.realRpowENN
          (Real.sqrt scales.rhoHat.1 / scales.rhoHat.1) (1 - sigma))) ≤
    (coverBudget.coverBudget : ENNReal)
  coverBudget_upper : (coverBudget.coverBudget : ENNReal) ≤
    (1605264998400 : ENNReal) *
      (((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ENNReal) ^ 3 *
      Kakeya.realRpowENN scales.rhoHat.1
        (-(proposition63FourCallPaperFinalExponent sigma
          (backward.seed index hindex).schedule.fourth.normalizationLoss
          (backward.seed index hindex).fourthKernel.internalLoss
          (backward.seed index hindex).epsilon₁
          (backward.seed index hindex).paperAngularExponent)) + 2
  nestedInterval : Proposition63NestedIntervalAbsorptionData
    ((((4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient)) : NNReal) : ℝ)
    firstConstant.firstConstant
    (backward.seed index hindex).alignedAbsorption.internalLoss
  nestedInterval_delta_eq : nestedInterval.delta₀ = delta
  legacyAncestorUpper : ENNReal
  legacyAncestorUpper_eq : legacyAncestorUpper =
    proposition63FourCallAncestorRetentionUpper
      root.normalization.croppedFamily scales.rhoHat.1 sigma
      (backward.seed index hindex).schedule.firstOutputLoss
      (backward.seed index hindex).schedule.second.normalizationLoss
      (backward.seed index hindex).schedule.second.sourceLoss
      (backward.seed index hindex).rhoWeightLoss
      (backward.seed index hindex).firstStageWeightLoss
  paperAncestorUpper : ENNReal
  paperAncestorUpper_eq : paperAncestorUpper =
    proposition63FourCallPaperAncestorRetentionUpper
      root.normalization.croppedFamily legacyAncestorUpper
  uniformLevel : ℕ
  currentLevel_le : proposition63CanonicalNearbyLevelCount
    backward.rootNormalizationLoss ≤ uniformLevel
  secondLevel_le : proposition63CanonicalNearbyLevelCount
    (backward.seed index hindex).schedule.second.normalizationLoss ≤ uniformLevel
  thirdLevel_le : proposition63CanonicalNearbyLevelCount
    (backward.seed index hindex).schedule.third.normalizationLoss ≤ uniformLevel
  paperLeft : ENNReal
  paperLeft_eq : paperLeft = proposition63FourCallPaperLeftFactorAt root
    scales.rhoHat.1 (backward.seed index hindex).schedule.firstOutputLoss
    (backward.currentWeightLoss index hindex) legacyAncestorUpper
    (proposition63FourCallFrozenLineCoverBase cellFloor.cellVolumeFloor
      internalSqrt.sqrtRequested.1 coverBudget.coverBudget)
    (proposition63CanonicalReentryWeight scales.rhoHat.1
      (backward.seed index hindex).nextWeightLoss)
  paperRight : ENNReal
  paperRight_eq : paperRight =
    proposition63FourCallPaperRightFactorAt root uniformLevel
  paperLeft_pos : 0 < paperLeft
  paperLeft_finite : paperLeft ≠ ⊤
  paperRight_finite : paperRight ≠ ⊤
  massAbsorption : Proposition63FourCallInnerMassAbsorptionData paperLeft
    paperRight (backward.loss index) (backward.loss (index + 1))

/-- The square-root scale stored by the paper scalar datum is the canonical
geometric square root used by the paper runtime. -/
theorem Proposition63FourCallPaperScalarDataAt.internalSqrt_eq_sqrt
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {sourceCoefficient : NNReal} {index : ℕ}
    {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    (data : Proposition63FourCallPaperScalarDataAt (incidence := incidence)
      backward root grid sourceCoefficient index hindex) :
    data.internalSqrt.sqrtRequested.1 = Real.sqrt data.scales.rhoHat.1 :=
  data.internalSqrt.sqrtScale_eq

/-- Canonically rebuild every paper scalar at one index from frozen data. -/
theorem proposition63_four_call_paper_scalar_data_at
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (sourceCoefficient : NNReal) (index : ℕ)
    (hindex : index < (finiteIntervalOrderedPairs gridN).length)
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (sigma_lt_one : sigma < 1) (discreteLoss_pos : 0 < discreteLoss)
    (discreteLoss_lt_half : discreteLoss < 1 / 2)
    (incidence_nonneg : 0 ≤ incidence) (incidence_le_delta : incidence ≤ delta)
    (coefficient_one : 1 ≤
      ((((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : NNReal) : ℝ))
    (query_small : 2 * Real.rpow queryScale (discreteLoss / 2) ≤ 1)
    (delta_le_query : delta ≤ queryScale)
    (sqrt_query_small : 2 * Real.sqrt queryScale ≤ 1)
    (rho_sqrt_small : ∀ scales :
      Proposition63FourCallOrderedPairIndexScales grid index,
      scales.rhoHat.1 ≤ 1 / 144)
    (firstUniformCutoff : Proposition63FourCallFirstUniformCutoffData
      (backward.seed index hindex)
      ((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)))
    (delta_le_firstUniformCutoff :
      delta ≤ firstUniformCutoff.nested.delta₀)
    (legacyAncestor_pos : ∀ scales :
      Proposition63FourCallOrderedPairIndexScales grid index,
      0 < proposition63FourCallAncestorRetentionUpper
        root.normalization.croppedFamily scales.rhoHat.1 sigma
        (backward.seed index hindex).schedule.firstOutputLoss
        (backward.seed index hindex).schedule.second.normalizationLoss
        (backward.seed index hindex).schedule.second.sourceLoss
        (backward.seed index hindex).rhoWeightLoss
        (backward.seed index hindex).firstStageWeightLoss)
    (legacyAncestor_finite : ∀ scales :
      Proposition63FourCallOrderedPairIndexScales grid index,
      proposition63FourCallAncestorRetentionUpper
        root.normalization.croppedFamily scales.rhoHat.1 sigma
        (backward.seed index hindex).schedule.firstOutputLoss
        (backward.seed index hindex).schedule.second.normalizationLoss
        (backward.seed index hindex).schedule.second.sourceLoss
        (backward.seed index hindex).rhoWeightLoss
        (backward.seed index hindex).firstStageWeightLoss ≠ ⊤) :
    Nonempty (Proposition63FourCallPaperScalarDataAt
      (incidence := incidence) backward root grid sourceCoefficient
      index hindex) := by
  let seed := backward.seed index hindex
  let scales := (grid.orderedPairIndexScales delta_pos discreteLoss_pos
    query_small delta_le_query sqrt_query_small hindex).some
  let internalSqrt := scales.choiceSqrtScalePackage
    seed.fourthKernel.internalLoss seed.fourthKernel.internalLoss_pos
    (seed.fourthKernel.internalLoss_lt_discrete.le.trans
      discreteLoss_lt_half.le) (rho_sqrt_small scales)
  let paperScale := scales.choicePaperScalePackage seed discreteLoss_lt_half
  have rho_pos : 0 < scales.rhoHat.1 :=
    delta_pos.trans_le scales.rhoHat.property.1
  let coefficient : NNReal :=
    (4 : NNReal) * (lipschitzExtensionConstant Point3 * sourceCoefficient)
  let firstConstant := proposition63_four_call_first_constant_choice
    (rho := scales.rhoHat.1) (tau := scales.tau) (sigma := sigma)
    (normalizationLoss := seed.schedule.third.normalizationLoss)
    (outputLoss := seed.schedule.thirdOutputLoss)
    (robustScale := paperScale.targetRequested.1)
    (epsilon₁ := seed.epsilon₁) (epsilon₃ := seed.paperAngularExponent)
    (incidence := incidence) (coefficient := coefficient)
    rho_pos scales.rhoHat_le_tau sigma_lt_one
  let finalConstant := proposition63_four_call_final_constant_choice
    (rho := scales.rhoHat.1) (sigma := sigma)
    (normalizationLoss := seed.schedule.fourth.normalizationLoss)
    (outputLoss := seed.fourthKernel.internalLoss)
    (sqrtScale := internalSqrt.sqrtRequested.1)
    (epsilon₁ := seed.epsilon₁) (epsilon₃ := seed.paperAngularExponent)
    (incidence := incidence) (coefficient := coefficient)
    rho_pos internalSqrt.sqrtRequested.property.1 sigma_lt_one.le
  let cellFloor := proposition63_four_call_cell_volume_floor_choice
    (rho := scales.rhoHat.1) (sqrtScale := internalSqrt.sqrtRequested.1)
    (sigma := sigma) (outputLoss := seed.fourthKernel.internalLoss)
    (floorLoss := seed.floorLoss) rho_pos
    (rho_pos.trans_le internalSqrt.sqrtRequested.property.1)
  let coverBudget := proposition63_four_call_exact_cover_budget_choice
    coefficient finalConstant.finalConstant scales.rhoHat.1
    internalSqrt.sqrtRequested.1 sigma finalConstant.finite
  let nestedInterval := firstUniformCutoff.nestedInterval firstConstant
    delta_pos delta_le_firstUniformCutoff incidence_nonneg incidence_le_delta
    (le_max_left _ _) paperScale.targetLower paperScale.targetTau
    coefficient_one
  let legacyAncestorUpper := proposition63FourCallAncestorRetentionUpper
    root.normalization.croppedFamily scales.rhoHat.1 sigma
    seed.schedule.firstOutputLoss seed.schedule.second.normalizationLoss
    seed.schedule.second.sourceLoss seed.rhoWeightLoss seed.firstStageWeightLoss
  let paperAncestorUpper := proposition63FourCallPaperAncestorRetentionUpper
    root.normalization.croppedFamily legacyAncestorUpper
  let uniformLevel := max
    (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss)
    (max (proposition63CanonicalNearbyLevelCount
      seed.schedule.second.normalizationLoss)
      (proposition63CanonicalNearbyLevelCount
        seed.schedule.third.normalizationLoss))
  let lineCover := proposition63FourCallFrozenLineCoverBase
    cellFloor.cellVolumeFloor internalSqrt.sqrtRequested.1
    coverBudget.coverBudget
  let nestedWeight := proposition63CanonicalReentryWeight scales.rhoHat.1
    seed.nextWeightLoss
  let paperLeft := proposition63FourCallPaperLeftFactorAt root scales.rhoHat.1
    seed.schedule.firstOutputLoss (backward.currentWeightLoss index hindex)
    legacyAncestorUpper lineCover nestedWeight
  let paperRight := proposition63FourCallPaperRightFactorAt root uniformLevel
  have root_nonempty : root.normalization.croppedFamily.Nonempty :=
    root.normalization.final_extremal.nonempty
  have legacy_pos_top : 0 < legacyAncestorUpper ∧ legacyAncestorUpper ≠ ⊤ :=
    ⟨legacyAncestor_pos scales, legacyAncestor_finite scales⟩
  have target_pos_top :
      0 < proposition63FourCallPaperTargetRetainedLower
          root.normalization.croppedFamily ∧
      proposition63FourCallPaperTargetRetainedLower
          root.normalization.croppedFamily ≠ ⊤ := by
    unfold proposition63FourCallPaperTargetRetainedLower
    have hlogPos : (0 : ENNReal) <
        (Nat.log 2 root.normalization.croppedFamily.card + 1 : ℕ) := by
      exact_mod_cast Nat.zero_lt_succ
        (Nat.log 2 root.normalization.croppedFamily.card)
    exact ⟨ENNReal.mul_pos (by norm_num)
      (ENNReal.inv_pos.mpr ENNReal.coe_ne_top).ne',
      ENNReal.mul_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num))
        (ENNReal.inv_ne_top.mpr hlogPos.ne')⟩
  have paper_ancestor_pos : 0 < paperAncestorUpper := by
    dsimp only [paperAncestorUpper, proposition63FourCallPaperAncestorRetentionUpper]
    exact ENNReal.inv_pos.mpr <| ENNReal.mul_ne_top target_pos_top.2
      (ENNReal.inv_ne_top.mpr legacy_pos_top.1.ne')
  have paper_ancestor_top : paperAncestorUpper ≠ ⊤ := by
    dsimp only [paperAncestorUpper, proposition63FourCallPaperAncestorRetentionUpper]
    exact ENNReal.inv_ne_top.mpr <|
      (ENNReal.mul_pos target_pos_top.1.ne'
        (ENNReal.inv_pos.mpr legacy_pos_top.2).ne').ne'
  have line_pos : 0 < lineCover := by
    dsimp only [lineCover, proposition63FourCallFrozenLineCoverBase]
    have hsqrtPos : 0 < internalSqrt.sqrtRequested.1 :=
      rho_pos.trans_le internalSqrt.sqrtRequested.property.1
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (div_pos
        (div_pos cellFloor.positive (by norm_num))
        (mul_pos (by norm_num) (sq_pos_of_pos (by positivity))))).ne'
      (ENNReal.div_pos (by norm_num)
        (ENNReal.mul_ne_top (by norm_num)
          (ENNReal.natCast_ne_top _))).ne'
  have line_top : lineCover ≠ ⊤ := by
    dsimp only [lineCover, proposition63FourCallFrozenLineCoverBase]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.div_ne_top (by norm_num)
        (ENNReal.mul_pos (by norm_num)
          (by exact_mod_cast (Nat.ne_of_gt coverBudget.positive))).ne')
  have nested_pos : 0 < nestedWeight := by
    dsimp only [nestedWeight, proposition63CanonicalReentryWeight]
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos rho_pos _)
  have nested_top : nestedWeight ≠ ⊤ := by
    exact proposition63CanonicalReentryWeight_ne_top
  have retained_pos_top :
      0 < proposition63FourCallFrozenNestedRetainedFactor scales.rhoHat.1
          root.normalization.croppedFamily.card nestedWeight ∧
      proposition63FourCallFrozenNestedRetainedFactor scales.rhoHat.1
          root.normalization.croppedFamily.card nestedWeight ≠ ⊤ := by
    unfold proposition63FourCallFrozenNestedRetainedFactor
    constructor
    · have rho_lt_one : scales.rhoHat.1 < 1 :=
        (rho_sqrt_small scales).trans_lt (by norm_num)
      have fraction := pure_refinement_fraction_pos_ne_top
        rho_pos rho_lt_one 61
      exact ENNReal.mul_pos
        (ENNReal.mul_pos
          (ENNReal.mul_pos
            (ENNReal.mul_pos (by norm_num)
              (ENNReal.inv_pos.mpr ENNReal.coe_ne_top).ne').ne'
            fraction.1.ne').ne'
          (ENNReal.mul_pos (by norm_num) nested_pos.ne').ne').ne'
        (ENNReal.mul_pos (by norm_num)
          (ENNReal.inv_pos.mpr ENNReal.coe_ne_top).ne').ne'
    · exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top
              (ENNReal.div_ne_top (by norm_num) (by norm_num))
              (ENNReal.inv_ne_top.mpr (by norm_num)))
            (by
              unfold wz2PaperPureRefinementFraction
              exact ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr <|
                (ENNReal.ofReal_pos.mpr <| Real.log_pos <|
                  one_lt_one_div rho_pos <|
                    (rho_sqrt_small scales).trans_lt (by norm_num)).ne')))
          (ENNReal.mul_ne_top
            (ENNReal.div_ne_top (by norm_num) (by norm_num)) nested_top))
        (ENNReal.mul_ne_top
          (ENNReal.div_ne_top (by norm_num) (by norm_num))
          (ENNReal.inv_ne_top.mpr (by norm_num)))
  have outer_pos_top := proposition63UniformOuterCoarsePullbackCost_pos_ne_top
    (sigma := sigma) (outputLoss := seed.schedule.firstOutputLoss)
    root_nonempty delta_pos rho_pos
  have delta_fraction := pure_refinement_fraction_pos_ne_top
    delta_pos delta_lt_one 61
  have fine_weight_pos : 0 < proposition63CanonicalReentryWeight delta
      (backward.currentWeightLoss index hindex) := by
    unfold proposition63CanonicalReentryWeight
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos delta_pos _)
  have paper_left_pos : 0 < paperLeft := by
    dsimp only [paperLeft, proposition63FourCallPaperLeftFactorAt,
      proposition63FourCallFrozenActualLeftFactor,
      proposition63UniformDependentFinePullbackLeft]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos
          (ENNReal.mul_pos
            (ENNReal.mul_pos line_pos.ne' retained_pos_top.1.ne').ne'
            (ENNReal.inv_pos.mpr legacy_pos_top.2).ne').ne'
          (ENNReal.inv_pos.mpr outer_pos_top.2).ne').ne'
        delta_fraction.1.ne').ne'
      (ENNReal.mul_pos (by norm_num) fine_weight_pos.ne').ne'
  have paper_left_top : paperLeft ≠ ⊤ := by
    dsimp only [paperLeft, proposition63FourCallPaperLeftFactorAt,
      proposition63FourCallFrozenActualLeftFactor,
      proposition63UniformDependentFinePullbackLeft]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.mul_ne_top line_top retained_pos_top.2)
            (ENNReal.inv_ne_top.mpr legacy_pos_top.1.ne'))
          (ENNReal.inv_ne_top.mpr outer_pos_top.1.ne'))
        delta_fraction.2)
      (ENNReal.mul_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num))
        proposition63CanonicalReentryWeight_ne_top)
  have paper_right_top : paperRight ≠ ⊤ := by
    exact (proposition63UniformDependentRightFactor_pos_ne_top
      root.normalization.croppedFamily uniformLevel delta_pos delta_lt_one.le).2
  let massAbsorption := Classical.choice <|
    proposition63_four_call_inner_mass_absorption paperLeft paperRight
      paper_left_pos paper_left_top paper_right_top
      (backward.loss index) (backward.loss (index + 1))
      (backward.loss_lt_next index hindex)
  exact ⟨{
    scales := scales
    internalSqrt := internalSqrt
    paperScale := paperScale
    firstConstant := firstConstant
    firstConstant_value := firstConstant.normalized
    finalConstant := finalConstant
    finalConstant_value := rfl
    finalConstant_sqrt := by
      simpa only [internalSqrt.sqrtScale_eq] using finalConstant
    finalConstant_sqrt_value := rfl
    finalConstant_sqrt_finite := by
      simpa only [internalSqrt.sqrtScale_eq] using finalConstant.finite
    cellFloor := cellFloor
    coverBudget := coverBudget
    coverBudget_value := rfl
    coverBudget_sqrt_bound := by
      simpa only [proposition63FourCallCoverRequirement,
        internalSqrt.sqrtScale_eq] using coverBudget.bound
    coverBudget_upper := by
      have h := proposition63_four_call_exact_cover_budget_upper
          (rho := scales.rhoHat.1) (sigma := sigma)
          (normalizationLoss := seed.schedule.fourth.normalizationLoss)
          (outputLoss := seed.fourthKernel.internalLoss)
          (epsilon₁ := seed.epsilon₁)
          (angular := seed.paperAngularExponent) (incidence := incidence)
          (coefficient := coefficient)
          rho_pos scales.rhoHat.property.2 incidence_nonneg
          (incidence_le_delta.trans scales.rhoHat.property.1) coefficient_one
          finalConstant coverBudget
      convert h using 1 <;> simp only [seed, coefficient]
      push_cast
      rfl
    nestedInterval := nestedInterval
    nestedInterval_delta_eq := by
      simp only [nestedInterval]
      exact firstUniformCutoff.nestedInterval_delta₀ firstConstant delta_pos
        delta_le_firstUniformCutoff incidence_nonneg incidence_le_delta
        (le_max_left _ _) paperScale.targetLower paperScale.targetTau
        coefficient_one
    legacyAncestorUpper := legacyAncestorUpper
    legacyAncestorUpper_eq := rfl
    paperAncestorUpper := paperAncestorUpper
    paperAncestorUpper_eq := rfl
    uniformLevel := uniformLevel
    currentLevel_le := le_max_left _ _
    secondLevel_le := le_max_of_le_right (le_max_left _ _)
    thirdLevel_le := le_max_of_le_right (le_max_right _ _)
    paperLeft := paperLeft
    paperLeft_eq := rfl
    paperRight := paperRight
    paperRight_eq := rfl
    paperLeft_pos := paper_left_pos
    paperLeft_finite := paper_left_top
    paperRight_finite := paper_right_top
    massAbsorption := massAbsorption
  }⟩

/-- The mass-only projection of a paper scalar datum. -/
structure Proposition63FourCallPaperMassSeedAt
    (currentLoss outputLoss : ℝ) where
  leftFactor : ENNReal
  rightFactor : ENNReal
  left_pos : 0 < leftFactor
  left_finite : leftFactor ≠ ⊤
  right_finite : rightFactor ≠ ⊤
  loss_gap : currentLoss < outputLoss
  output_loss_pos : 0 < outputLoss
  absorption : Proposition63FourCallInnerMassAbsorptionData leftFactor
    rightFactor currentLoss outputLoss

/-- Construct one paper mass seed from its already frozen factors. -/
theorem proposition63_four_call_paper_mass_seed
    (leftFactor rightFactor : ENNReal)
    (left_pos : 0 < leftFactor) (left_finite : leftFactor ≠ ⊤)
    (right_finite : rightFactor ≠ ⊤)
    (currentLoss outputLoss : ℝ) (loss_gap : currentLoss < outputLoss)
    (output_loss_pos : 0 < outputLoss) :
    Nonempty (Proposition63FourCallPaperMassSeedAt
      currentLoss outputLoss) := by
  let absorption := Classical.choice <|
    proposition63_four_call_inner_mass_absorption leftFactor rightFactor
      left_pos left_finite right_finite currentLoss outputLoss loss_gap
  exact ⟨{
    leftFactor := leftFactor
    rightFactor := rightFactor
    left_pos := left_pos
    left_finite := left_finite
    right_finite := right_finite
    loss_gap := loss_gap
    output_loss_pos := output_loss_pos
    absorption := absorption
  }⟩

/-- Forget geometry-free scalar provenance while retaining the exact factors
and cutoff used by the mass schedule. -/
def Proposition63FourCallPaperScalarDataAt.massSeed
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {sourceCoefficient : NNReal} {index : ℕ}
    {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    (data : Proposition63FourCallPaperScalarDataAt (incidence := incidence)
      backward root grid sourceCoefficient index hindex) :
    Proposition63FourCallPaperMassSeedAt
      (backward.loss index) (backward.loss (index + 1)) where
  leftFactor := data.paperLeft
  rightFactor := data.paperRight
  left_pos := data.paperLeft_pos
  left_finite := data.paperLeft_finite
  right_finite := data.paperRight_finite
  loss_gap := backward.loss_lt_next index hindex
  output_loss_pos := backward.loss_pos (index + 1) (by omega)
  absorption := data.massAbsorption

/-- Total paper scalar functions, extended by `1` outside the finite pair list. -/
noncomputable def proposition63FourCallPaperLeftFactor
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {sourceCoefficient : NNReal}
    (pair : ∀ index (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPaperScalarDataAt (incidence := incidence) backward
        root grid sourceCoefficient index hindex) (index : ℕ) : ENNReal :=
  if hindex : index < (finiteIntervalOrderedPairs gridN).length then
    (pair index hindex).paperLeft
  else 1

noncomputable def proposition63FourCallPaperRightFactor
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    {backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length}
    {root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {sourceCoefficient : NNReal}
    (pair : ∀ index (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPaperScalarDataAt (incidence := incidence) backward
        root grid sourceCoefficient index hindex) (index : ℕ) : ENNReal :=
  if hindex : index < (finiteIntervalOrderedPairs gridN).length then
    (pair index hindex).paperRight
  else 1

/-- Complete pre-runtime paper scalar family. -/
structure Proposition63FourCallPaperScalarFamilyData
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (sourceCoefficient : NNReal) where
  pair : ∀ index (hindex : index < (finiteIntervalOrderedPairs gridN).length),
    Proposition63FourCallPaperScalarDataAt (incidence := incidence) backward
      root grid sourceCoefficient index hindex

/-- Aggregate the paper per-index scalar choices.  Smallness receipts remain
attached to the global pre-runtime input, so this package does not manufacture
a fixed-`delta` cutoff from choices made at that same `delta`. -/
theorem proposition63_four_call_paper_scalar_family_of_pair
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (sourceCoefficient : NNReal)
    (pair : ∀ index (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPaperScalarDataAt (incidence := incidence) backward
        root grid sourceCoefficient index hindex) :
    Nonempty (Proposition63FourCallPaperScalarFamilyData
      (incidence := incidence) backward root grid sourceCoefficient) := by
  exact ⟨{ pair := pair }⟩

end Kakeya.Assouad.PureWZ2
