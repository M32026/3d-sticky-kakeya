import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperInnerScheduleRun
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPairScalarFamily

/-!
# Paper Lemma 4.11 at one query scale

This module assembles the pre-runtime data hidden by the stable one-query
producer.  Every scale, loss, cutoff, and nearby-scale schedule is fixed before
the inner iterator exposes its current shading.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The ordered-pair scale package is unique.  Although its constructor carries
proof fields, both numerical scales are forced by the grid and index: `tau` is
the second grid coordinate and `rhoHat` is the unique positive integral
multiple of `delta` in the half-open aligned interval. -/
theorem Proposition63FourCallOrderedPairIndexScales.eq_of_same_index
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN}
    (hdelta : 0 < delta)
    (first second : Proposition63FourCallOrderedPairIndexScales grid index) :
    first = second := by
  have hfactor : first.scaleFactor = second.scaleFactor := by
    apply le_antisymm
    · by_contra hnot
      have hsucc : second.scaleFactor + 1 ≤ first.scaleFactor := by omega
      have hmul :
          ((second.scaleFactor + 1 : ℕ) : ℝ) * delta ≤
            (first.scaleFactor : ℝ) * delta :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hsucc) hdelta.le
      have hfirstUpper := first.rhoHat_lt_logicalR_add_delta
      have hsecondLower := second.logicalR_le_rhoHat
      rw [first.rhoHat_aligned] at hfirstUpper
      rw [second.rhoHat_aligned] at hsecondLower
      push_cast at hmul
      linarith
    · by_contra hnot
      have hsucc : first.scaleFactor + 1 ≤ second.scaleFactor := by omega
      have hmul :
          ((first.scaleFactor + 1 : ℕ) : ℝ) * delta ≤
            (second.scaleFactor : ℝ) * delta :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hsucc) hdelta.le
      have hsecondUpper := second.rhoHat_lt_logicalR_add_delta
      have hfirstLower := first.logicalR_le_rhoHat
      rw [second.rhoHat_aligned] at hsecondUpper
      rw [first.rhoHat_aligned] at hfirstLower
      push_cast at hmul
      linarith
  have hrho : first.rhoHat = second.rhoHat := by
    apply Subtype.ext
    rw [first.rhoHat_aligned, second.rhoHat_aligned, hfactor]
  have htau : first.tau = second.tau :=
    first.tau_eq.trans second.tau_eq.symm
  cases first
  cases second
  simp_all

/-- For fixed output loss and ordered-pair scales the square-root package is
unique, because its requested scale is definitionally forced to `sqrt rhoHat`. -/
theorem Proposition63FourCallFrozenChoiceSqrtScalePackage.eq_of_same_scales
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {outputLoss : ℝ}
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    (first second :
      Proposition63FourCallFrozenChoiceSqrtScalePackage outputLoss scales) :
    first = second := by
  have hsqrt : first.sqrtRequested = second.sqrtRequested := by
    apply Subtype.ext
    exact first.sqrtScale_eq.trans second.sqrtScale_eq.symm
  cases first
  cases second
  simp_all

/-- The legacy robust-scale package is unique at fixed seed and pair scales. -/
theorem Proposition63FourCallFrozenRobustScalePackage.eq_of_same_scales
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {outputLoss : ℝ}
    {seed : Proposition63FourCallInnerLossSeed sigma outputLoss discreteLoss}
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    (first second : Proposition63FourCallFrozenRobustScalePackage seed scales) :
    first = second := by
  have hrequested : first.requested = second.requested := by
    apply Subtype.ext
    exact first.scale_eq.trans second.scale_eq.symm
  cases first
  cases second
  simp_all

/-- The legacy ancestry envelope is always positive and finite at a genuine
ordered-pair scale.  This is a scalar fact and does not use runtime geometry. -/
theorem proposition63FourCallAncestorRetentionUpper_pos_ne_top
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN index : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN}
    (rootFamily : Kakeya.Streamlined.TubeFamily delta)
    (root_nonempty : rootFamily.Nonempty)
    (scales : Proposition63FourCallOrderedPairIndexScales grid index)
    (firstOutputLoss secondNormalizationLoss secondSourceLoss
      rhoWeightLoss firstStageWeightLoss : ℝ)
    (rho_lt_one : scales.rhoHat.1 < 1) :
    0 < proposition63FourCallAncestorRetentionUpper rootFamily
        scales.rhoHat.1 sigma firstOutputLoss secondNormalizationLoss
        secondSourceLoss rhoWeightLoss firstStageWeightLoss ∧
      proposition63FourCallAncestorRetentionUpper rootFamily
        scales.rhoHat.1 sigma firstOutputLoss secondNormalizationLoss
        secondSourceLoss rhoWeightLoss firstStageWeightLoss ≠ ⊤ := by
  have rho_pos : 0 < scales.rhoHat.1 :=
    (grid.scale_pos _
      (scales.first_lt_second.le.trans scales.second_le_gridN)).trans_le
      scales.logicalR_le_rhoHat
  have rho_fraction := pure_refinement_fraction_pos_ne_top
    rho_pos rho_lt_one 61
  have regularization_one :=
    proposition63UniformReentryRegularizationLoss_pos_ne_top rootFamily
      (proposition63CanonicalNearbyLevelCount secondNormalizationLoss)
  have regularization_two :=
    proposition63UniformReentryRegularizationLoss_pos_ne_top rootFamily
      (proposition63CanonicalNearbyLevelCount (secondSourceLoss / 4))
  have c73_pos : (0 : ENNReal) < 73 / 100 := by norm_num
  have c73_top : (73 / 100 : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top (by norm_num) (by norm_num)
  have first_weight_pos : 0 < proposition63CanonicalReentryWeight
      scales.rhoHat.1 firstStageWeightLoss := by
    unfold proposition63CanonicalReentryWeight
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos rho_pos _)
  have first_weight_top : proposition63CanonicalReentryWeight
      scales.rhoHat.1 firstStageWeightLoss ≠ ⊤ :=
    proposition63CanonicalReentryWeight_ne_top
  have rho_weight_pos : 0 < proposition63CanonicalReentryWeight
      scales.rhoHat.1 rhoWeightLoss := by
    unfold proposition63CanonicalReentryWeight
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos rho_pos _)
  have rho_weight_top : proposition63CanonicalReentryWeight
      scales.rhoHat.1 rhoWeightLoss ≠ ⊤ :=
    proposition63CanonicalReentryWeight_ne_top
  have incoming_pos : 0 < proposition63FourCallIncomingRetentionUpper
      rootFamily scales.rhoHat.1 sigma firstOutputLoss := by
    unfold proposition63FourCallIncomingRetentionUpper
    have card_pos : 0 < rootFamily.enncard := by
      simp only [Kakeya.Streamlined.TubeFamily.enncard]
      exact_mod_cast root_nonempty
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos rho_pos _)).ne'
      card_pos.ne'
  have incoming_top : proposition63FourCallIncomingRetentionUpper
      rootFamily scales.rhoHat.1 sigma firstOutputLoss ≠ ⊤ := by
    unfold proposition63FourCallIncomingRetentionUpper
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
  have reentry_pos : 0 < proposition63FourCallReentryRetentionFormula
      (proposition63UniformReentryRegularizationLoss rootFamily
        (proposition63CanonicalNearbyLevelCount (secondSourceLoss / 4)))
      (proposition63CanonicalReentryWeight scales.rhoHat.1 rhoWeightLoss)
      (proposition63FourCallIncomingRetentionUpper rootFamily
        scales.rhoHat.1 sigma firstOutputLoss) := by
    unfold proposition63FourCallReentryRetentionFormula
    apply ENNReal.inv_pos.mpr
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.inv_ne_top.mpr regularization_two.1.ne')
        (ENNReal.mul_ne_top c73_top rho_weight_top))
      (ENNReal.inv_ne_top.mpr incoming_pos.ne')
  have reentry_top : proposition63FourCallReentryRetentionFormula
      (proposition63UniformReentryRegularizationLoss rootFamily
        (proposition63CanonicalNearbyLevelCount (secondSourceLoss / 4)))
      (proposition63CanonicalReentryWeight scales.rhoHat.1 rhoWeightLoss)
      (proposition63FourCallIncomingRetentionUpper rootFamily
        scales.rhoHat.1 sigma firstOutputLoss) ≠ ⊤ := by
    unfold proposition63FourCallReentryRetentionFormula
    apply ENNReal.inv_ne_top.mpr
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (ENNReal.inv_pos.mpr regularization_two.2).ne'
        (ENNReal.mul_pos c73_pos.ne' rho_weight_pos.ne').ne').ne'
      (ENNReal.inv_pos.mpr incoming_top).ne' |>.ne'
  unfold proposition63FourCallAncestorRetentionUpper
    proposition63FourCallPullbackRetentionFormula
  constructor
  · apply ENNReal.inv_pos.mpr
    exact ENNReal.mul_ne_top rho_fraction.2 <|
      ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.inv_ne_top.mpr regularization_one.1.ne')
          (ENNReal.mul_ne_top c73_top first_weight_top))
        (ENNReal.mul_ne_top rho_fraction.2
          (ENNReal.inv_ne_top.mpr reentry_pos.ne'))
  · apply ENNReal.inv_ne_top.mpr
    exact ((ENNReal.mul_pos_iff).2 ⟨rho_fraction.1,
      (ENNReal.mul_pos_iff).2 ⟨
        (ENNReal.mul_pos_iff).2 ⟨
          ENNReal.inv_pos.mpr regularization_one.2,
          (ENNReal.mul_pos_iff).2 ⟨c73_pos, first_weight_pos⟩⟩,
        (ENNReal.mul_pos_iff).2 ⟨rho_fraction.1,
          ENNReal.inv_pos.mpr reentry_top⟩⟩⟩).ne'

/-- Turn one canonical legacy scalar package and its frozen seed cutoff into
the complete legacy receipt.  The three cutoff hypotheses distinguish the
coarse scale, the original fine scale, and the pair-dependent interval
constant instead of conflating them. -/
noncomputable def Proposition63FourCallPairScalarDataAt.frozenReceipts
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale K : ℝ}
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
    (pair : Proposition63FourCallPairScalarDataAt (incidence := incidence)
      backward grid sourceCoefficient index hindex)
    (cutoff : Proposition63FourCallFrozenSeedCutoffData
      (backward.seed index hindex))
    (leftFactor rightFactor : ℕ → ENNReal)
    (_delta_pos : 0 < delta)
    (delta_le_rho_cutoff : delta ≤ cutoff.rhoCutoff)
    (delta_le_fine_cutoff : delta ≤ cutoff.fineCutoff)
    (delta_le_interval : delta ≤ pair.core.nestedInterval.delta₀)
    (rho_le_cutoff : pair.scales.rhoHat.1 ≤ cutoff.rhoCutoff)
    (coefficient_one : 1 ≤
      (((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ))
    (amplified_query_small : Real.rpow queryScale (discreteLoss / 2) ≤
      1 / (16 * (((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)))
    (hleft : leftFactor index =
      proposition63FourCallFrozenActualLeftFactor
        root.normalization.croppedFamily delta pair.scales.rhoHat.1 sigma
        (backward.seed index hindex).schedule.firstOutputLoss
        (backward.currentWeightLoss index hindex) 61
        (proposition63FourCallAncestorRetentionUpper
          root.normalization.croppedFamily pair.scales.rhoHat.1 sigma
          (backward.seed index hindex).schedule.firstOutputLoss
          (backward.seed index hindex).schedule.second.normalizationLoss
          (backward.seed index hindex).schedule.second.sourceLoss
          (backward.seed index hindex).rhoWeightLoss
          (backward.seed index hindex).firstStageWeightLoss)
        (proposition63FourCallFrozenLineCoverBase
          pair.core.cell.cellVolumeFloor pair.sqrtPackage.sqrtRequested.1
          pair.core.cover.coverBudget)
        (proposition63CanonicalReentryWeight pair.scales.rhoHat.1
          (backward.seed index hindex).nextWeightLoss))
    (hright : rightFactor index =
      proposition63UniformDependentRightFactor
        root.normalization.croppedFamily pair.core.level.uniformLevel) :
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
      (backward.seed index hindex) sourceCoefficient index pair.scales
      pair.sqrtPackage pair.robustPackage.requested := by
  let seed := backward.seed index hindex
  have rho_pos : 0 < pair.scales.rhoHat.1 :=
    (grid.scale_pos _
      (pair.scales.first_lt_second.le.trans
        pair.scales.second_le_gridN)).trans_le
      pair.scales.logicalR_le_rhoHat
  have hscaleSmall := pair.scales.scale_smallness coefficient_one
    (by
      have hangular := seed.paperAngularExponent_pos
      have hupper : seed.paperAngularExponent ≤ discreteLoss / 4 := by
        rw [seed.paperAngularExponent_eq]
        exact min_le_left _ _
      linarith) amplified_query_small
  exact {
    hdeltaFirstCall := delta_le_rho_cutoff.trans cutoff.rhoCutoff_le_first
    hcellError := by
      have hsqrtThree : Real.sqrt 3 ≤ 2 := by
        nlinarith [Real.sqrt_nonneg 3,
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
      have hcoefficient : 0 ≤
          ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) :=
        by positivity
      have hsmall := hscaleSmall.1.trans pair.scales.tau_le_one
      have hmul :
          ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
              (pair.scales.rhoHat.1 * Real.sqrt 3) ≤
            ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
              (pair.scales.rhoHat.1 * 2) := by gcongr
      push_cast at hsmall
      calc
        ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
              (pair.scales.rhoHat.1 * Real.sqrt 3) ≤
            ((lipschitzExtensionConstant Point3 * sourceCoefficient : NNReal) : ℝ) *
              (pair.scales.rhoHat.1 * 2) := hmul
        _ = (1 / 16 : ℝ) *
              (8 * (4 *
                ((lipschitzExtensionConstant Point3 * sourceCoefficient :
                  NNReal) : ℝ)) * pair.scales.rhoHat.1) := by ring
        _ ≤ (1 / 16 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hsmall (by norm_num)
        _ ≤ 1 / 2 := by norm_num
    hrhoAbsorption := rho_le_cutoff.trans cutoff.rhoCutoff_le_rhoAbsorption
    hdeltaSecondCall := rho_le_cutoff.trans cutoff.rhoCutoff_le_second
    hdeltaThirdCall := rho_le_cutoff.trans cutoff.rhoCutoff_le_third
    hdeltaFirstStage :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_firstStageAbsorption
    hsourceOuter := by
      rw [seed.outerExtremalLoss_eq]
      exact seed.schedule.second.normalizationLoss_lt_output.le.trans <| by
        rw [seed.schedule.secondOutputLoss_eq]
    houterExtremalLoss := by
      rw [seed.outerExtremalLoss_eq]
      exact div_pos seed.schedule.third.sourceLoss_pos (by norm_num)
    hrhoOuterRetention :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_outerRetentionAbsorption
    houterTargetReentry := by
      rw [seed.outerExtremalLoss_eq]
      linarith [seed.schedule.third.sourceLoss_pos]
    hdeltaFirstGrid :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_firstGridAbsorption
    hdeltaFirstCross :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_firstCrossAbsorption
    hdeltaFirstBoundary :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_firstBoundaryAbsorption
    hrobustSmall := by
      rw [pair.robustPackage.scale_eq]
      exact cutoff.robustScale_small pair.scales.rhoHat.1 rho_pos rho_le_cutoff
    hsigma := by
      linarith [seed.paperAngularExponent_pos,
        seed.paperAngularExponent_lt_sigma]
    hsigmaOne := seed.sigma_lt_one
    logScale := cutoff.rhoCutoff
    hdeltaLog := rho_le_cutoff
    hlog := by
      intro _ scale hscale hscaleCutoff k hk hkUpper
      exact cutoff.cordobaLog scale hscale hscaleCutoff k hk hkUpper
    haxis := cutoff.cordobaAxis pair.scales.rhoHat.1 rho_pos rho_le_cutoff
    firstConstant := pair.core.first.firstConstant
    hfirstArithmetic := pair.core.first.arithmetic
    hrhoParentRetention :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_parentRetentionAbsorption
    hdeltaFirstRestore :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_firstRestoreAbsorption
    hdeltaSecondReentry :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_secondReentryAbsorption
    hdeltaFourth := rho_le_cutoff.trans cutoff.rhoCutoff_le_fourth
    hdeltaSecondBoundary :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_secondBoundaryAbsorption
    hdeltaSecondGrid :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_secondGridAbsorption
    hdeltaSecondCross :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_secondCrossAbsorption
    htargetRobustSmall := by
      rw [pair.robustPackage.scale_eq]
      exact cutoff.robustScale_small pair.scales.rhoHat.1 rho_pos rho_le_cutoff
    finalConstant := pair.core.final.finalConstant
    hfinalArithmetic := pair.core.final.arithmetic
    hdeltaSecondRestore :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_secondRestoreAbsorption
    hdeltaMultiplicity :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_multiplicityAbsorption
    hrhoBalancingBoundary :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_balancingBoundaryAbsorption
    hdeltaBalancing :=
      rho_le_cutoff.trans cutoff.rhoCutoff_le_balancingAbsorption
    cellVolumeFloor := pair.core.cell.cellVolumeFloor
    outputCandidateLoss := pair.core.next.outputCandidateLoss
    spatialScale := pair.core.next.spatialScale
    coarseCritical := rho_le_cutoff.trans cutoff.rhoCutoff_le_critical
    hcriticalTrace := rho_le_cutoff.trans cutoff.rhoCutoff_le_traceAbsorption
    cellVolumeFloor_pos := pair.core.cell.positive
    cellBudget := pair.core.cell.budget
    coverBudget := pair.core.cover.coverBudget
    hcoverBudgetPos := pair.core.cover.positive
    hcoverBudget := pair.core.cover.bound
    hsqrtConstantFinite := pair.core.final.finite
    hdeltaAlignedAbsorption :=
      delta_le_fine_cutoff.trans cutoff.fineCutoff_le_alignedAbsorption
    intervalAbsorption := pair.core.nestedInterval
    hdeltaIntervalAbsorption := delta_le_interval
    uniformLevel := pair.core.level.uniformLevel
    hleftFactor := hleft
    hrightFactor := hright
    hcurrentLevel := pair.core.level.current_le
    hpaperNestedLevel := pair.core.hpaperNestedLevel
    hnestedLevel := pair.core.level.nested_le
  }

/-- The legacy left factor attached to a canonical family of pair-scalar
choices.  This remains separate from the paper iterator factor. -/
noncomputable def proposition63FourCallLegacyLeftFactor
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
      Proposition63FourCallPairScalarDataAt (incidence := incidence) backward
        grid sourceCoefficient index hindex) (index : ℕ) : ENNReal :=
  if hindex : index < (finiteIntervalOrderedPairs gridN).length then
    proposition63FourCallFrozenActualLeftFactor
      root.normalization.croppedFamily delta
      (pair index hindex).scales.rhoHat.1 sigma
      (backward.seed index hindex).schedule.firstOutputLoss
      (backward.currentWeightLoss index hindex) 61
      (proposition63FourCallAncestorRetentionUpper
        root.normalization.croppedFamily (pair index hindex).scales.rhoHat.1
        sigma (backward.seed index hindex).schedule.firstOutputLoss
        (backward.seed index hindex).schedule.second.normalizationLoss
        (backward.seed index hindex).schedule.second.sourceLoss
        (backward.seed index hindex).rhoWeightLoss
        (backward.seed index hindex).firstStageWeightLoss)
      (proposition63FourCallFrozenLineCoverBase
        (pair index hindex).core.cell.cellVolumeFloor
        (pair index hindex).sqrtPackage.sqrtRequested.1
        (pair index hindex).core.cover.coverBudget)
      (proposition63CanonicalReentryWeight
        (pair index hindex).scales.rhoHat.1
        (backward.seed index hindex).nextWeightLoss)
  else 1

/-- The matching legacy right factor for the canonical pair-scalar family. -/
noncomputable def proposition63FourCallLegacyRightFactor
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
      Proposition63FourCallPairScalarDataAt (incidence := incidence) backward
        grid sourceCoefficient index hindex) (index : ℕ) : ENNReal :=
  if hindex : index < (finiteIntervalOrderedPairs gridN).length then
    proposition63UniformDependentRightFactor root.normalization.croppedFamily
      (pair index hindex).core.level.uniformLevel
  else 1

/-- Assemble the legacy geometry-global record from canonical pair scalars and
honest fine/coarse cutoff receipts.  The result is still independent of the
runtime current shading. -/
theorem proposition63_four_call_legacy_global_of_pair
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
    (sourceCoefficient : NNReal)
    (pair : ∀ index (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPairScalarDataAt (incidence := incidence) backward
        grid sourceCoefficient index hindex)
    (cutoff : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallFrozenSeedCutoffData (backward.seed index hindex))
    (delta_pos : 0 < delta)
    (discreteLoss_pos : 0 < discreteLoss)
    (discreteLoss_lt_half : discreteLoss < 1 / 2)
    (query_small : 2 * Real.rpow queryScale (discreteLoss / 2) ≤ 1)
    (delta_le_query : delta ≤ queryScale)
    (sqrt_query_small : 2 * Real.sqrt queryScale ≤ 1)
    (outputLoss_le_half : gridOutputLoss ≤ 1 / 2)
    (coefficient_one : 1 ≤
      (((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ))
    (amplified_query_small : Real.rpow queryScale (discreteLoss / 2) ≤
      1 / (16 * (((4 : NNReal) *
        (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)))
    (rho_small : ∀ index
      (_hindex : index < (finiteIntervalOrderedPairs gridN).length),
      ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
        scales.rhoHat.1 ≤ 1 / 144)
    (rho_le_cutoff : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
        scales.rhoHat.1 ≤ (cutoff index hindex).rhoCutoff)
    (delta_le_rho_cutoff : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (cutoff index hindex).rhoCutoff)
    (delta_le_fine_cutoff : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (cutoff index hindex).fineCutoff)
    (delta_le_interval : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (pair index hindex).core.nestedInterval.delta₀)
    (firstOutput_gap_small : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        Real.rpow delta (discreteLoss -
          (backward.seed index hindex).schedule.firstOutputLoss) ≤ 1 / 2)
    (hdeltaCurrentReentry : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
        delta ≤ (proposition63_four_call_inner_current_reentry_schedule_at
          backward source root index hindex).density_absorb.delta₀) :
    Nonempty (Proposition63FourCallFrozenChoiceGlobalData
      (incidence := incidence) K backward root grid
      (proposition63FourCallLegacyLeftFactor (root := root) pair)
      (proposition63FourCallLegacyRightFactor (root := root) pair)
      sourceCoefficient) := by
  let legacyLeft := proposition63FourCallLegacyLeftFactor (root := root) pair
  let legacyRight := proposition63FourCallLegacyRightFactor (root := root) pair
  refine ⟨{
    delta_pos := delta_pos
    discreteLoss_pos := discreteLoss_pos
    discreteLoss_lt_half := discreteLoss_lt_half
    query_small := query_small
    delta_le_query := delta_le_query
    sqrt_query_small := sqrt_query_small
    outputLoss_le_half := outputLoss_le_half
    coefficient_one := coefficient_one
    amplified_query_small := amplified_query_small
    rho_small := rho_small
    firstOutputLoss_le_discrete := ?_
    firstOutputLoss_lt_discrete := ?_
    firstOutput_gap_small := firstOutput_gap_small
    hdeltaCurrentReentry := hdeltaCurrentReentry
    scalar_receipts := ?_
  }⟩
  · intro index hindex
    let seed := backward.seed index hindex
    exact seed.schedule.firstOutputLoss_lt_secondSource.le.trans <|
      seed.schedule.second.sourceLoss_le_half.trans <|
        (half_le_self seed.schedule.second.normalizationLoss_pos.le).trans <|
          seed.schedule.second.normalizationLoss_lt_output.le.trans
            seed.secondOutputLoss_le_discrete
  · intro index hindex
    let seed := backward.seed index hindex
    exact seed.schedule.firstOutputLoss_lt_secondSource.trans_le <|
      seed.schedule.second.sourceLoss_le_half.trans <|
        (half_le_self seed.schedule.second.normalizationLoss_pos.le).trans <|
          seed.schedule.second.normalizationLoss_lt_output.le.trans
            seed.secondOutputLoss_le_discrete
  · intro index hindex scales sqrtPackage
    have hscales : scales = (pair index hindex).scales :=
      scales.eq_of_same_index delta_pos (pair index hindex).scales
    subst scales
    have hsqrt : sqrtPackage = (pair index hindex).sqrtPackage :=
      sqrtPackage.eq_of_same_scales (pair index hindex).sqrtPackage
    subst sqrtPackage
    let canonicalRobust := (pair index hindex).scales.choiceRobustScalePackage
      (backward.seed index hindex) discreteLoss_lt_half
    have hrobust : canonicalRobust = (pair index hindex).robustPackage :=
      canonicalRobust.eq_of_same_scales (pair index hindex).robustPackage
    change Proposition63FourCallFrozenScalarReceiptsAt root grid backward.loss
      legacyLeft legacyRight (backward.seed index hindex).schedule
      (backward.seed index hindex) sourceCoefficient index
      (pair index hindex).scales (pair index hindex).sqrtPackage
      canonicalRobust.requested
    rw [hrobust]
    apply (pair index hindex).frozenReceipts (root := root)
      (cutoff index hindex) legacyLeft legacyRight delta_pos
      (delta_le_rho_cutoff index hindex)
      (delta_le_fine_cutoff index hindex)
      (delta_le_interval index hindex)
      (rho_le_cutoff index hindex (pair index hindex).scales)
      coefficient_one amplified_query_small
    · simp only [legacyLeft, proposition63FourCallLegacyLeftFactor, dif_pos hindex]
    · simp only [legacyRight, proposition63FourCallLegacyRightFactor,
        dif_pos hindex]

/-- Assemble the complete paper scalar family from the already frozen global
geometry.  The only additional hypotheses are genuine sign information: strict
smallness of `delta` and nonnegativity of the incidence parameter. -/
theorem proposition63_four_call_paper_scalar_family_producer
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    {K : ℝ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (legacyLeft legacyRight : ℕ → ENNReal)
    (sourceCoefficient : NNReal)
    (paperGlobal : Proposition63FourCallPaperGlobalData
      (incidence := incidence) K backward root grid legacyLeft legacyRight
      sourceCoefficient)
    (delta_lt_one : delta < 1)
    (incidence_nonneg : 0 ≤ incidence) :
    Nonempty (Proposition63FourCallPaperScalarFamilyData
      (incidence := incidence) backward root grid sourceCoefficient) := by
  let pair : ∀ index
      (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPaperScalarDataAt (incidence := incidence) backward
        root grid sourceCoefficient index hindex := fun index hindex => by
    let seed := backward.seed index hindex
    have hancestor : ∀ scales :
        Proposition63FourCallOrderedPairIndexScales grid index,
        0 < proposition63FourCallAncestorRetentionUpper
              root.normalization.croppedFamily scales.rhoHat.1 sigma
              seed.schedule.firstOutputLoss
              seed.schedule.second.normalizationLoss
              seed.schedule.second.sourceLoss seed.rhoWeightLoss
              seed.firstStageWeightLoss ∧
          proposition63FourCallAncestorRetentionUpper
              root.normalization.croppedFamily scales.rhoHat.1 sigma
              seed.schedule.firstOutputLoss
              seed.schedule.second.normalizationLoss
              seed.schedule.second.sourceLoss seed.rhoWeightLoss
              seed.firstStageWeightLoss ≠ ⊤ := by
      intro scales
      exact proposition63FourCallAncestorRetentionUpper_pos_ne_top
        root.normalization.croppedFamily
        root.normalization.final_extremal.nonempty scales
        seed.schedule.firstOutputLoss seed.schedule.second.normalizationLoss
        seed.schedule.second.sourceLoss seed.rhoWeightLoss
        seed.firstStageWeightLoss
        ((paperGlobal.prelude.rho_small index hindex scales).trans_lt
          (by norm_num))
    exact Classical.choice <| proposition63_four_call_paper_scalar_data_at
      backward root grid sourceCoefficient index hindex
      paperGlobal.prelude.delta_pos delta_lt_one seed.sigma_lt_one
      paperGlobal.prelude.discreteLoss_pos
      paperGlobal.prelude.discreteLoss_lt_half incidence_nonneg
      paperGlobal.incidence_le_delta paperGlobal.prelude.coefficient_one
      paperGlobal.prelude.query_small paperGlobal.prelude.delta_le_query
      paperGlobal.prelude.sqrt_query_small
      (paperGlobal.prelude.rho_small index hindex)
      (paperGlobal.firstUniformCutoff index hindex)
      (paperGlobal.delta_le_firstUniformCutoff index hindex)
      (fun scales => (hancestor scales).1)
      (fun scales => (hancestor scales).2)
  exact proposition63_four_call_paper_scalar_family_of_pair backward root grid
    sourceCoefficient pair

/-- Canonical pair-scalar family used by the stable one-query producer. -/
noncomputable def proposition63Lemma411PairFamily
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
    (delta_pos : 0 < delta) (delta_lt_one : delta < 1)
    (sigma_lt_one : sigma < 1) (discreteLoss_pos : 0 < discreteLoss)
    (discreteLoss_lt_half : discreteLoss < 1 / 2)
    (query_small : 2 * Real.rpow queryScale (discreteLoss / 2) ≤ 1)
    (delta_le_query : delta ≤ queryScale)
    (sqrt_query_small : 2 * Real.sqrt queryScale ≤ 1)
    (outputLoss_le_half : gridOutputLoss ≤ 1 / 2)
    (rho_small : ∀ index
      (_hindex : index < (finiteIntervalOrderedPairs gridN).length),
      ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
        scales.rhoHat.1 ≤ 1 / 144) :
    Proposition63FourCallPairScalarFamilyData (incidence := incidence)
      backward root grid sourceCoefficient :=
  Classical.choice <| proposition63_four_call_pair_scalar_family
    (incidence := incidence) backward root grid sourceCoefficient delta_pos
    delta_lt_one sigma_lt_one discreteLoss_pos discreteLoss_lt_half
    query_small delta_le_query sqrt_query_small outputLoss_le_half rho_small
    (fun index hindex scales =>
      (rho_small index hindex scales).trans (by norm_num))

/-- Canonical family-free cutoff for one frozen loss seed. -/
noncomputable def proposition63Lemma411SeedCutoff
    {sigma gridOutputLoss discreteLoss : ℝ} {gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (index : ℕ)
    (hindex : index < (finiteIntervalOrderedPairs gridN).length) :
    Proposition63FourCallFrozenSeedCutoffData
      (backward.seed index hindex) :=
  Classical.choice <| proposition63_four_call_frozen_seed_cutoff
    (backward.seed index hindex)

/-- Canonical paper-global cutoff package. -/
noncomputable def proposition63Lemma411PaperGlobalCutoff
    {delta sigma inputLoss discreteLoss gridOutputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent gridN : ℕ}
    (backward : Proposition63FourCallInnerBackwardLossSchedule sigma
      gridOutputLoss discreteLoss (finiteIntervalOrderedPairs gridN).length)
    (root : Proposition63RootNormalizationData
      (outputLoss := backward.rootNormalizationLoss) source
      normalizationExponent backward.rootDensityLoss)
    (sourceCoefficient : NNReal)
    (inputLoss_lt_density : inputLoss < backward.rootDensityLoss) :
    Proposition63FourCallPaperGlobalCutoffData
      (inputLoss := inputLoss) backward sourceCoefficient :=
  Classical.choice <|
    proposition63_four_call_paper_global_cutoff backward sourceCoefficient
      inputLoss_lt_density

/-- All loss and grid choices for one application of Lemma 4.11.  These data
are selected before the fine scale, query scale, root configuration, or
runtime current shading is exposed. -/
structure Proposition63Lemma411ScheduleData
    (sigma gridOutputLoss : ℝ) where
  gridSchedule : Proposition63InnerIntervalGridScheduleData
    sigma gridOutputLoss
  backward : Proposition63FourCallInnerBackwardLossSchedule sigma
    gridOutputLoss gridSchedule.discreteLoss
      (finiteIntervalOrderedPairs gridSchedule.gridN).length
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  output_loss_le_half : gridOutputLoss ≤ 1 / 2
  discrete_loss_lt_half : gridSchedule.discreteLoss < 1 / 2

/-- Freeze the complete one-query loss hierarchy and inner grid schedule. -/
theorem proposition63_lemma411_schedule
    (sigma : ℝ) (critical : PureWZ2CriticalPackage sigma)
    (gridOutputLoss floorLoss : ℝ)
    (gridOutputLoss_pos : 0 < gridOutputLoss)
    (gridOutputLoss_le_half : gridOutputLoss ≤ 1 / 2)
    (floorLoss_pos : 0 < floorLoss)
    (gridOutputLoss_lt_sigma : gridOutputLoss < 2 * sigma / 5) :
    Nonempty (Proposition63Lemma411ScheduleData sigma gridOutputLoss) := by
  let gridSchedule := Classical.choice <|
    proposition63_inner_interval_grid_schedule sigma gridOutputLoss
      critical.sigma_pos critical.sigma_lt_one gridOutputLoss_pos
      gridOutputLoss_le_half
  have discrete_lt_half : gridSchedule.discreteLoss < 1 / 2 := by
    rw [gridSchedule.discrete_loss_eq]
    linarith
  have discrete_lt_sigma : gridSchedule.discreteLoss < sigma / 10 := by
    rw [gridSchedule.discrete_loss_eq]
    linarith
  let backward := Classical.choice <|
    proposition63_four_call_inner_backward_loss_schedule sigma critical
      gridOutputLoss floorLoss gridSchedule.discreteLoss gridOutputLoss_pos
      (gridOutputLoss_le_half.trans (by norm_num)) floorLoss_pos
      gridSchedule.discrete_loss_pos discrete_lt_half discrete_lt_sigma
      (finiteIntervalOrderedPairs gridSchedule.gridN).length
  exact ⟨{
    gridSchedule := gridSchedule
    backward := backward
    sigma_pos := critical.sigma_pos
    sigma_lt_one := critical.sigma_lt_one
    output_loss_le_half := gridOutputLoss_le_half
    discrete_loss_lt_half := discrete_lt_half
  }⟩

/-- Scalar and root-dependent smallness facts which precede every canonical
pair/cutoff choice.  No field depends on the runtime current shading. -/
structure Proposition63Lemma411ScalarSmallnessData
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
  delta_lt_one : delta < 1
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  discrete_loss_pos : 0 < discreteLoss
  discrete_loss_lt_half : discreteLoss < 1 / 2
  output_loss_le_half : gridOutputLoss ≤ 1 / 2
  coefficient_one : 1 ≤
    (((4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ)
  query_small : 2 * Real.rpow queryScale (discreteLoss / 2) ≤ 1
  delta_le_query : delta ≤ queryScale
  sqrt_query_small : 2 * Real.sqrt queryScale ≤ 1
  amplified_query_small : Real.rpow queryScale (discreteLoss / 2) ≤
    1 / (16 * (((4 : NNReal) *
      (lipschitzExtensionConstant Point3 * sourceCoefficient)) : ℝ))
  incidence_nonneg : 0 ≤ incidence
  incidence_le_delta : incidence ≤ delta
  rho_small : ∀ index
    (_hindex : index < (finiteIntervalOrderedPairs gridN).length),
    ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
      scales.rhoHat.1 ≤ 1 / 144
  firstOutput_gap_small : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Real.rpow delta (discreteLoss -
        (backward.seed index hindex).schedule.firstOutputLoss) ≤ 1 / 2

/-- The exact canonical pair family selected from scalar smallness. -/
noncomputable def Proposition63Lemma411ScalarSmallnessData.pairFamily
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
    (data : Proposition63Lemma411ScalarSmallnessData
      (incidence := incidence) backward root grid sourceCoefficient) :
    Proposition63FourCallPairScalarFamilyData (incidence := incidence)
      backward root grid sourceCoefficient :=
  proposition63Lemma411PairFamily backward root grid sourceCoefficient
    root.normalization.final_extremal.delta_pos data.delta_lt_one
    data.sigma_lt_one data.discrete_loss_pos data.discrete_loss_lt_half
    data.query_small data.delta_le_query
    data.sqrt_query_small data.output_loss_le_half data.rho_small

/-- The paper-only scalar prelude extracted before any pair-local nested
interval cutoff is selected. -/
noncomputable def Proposition63Lemma411ScalarSmallnessData.paperPrelude
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale K : ℝ}
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
    (data : Proposition63Lemma411ScalarSmallnessData
      (incidence := incidence) backward root grid sourceCoefficient) :
    Proposition63FourCallPaperPreludeGlobalData (incidence := incidence) K
      backward root grid
      proposition63FourCallPaperPlaceholderFactor
      proposition63FourCallPaperPlaceholderFactor sourceCoefficient := {
  delta_pos := root.normalization.final_extremal.delta_pos
  discreteLoss_pos := data.discrete_loss_pos
  discreteLoss_lt_half := data.discrete_loss_lt_half
  query_small := data.query_small
  delta_le_query := data.delta_le_query
  sqrt_query_small := data.sqrt_query_small
  outputLoss_le_half := data.output_loss_le_half
  coefficient_one := data.coefficient_one
  amplified_query_small := data.amplified_query_small
  rho_small := data.rho_small
  firstOutput_gap_small := data.firstOutput_gap_small
}

/-- Smallness facts for the exact canonical legacy pair/cutoff family. -/
structure Proposition63Lemma411LegacySmallnessData
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
  scalar : Proposition63Lemma411ScalarSmallnessData
    (incidence := incidence) backward root grid sourceCoefficient
  rho_le_legacy_cutoff : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
    ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
      scales.rhoHat.1 ≤
        (proposition63Lemma411SeedCutoff backward index hindex).rhoCutoff
  delta_le_legacy_rho_cutoff : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      delta ≤ (proposition63Lemma411SeedCutoff backward index hindex).rhoCutoff
  delta_le_legacy_fine_cutoff : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      delta ≤ (proposition63Lemma411SeedCutoff backward index hindex).fineCutoff
  delta_le_legacy_interval : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      delta ≤ (scalar.pairFamily.pair index hindex).core.nestedInterval.delta₀
  hdeltaCurrentReentry : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      delta ≤ (proposition63_four_call_inner_current_reentry_schedule_at
        backward source root index hindex).density_absorb.delta₀

/-- Canonical legacy global data built from its exact receipts. -/
noncomputable def Proposition63Lemma411LegacySmallnessData.legacyGlobal
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale K : ℝ}
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
    (data : Proposition63Lemma411LegacySmallnessData
      (incidence := incidence) backward root grid sourceCoefficient) :
    Proposition63FourCallFrozenChoiceGlobalData (incidence := incidence) K
      backward root grid
      (proposition63FourCallLegacyLeftFactor (root := root)
        data.scalar.pairFamily.pair)
      (proposition63FourCallLegacyRightFactor (root := root)
        data.scalar.pairFamily.pair) sourceCoefficient :=
  Classical.choice <| proposition63_four_call_legacy_global_of_pair K backward
    root grid sourceCoefficient data.scalar.pairFamily.pair
    (proposition63Lemma411SeedCutoff backward)
    root.normalization.final_extremal.delta_pos
    data.scalar.discrete_loss_pos data.scalar.discrete_loss_lt_half
    data.scalar.query_small data.scalar.delta_le_query
    data.scalar.sqrt_query_small data.scalar.output_loss_le_half
    data.scalar.coefficient_one data.scalar.amplified_query_small
    data.scalar.rho_small data.rho_le_legacy_cutoff
    data.delta_le_legacy_rho_cutoff data.delta_le_legacy_fine_cutoff
    data.delta_le_legacy_interval data.scalar.firstOutput_gap_small
    data.hdeltaCurrentReentry

/-- Smallness facts for the exact canonical paper-global cutoff. -/
structure Proposition63Lemma411PaperGlobalSmallnessData
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
  scalar : Proposition63Lemma411ScalarSmallnessData
    (incidence := incidence) backward root grid sourceCoefficient
  cutoff : Proposition63FourCallPaperGlobalCutoffData
    (inputLoss := inputLoss) backward sourceCoefficient
  rho_le_paper_common :
    ∀ index (_hindex : index <
      (finiteIntervalOrderedPairs gridN).length),
    ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
      scales.rhoHat.1 ≤
        cutoff.rhoCommon.delta₀
  delta_le_paper_common : delta ≤
    cutoff.deltaCommon.delta₀

/-- Pairwise version of the paper-global smallness package.  It removes the
unnecessary requirement that every ordered-pair scale lie below one common
minimum while retaining a single common cutoff for the fine input scale. -/
structure Proposition63Lemma411PaperPairwiseSmallnessData
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
  scalar : Proposition63Lemma411ScalarSmallnessData
    (incidence := incidence) backward root grid sourceCoefficient
  paperCutoff : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallPaperSeedCutoffData
        (backward.seed index hindex)
        ((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient))
  firstUniformCutoff : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63FourCallFirstUniformCutoffData
        (backward.seed index hindex)
        ((4 : NNReal) *
          (lipschitzExtensionConstant Point3 * sourceCoefficient))
  currentReentryAbsorption : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63CurrentReentryAbsorptionData
        inputLoss backward.rootNormalizationLoss backward.rootDensityLoss
        (backward.loss index) (backward.currentWeightLoss index hindex)
        (backward.seed index hindex).schedule.first.sourceLoss
        (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss)
  finalCandidateLiftAbsorption : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      Proposition63ReentryDensityLiftAbsorptionData
        (backward.currentWeightLoss index hindex)
        (backward.seed index hindex).goodCellCandidateLoss
        (backward.loss (index + 1))
        (proposition63CanonicalNearbyLevelCount backward.rootNormalizationLoss)
  rho_le_paper_pair : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
    ∀ scales : Proposition63FourCallOrderedPairIndexScales grid index,
      scales.rhoHat.1 ≤ (paperCutoff index hindex).rhoCutoff
  delta_le_current : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      delta ≤ (currentReentryAbsorption index hindex).delta₀
  delta_le_final : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      delta ≤ (finalCandidateLiftAbsorption index hindex).delta₀
  delta_le_aligned : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      delta ≤ (backward.seed index hindex).alignedAbsorption.delta₀
  delta_le_first : ∀ index
    (hindex : index < (finiteIntervalOrderedPairs gridN).length),
      delta ≤ (firstUniformCutoff index hindex).nested.delta₀

/-- Canonical paper global package from pairwise coarse-scale bounds. -/
noncomputable def Proposition63Lemma411PaperPairwiseSmallnessData.paperGlobal
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale K : ℝ}
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
    (data : Proposition63Lemma411PaperPairwiseSmallnessData
      (incidence := incidence) backward root grid sourceCoefficient) :
    Proposition63FourCallPaperGlobalData (incidence := incidence) K backward
      root grid
      proposition63FourCallPaperPlaceholderFactor
      proposition63FourCallPaperPlaceholderFactor sourceCoefficient :=
  proposition63_four_call_paper_global_data_of_pairwise
    K backward root grid proposition63FourCallPaperPlaceholderFactor
    proposition63FourCallPaperPlaceholderFactor sourceCoefficient
    (data.scalar.paperPrelude (K := K)) data.paperCutoff
    data.firstUniformCutoff data.currentReentryAbsorption
    data.finalCandidateLiftAbsorption data.rho_le_paper_pair
    data.delta_le_current data.delta_le_final data.delta_le_aligned
    data.delta_le_first
    data.scalar.incidence_le_delta

/-- Canonical paper scalar family built from the pairwise paper-global
package.  This is the active M9 route; it retains each ordered pair's own
coarse cutoff instead of introducing a common rho threshold. -/
noncomputable def Proposition63Lemma411PaperPairwiseSmallnessData.scalarFamily
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale K : ℝ}
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
    (data : Proposition63Lemma411PaperPairwiseSmallnessData
      (incidence := incidence) backward root grid sourceCoefficient) :
    Proposition63FourCallPaperScalarFamilyData (incidence := incidence)
      backward root grid sourceCoefficient :=
  Classical.choice <| proposition63_four_call_paper_scalar_family_producer
    backward root grid proposition63FourCallPaperPlaceholderFactor
    proposition63FourCallPaperPlaceholderFactor sourceCoefficient
    (data.paperGlobal (K := K)) data.scalar.delta_lt_one
    data.scalar.incidence_nonneg

/-- Canonical paper global package. -/
noncomputable def Proposition63Lemma411PaperGlobalSmallnessData.paperGlobal
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale K : ℝ}
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
    (data : Proposition63Lemma411PaperGlobalSmallnessData
      (incidence := incidence) backward root grid sourceCoefficient) :
    Proposition63FourCallPaperGlobalData (incidence := incidence) K backward
      root grid
      proposition63FourCallPaperPlaceholderFactor
      proposition63FourCallPaperPlaceholderFactor sourceCoefficient :=
  Classical.choice <| proposition63_four_call_paper_global_producer K backward
    root grid proposition63FourCallPaperPlaceholderFactor
    proposition63FourCallPaperPlaceholderFactor sourceCoefficient
    (data.scalar.paperPrelude (K := K))
    data.cutoff
    data.rho_le_paper_common data.delta_le_paper_common
    data.scalar.incidence_le_delta

/-- Canonical paper scalar family built from the canonical paper global. -/
noncomputable def Proposition63Lemma411PaperGlobalSmallnessData.scalarFamily
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale K : ℝ}
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
    (data : Proposition63Lemma411PaperGlobalSmallnessData
      (incidence := incidence) backward root grid sourceCoefficient) :
    Proposition63FourCallPaperScalarFamilyData (incidence := incidence)
      backward root grid sourceCoefficient :=
  Classical.choice <| proposition63_four_call_paper_scalar_family_producer
    backward root grid proposition63FourCallPaperPlaceholderFactor
    proposition63FourCallPaperPlaceholderFactor sourceCoefficient
    (data.paperGlobal (K := K)) data.scalar.delta_lt_one
    data.scalar.incidence_nonneg

/-- Final pre-current smallness receipt for the exact canonical paper scalar
family selected from the preceding canonical global package. -/
structure Proposition63Lemma411UniformSmallnessData
    {delta sigma inputLoss incidence discreteLoss intervalLoss
      gridOutputLoss queryScale K : ℝ}
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
  global : Proposition63Lemma411PaperPairwiseSmallnessData
    (incidence := incidence) backward root grid sourceCoefficient

/-- One Lemma 4.11 output together with the one-step mass receipt needed by
the outer Lemma 4.12 recursion.  The mass factor is an audit ledger only; the
stored extremality and CWA are those proved locally by the one-query run. -/
structure Proposition63Lemma411OneQueryStepData
    {delta sigma outputLoss queryScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (current : WZ1PaperTubeShading family)
    (planeMap : {point : Point3 // point ∈ current.union} → Point3) where
  oneQuery : PureWZ2OneScaleLocalGrainData
    (sigma := sigma) (outputLoss := outputLoss) (rho := queryScale)
    (Y := current) planeMap
  massLoss : ENNReal
  massLoss_pos : 0 < massLoss
  massLoss_ne_top : massLoss ≠ ⊤
  mass_retention : massLoss⁻¹ * current.mass ≤ oneQuery.shading.mass
  shading_mass_pos : 0 < oneQuery.shading.mass

/-- Stable Lemma 4.11 producer on an arbitrary restored current shading,
retaining the local one-step mass receipt for the outer iterator.
All geometric/scalar packages are selected in this proof before `current` is
passed to the inner runner.  The explicit smallness hypotheses are uniform
receipts for those pre-runtime choices; none mentions the callback state. -/
theorem proposition63_lemma411_one_query_step_from_current
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
    (rootInput : Proposition63FourCallRootInput root)
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN)
    (sourceCoefficient : NNReal)
    (smallness : Proposition63Lemma411UniformSmallnessData (K := K)
      (incidence := incidence) backward root grid sourceCoefficient)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    (current_sub : PaperIsSubshading current
      root.normalization.croppedRefined)
    (sourceMap : PaperWZ1WeakPlaneMapData current incidence)
    (sourceMap_lipschitz : LipschitzWith sourceCoefficient
      (fun point : {point : Point3 // point ∈ current.union} =>
        sourceMap.planeMap point))
    (current_cubical : WZ1PaperIsCubicalShading current)
    (current_extremal : WZ2PaperCroppedIsExtremal sigma (backward.loss 0)
      root.normalization.croppedFamily current)
    (current_cwa : WZ2PaperConvexWolffBound
      root.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-(backward.loss 0))))
    (current_mass_pos : 0 < current.mass) :
    Nonempty (Proposition63Lemma411OneQueryStepData
      (sigma := sigma) (outputLoss := gridOutputLoss)
      (queryScale := queryScale) current
      (fun point => sourceMap.planeMap point)) := by
  let scalar := smallness.global.scalar
  let legacyLeft := proposition63FourCallPaperPlaceholderFactor
  let legacyRight := proposition63FourCallPaperPlaceholderFactor
  let paperGlobal := smallness.global.paperGlobal (K := K)
  let scalarFamily := smallness.global.scalarFamily (K := K)
  let extension := Classical.choice <|
    weak_plane_map_unit_ambient_extension sourceMap sourceCoefficient
      sourceMap_lipschitz
  rcases proposition63_four_call_paper_inner_schedule_run_from_current K
      backward root rootInput grid legacyLeft legacyRight sourceCoefficient
      paperGlobal scalarFamily
      (fun index hindex => le_of_eq
        (scalarFamily.pair index hindex).nestedInterval_delta_eq.symm)
      paperGlobal.delta_le_alignedAbsorption
      current current_sub sourceMap extension current_cubical current_extremal
      current_cwa current_mass_pos scalar.sigma_pos scalar.sigma_lt_one with
    ⟨data, _multiplicity, mass, mass_pos⟩
  have sameMap :
      (fun point : {point : Point3 // point ∈ current.union} =>
        extension.ambient.planeMap point) =
      (fun point : {point : Point3 // point ∈ current.union} =>
        sourceMap.planeMap point) := by
    funext point
    exact extension.agrees point
  let sourceData : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := gridOutputLoss)
      (rho := queryScale) (Y := current)
      (fun point => sourceMap.planeMap point) := {
    shading := data.shading
    subshading := data.subshading
    extremal := data.extremal
    cwa := data.cwa
    local_ad := by
      intro point point_mem
      have h := data.local_ad point point_mem
      rw [congrFun sameMap
        ⟨point, paperSubshading_union data.subshading point_mem⟩] at h
      exact h
  }
  let leftProduct : ENNReal :=
    ∏ index ∈ Finset.range (finiteIntervalOrderedPairs gridN).length,
      proposition63FourCallPaperLeftFactor scalarFamily.pair index
  let rightProduct : ENNReal :=
    ∏ index ∈ Finset.range (finiteIntervalOrderedPairs gridN).length,
      proposition63FourCallPaperRightFactor scalarFamily.pair index
  have left_pos : 0 < leftProduct := by
    dsimp only [leftProduct]
    rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro index index_mem
    have hindex := Finset.mem_range.mp index_mem
    simp only [proposition63FourCallPaperLeftFactor, dif_pos hindex]
    exact (scalarFamily.pair index hindex).paperLeft_pos.ne'
  have left_ne_top : leftProduct ≠ ⊤ := by
    dsimp only [leftProduct]
    apply ENNReal.prod_ne_top
    intro index index_mem
    have hindex := Finset.mem_range.mp index_mem
    simp only [proposition63FourCallPaperLeftFactor, dif_pos hindex]
    exact (scalarFamily.pair index hindex).paperLeft_finite
  have right_ne_top : rightProduct ≠ ⊤ := by
    dsimp only [rightProduct]
    apply ENNReal.prod_ne_top
    intro index index_mem
    have hindex := Finset.mem_range.mp index_mem
    simp only [proposition63FourCallPaperRightFactor, dif_pos hindex]
    exact (scalarFamily.pair index hindex).paperRight_finite
  have source_mass : leftProduct * current.mass ≤
      rightProduct * sourceData.shading.mass := by
    simpa only [leftProduct, rightProduct] using mass
  have source_mass_pos : 0 < sourceData.shading.mass := by
    exact mass_pos
  let massLoss := proposition63Lemma43MassLoss leftProduct rightProduct
  exact ⟨{
    oneQuery := sourceData
    massLoss := massLoss
    massLoss_pos := proposition63Lemma43MassLoss_pos _ _
    massLoss_ne_top := proposition63Lemma43MassLoss_ne_top left_pos right_ne_top
    mass_retention := proposition63Lemma43MassLoss_inv_mul_le left_pos
      left_ne_top right_ne_top source_mass
    shading_mass_pos := source_mass_pos
  }⟩

/-- The canonical concrete inner grid materialized from a frozen schedule and
one requested query scale. -/
noncomputable def Proposition63Lemma411ScheduleData.runtimeGrid
    {sigma gridOutputLoss : ℝ}
    (schedule : Proposition63Lemma411ScheduleData sigma gridOutputLoss)
    {delta : ℝ} (query : WZ2PaperRequestedScale delta)
    (delta_pos : 0 < delta)
    (delta_le_grid : delta ≤ schedule.gridSchedule.delta₀)
    (query_lower : Real.rpow delta (1 - gridOutputLoss) ≤ query.1)
    (query_upper : query.1 ≤ Real.rpow delta gridOutputLoss) :
    Proposition63InnerIntervalGridData delta sigma
      schedule.gridSchedule.discreteLoss schedule.gridSchedule.intervalLoss
      gridOutputLoss query.1 schedule.gridSchedule.gridN :=
  Classical.choice <| schedule.gridSchedule.run delta_pos delta_le_grid query
    query_lower query_upper

/-- Run a fully frozen Lemma 4.11 schedule while retaining its one-step mass
receipt for the outer Lemma 4.12 recursion. -/
theorem Proposition63Lemma411ScheduleData.runWithReceipt
    {sigma gridOutputLoss : ℝ}
    (schedule : Proposition63Lemma411ScheduleData sigma gridOutputLoss)
    {delta inputLoss incidence : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (K : ℝ)
    (root : Proposition63RootNormalizationData
      (outputLoss := schedule.backward.rootNormalizationLoss) source
      normalizationExponent schedule.backward.rootDensityLoss)
    (rootInput : Proposition63FourCallRootInput root)
    (query : WZ2PaperRequestedScale delta)
    (delta_le_grid : delta ≤ schedule.gridSchedule.delta₀)
    (query_lower : Real.rpow delta (1 - gridOutputLoss) ≤ query.1)
    (query_upper : query.1 ≤ Real.rpow delta gridOutputLoss)
    (sourceCoefficient : NNReal)
    (smallness : Proposition63Lemma411UniformSmallnessData (K := K)
      (incidence := incidence) schedule.backward root
      (schedule.runtimeGrid query root.normalization.final_extremal.delta_pos
        delta_le_grid query_lower query_upper) sourceCoefficient)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    (current_sub : PaperIsSubshading current
      root.normalization.croppedRefined)
    (sourceMap : PaperWZ1WeakPlaneMapData current incidence)
    (sourceMap_lipschitz : LipschitzWith sourceCoefficient
      (fun point : {point : Point3 // point ∈ current.union} =>
        sourceMap.planeMap point))
    (current_extremal : WZ2PaperCroppedIsExtremal sigma
      (schedule.backward.loss 0) root.normalization.croppedFamily current)
    (current_cwa : WZ2PaperConvexWolffBound
      root.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-(schedule.backward.loss 0))))
    (current_mass_pos : 0 < current.mass) :
    Nonempty (Proposition63Lemma411OneQueryStepData
      (sigma := sigma) (outputLoss := gridOutputLoss)
      (queryScale := query.1) current
      (fun point => sourceMap.planeMap point)) := by
  let grid := schedule.runtimeGrid query
    root.normalization.final_extremal.delta_pos delta_le_grid query_lower
    query_upper
  let hsmall := smallness
  exact proposition63_lemma411_one_query_step_from_current K schedule.backward root
    rootInput grid sourceCoefficient hsmall current current_sub sourceMap
    sourceMap_lipschitz current_extremal.cubical current_extremal current_cwa
    current_mass_pos

/-- Run a fully frozen Lemma 4.11 schedule at one requested query scale.
The `smallness` argument names exactly the canonical concrete grid used below
and is quantified before the runtime current shading. -/
theorem Proposition63Lemma411ScheduleData.run
    {sigma gridOutputLoss : ℝ}
    (schedule : Proposition63Lemma411ScheduleData sigma gridOutputLoss)
    {delta inputLoss incidence : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (K : ℝ)
    (root : Proposition63RootNormalizationData
      (outputLoss := schedule.backward.rootNormalizationLoss) source
      normalizationExponent schedule.backward.rootDensityLoss)
    (rootInput : Proposition63FourCallRootInput root)
    (query : WZ2PaperRequestedScale delta)
    (delta_le_grid : delta ≤ schedule.gridSchedule.delta₀)
    (query_lower : Real.rpow delta (1 - gridOutputLoss) ≤ query.1)
    (query_upper : query.1 ≤ Real.rpow delta gridOutputLoss)
    (sourceCoefficient : NNReal)
    (smallness : Proposition63Lemma411UniformSmallnessData (K := K)
      (incidence := incidence) schedule.backward root
      (schedule.runtimeGrid query root.normalization.final_extremal.delta_pos
        delta_le_grid query_lower query_upper) sourceCoefficient)
    (current : WZ1PaperTubeShading root.normalization.croppedFamily)
    (current_sub : PaperIsSubshading current
      root.normalization.croppedRefined)
    (sourceMap : PaperWZ1WeakPlaneMapData current incidence)
    (sourceMap_lipschitz : LipschitzWith sourceCoefficient
      (fun point : {point : Point3 // point ∈ current.union} =>
        sourceMap.planeMap point))
    (current_extremal : WZ2PaperCroppedIsExtremal sigma
      (schedule.backward.loss 0) root.normalization.croppedFamily current)
    (current_cwa : WZ2PaperConvexWolffBound
      root.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-(schedule.backward.loss 0))))
    (current_mass_pos : 0 < current.mass) :
    Nonempty (PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := gridOutputLoss)
      (rho := query.1) (Y := current)
      (fun point => sourceMap.planeMap point)) := by
  rcases schedule.runWithReceipt K root rootInput query delta_le_grid
      query_lower query_upper sourceCoefficient smallness current current_sub
      sourceMap sourceMap_lipschitz current_extremal current_cwa
      current_mass_pos with ⟨step⟩
  exact ⟨step.oneQuery⟩

end Kakeya.Assouad.PureWZ2
