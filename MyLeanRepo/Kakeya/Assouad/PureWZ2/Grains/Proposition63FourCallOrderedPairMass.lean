import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallFinalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteIntervalCoveringIteration
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentStepArithmetic

/-!
# Uniform scalar receipts for the four-call ordered-pair iteration

The finite iterator must choose its two mass-ledger factors before entering
the callback.  This file packages exactly that family-free scalar choice.
At runtime one only proves that the concrete left expression dominates the
preselected left factor and that the concrete right expression is dominated
by the preselected right factor.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- The interval-covering constant attached to one enumerated ordered pair.
It depends only on the fixed grid and the pair index. -/
noncomputable def proposition63FourCallOrderedPairConstant
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (index : ℕ) : ENNReal :=
  ENNReal.ofReal
    (Real.rpow delta (-discreteLoss) *
      Real.rpow
        ((grid.scale (finiteIntervalOrderedPair gridN index).2 : ℝ) /
          (grid.scale (finiteIntervalOrderedPair gridN index).1 : ℝ))
        (1 - sigma))

/-- Pre-runtime scalar data for all ordered pairs.  In particular, neither
factor is allowed to mention the callback's current shading or its freshly
constructed four-call runtime. -/
structure Proposition63FourCallUniformMassSchedule
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (loss : ℕ → ℝ) (leftFactor rightFactor : ℕ → ENNReal) where
  left_pos : ∀ index,
    index < (finiteIntervalOrderedPairs gridN).length →
      0 < leftFactor index
  left_finite : ∀ index,
    index < (finiteIntervalOrderedPairs gridN).length →
      leftFactor index ≠ ⊤
  right_finite : ∀ index,
    index < (finiteIntervalOrderedPairs gridN).length →
      rightFactor index ≠ ⊤
  loss_mono : ∀ index,
    index < (finiteIntervalOrderedPairs gridN).length →
      loss index ≤ loss (index + 1)
  next_loss_pos : ∀ index,
    index < (finiteIntervalOrderedPairs gridN).length →
      0 < loss (index + 1)
  restore : ∀ index,
    index < (finiteIntervalOrderedPairs gridN).length →
      proposition63Lemma43MassLoss (leftFactor index) (rightFactor index) *
          Kakeya.realRpowENN delta (loss (index + 1)) ≤
        Kakeya.realRpowENN delta (loss index)

/-- The existing two-half-budget absorption lemma supplies the restore field
of a uniform schedule at one pair index. -/
theorem proposition63_four_call_ordered_pair_restore_of_two_bounds
    {delta : ℝ} {loss : ℕ → ℝ} {leftFactor rightFactor : ℕ → ENNReal}
    {index : ℕ}
    (left_pos : 0 < leftFactor index)
    (left_finite : leftFactor index ≠ ⊤)
    (one_bound :
      2 * Kakeya.realRpowENN delta (loss (index + 1)) ≤
        Kakeya.realRpowENN delta (loss index))
    (ratio_bound :
      2 * rightFactor index *
          Kakeya.realRpowENN delta (loss (index + 1)) ≤
        leftFactor index * Kakeya.realRpowENN delta (loss index)) :
    proposition63Lemma43MassLoss (leftFactor index) (rightFactor index) *
        Kakeya.realRpowENN delta (loss (index + 1)) ≤
      Kakeya.realRpowENN delta (loss index) := by
  exact proposition63Lemma43MassLoss_slack_of_two_bounds
    left_pos left_finite one_bound ratio_bound

/-- Build the uniform schedule from the two standard absorption inequalities
at each ordered pair. -/
theorem proposition63FourCallUniformMassScheduleOfTwoBounds
    {delta sigma discreteLoss intervalLoss outputLoss queryScale : ℝ}
    {gridN : ℕ}
    (grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss outputLoss queryScale gridN)
    (loss : ℕ → ℝ) (leftFactor rightFactor : ℕ → ENNReal)
    (left_pos : ∀ index,
      index < (finiteIntervalOrderedPairs gridN).length →
        0 < leftFactor index)
    (left_finite : ∀ index,
      index < (finiteIntervalOrderedPairs gridN).length →
        leftFactor index ≠ ⊤)
    (right_finite : ∀ index,
      index < (finiteIntervalOrderedPairs gridN).length →
        rightFactor index ≠ ⊤)
    (loss_mono : ∀ index,
      index < (finiteIntervalOrderedPairs gridN).length →
        loss index ≤ loss (index + 1))
    (next_loss_pos : ∀ index,
      index < (finiteIntervalOrderedPairs gridN).length →
        0 < loss (index + 1))
    (one_bound : ∀ index,
      index < (finiteIntervalOrderedPairs gridN).length →
        2 * Kakeya.realRpowENN delta (loss (index + 1)) ≤
          Kakeya.realRpowENN delta (loss index))
    (ratio_bound : ∀ index,
      index < (finiteIntervalOrderedPairs gridN).length →
        2 * rightFactor index *
            Kakeya.realRpowENN delta (loss (index + 1)) ≤
          leftFactor index * Kakeya.realRpowENN delta (loss index)) :
    Proposition63FourCallUniformMassSchedule grid loss
      leftFactor rightFactor where
  left_pos := left_pos
  left_finite := left_finite
  right_finite := right_finite
  loss_mono := loss_mono
  next_loss_pos := next_loss_pos
  restore := fun index hindex =>
    proposition63_four_call_ordered_pair_restore_of_two_bounds
      (left_pos index hindex) (left_finite index hindex)
      (one_bound index hindex) (ratio_bound index hindex)

/-- Increasing the ambient cardinality decreases the inverse dyadic-log loss. -/
theorem proposition63_four_call_log_card_inv_mono
    {runtimeCard uniformCard : ℕ} (card_le : runtimeCard ≤ uniformCard) :
    ((((Nat.log 2 uniformCard + 1 : ℕ) : ENNReal))⁻¹) ≤
      (((Nat.log 2 runtimeCard + 1 : ℕ) : ENNReal))⁻¹ := by
  apply ENNReal.inv_le_inv.mpr
  exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right card_le) 1

/-- The retained part of the concrete M3 left factor, using one cardinality
envelope fixed before the M3 runtime is selected. -/
noncomputable def proposition63FourCallFrozenNestedRetainedFactor
    (delta : ℝ) (uniformCard : ℕ)
    (canonicalWeight : ENNReal) : ENNReal :=
  ((81 / 400 : ENNReal) *
      (((Nat.log 2 uniformCard + 1 : ℕ) : ENNReal))⁻¹ *
      wz2PaperPureRefinementFraction delta 61) *
    ((73 / 100 : ENNReal) * canonicalWeight) *
    ((81 / 400 : ENNReal) *
      (((Nat.log 2 uniformCard + 1 : ℕ) : ENNReal))⁻¹)

/-- The same retained product before replacing its two runtime cardinalities
by the fixed uniform envelope.  This is kept as the exact receipt-facing
compatibility layer. -/
noncomputable def proposition63FourCallRuntimeNestedRetainedFactor
    (delta : ℝ) (firstTargetCard secondTargetCard : ℕ)
    (canonicalWeight : ENNReal) : ENNReal :=
  ((81 / 400 : ENNReal) *
      (((Nat.log 2 secondTargetCard + 1 : ℕ) : ENNReal))⁻¹ *
      wz2PaperPureRefinementFraction delta 61) *
    ((73 / 100 : ENNReal) * canonicalWeight) *
    ((81 / 400 : ENNReal) *
      (((Nat.log 2 firstTargetCard + 1 : ℕ) : ENNReal))⁻¹)

/-- The strengthened M3 receipt identifies its runtime retained product with
the corresponding pre-runtime scalar formula. -/
theorem Proposition63FourCallNestedMassReceipt.frozen_retained_eq
    {delta : ℝ}
    {firstRetainedFactor normalizationWeight secondRetainedFactor
      preparationLoss canonicalWeight preparationUpper : ENNReal}
    {levelCount firstTargetCard secondTargetCard canonicalLevel : ℕ}
    (receipt : Proposition63FourCallNestedMassReceipt delta
      firstRetainedFactor normalizationWeight levelCount secondRetainedFactor
      preparationLoss firstTargetCard secondTargetCard canonicalWeight
      canonicalLevel preparationUpper) :
    proposition63FourCallRuntimeNestedRetainedFactor delta firstTargetCard
        secondTargetCard canonicalWeight =
      secondRetainedFactor *
        ((73 / 100 : ENNReal) * normalizationWeight) *
        firstRetainedFactor := by
  unfold proposition63FourCallRuntimeNestedRetainedFactor
  rw [receipt.firstRetainedFactor_eq, receipt.reentryWeight_eq,
    receipt.secondRetainedFactor_eq]

/-- Two embeddings of the runtime target families into a pre-runtime family
give a fixed lower envelope for their combined retained mass. -/
theorem Proposition63FourCallNestedMassReceipt.frozen_retained_le
    {delta : ℝ}
    {firstRetainedFactor normalizationWeight secondRetainedFactor
      preparationLoss canonicalWeight preparationUpper : ENNReal}
    {levelCount firstTargetCard secondTargetCard canonicalLevel uniformCard : ℕ}
    (receipt : Proposition63FourCallNestedMassReceipt delta
      firstRetainedFactor normalizationWeight levelCount secondRetainedFactor
      preparationLoss firstTargetCard secondTargetCard canonicalWeight
      canonicalLevel preparationUpper)
    (first_card_le : firstTargetCard ≤ uniformCard)
    (second_card_le : secondTargetCard ≤ uniformCard) :
    proposition63FourCallFrozenNestedRetainedFactor delta uniformCard
        canonicalWeight ≤
      secondRetainedFactor *
        ((73 / 100 : ENNReal) * normalizationWeight) *
        firstRetainedFactor := by
  rw [← receipt.frozen_retained_eq]
  unfold proposition63FourCallFrozenNestedRetainedFactor
    proposition63FourCallRuntimeNestedRetainedFactor
  gcongr

/-- Embeddings of both runtime target index types into the fixed uniform
index type discharge the two cardinality premises of `frozen_retained_le`. -/
theorem Proposition63FourCallNestedMassReceipt.frozen_retained_le_of_embeddings
    {delta : ℝ}
    {firstRetainedFactor normalizationWeight secondRetainedFactor
      preparationLoss canonicalWeight preparationUpper : ENNReal}
    {levelCount firstTargetCard secondTargetCard canonicalLevel uniformCard : ℕ}
    (receipt : Proposition63FourCallNestedMassReceipt delta
      firstRetainedFactor normalizationWeight levelCount secondRetainedFactor
      preparationLoss firstTargetCard secondTargetCard canonicalWeight
      canonicalLevel preparationUpper)
    (firstEmbedding : Fin firstTargetCard → Fin uniformCard)
    (secondEmbedding : Fin secondTargetCard → Fin uniformCard)
    (first_injective : Function.Injective firstEmbedding)
    (second_injective : Function.Injective secondEmbedding) :
    proposition63FourCallFrozenNestedRetainedFactor delta uniformCard
        canonicalWeight ≤
      secondRetainedFactor *
        ((73 / 100 : ENNReal) * normalizationWeight) *
        firstRetainedFactor := by
  apply receipt.frozen_retained_le
  · simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective firstEmbedding first_injective
  · simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective secondEmbedding second_injective

/-- The pre-runtime left factor obtained by combining a fixed line/cover
base, a fixed ancestry-retention budget, and the concrete M3 scalar receipt.
No callback-local shading or runtime occurs in this definition. -/
noncomputable def proposition63FourCallFrozenActualLeftFactor
    {rootDelta : ℝ}
    (rootFamily : Kakeya.Streamlined.TubeFamily rootDelta)
    (delta rho sigma outerLoss fineWeightLoss : ℝ)
    (outerLogExponent : ℕ)
    (ancestorRetentionUpper frozenLineCoverBase : ENNReal)
    (canonicalNestedWeight : ENNReal) : ENNReal :=
  proposition63UniformDependentFinePullbackLeft rootFamily delta rho sigma
    outerLoss outerLogExponent
    (proposition63CanonicalReentryWeight delta fineWeightLoss)
    ancestorRetentionUpper
    (frozenLineCoverBase *
      proposition63FourCallFrozenNestedRetainedFactor rho rootFamily.card
        canonicalNestedWeight)

/-- Concrete actual-left majorization.  The strengthened M3 receipt closes
all nested retained-factor identities.  The only genuinely external scalar
premise left is `frozen_base_le`: it compares the preselected line/cover
base with the later critical-floor and cover-budget expression. -/
theorem proposition63_four_call_frozen_left_le_actual
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss
      outerLoss fineWeightLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {rho : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined rho outerLogExponent)
    {firstRetainedFactor normalizationWeight secondRetainedFactor
      preparationLoss canonicalNestedWeight preparationUpper : ENNReal}
    {levelCount firstTargetCard secondTargetCard canonicalLevel : ℕ}
    (nestedReceipt : Proposition63FourCallNestedMassReceipt rho.1
      firstRetainedFactor normalizationWeight levelCount secondRetainedFactor
      preparationLoss firstTargetCard secondTargetCard canonicalNestedWeight
      canonicalLevel preparationUpper)
    (ancestorRetentionFactor ancestorRetentionUpper
      frozenLineCoverBase actualLineCoverBase : ENNReal)
    (first_card_le : firstTargetCard ≤ initialNormalized.croppedFamily.card)
    (second_card_le : secondTargetCard ≤ initialNormalized.croppedFamily.card)
    (ancestor_le : ancestorRetentionFactor ≤ ancestorRetentionUpper)
    (fine_weight_eq : fineReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta fineWeightLoss)
    (frozen_base_le : frozenLineCoverBase ≤ actualLineCoverBase) :
    proposition63FourCallFrozenActualLeftFactor
        initialNormalized.croppedFamily delta rho.1 sigma outerLoss
        fineWeightLoss outerLogExponent ancestorRetentionUpper
        frozenLineCoverBase canonicalNestedWeight ≤
      proposition63DependentFinePullbackLeft fineReentry outer
        ancestorRetentionFactor
        (actualLineCoverBase *
          (secondRetainedFactor *
            ((73 / 100 : ENNReal) * normalizationWeight) *
            firstRetainedFactor)) := by
  have retained_le := nestedReceipt.frozen_retained_le
    first_card_le second_card_le
  have coarse_le :
      frozenLineCoverBase *
          proposition63FourCallFrozenNestedRetainedFactor rho.1
            initialNormalized.croppedFamily.card canonicalNestedWeight ≤
        actualLineCoverBase *
          (secondRetainedFactor *
            ((73 / 100 : ENNReal) * normalizationWeight) *
            firstRetainedFactor) := by
    gcongr
  unfold proposition63FourCallFrozenActualLeftFactor
  calc
    proposition63UniformDependentFinePullbackLeft
          initialNormalized.croppedFamily delta rho.1 sigma outerLoss
          outerLogExponent
          (proposition63CanonicalReentryWeight delta fineWeightLoss)
          ancestorRetentionUpper
          (frozenLineCoverBase *
            proposition63FourCallFrozenNestedRetainedFactor rho.1
              initialNormalized.croppedFamily.card canonicalNestedWeight) ≤
        proposition63UniformDependentFinePullbackLeft
          initialNormalized.croppedFamily delta rho.1 sigma outerLoss
          outerLogExponent
          (proposition63CanonicalReentryWeight delta fineWeightLoss)
          ancestorRetentionFactor
          (actualLineCoverBase *
            (secondRetainedFactor *
              ((73 / 100 : ENNReal) * normalizationWeight) *
              firstRetainedFactor)) := by
      unfold proposition63UniformDependentFinePullbackLeft
      gcongr
    _ ≤ proposition63DependentFinePullbackLeft fineReentry outer
          ancestorRetentionFactor
          (actualLineCoverBase *
            (secondRetainedFactor *
              ((73 / 100 : ENNReal) * normalizationWeight) *
              firstRetainedFactor)) :=
      proposition63_uniformDependentFinePullbackLeft_le fineReentry outer
        ancestorRetentionFactor _ fine_weight_eq

/-- Concrete actual-right majorization.  Both runtime regularization losses
are bounded by the fixed root-family envelope from
`Proposition63DependentStepArithmetic`; the strengthened M3 receipt supplies
the nested level identity and preparation upper bound. -/
theorem proposition63_four_call_actual_right_le_uniform
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss : ℝ}
    {initialSource :
      PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalizationExponent nestedNormalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource initialNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {nestedInputLoss nestedNormalizationLoss nestedReentryLoss rho : ℝ}
    {nestedSource : PureWZ2ExtremalConfiguration
      sigma nestedInputLoss rho}
    {nestedNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := nestedNormalizationLoss) nestedSource
      nestedNormalizationExponent}
    {nestedCurrent : WZ1PaperTubeShading nestedNormalized.croppedFamily}
    (nestedReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := nestedReentryLoss) nestedNormalized nestedCurrent)
    {firstRetainedFactor normalizationWeight secondRetainedFactor
      preparationLoss canonicalWeight preparationUpper : ENNReal}
    {firstTargetCard secondTargetCard canonicalLevel
      uniformLevel : ℕ}
    (nestedReceipt : Proposition63FourCallNestedMassReceipt rho
      firstRetainedFactor normalizationWeight nestedReentry.levelCount
      secondRetainedFactor
      preparationLoss firstTargetCard secondTargetCard canonicalWeight
      canonicalLevel preparationUpper)
    (fine_level_le : fineReentry.levelCount ≤ uniformLevel)
    (nested_card_le : nestedNormalized.croppedFamily.card ≤
      initialNormalized.croppedFamily.card)
    (canonical_level_le : canonicalLevel ≤ uniformLevel)
    (preparation_upper_le : preparationUpper ≤
      proposition63UniformPreparationLoss initialNormalized.croppedFamily)
    (four_rho_le_one : 4 * rho ≤ 1) :
    proposition63DependentFinePullbackRight fineReentry
        ((nestedReentry.regularized.regularizationLoss * preparationLoss) *
          (2 * ENNReal.ofReal (4 * rho))) ≤
      proposition63UniformDependentRightFactor
        initialNormalized.croppedFamily uniformLevel := by
  have fine_regularization_le :
      fineReentry.regularized.regularizationLoss ≤
        proposition63UniformReentryRegularizationLoss
          initialNormalized.croppedFamily uniformLevel :=
    proposition63_reentry_regularizationLoss_le_uniform fineReentry
      initialNormalized.croppedFamily uniformLevel (by simp) fine_level_le
  have nested_level_le : nestedReentry.levelCount ≤ uniformLevel := by
    exact nestedReceipt.reentryLevel_eq.le.trans canonical_level_le
  have nested_regularization_le :
      nestedReentry.regularized.regularizationLoss ≤
        proposition63UniformReentryRegularizationLoss
          initialNormalized.croppedFamily uniformLevel :=
    proposition63_reentry_regularizationLoss_le_uniform nestedReentry
      initialNormalized.croppedFamily uniformLevel nested_card_le
      nested_level_le
  have preparation_le : preparationLoss ≤
      proposition63UniformPreparationLoss initialNormalized.croppedFamily :=
    nestedReceipt.preparationLoss_le.trans preparation_upper_le
  have rho_tail_le :
      2 * ENNReal.ofReal (4 * rho) ≤ (2 : ENNReal) := by
    calc
      2 * ENNReal.ofReal (4 * rho) ≤ 2 * ENNReal.ofReal 1 := by
        gcongr
      _ = 2 := by norm_num
  unfold proposition63DependentFinePullbackRight
    proposition63UniformDependentRightFactor
  calc
    ((nestedReentry.regularized.regularizationLoss * preparationLoss) *
          (2 * ENNReal.ofReal (4 * rho))) *
        fineReentry.regularized.regularizationLoss ≤
      ((proposition63UniformReentryRegularizationLoss
            initialNormalized.croppedFamily uniformLevel *
          proposition63UniformPreparationLoss
            initialNormalized.croppedFamily) * 2) *
        proposition63UniformReentryRegularizationLoss
          initialNormalized.croppedFamily uniformLevel := by
      gcongr
    _ =
      (proposition63UniformReentryRegularizationLoss
          initialNormalized.croppedFamily uniformLevel *
        (proposition63UniformPreparationLoss
          initialNormalized.croppedFamily * 2)) *
        proposition63UniformReentryRegularizationLoss
          initialNormalized.croppedFamily uniformLevel := by ring

/-- Convert pre-runtime factors into the exact M4 mass receipt.  The only
callback-local obligations are the three majorizations and the geometric
variation inequality; the selected factors and the extremality restoration
already come from the index-only schedule. -/
noncomputable def Proposition63FourCallUniformMassSchedule.massReceipt
    {delta sigma discreteLoss intervalLoss gridOutputLoss queryScale : ℝ}
    {gridN : ℕ}
    {grid : Proposition63InnerIntervalGridData delta sigma discreteLoss
      intervalLoss gridOutputLoss queryScale gridN}
    {loss : ℕ → ℝ} {leftFactor rightFactor : ℕ → ENNReal}
    (schedule : Proposition63FourCallUniformMassSchedule grid loss
      leftFactor rightFactor)
    {index : ℕ}
    (hindex : index < (finiteIntervalOrderedPairs gridN).length)
    {constantLeft leftExpression rightExpression : ENNReal}
    {outputCandidateLoss fineCurrentLoss coefficient spatialScale
      variationScale : ℝ}
    (constant_bound : constantLeft ≤
      proposition63FourCallOrderedPairConstant grid index)
    (left_bound : leftFactor index ≤ leftExpression)
    (right_bound : rightExpression ≤ rightFactor index)
    (current_loss : fineCurrentLoss = loss index)
    (output_loss : outputCandidateLoss = loss (index + 1))
    (variation : coefficient * spatialScale ≤ variationScale) :
    Proposition63FourCallMassReceipt constantLeft leftExpression
      rightExpression delta outputCandidateLoss fineCurrentLoss coefficient
      spatialScale variationScale where
  targetConstant := proposition63FourCallOrderedPairConstant grid index
  targetLeft := leftFactor index
  targetRight := rightFactor index
  constant_bound := constant_bound
  left_bound := left_bound
  right_bound := right_bound
  targetLeft_pos := schedule.left_pos index hindex
  targetLeft_finite := schedule.left_finite index hindex
  targetRight_finite := schedule.right_finite index hindex
  currentOutput := by
    rw [current_loss, output_loss]
    exact schedule.loss_mono index hindex
  outputCandidateLoss_pos := by
    rw [output_loss]
    exact schedule.next_loss_pos index hindex
  restore := by
    rw [output_loss, current_loss]
    exact schedule.restore index hindex
  variation := variation

end Kakeya.Assouad.PureWZ2
