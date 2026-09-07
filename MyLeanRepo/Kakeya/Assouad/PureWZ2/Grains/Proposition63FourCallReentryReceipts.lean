import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPullbackReceipt
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentStepArithmetic

/-!
# Canonical re-entry receipts for the four-call producer

The generic current-reentry structure intentionally permits arbitrary finite
normalization weights and schedule lengths.  Consequently its canonical
weight and level cannot be recovered after a producer has discarded the
construction equalities.  This file supplies only lightweight scalar
companions; it does not change either re-entry or four-call runtime data.

The call-one producer must retain its already-proved `_hweight` and `_hlevel`
as one additional conjunct of type `Proposition63CanonicalReentryReceipt`.
The target producer already obtains the corresponding equalities while
constructing `Proposition63FourCallNestedMassReceipt`; the combined producer
must expose both proofs as one `Proposition63FourCallReentryReceiptPair`.
-/

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Exact scalar provenance for one freshly constructed re-entry.  Both
parameters are chosen before the re-entry witness. -/
structure Proposition63CanonicalReentryReceipt
    {delta sigma inputLoss normalizationLoss reentryLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {current : WZ1PaperTubeShading normalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) normalized current)
    (canonicalWeight : ENNReal) (canonicalLevel : ℕ) : Prop where
  normalizationWeight_eq : reentry.normalizationWeight = canonicalWeight
  levelCount_eq : reentry.levelCount = canonicalLevel

/-- Canonical specialization used by a producer whose scale, weight loss, and
normalization loss were fixed before runtime. -/
abbrev Proposition63CanonicalReentryAt
    {delta sigma inputLoss normalizationLoss reentryLoss weightLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {current : WZ1PaperTubeShading normalized.croppedFamily}
    (reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) normalized current) :=
  Proposition63CanonicalReentryReceipt reentry
    (proposition63CanonicalReentryWeight delta weightLoss)
    (proposition63CanonicalNearbyLevelCount normalizationLoss)

/-- The two re-entry receipts which the concrete four-call producer must keep:
the call-one source-witness re-entry and the later target re-entry used in the
closed pullback-retention formula. -/
structure Proposition63FourCallReentryReceiptPair
    {currentDelta currentSigma currentInputLoss currentNormalizationLoss
      currentReentryLoss targetDelta targetSigma targetInputLoss
      targetNormalizationLoss targetReentryLoss : ℝ}
    {currentSource : PureWZ2ExtremalConfiguration currentSigma
      currentInputLoss currentDelta}
    {currentNormalizationExponent : ℕ}
    {currentNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := currentNormalizationLoss) currentSource
      currentNormalizationExponent}
    {currentShading : WZ1PaperTubeShading currentNormalized.croppedFamily}
    (currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) currentNormalized currentShading)
    {targetSource : PureWZ2ExtremalConfiguration targetSigma
      targetInputLoss targetDelta}
    {targetNormalizationExponent : ℕ}
    {targetNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := targetNormalizationLoss) targetSource
      targetNormalizationExponent}
    {targetShading : WZ1PaperTubeShading targetNormalized.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) targetNormalized targetShading)
    (currentCanonicalWeight targetCanonicalWeight : ENNReal)
    (currentCanonicalLevel targetCanonicalLevel : ℕ) : Prop where
  current : Proposition63CanonicalReentryReceipt currentReentry
    currentCanonicalWeight currentCanonicalLevel
  target : Proposition63CanonicalReentryReceipt targetReentry
    targetCanonicalWeight targetCanonicalLevel

/-- Exact additional conjunct for the combined producer when both losses and
normalization losses are schedule data.  In the present four-call route, use
`currentWeightLoss = weightLoss` for call one and
`targetWeightLoss = weightLoss` for the target re-entry preceding call three.
The later nested re-entry instead uses `nextWeightLoss` and is already recorded
by `Proposition63FourCallNestedMassReceipt`. -/
abbrev Proposition63FourCallCanonicalReentryPairAt
    {currentDelta currentSigma currentInputLoss currentNormalizationLoss
      currentReentryLoss currentWeightLoss targetDelta targetSigma
      targetInputLoss targetNormalizationLoss targetReentryLoss
      targetWeightLoss : ℝ}
    {currentSource : PureWZ2ExtremalConfiguration currentSigma
      currentInputLoss currentDelta}
    {currentNormalizationExponent : ℕ}
    {currentNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := currentNormalizationLoss) currentSource
      currentNormalizationExponent}
    {currentShading : WZ1PaperTubeShading currentNormalized.croppedFamily}
    (currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) currentNormalized currentShading)
    {targetSource : PureWZ2ExtremalConfiguration targetSigma
      targetInputLoss targetDelta}
    {targetNormalizationExponent : ℕ}
    {targetNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := targetNormalizationLoss) targetSource
      targetNormalizationExponent}
    {targetShading : WZ1PaperTubeShading targetNormalized.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) targetNormalized targetShading) :=
  Proposition63FourCallReentryReceiptPair currentReentry targetReentry
    (proposition63CanonicalReentryWeight currentDelta currentWeightLoss)
    (proposition63CanonicalReentryWeight targetDelta targetWeightLoss)
    (proposition63CanonicalNearbyLevelCount currentNormalizationLoss)
    (proposition63CanonicalNearbyLevelCount targetNormalizationLoss)

/-- Package the four scalar equalities without changing either runtime data
structure.  This is intended for the producer branch where the equalities are
already in scope. -/
theorem proposition63_four_call_reentry_receipt_pair_of_equalities
    {currentDelta currentSigma currentInputLoss currentNormalizationLoss
      currentReentryLoss targetDelta targetSigma targetInputLoss
      targetNormalizationLoss targetReentryLoss : ℝ}
    {currentSource : PureWZ2ExtremalConfiguration currentSigma
      currentInputLoss currentDelta}
    {currentNormalizationExponent : ℕ}
    {currentNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := currentNormalizationLoss) currentSource
      currentNormalizationExponent}
    {currentShading : WZ1PaperTubeShading currentNormalized.croppedFamily}
    {currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) currentNormalized currentShading}
    {targetSource : PureWZ2ExtremalConfiguration targetSigma
      targetInputLoss targetDelta}
    {targetNormalizationExponent : ℕ}
    {targetNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := targetNormalizationLoss) targetSource
      targetNormalizationExponent}
    {targetShading : WZ1PaperTubeShading targetNormalized.croppedFamily}
    {targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) targetNormalized targetShading}
    {currentCanonicalWeight targetCanonicalWeight : ENNReal}
    {currentCanonicalLevel targetCanonicalLevel : ℕ}
    (hcurrentWeight : currentReentry.normalizationWeight =
      currentCanonicalWeight)
    (hcurrentLevel : currentReentry.levelCount = currentCanonicalLevel)
    (htargetWeight : targetReentry.normalizationWeight =
      targetCanonicalWeight)
    (htargetLevel : targetReentry.levelCount = targetCanonicalLevel) :
    Proposition63FourCallReentryReceiptPair currentReentry targetReentry
      currentCanonicalWeight targetCanonicalWeight currentCanonicalLevel
      targetCanonicalLevel where
  current := ⟨hcurrentWeight, hcurrentLevel⟩
  target := ⟨htargetWeight, htargetLevel⟩

/-- Exact canonical level plus a cardinality comparison gives the uniform
regularization bound needed before the runtime family is known. -/
theorem Proposition63CanonicalReentryReceipt.regularizationLoss_le_uniform
    {delta sigma inputLoss normalizationLoss reentryLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {current : WZ1PaperTubeShading normalized.croppedFamily}
    {reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) normalized current}
    {canonicalWeight : ENNReal} {canonicalLevel : ℕ}
    (receipt : Proposition63CanonicalReentryReceipt reentry
      canonicalWeight canonicalLevel)
    {referenceDelta : ℝ}
    (referenceFamily : Kakeya.Streamlined.TubeFamily referenceDelta)
    (card_le : normalized.croppedFamily.card ≤ referenceFamily.card) :
    reentry.regularized.regularizationLoss ≤
      proposition63UniformReentryRegularizationLoss referenceFamily
        canonicalLevel := by
  apply proposition63_reentry_regularizationLoss_le_uniform reentry
    referenceFamily canonicalLevel card_le
  exact receipt.levelCount_eq.le

/-- Simultaneous regularization bounds for both four-call re-entries against
one pre-runtime reference family. -/
theorem Proposition63FourCallReentryReceiptPair.regularizationLoss_bounds
    {currentDelta currentSigma currentInputLoss currentNormalizationLoss
      currentReentryLoss targetDelta targetSigma targetInputLoss
      targetNormalizationLoss targetReentryLoss referenceDelta : ℝ}
    {currentSource : PureWZ2ExtremalConfiguration currentSigma
      currentInputLoss currentDelta}
    {currentNormalizationExponent : ℕ}
    {currentNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := currentNormalizationLoss) currentSource
      currentNormalizationExponent}
    {currentShading : WZ1PaperTubeShading currentNormalized.croppedFamily}
    {currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) currentNormalized currentShading}
    {targetSource : PureWZ2ExtremalConfiguration targetSigma
      targetInputLoss targetDelta}
    {targetNormalizationExponent : ℕ}
    {targetNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := targetNormalizationLoss) targetSource
      targetNormalizationExponent}
    {targetShading : WZ1PaperTubeShading targetNormalized.croppedFamily}
    {targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) targetNormalized targetShading}
    {currentCanonicalWeight targetCanonicalWeight : ENNReal}
    {currentCanonicalLevel targetCanonicalLevel : ℕ}
    (receipts : Proposition63FourCallReentryReceiptPair currentReentry
      targetReentry currentCanonicalWeight targetCanonicalWeight
      currentCanonicalLevel targetCanonicalLevel)
    (referenceFamily : Kakeya.Streamlined.TubeFamily referenceDelta)
    (current_card_le : currentNormalized.croppedFamily.card ≤
      referenceFamily.card)
    (target_card_le : targetNormalized.croppedFamily.card ≤
      referenceFamily.card) :
    currentReentry.regularized.regularizationLoss ≤
        proposition63UniformReentryRegularizationLoss referenceFamily
          currentCanonicalLevel ∧
      targetReentry.regularized.regularizationLoss ≤
        proposition63UniformReentryRegularizationLoss referenceFamily
          targetCanonicalLevel :=
  ⟨receipts.current.regularizationLoss_le_uniform referenceFamily
      current_card_le,
    receipts.target.regularizationLoss_le_uniform referenceFamily
      target_card_le⟩

/-- Closed retention formula for the call-one current re-entry before the two
outer refinement fractions are applied. -/
noncomputable def proposition63FourCallReentryRetentionFormula
    (regularizationLoss normalizationWeight incomingRetention : ENNReal) :
    ENNReal :=
  ((regularizationLoss⁻¹ *
      ((73 / 100 : ENNReal) * normalizationWeight)) *
    incomingRetention⁻¹)⁻¹

/-- Construction receipt for the call-one retention factor.  This equality is
definitionally available from `proposition63DependentCoarseReentryOfCurrent`
but disappears if only its abstract result is retained. -/
structure Proposition63FourCallReentryRetentionReceipt
    (actual regularizationLoss normalizationWeight incomingRetention : ENNReal) :
    Prop where
  retentionFactor_eq : actual =
    proposition63FourCallReentryRetentionFormula regularizationLoss
      normalizationWeight incomingRetention

/-- Monotonicity of the call-one formula: regularization and incoming retention
are costs, while normalization weight is retained mass. -/
theorem proposition63_four_call_reentry_retention_formula_le
    {regularizationLoss regularizationUpper weightLower normalizationWeight
      incomingRetention incomingUpper : ENNReal}
    (hregularization : regularizationLoss ≤ regularizationUpper)
    (hweight : weightLower ≤ normalizationWeight)
    (hincoming : incomingRetention ≤ incomingUpper) :
    proposition63FourCallReentryRetentionFormula regularizationLoss
        normalizationWeight incomingRetention ≤
      proposition63FourCallReentryRetentionFormula regularizationUpper
        weightLower incomingUpper := by
  unfold proposition63FourCallReentryRetentionFormula
  apply ENNReal.inv_le_inv.mpr
  gcongr

/-- The exact call-one canonical receipt, its cardinality comparison, and a
pre-runtime incoming-retention budget give an upper bound for the abstract
call-one retention factor. -/
theorem Proposition63FourCallReentryRetentionReceipt.le_uniform
    {delta sigma inputLoss normalizationLoss reentryLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {current : WZ1PaperTubeShading normalized.croppedFamily}
    {reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) normalized current}
    {canonicalWeight : ENNReal} {canonicalLevel : ℕ}
    (canonical : Proposition63CanonicalReentryReceipt reentry
      canonicalWeight canonicalLevel)
    {referenceDelta : ℝ}
    (referenceFamily : Kakeya.Streamlined.TubeFamily referenceDelta)
    (card_le : normalized.croppedFamily.card ≤ referenceFamily.card)
    {actual incomingRetention incomingUpper : ENNReal}
    (retention : Proposition63FourCallReentryRetentionReceipt actual
      reentry.regularized.regularizationLoss reentry.normalizationWeight
      incomingRetention)
    (hincoming : incomingRetention ≤ incomingUpper) :
    actual ≤ proposition63FourCallReentryRetentionFormula
      (proposition63UniformReentryRegularizationLoss referenceFamily
        canonicalLevel) canonicalWeight incomingUpper := by
  rw [retention.retentionFactor_eq]
  apply proposition63_four_call_reentry_retention_formula_le
  · exact canonical.regularizationLoss_le_uniform referenceFamily card_le
  · exact canonical.normalizationWeight_eq.ge
  · exact hincoming

/-- Pre-runtime upper bound for the concrete pullback-retention formula.  The
target receipt supplies its exact canonical weight and level; cardinality
transport supplies the regularization envelope. -/
theorem Proposition63CanonicalReentryReceipt.pullbackRetentionFormula_le
    {delta sigma inputLoss normalizationLoss reentryLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {current : WZ1PaperTubeShading normalized.croppedFamily}
    {reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) normalized current}
    {canonicalWeight : ENNReal} {canonicalLevel : ℕ}
    (receipt : Proposition63CanonicalReentryReceipt reentry
      canonicalWeight canonicalLevel)
    {referenceDelta : ℝ}
    (referenceFamily : Kakeya.Streamlined.TubeFamily referenceDelta)
    (card_le : normalized.croppedFamily.card ≤ referenceFamily.card)
    (fraction ancestorRetentionFactor ancestorRetentionUpper : ENNReal)
    (ancestor_le : ancestorRetentionFactor ≤ ancestorRetentionUpper) :
    proposition63FourCallPullbackRetentionFormula fraction
        reentry.regularized.regularizationLoss reentry.normalizationWeight
        ancestorRetentionFactor ≤
      proposition63FourCallPullbackRetentionFormula fraction
        (proposition63UniformReentryRegularizationLoss referenceFamily
          canonicalLevel) canonicalWeight ancestorRetentionUpper := by
  apply proposition63_four_call_pullback_retention_formula_le
      (fractionLower := fraction)
  · exact le_rfl
  · exact receipt.regularizationLoss_le_uniform referenceFamily card_le
  · exact receipt.normalizationWeight_eq.ge
  · exact ancestor_le

/-- Receipt-facing version for the actual pullback factor returned by its
concrete producer. -/
theorem Proposition63FourCallPullbackRetentionReceipt.le_uniform_of_reentry
    {delta sigma inputLoss normalizationLoss reentryLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {current : WZ1PaperTubeShading normalized.croppedFamily}
    {reentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) normalized current}
    {canonicalWeight : ENNReal} {canonicalLevel : ℕ}
    (reentryReceipt : Proposition63CanonicalReentryReceipt reentry
      canonicalWeight canonicalLevel)
    {referenceDelta : ℝ}
    (referenceFamily : Kakeya.Streamlined.TubeFamily referenceDelta)
    (card_le : normalized.croppedFamily.card ≤ referenceFamily.card)
    {actual fraction ancestorRetentionFactor ancestorRetentionUpper : ENNReal}
    (pullbackReceipt : Proposition63FourCallPullbackRetentionReceipt actual
      fraction reentry.regularized.regularizationLoss
      reentry.normalizationWeight ancestorRetentionFactor)
    (ancestor_le : ancestorRetentionFactor ≤ ancestorRetentionUpper) :
    actual ≤ proposition63FourCallPullbackRetentionFormula fraction
      (proposition63UniformReentryRegularizationLoss referenceFamily
        canonicalLevel) canonicalWeight ancestorRetentionUpper := by
  rw [pullbackReceipt.retentionFactor_eq]
  exact reentryReceipt.pullbackRetentionFormula_le referenceFamily card_le
    fraction ancestorRetentionFactor ancestorRetentionUpper ancestor_le

/-- Fully pre-runtime upper bound for the concrete four-call pullback formula.
The inner bound is generated from the call-one receipt; the outer formula is
controlled by the target receipt. -/
theorem Proposition63FourCallPullbackRetentionReceipt.le_uniform_of_pair
    {currentDelta currentSigma currentInputLoss currentNormalizationLoss
      currentReentryLoss targetDelta targetSigma targetInputLoss
      targetNormalizationLoss targetReentryLoss referenceDelta : ℝ}
    {currentSource : PureWZ2ExtremalConfiguration currentSigma
      currentInputLoss currentDelta}
    {currentNormalizationExponent : ℕ}
    {currentNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := currentNormalizationLoss) currentSource
      currentNormalizationExponent}
    {currentShading : WZ1PaperTubeShading currentNormalized.croppedFamily}
    {currentReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := currentReentryLoss) currentNormalized currentShading}
    {targetSource : PureWZ2ExtremalConfiguration targetSigma
      targetInputLoss targetDelta}
    {targetNormalizationExponent : ℕ}
    {targetNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := targetNormalizationLoss) targetSource
      targetNormalizationExponent}
    {targetShading : WZ1PaperTubeShading targetNormalized.croppedFamily}
    {targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) targetNormalized targetShading}
    {currentCanonicalWeight targetCanonicalWeight : ENNReal}
    {currentCanonicalLevel targetCanonicalLevel : ℕ}
    (pair : Proposition63FourCallReentryReceiptPair currentReentry
      targetReentry currentCanonicalWeight targetCanonicalWeight
      currentCanonicalLevel targetCanonicalLevel)
    (referenceFamily : Kakeya.Streamlined.TubeFamily referenceDelta)
    (current_card_le : currentNormalized.croppedFamily.card ≤
      referenceFamily.card)
    (target_card_le : targetNormalized.croppedFamily.card ≤
      referenceFamily.card)
    {incomingRetention incomingUpper ancestorRetention actual fraction : ENNReal}
    (ancestorReceipt : Proposition63FourCallReentryRetentionReceipt
      ancestorRetention currentReentry.regularized.regularizationLoss
      currentReentry.normalizationWeight incomingRetention)
    (incoming_le : incomingRetention ≤ incomingUpper)
    (pullbackReceipt : Proposition63FourCallPullbackRetentionReceipt actual
      fraction targetReentry.regularized.regularizationLoss
      targetReentry.normalizationWeight ancestorRetention) :
    actual ≤ proposition63FourCallPullbackRetentionFormula fraction
      (proposition63UniformReentryRegularizationLoss referenceFamily
        targetCanonicalLevel) targetCanonicalWeight
      (proposition63FourCallReentryRetentionFormula
        (proposition63UniformReentryRegularizationLoss referenceFamily
          currentCanonicalLevel) currentCanonicalWeight incomingUpper) := by
  apply pullbackReceipt.le_uniform_of_reentry pair.target referenceFamily
    target_card_le
  exact ancestorReceipt.le_uniform pair.current referenceFamily current_card_le
    incoming_le

end Kakeya.Assouad.PureWZ2
