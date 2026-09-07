import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallPaperFinalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63FourCallOrderedPairMass

/-!
# Paper-order mass majorizations for the four-call step

The paper assembly moves the target first-cover retained factor into the
pullback coefficient.  Consequently its ancestry cost is not bounded by the
legacy ancestry envelope itself.  This module records the corrected envelope
and the two M6 majorizations used to construct the actual mass receipt.
-/

noncomputable section

open scoped ENNReal NNReal

namespace Kakeya.Assouad.PureWZ2

/-- Root-cardinality lower bound for the retained fraction of the target's
first point cover. -/
noncomputable def proposition63FourCallPaperTargetRetainedLower
    {delta : ℝ} (rootFamily : Kakeya.Streamlined.TubeFamily delta) : ENNReal :=
  (81 / 400 : ENNReal) *
    (((Nat.log 2 rootFamily.card + 1 : ℕ) : ENNReal))⁻¹

/-- Correct ancestry envelope for the paper-order final assembly.  The target
first-cover factor has moved from the final coarse-left product into the
pullback coefficient, so its lower bound must be charged here. -/
noncomputable def proposition63FourCallPaperAncestorRetentionUpper
    {delta : ℝ} (rootFamily : Kakeya.Streamlined.TubeFamily delta)
    (legacyUpper : ENNReal) : ENNReal :=
  (proposition63FourCallPaperTargetRetainedLower rootFamily *
    legacyUpper⁻¹)⁻¹

/-- Scalar algebra behind the corrected paper ancestry envelope. -/
theorem proposition63_four_call_paper_assembly_retention_le
    {targetFactor targetLower fraction regularizationLoss normalizationWeight
      firstPullbackFactor legacyUpper assemblyFactor : ENNReal}
    (htarget : targetLower ≤ targetFactor)
    (hlegacy : proposition63FourCallPullbackRetentionFormula fraction
        regularizationLoss normalizationWeight firstPullbackFactor ≤
      legacyUpper)
    (hassembly : assemblyFactor =
      (regularizationLoss⁻¹ *
        (((73 / 100 : ENNReal) * normalizationWeight) *
          (fraction * targetFactor)) *
        (fraction * firstPullbackFactor⁻¹))⁻¹) :
    assemblyFactor ≤ (targetLower * legacyUpper⁻¹)⁻¹ := by
  rw [hassembly]
  apply ENNReal.inv_le_inv.mpr
  have hlegacyInv : legacyUpper⁻¹ ≤
      (proposition63FourCallPullbackRetentionFormula fraction
        regularizationLoss normalizationWeight firstPullbackFactor)⁻¹ :=
    ENNReal.inv_le_inv.mpr hlegacy
  unfold proposition63FourCallPullbackRetentionFormula at hlegacyInv
  rw [inv_inv] at hlegacyInv
  calc
    targetLower * legacyUpper⁻¹ ≤ targetFactor *
        (fraction *
          ((regularizationLoss⁻¹ *
              ((73 / 100 : ENNReal) * normalizationWeight)) *
            (fraction * firstPullbackFactor⁻¹))) := by
      gcongr
    _ = regularizationLoss⁻¹ *
          (((73 / 100 : ENNReal) * normalizationWeight) *
            (fraction * targetFactor)) *
          (fraction * firstPullbackFactor⁻¹) := by ring

/-- Inverse form used by the left-factor calculation: the target first-cover
retention and the legacy inverse ancestry cost fit inside the actual paper
assembly coefficient. -/
theorem proposition63_four_call_paper_target_mul_legacy_inv_le_assembly_inv
    {targetFactor targetLower fraction regularizationLoss normalizationWeight
      firstPullbackFactor legacyUpper assemblyFactor : ENNReal}
    (htarget : targetLower ≤ targetFactor)
    (hlegacy : proposition63FourCallPullbackRetentionFormula fraction
        regularizationLoss normalizationWeight firstPullbackFactor ≤
      legacyUpper)
    (hassembly : assemblyFactor =
      (regularizationLoss⁻¹ *
        (((73 / 100 : ENNReal) * normalizationWeight) *
          (fraction * targetFactor)) *
        (fraction * firstPullbackFactor⁻¹))⁻¹) :
    targetLower * legacyUpper⁻¹ ≤ assemblyFactor⁻¹ := by
  rw [hassembly, inv_inv]
  have hlegacyInv : legacyUpper⁻¹ ≤
      (proposition63FourCallPullbackRetentionFormula fraction
        regularizationLoss normalizationWeight firstPullbackFactor)⁻¹ :=
    ENNReal.inv_le_inv.mpr hlegacy
  unfold proposition63FourCallPullbackRetentionFormula at hlegacyInv
  rw [inv_inv] at hlegacyInv
  calc
    targetLower * legacyUpper⁻¹ ≤ targetFactor *
        (fraction *
          ((regularizationLoss⁻¹ *
              ((73 / 100 : ENNReal) * normalizationWeight)) *
            (fraction * firstPullbackFactor⁻¹))) := by
      gcongr
    _ = regularizationLoss⁻¹ *
          (((73 / 100 : ENNReal) * normalizationWeight) *
            (fraction * targetFactor)) *
          (fraction * firstPullbackFactor⁻¹) := by ring

/-- The target retained fraction has the advertised root-cardinality lower
bound along the complete embedding chain. -/
theorem Proposition63FourCallPaperRuntimeAssemblyData.targetRetainedLower_le
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
    {global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient}
    {index : ℕ} {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading family}
    {fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      (backward.seed index hindex).schedule.first.sourceLoss
      (backward.seed index hindex).schedule.first.normalizationLoss}
    {rootAxialWindow : ∀ sourceIndex point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8}
    {sourceMap : PaperWZ1WeakPlaneMapData fineShading incidence}
    {extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient}
    (fine_card_le : family.card ≤ root.normalization.croppedFamily.card)
    (runtime : Proposition63FourCallPaperRuntimeAssemblyData K backward root
      grid leftFactor rightFactor sourceCoefficient global index hindex scales
      fineReentry rootAxialWindow extension) :
    proposition63FourCallPaperTargetRetainedLower
        root.normalization.croppedFamily ≤
      runtime.paperNested.targetFirst.retainedFactor := by
  rw [runtime.paperNested.targetFirstRetainedFactor]
  unfold proposition63FourCallPaperTargetRetainedLower
  have htargetCurrent :
      runtime.paperNested.targetReentry.normalization.croppedFamily.card ≤
        runtime.currentResult.currentReentry.normalization.croppedFamily.card := by
    rw [runtime.paperNested.targetReentry.normalization_croppedFamily]
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      runtime.paperNested.targetReentry.regularized.selected.embedding
      runtime.paperNested.targetReentry.regularized.selected.embedding.injective
  have hcurrentRoot :
      runtime.currentResult.currentReentry.normalization.croppedFamily.card ≤
        root.normalization.croppedFamily.card := by
    rw [runtime.currentResult.currentReentry.normalization_croppedFamily]
    have hselectedCurrent :
        runtime.currentResult.currentReentry.regularized.selected.family.card ≤
          ((backward.seed index hindex).schedule.callOneRhoRootNormalization
            runtime.rich1 rootAxialWindow).croppedFamily.card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        runtime.currentResult.currentReentry.regularized.selected.embedding
        runtime.currentResult.currentReentry.regularized.selected.embedding.injective
    have hcurrentInitial :
        ((backward.seed index hindex).schedule.callOneRhoRootNormalization
            runtime.rich1 rootAxialWindow).croppedFamily.card ≤
          root.normalization.croppedFamily.card := by
      change runtime.rich1.data.coarse.card ≤
        root.normalization.croppedFamily.card
      have hcoarseSelected : runtime.rich1.data.coarse.card ≤
          runtime.rich1.data.selected.family.card := by
        simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective
          runtime.rich1.data.cover.toPaperTubeCover.parent
          runtime.rich1.data.cover.toPaperTubeCover.parent_surjective
      have hselectedFine : runtime.rich1.data.selected.family.card ≤ family.card := by
        simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
          runtime.rich1.data.selected.embedding
          runtime.rich1.data.selected.embedding.injective
      exact hcoarseSelected.trans (hselectedFine.trans fine_card_le)
    exact hselectedCurrent.trans hcurrentInitial
  have htargetSelected : runtime.paperNested.target.data.selected.family.card ≤
      runtime.paperNested.targetReentry.normalization.croppedFamily.card := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      runtime.paperNested.target.data.selected.embedding
      runtime.paperNested.target.data.selected.embedding.injective
  have hlog := proposition63_four_call_log_card_inv_mono <|
    htargetSelected.trans <| htargetCurrent.trans hcurrentRoot
  gcongr

/-- The call-one/call-two pullback occurring inside a paper runtime is still
controlled by the legacy ancestry envelope.  The extra target-first factor is
paid only when this pullback is composed into the final paper assembly. -/
theorem Proposition63FourCallPaperRuntimeAssemblyData.legacyPullbackRetention_le
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
    {global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient}
    {index : ℕ} {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading family}
    {fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      (backward.seed index hindex).schedule.first.sourceLoss
      (backward.seed index hindex).schedule.first.normalizationLoss}
    {rootAxialWindow : ∀ sourceIndex point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8}
    {sourceMap : PaperWZ1WeakPlaneMapData fineShading incidence}
    {extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient}
    (runtime : Proposition63FourCallPaperRuntimeAssemblyData K backward root
      grid leftFactor rightFactor sourceCoefficient global index hindex scales
      fineReentry rootAxialWindow extension)
    (fine_card_le : family.card ≤ root.normalization.croppedFamily.card) :
    proposition63FourCallPullbackRetentionFormula
        (wz2PaperPureRefinementFraction scales.rhoHat.1 61)
        runtime.paperNested.targetReentry.regularized.regularizationLoss
        runtime.paperNested.targetReentry.normalizationWeight
        runtime.firstPullback.retentionFactor ≤
      proposition63FourCallAncestorRetentionUpper
        root.normalization.croppedFamily scales.rhoHat.1 sigma
        (backward.seed index hindex).schedule.firstOutputLoss
        (backward.seed index hindex).schedule.second.normalizationLoss
        (backward.seed index hindex).schedule.second.sourceLoss
        (backward.seed index hindex).rhoWeightLoss
        (backward.seed index hindex).firstStageWeightLoss := by
  let seed := backward.seed index hindex
  let currentReentry := runtime.currentResult.currentReentry
  let targetReentry := runtime.paperNested.targetReentry
  let p1 := runtime.firstPullback
  let incomingRetention : ENNReal :=
    Kakeya.realRpowENN scales.rhoHat.1
        (2 - sigma - seed.schedule.firstOutputLoss) *
      runtime.rich1.data.coarse.enncard
  let incomingUpper : ENNReal :=
    proposition63FourCallIncomingRetentionUpper
      root.normalization.croppedFamily scales.rhoHat.1 sigma
      seed.schedule.firstOutputLoss
  have hcurrentInitialCard :
      (seed.schedule.callOneRhoRootNormalization runtime.rich1
          rootAxialWindow).croppedFamily.card ≤
        root.normalization.croppedFamily.card := by
    change runtime.rich1.data.coarse.card ≤
      root.normalization.croppedFamily.card
    have hcoarseSelected : runtime.rich1.data.coarse.card ≤
        runtime.rich1.data.selected.family.card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective
        runtime.rich1.data.cover.toPaperTubeCover.parent
        runtime.rich1.data.cover.toPaperTubeCover.parent_surjective
    have hselectedFine : runtime.rich1.data.selected.family.card ≤ family.card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        runtime.rich1.data.selected.embedding
        runtime.rich1.data.selected.embedding.injective
    exact hcoarseSelected.trans (hselectedFine.trans fine_card_le)
  have hcurrentNormalizedCard : currentReentry.normalization.croppedFamily.card ≤
      root.normalization.croppedFamily.card := by
    rw [runtime.currentResult.currentReentry.normalization_croppedFamily]
    have hselectedCurrent :
        runtime.currentResult.currentReentry.regularized.selected.family.card ≤
          (seed.schedule.callOneRhoRootNormalization runtime.rich1
            rootAxialWindow).croppedFamily.card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        runtime.currentResult.currentReentry.regularized.selected.embedding
        runtime.currentResult.currentReentry.regularized.selected.embedding.injective
    exact hselectedCurrent.trans hcurrentInitialCard
  let p1Receipt : Proposition63FourCallReentryRetentionReceipt
      p1.retentionFactor currentReentry.regularized.regularizationLoss
      currentReentry.normalizationWeight incomingRetention := ⟨by rfl⟩
  have hincoming : incomingRetention ≤ incomingUpper := by
    dsimp only [incomingRetention, incomingUpper,
      proposition63FourCallIncomingRetentionUpper]
    gcongr
    change (runtime.rich1.data.coarse.card : ENNReal) ≤
      (root.normalization.croppedFamily.card : ENNReal)
    exact_mod_cast hcurrentInitialCard
  let currentReceipt : Proposition63CanonicalReentryReceipt currentReentry
      (proposition63CanonicalReentryWeight scales.rhoHat.1 seed.rhoWeightLoss)
      (proposition63CanonicalNearbyLevelCount
        (seed.schedule.second.sourceLoss / 4)) :=
    ⟨runtime.currentResult.currentCanonicalWeight,
      runtime.currentResult.currentCanonicalLevel⟩
  have hp1Upper : p1.retentionFactor ≤
      proposition63FourCallReentryRetentionFormula
        (proposition63UniformReentryRegularizationLoss
          root.normalization.croppedFamily
          (proposition63CanonicalNearbyLevelCount
            (seed.schedule.second.sourceLoss / 4)))
        (proposition63CanonicalReentryWeight scales.rhoHat.1 seed.rhoWeightLoss)
        incomingUpper :=
    p1Receipt.le_uniform currentReceipt root.normalization.croppedFamily
      hcurrentInitialCard hincoming
  have htargetLevel : targetReentry.levelCount =
      proposition63CanonicalNearbyLevelCount
        seed.schedule.second.normalizationLoss :=
    runtime.paperNested.targetCanonicalLevel.trans <| congrArg
      proposition63CanonicalNearbyLevelCount
      runtime.currentResult.currentNormalization
  let targetReceipt : Proposition63CanonicalReentryReceipt targetReentry
      (proposition63CanonicalReentryWeight scales.rhoHat.1
        seed.firstStageWeightLoss)
      (proposition63CanonicalNearbyLevelCount
        seed.schedule.second.normalizationLoss) :=
    ⟨runtime.paperNested.targetCanonicalWeightExact, htargetLevel⟩
  exact targetReceipt.pullbackRetentionFormula_le
    root.normalization.croppedFamily hcurrentNormalizedCard
    (wz2PaperPureRefinementFraction scales.rhoHat.1 61)
    p1.retentionFactor _ hp1Upper

/-- The nested square-root selected family remains cardinality-bounded by the
fixed root family. -/
theorem Proposition63FourCallPaperRuntimeAssemblyData.nestedSqrtCard_le_root
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
    {global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient}
    {index : ℕ} {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading family}
    {fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      (backward.seed index hindex).schedule.first.sourceLoss
      (backward.seed index hindex).schedule.first.normalizationLoss}
    {rootAxialWindow : ∀ sourceIndex point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8}
    {sourceMap : PaperWZ1WeakPlaneMapData fineShading incidence}
    {extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient}
    (runtime : Proposition63FourCallPaperRuntimeAssemblyData K backward root
      grid leftFactor rightFactor sourceCoefficient global index hindex scales
      fineReentry rootAxialWindow extension)
    (fine_card_le : family.card ≤ root.normalization.croppedFamily.card) :
    runtime.paperNested.nested.sqrtSticky.selected.family.card ≤
      root.normalization.croppedFamily.card := by
  have hsqrtNested : runtime.paperNested.nested.sqrtSticky.selected.family.card ≤
      runtime.paperNested.nested.reentry.normalization.croppedFamily.card := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      runtime.paperNested.nested.sqrtSticky.selected.embedding
      runtime.paperNested.nested.sqrtSticky.selected.embedding.injective
  have hnestedCurrent :
      runtime.paperNested.nested.reentry.normalization.croppedFamily.card ≤
        runtime.currentResult.currentReentry.normalization.croppedFamily.card := by
    rw [runtime.paperNested.nested.reentry.normalization_croppedFamily]
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      runtime.paperNested.nested.reentry.regularized.selected.embedding
      runtime.paperNested.nested.reentry.regularized.selected.embedding.injective
  have hcurrentRoot :
      runtime.currentResult.currentReentry.normalization.croppedFamily.card ≤
        root.normalization.croppedFamily.card := by
    rw [runtime.currentResult.currentReentry.normalization_croppedFamily]
    have hselectedCurrent :
        runtime.currentResult.currentReentry.regularized.selected.family.card ≤
          ((backward.seed index hindex).schedule.callOneRhoRootNormalization
            runtime.rich1 rootAxialWindow).croppedFamily.card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        runtime.currentResult.currentReentry.regularized.selected.embedding
        runtime.currentResult.currentReentry.regularized.selected.embedding.injective
    have hcoarseRoot : runtime.rich1.data.coarse.card ≤
        root.normalization.croppedFamily.card := by
      have hcoarseSelected : runtime.rich1.data.coarse.card ≤
          runtime.rich1.data.selected.family.card := by
        simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective
          runtime.rich1.data.cover.toPaperTubeCover.parent
          runtime.rich1.data.cover.toPaperTubeCover.parent_surjective
      have hselectedFine : runtime.rich1.data.selected.family.card ≤ family.card := by
        simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
          runtime.rich1.data.selected.embedding
          runtime.rich1.data.selected.embedding.injective
      exact hcoarseSelected.trans (hselectedFine.trans fine_card_le)
    exact hselectedCurrent.trans hcoarseRoot
  exact hsqrtNested.trans (hnestedCurrent.trans hcurrentRoot)

/-- The normalization on which the nested re-entry starts is cardinality
bounded by the fixed root family. -/
theorem Proposition63FourCallPaperRuntimeAssemblyData.currentReentryCard_le_root
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
    {global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient}
    {index : ℕ} {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading family}
    {fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      (backward.seed index hindex).schedule.first.sourceLoss
      (backward.seed index hindex).schedule.first.normalizationLoss}
    {rootAxialWindow : ∀ sourceIndex point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8}
    {sourceMap : PaperWZ1WeakPlaneMapData fineShading incidence}
    {extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient}
    (runtime : Proposition63FourCallPaperRuntimeAssemblyData K backward root
      grid leftFactor rightFactor sourceCoefficient global index hindex scales
      fineReentry rootAxialWindow extension)
    (fine_card_le : family.card ≤ root.normalization.croppedFamily.card) :
    runtime.currentResult.currentReentry.normalization.croppedFamily.card ≤
      root.normalization.croppedFamily.card := by
  rw [runtime.currentResult.currentReentry.normalization_croppedFamily]
  have hselectedCurrent :
      runtime.currentResult.currentReentry.regularized.selected.family.card ≤
        ((backward.seed index hindex).schedule.callOneRhoRootNormalization
          runtime.rich1 rootAxialWindow).croppedFamily.card := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
      runtime.currentResult.currentReentry.regularized.selected.embedding
      runtime.currentResult.currentReentry.regularized.selected.embedding.injective
  have hcoarseRoot : runtime.rich1.data.coarse.card ≤
      root.normalization.croppedFamily.card := by
    have hcoarseSelected : runtime.rich1.data.coarse.card ≤
        runtime.rich1.data.selected.family.card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective
        runtime.rich1.data.cover.toPaperTubeCover.parent
        runtime.rich1.data.cover.toPaperTubeCover.parent_surjective
    have hselectedFine : runtime.rich1.data.selected.family.card ≤ family.card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        runtime.rich1.data.selected.embedding
        runtime.rich1.data.selected.embedding.injective
    exact hcoarseSelected.trans (hselectedFine.trans fine_card_le)
  exact hselectedCurrent.trans hcoarseRoot

/-- The paper nested preparation budget is bounded by the fixed root-family
budget, with both cardinality and scale monotonicity made explicit. -/
theorem Proposition63FourCallPaperRuntimeAssemblyData.nestedPreparationLoss_le_root
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
    {global : Proposition63FourCallPaperPreludeGlobalData
      (incidence := incidence) K backward root grid leftFactor rightFactor
      sourceCoefficient}
    {index : ℕ} {hindex : index < (finiteIntervalOrderedPairs gridN).length}
    {scales : Proposition63FourCallOrderedPairIndexScales grid index}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading family}
    {fineReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) fineShading normalizationExponent
      (backward.seed index hindex).schedule.first.sourceLoss
      (backward.seed index hindex).schedule.first.normalizationLoss}
    {rootAxialWindow : ∀ sourceIndex point,
      point ∈ fineReentry.geometry.frame ''
          fineReentry.geometry.ordinaryRefined.carrier sourceIndex →
        |point (2 : Fin 3)| ≤ 1 / 8}
    {sourceMap : PaperWZ1WeakPlaneMapData fineShading incidence}
    {extension : PureWZ2UnitAmbientWeakPlaneMapExtension
      sourceMap sourceCoefficient}
    (runtime : Proposition63FourCallPaperRuntimeAssemblyData K backward root
      grid leftFactor rightFactor sourceCoefficient global index hindex scales
      fineReentry rootAxialWindow extension)
    (fine_card_le : family.card ≤ root.normalization.croppedFamily.card) :
    runtime.paperNested.nested.prepared.preparationLoss ≤
      proposition63UniformPreparationLoss root.normalization.croppedFamily := by
  refine runtime.paperNested.nestedPreparationLoss.trans ?_
  have hcoarseRoot : runtime.rich1.data.coarse.card ≤
      root.normalization.croppedFamily.card := by
    have hcoarseSelected : runtime.rich1.data.coarse.card ≤
        runtime.rich1.data.selected.family.card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective
        runtime.rich1.data.cover.toPaperTubeCover.parent
        runtime.rich1.data.cover.toPaperTubeCover.parent_surjective
    have hselectedFine : runtime.rich1.data.selected.family.card ≤ family.card := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
        runtime.rich1.data.selected.embedding
        runtime.rich1.data.selected.embedding.injective
    exact hcoarseSelected.trans (hselectedFine.trans fine_card_le)
  have hlog :
      ((Nat.log 2 runtime.rich1.data.coarse.card + 1 : ℕ) : ENNReal) ≤
        ((Nat.log 2 root.normalization.croppedFamily.card + 1 : ℕ) : ENNReal) := by
    exact_mod_cast Nat.add_le_add_right (Nat.log_mono_right hcoarseRoot) 1
  unfold proposition63UniformPreparationLoss
  exact mul_le_mul hlog
    (proposition63FreshBalancingEnvelope_antitone
      root.normalization.final_extremal.delta_pos
      scales.rhoHat.property.1) (by positivity) (by positivity)

/-- The exact paper final assembly is bounded by the corrected ancestry
envelope once the legacy first-pullback bound is known. -/
theorem Proposition63FourCallPaperFinalAssemblyData.retentionFactor_le_paperUpper
    {delta : ℝ} {innerFamily outerFamily : Kakeya.Streamlined.TubeFamily delta}
    {inner : WZ1PaperTubeShading innerFamily}
    {outer : WZ1PaperTubeShading outerFamily}
    {targetFactor targetLower restoredFactor firstPullbackFactor
      regularizationLoss normalizationWeight legacyUpper : ENNReal}
    (assembly : Proposition63FourCallPaperFinalAssemblyData inner outer
      (proposition63FourCallPaperPullbackCoefficient delta restoredFactor
        firstPullbackFactor))
    (htarget : targetLower ≤ targetFactor)
    (hrestored : restoredFactor = regularizationLoss⁻¹ *
      (((73 / 100 : ENNReal) * normalizationWeight) *
        (wz2PaperPureRefinementFraction delta 61 * targetFactor)))
    (hlegacy : proposition63FourCallPullbackRetentionFormula
        (wz2PaperPureRefinementFraction delta 61) regularizationLoss
        normalizationWeight firstPullbackFactor ≤ legacyUpper) :
    assembly.pullback.retentionFactor ≤
      (targetLower * legacyUpper⁻¹)⁻¹ := by
  apply proposition63_four_call_paper_assembly_retention_le htarget hlegacy
  rw [assembly.retentionFactor_eq]
  unfold proposition63FourCallPaperPullbackCoefficient
  rw [hrestored]

/-- The paper nested retained product after the target-first factor has moved
into the assembly pullback. -/
noncomputable def proposition63FourCallPaperFrozenNestedRetainedFactor
    (delta : ℝ) (uniformCard : ℕ) (canonicalWeight : ENNReal) : ENNReal :=
  ((81 / 400 : ENNReal) *
      (((Nat.log 2 uniformCard + 1 : ℕ) : ENNReal))⁻¹ *
      wz2PaperPureRefinementFraction delta 61) *
    ((73 / 100 : ENNReal) * canonicalWeight)

/-- Moving the target-first retained factor into the ancestry coefficient does
not change the frozen left scalar. -/
theorem proposition63_four_call_frozen_left_eq_paper_left
    {delta : ℝ} (rootFamily : Kakeya.Streamlined.TubeFamily delta)
    (rho sigma outerLoss fineWeightLoss : ℝ) (outerLogExponent : ℕ)
    (legacyUpper frozenLineCoverBase canonicalNestedWeight : ENNReal) :
    proposition63FourCallFrozenActualLeftFactor rootFamily delta rho sigma
        outerLoss fineWeightLoss outerLogExponent legacyUpper
        frozenLineCoverBase canonicalNestedWeight =
      proposition63UniformDependentFinePullbackLeft rootFamily delta rho sigma
        outerLoss outerLogExponent
        (proposition63CanonicalReentryWeight delta fineWeightLoss)
        (proposition63FourCallPaperAncestorRetentionUpper rootFamily
          legacyUpper)
        (frozenLineCoverBase *
          proposition63FourCallPaperFrozenNestedRetainedFactor rho
            rootFamily.card canonicalNestedWeight) := by
  unfold proposition63FourCallFrozenActualLeftFactor
    proposition63FourCallFrozenNestedRetainedFactor
    proposition63FourCallPaperFrozenNestedRetainedFactor
    proposition63FourCallPaperAncestorRetentionUpper
    proposition63FourCallPaperTargetRetainedLower
    proposition63UniformDependentFinePullbackLeft
  rw [inv_inv]
  ring

/-- M6 left majorization in paper order.  The caller supplies the corrected
assembly ancestry bound; only the nested second-cover cardinality remains in
the coarse retained product because `nested.firstRetainedFactor = 1`. -/
theorem proposition63_four_call_paper_frozen_left_le_actual
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss
      outerLoss fineWeightLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent outerLogExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {requested : WZ2PaperRequestedScale delta}
    (outer : PureWZ2PropStickyData (sigma := sigma) (outputLoss := outerLoss)
      fineReentry.normalization.croppedRefined requested outerLogExponent)
    (legacyUpper assemblyFactor frozenLineCoverBase actualLineCoverBase
      canonicalNestedWeight secondRetainedFactor normalizationWeight : ENNReal)
    (secondTargetCard : ℕ)
    (hassembly : assemblyFactor ≤
      proposition63FourCallPaperAncestorRetentionUpper
        initialNormalized.croppedFamily legacyUpper)
    (hsecond : secondRetainedFactor =
      (81 / 400 : ENNReal) *
        (((Nat.log 2 secondTargetCard + 1 : ℕ) : ENNReal))⁻¹ *
        wz2PaperPureRefinementFraction requested.1 61)
    (hweight : normalizationWeight = canonicalNestedWeight)
    (hsecondCard : secondTargetCard ≤ initialNormalized.croppedFamily.card)
    (hfineWeight : fineReentry.normalizationWeight =
      proposition63CanonicalReentryWeight delta fineWeightLoss)
    (hbase : frozenLineCoverBase ≤ actualLineCoverBase) :
    proposition63FourCallFrozenActualLeftFactor
        initialNormalized.croppedFamily delta requested.1 sigma outerLoss
        fineWeightLoss outerLogExponent legacyUpper frozenLineCoverBase
        canonicalNestedWeight ≤
      proposition63DependentFinePullbackLeft fineReentry outer assemblyFactor
        (actualLineCoverBase *
          (secondRetainedFactor *
            ((73 / 100 : ENNReal) * normalizationWeight) * 1)) := by
  rw [proposition63_four_call_frozen_left_eq_paper_left]
  calc
    proposition63UniformDependentFinePullbackLeft
          initialNormalized.croppedFamily delta requested.1 sigma outerLoss
          outerLogExponent
          (proposition63CanonicalReentryWeight delta fineWeightLoss)
          (proposition63FourCallPaperAncestorRetentionUpper
            initialNormalized.croppedFamily legacyUpper)
          (frozenLineCoverBase *
            proposition63FourCallPaperFrozenNestedRetainedFactor requested.1
              initialNormalized.croppedFamily.card canonicalNestedWeight) ≤
        proposition63UniformDependentFinePullbackLeft
          initialNormalized.croppedFamily delta requested.1 sigma outerLoss
          outerLogExponent
          (proposition63CanonicalReentryWeight delta fineWeightLoss)
          assemblyFactor
          (actualLineCoverBase *
            (secondRetainedFactor *
              ((73 / 100 : ENNReal) * normalizationWeight) * 1)) := by
      unfold proposition63UniformDependentFinePullbackLeft
      have hretained :
          proposition63FourCallPaperFrozenNestedRetainedFactor requested.1
              initialNormalized.croppedFamily.card canonicalNestedWeight ≤
            secondRetainedFactor *
              ((73 / 100 : ENNReal) * normalizationWeight) * 1 := by
        have hlog := proposition63_four_call_log_card_inv_mono hsecondCard
        unfold proposition63FourCallPaperFrozenNestedRetainedFactor
        rw [hsecond, hweight]
        calc
          ((81 / 400 : ENNReal) *
                (((Nat.log 2 initialNormalized.croppedFamily.card + 1 : ℕ) :
                  ENNReal))⁻¹ * wz2PaperPureRefinementFraction requested.1 61) *
              ((73 / 100 : ENNReal) * canonicalNestedWeight) ≤
            ((81 / 400 : ENNReal) *
                (((Nat.log 2 secondTargetCard + 1 : ℕ) : ENNReal))⁻¹ *
                wz2PaperPureRefinementFraction requested.1 61) *
              ((73 / 100 : ENNReal) * canonicalNestedWeight) := by gcongr
          _ = (((81 / 400 : ENNReal) *
                (((Nat.log 2 secondTargetCard + 1 : ℕ) : ENNReal))⁻¹ *
                wz2PaperPureRefinementFraction requested.1 61) *
              ((73 / 100 : ENNReal) * canonicalNestedWeight)) * 1 := by simp
      gcongr
    _ ≤ proposition63DependentFinePullbackLeft fineReentry outer assemblyFactor
          (actualLineCoverBase *
            (secondRetainedFactor *
              ((73 / 100 : ENNReal) * normalizationWeight) * 1)) :=
      proposition63_uniformDependentFinePullbackLeft_le fineReentry outer
        assemblyFactor _ hfineWeight

/-- M6 right majorization for the old `8 * rho` tail.  Unlike the legacy
route, the nested level bound is the paper-nested level frozen before the
runtime is selected. -/
theorem proposition63_four_call_paper_actual_right_le_frozen
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalizationExponent nestedNormalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource
      initialNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {nestedInputLoss nestedNormalizationLoss nestedReentryLoss rho : ℝ}
    {nestedSource : PureWZ2ExtremalConfiguration sigma nestedInputLoss rho}
    {nestedNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := nestedNormalizationLoss) nestedSource
      nestedNormalizationExponent}
    {nestedCurrent : WZ1PaperTubeShading nestedNormalized.croppedFamily}
    (nestedReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := nestedReentryLoss) nestedNormalized nestedCurrent)
    (preparationLoss : ENNReal) (uniformLevel : ℕ)
    (fine_level_le : fineReentry.levelCount ≤ uniformLevel)
    (nested_card_le : nestedNormalized.croppedFamily.card ≤
      initialNormalized.croppedFamily.card)
    (nested_level_le : nestedReentry.levelCount ≤ uniformLevel)
    (preparation_le : preparationLoss ≤
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
  have nested_regularization_le :
      nestedReentry.regularized.regularizationLoss ≤
        proposition63UniformReentryRegularizationLoss
          initialNormalized.croppedFamily uniformLevel :=
    proposition63_reentry_regularizationLoss_le_uniform nestedReentry
      initialNormalized.croppedFamily uniformLevel nested_card_le nested_level_le
  have rho_tail_le : 2 * ENNReal.ofReal (4 * rho) ≤ (2 : ENNReal) := by
    calc
      2 * ENNReal.ofReal (4 * rho) ≤ 2 * ENNReal.ofReal 1 := by gcongr
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
          initialNormalized.croppedFamily uniformLevel := by gcongr
    _ = (proposition63UniformReentryRegularizationLoss
          initialNormalized.croppedFamily uniformLevel *
        (proposition63UniformPreparationLoss
          initialNormalized.croppedFamily * 2)) *
        proposition63UniformReentryRegularizationLoss
          initialNormalized.croppedFamily uniformLevel := by ring

/-- Receipt-facing specialization of the right majorization.  Its final two
premises are discharged in the paper runtime by
`paperNested.nestedCanonicalLevel` followed by the frozen
`hpaperNestedLevel`, and by `paperNested.nestedPreparationLoss`. -/
theorem Proposition63FourCallPaperNestedPointCoverData.actualRight_le_frozen
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource
      initialNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {initialInputLoss' normalizationLoss' firstReentryLoss
      outerLoss targetReentryLoss targetNormalizationLoss targetLoss
      targetFirstLoss restoredFirstLoss reentryLoss sqrtStickyLoss secondLoss
      finalLoss tauScale sqrtScale incidenceBound : ℝ}
    {initialSource' : PureWZ2ExtremalConfiguration sigma initialInputLoss' delta}
    {initialNormalized' : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss') initialSource' 0}
    {current : WZ1PaperTubeShading initialNormalized'.croppedFamily}
    {firstReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := firstReentryLoss) initialNormalized' current}
    {hfirstReentryLoss : 0 < firstReentryLoss}
    {robustScale targetScale sqrtRequested : WZ2PaperRequestedScale delta}
    {currentMap : PaperWZ1WeakPlaneMapData current incidenceBound}
    {tauConstant sqrtConstant : ENNReal}
    {targetWeightLoss nestedWeightLoss : ℝ}
    (paperNested : Proposition63FourCallPaperNestedPointCoverData
      (outerLoss := outerLoss) (targetReentryLoss := targetReentryLoss)
      (targetNormalizationLoss := targetNormalizationLoss)
      (targetLoss := targetLoss) (targetFirstLoss := targetFirstLoss)
      (restoredFirstLoss := restoredFirstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := sqrtStickyLoss) (secondLoss := secondLoss)
      (finalLoss := finalLoss) (tauScale := tauScale)
      (sqrtScale := sqrtScale) firstReentry hfirstReentryLoss robustScale
      targetScale sqrtRequested currentMap tauConstant sqrtConstant
      targetWeightLoss nestedWeightLoss)
    (uniformLevel : ℕ)
    (fine_level_le : fineReentry.levelCount ≤ uniformLevel)
    (nested_card_le : firstReentry.normalization.croppedFamily.card ≤
      initialNormalized.croppedFamily.card)
    (paper_nested_level_le :
      proposition63CanonicalNearbyLevelCount
        firstReentry.reentryNormalizationLoss ≤ uniformLevel)
    (preparation_upper_le :
      proposition63UniformPreparationLoss initialNormalized'.croppedFamily ≤
        proposition63UniformPreparationLoss initialNormalized.croppedFamily)
    (four_rho_le_one : 4 * delta ≤ 1) :
    proposition63DependentFinePullbackRight fineReentry
        ((paperNested.nested.reentry.regularized.regularizationLoss *
            paperNested.nested.prepared.preparationLoss) *
          (2 * ENNReal.ofReal (4 * delta))) ≤
      proposition63UniformDependentRightFactor
        initialNormalized.croppedFamily uniformLevel := by
  apply proposition63_four_call_paper_actual_right_le_frozen
  · exact fine_level_le
  · exact nested_card_le
  · exact paperNested.nestedCanonicalLevel.le.trans paper_nested_level_le
  · exact paperNested.nestedPreparationLoss.trans preparation_upper_le
  · exact four_rho_le_one

/-- Specialize the paper right majorization when the intermediate
normalization and preparation budgets have already been transported to the
root family. -/
theorem proposition63_four_call_paper_actual_right_le_root
    {delta sigma initialInputLoss normalizationLoss fineReentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource
      initialNormalizationExponent}
    {fineCurrent : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (fineReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := fineReentryLoss) initialNormalized fineCurrent)
    {nestedInputLoss nestedNormalizationLoss nestedReentryLoss rho : ℝ}
    {nestedSource : PureWZ2ExtremalConfiguration sigma nestedInputLoss rho}
    {nestedNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := nestedNormalizationLoss) nestedSource 0}
    {nestedCurrent : WZ1PaperTubeShading nestedNormalized.croppedFamily}
    (nestedReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := nestedReentryLoss) nestedNormalized nestedCurrent)
    (preparationLoss : ENNReal) (uniformLevel : ℕ)
    (fine_level_le : fineReentry.levelCount ≤ uniformLevel)
    (nested_card_le : nestedNormalized.croppedFamily.card ≤
      initialNormalized.croppedFamily.card)
    (nested_level_le : nestedReentry.levelCount ≤ uniformLevel)
    (preparation_le : preparationLoss ≤
      proposition63UniformPreparationLoss initialNormalized.croppedFamily)
    (four_rho_le_one : 4 * rho ≤ 1) :
    proposition63DependentFinePullbackRight fineReentry
        ((nestedReentry.regularized.regularizationLoss * preparationLoss) *
          (2 * ENNReal.ofReal (4 * rho))) ≤
      proposition63UniformDependentRightFactor
        initialNormalized.croppedFamily uniformLevel :=
  proposition63_four_call_paper_actual_right_le_frozen fineReentry
    nestedReentry preparationLoss uniformLevel fine_level_le nested_card_le
    nested_level_le preparation_le four_rho_le_one

end Kakeya.Assouad.PureWZ2
