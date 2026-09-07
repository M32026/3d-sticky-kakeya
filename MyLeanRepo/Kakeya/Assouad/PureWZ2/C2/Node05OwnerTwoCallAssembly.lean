import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerIntermediateGrains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05SecondOwnerInputCompanion
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerTwoCallWiring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05DeterministicOwnerCall

/-!
# Dependent assembly of two concrete Node 5 owner calls

This module packages the complete input ledger of the concrete owner call and
wires two supplied calls through the actual coarse grain refinement selected
after the first call.  The second re-entry is produced from the canonical
post-grain trace receipt; the universal owner inputs remain explicit.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Transport exact re-entry data across an equality of the indexed family and
a heterogeneous equality of the corresponding shading. -/
private noncomputable def transportReentry
    {sigma delta sourceLoss normalizationLoss : ℝ}
    {firstFamily secondFamily : Kakeya.Streamlined.TubeFamily delta}
    {firstShading : WZ1PaperTubeShading firstFamily}
    {secondShading : WZ1PaperTubeShading secondFamily}
    {normalizationExponent : ℕ}
    (familyEq : firstFamily = secondFamily)
    (shadingEq : HEq firstShading secondShading)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) firstShading normalizationExponent
      sourceLoss normalizationLoss) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) secondShading normalizationExponent
      sourceLoss normalizationLoss := by
  subst secondFamily
  have shadingEq' : firstShading = secondShading := eq_of_heq shadingEq
  subst secondShading
  exact reentry

/-- The parentwise density receipt used by one concrete owner call. -/
def PureWZ2Node05OwnerDensityAbsorption
    {delta sigma sourceLoss normalizationLoss seedLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent seedLogExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (input : PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := seedLoss) normalized callerRequested seedLogExponent)
    (outputLoss : ℝ) : Prop :=
  ∀ parent : Fin input.data.selectedPacked.family.card,
    Kakeya.realRpowENN (delta / callerRequested.1) outputLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
        (((restrictPaperShading
              (input.data.internalCover.fullFiberSubfamily parent)
              input.data.finalFineShading).mass / 2) /
          ((input.data.internalCover.fullFiberSubfamily parent).family.enncard *
            Kakeya.realRpowENN delta 2))

/-- The owner full-fiber comparison used by one concrete owner call. -/
def PureWZ2Node05OwnerUniformity
    {delta sigma sourceLoss normalizationLoss seedLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent seedLogExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (input : PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := seedLoss) normalized callerRequested seedLogExponent)
    (outputLoss : ℝ) : Prop :=
  ∀ first second : Fin input.data.selectedPacked.family.card,
    ((wz2PaperFullFiberIndices input.data.selectedFine.family
        input.data.selectedPacked.family first).card : ENNReal) ≤
      Kakeya.realRpowENN callerRequested.1 (-outputLoss) *
        ((wz2PaperFullFiberIndices input.data.selectedFine.family
          input.data.selectedPacked.family second).card : ENNReal)

/-- All receipts needed to run the concrete owner post-refinement call on one
fixed universal input.  The dependent indices of the input are retained by the
type of the package. -/
structure PureWZ2Node05OwnerCallReceipt
    {delta sigma sourceLoss normalizationLoss seedLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent seedLogExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (input : PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := seedLoss) normalized callerRequested seedLogExponent)
    (outputLoss : ℝ) (outputLogExponent : ℕ) where
  sourceFineLoss : ℝ
  structuralBudget : ℝ
  companion : PureWZ2Node05OwnerReentryCompanion input
  fineExponent : ℕ
  logExponent_eq : seedLogExponent + fineExponent = outputLogExponent
  refinementScalar :
    2 * wz1PaperRefinementFraction delta fineExponent ≤ 1
  sourceFineExtremal :
    WZ2PaperCroppedIsExtremal sigma sourceFineLoss
      companion.toReentrant.data.selected.family input.data.finalFineShading
  criticalFloor : PureWZ2CroppedCriticalFloorSelectionData
    sigma outputLoss structuralBudget
  seed_le_structural : seedLoss ≤ criticalFloor.structuralLoss
  source_le_structural : sourceFineLoss ≤ criticalFloor.structuralLoss
  structural_le_output : criticalFloor.structuralLoss ≤ outputLoss
  absorption :
    2 * Kakeya.realRpowENN delta criticalFloor.structuralLoss ≤
      Kakeya.realRpowENN delta sourceFineLoss
  delta_cutoff : delta ≤ criticalFloor.delta₀
  rho_cutoff : callerRequested.1 ≤ criticalFloor.delta₀
  ratioSmall : delta / callerRequested.1 ≤ 1 / 24
  densityAbsorption : PureWZ2Node05OwnerDensityAbsorption input outputLoss
  ownerUniform : PureWZ2Node05OwnerUniformity input outputLoss

namespace PureWZ2Node05OwnerCallReceipt

/-- Legacy universal-input adapter into the deterministic/re-entry call ABI. -/
noncomputable def toDeterministic
    {delta sigma sourceLoss normalizationLoss seedLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent seedLogExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    {input : PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := seedLoss) normalized callerRequested seedLogExponent}
    {outputLogExponent : ℕ}
    (receipt : PureWZ2Node05OwnerCallReceipt
      input outputLoss outputLogExponent) :
    PureWZ2Node05DeterministicOwnerCallReceipt
      receipt.companion.toReentrant outputLoss outputLogExponent := by
  let oldExact := input.data.toExactMultiplicityData
  let exact :
      PureWZ2Node05DeterministicExactInput
        receipt.companion.toReentrant source.extremal.delta_pos :=
    { m := oldExact.m
      m_pos := oldExact.m_pos
      truncation := oldExact.truncation
      fineCellNested := input.data.fineCellNested }
  refine
    { delta_pos := source.extremal.delta_pos
      sourceFineLoss := receipt.sourceFineLoss
      structuralBudget := receipt.structuralBudget
      fineExponent := receipt.fineExponent
      logExponent_eq := receipt.logExponent_eq
      refinementScalar := receipt.refinementScalar
      exact := exact
      sourceFineExtremal := receipt.sourceFineExtremal
      criticalFloor := receipt.criticalFloor
      seed_le_structural := receipt.seed_le_structural
      source_le_structural := receipt.source_le_structural
      structural_le_output := receipt.structural_le_output
      absorption := receipt.absorption
      delta_cutoff := receipt.delta_cutoff
      rho_cutoff := receipt.rho_cutoff
      density := ?_
      uniform := ?_ }
  · intro parent
    let oldOutput :=
      (Classical.choice
        (receipt.companion.toReentrant.data.rescaledFiber parent)).mono_loss
          (receipt.seed_le_structural.trans receipt.structural_le_output)
    exact
      ⟨input.data.refreshExactFiberOfOldDensity parent receipt.ratioSmall
        oldOutput (receipt.densityAbsorption parent)⟩
  · exact
      pureWZ2Node05Owner_fullFiberUniformity input receipt.companion
        receipt.fineExponent receipt.refinementScalar receipt.ownerUniform

/-- Transporting the concrete call only in its output log index does not
change its coarse family. -/
private theorem transported_coarse_eq
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {seedNormalizationExponent seedLogExponent firstLog secondLog : ℕ}
    (h : firstLog = secondLog)
    (raw : PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent firstLog) :
    (Eq.mp (congrArg (fun exponent =>
      PureWZ2Node05ExactMultiplicityPostRefinementData
        (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
        sourceShading rho seedNormalizationExponent seedLogExponent exponent) h)
        raw).toNode5StickyData.data.coarse =
      raw.toNode5StickyData.data.coarse := by
  subst secondLog
  rfl

/-- The same output-log transport preserves the exact cropped coarse shading. -/
private theorem transported_coarseShading_heq
    {delta sigma seedLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {seedNormalizationExponent seedLogExponent firstLog secondLog : ℕ}
    (h : firstLog = secondLog)
    (raw : PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      sourceShading rho seedNormalizationExponent seedLogExponent firstLog) :
    HEq
      (Eq.mp (congrArg (fun exponent =>
        PureWZ2Node05ExactMultiplicityPostRefinementData
          (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
          sourceShading rho seedNormalizationExponent seedLogExponent exponent) h)
          raw).toNode5StickyData.croppedCoarseShading
      raw.toNode5StickyData.croppedCoarseShading := by
  subst secondLog
  rfl

/-- Execute the owner call recorded by the receipt. -/
noncomputable def output
    {delta sigma sourceLoss normalizationLoss seedLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent seedLogExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    {input : PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := seedLoss) normalized callerRequested seedLogExponent}
    {outputLoss : ℝ} {outputLogExponent : ℕ}
    (receipt : PureWZ2Node05OwnerCallReceipt
      input outputLoss outputLogExponent) :
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss)
      (outputLoss := outputLoss) normalized.croppedRefined
      callerRequested normalizationExponent seedLogExponent
      outputLogExponent :=
  Eq.mp (congrArg (fun exponent =>
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss)
      (outputLoss := outputLoss) normalized.croppedRefined callerRequested
      normalizationExponent seedLogExponent exponent)
    receipt.logExponent_eq)
    (pureWZ2Node05OwnerConcretePostRefinement input receipt.companion
      receipt.fineExponent receipt.refinementScalar receipt.sourceFineExtremal
      receipt.criticalFloor receipt.seed_le_structural
      receipt.source_le_structural receipt.structural_le_output
      receipt.absorption receipt.delta_cutoff receipt.rho_cutoff
      receipt.ratioSmall receipt.densityAbsorption receipt.ownerUniform)

end PureWZ2Node05OwnerCallReceipt

/-- The explicitly supplied continuation after the actual intermediate grain
refinement has been chosen.  Its owner input is indexed by that refinement,
and the equality records that the second call ends at the requested common log
index. -/
structure PureWZ2Node05SecondOwnerContinuation
    {sigma firstLoss middleLoss fineSeedLoss secondLoss : ℝ}
    {delta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {firstLogExponent reentryNormalizationExponent secondLogExponent
      commonLogExponent : ℕ}
    (first : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := firstLoss)
      sourceShading rhoRequested firstLogExponent)
    (coarseGrains : PureWZ2GrainRefinementData
      first.croppedCoarseShading sigma middleLoss)
    (sqrtRequested : WZ2PaperRequestedScale rhoRequested.1) where
  reentrySourceLoss : ℝ
  ancestorNormalizationLoss : ℝ
  ancestor : PureWZ2PropStickyReentryData
    (sigma := sigma) first.croppedCoarseShading
    reentryNormalizationExponent reentrySourceLoss
    ancestorNormalizationLoss
  companion : PureWZ2Node05SecondOwnerInputCompanion
    (secondLoss := fineSeedLoss) first coarseGrains sqrtRequested
    reentryNormalizationExponent secondLogExponent
    reentrySourceLoss ancestorNormalizationLoss ancestor
  call : @PureWZ2Node05OwnerCallReceipt rhoRequested.1 sigma
    reentrySourceLoss middleLoss fineSeedLoss
    companion.reentry.ordinarySource reentryNormalizationExponent
    secondLogExponent companion.reentry.toNormalizationData sqrtRequested
    companion.secondInput secondLoss commonLogExponent

/-- Assemble the strongest two-call package available from existing receipts.
The continuation is dependent on the actual `coarseGrains` selected by the
same-extremizer schedule. -/
theorem pureWZ2Node05_twoCallOfFirstExact
    {sigma inputLoss delta rho middleLoss firstLoss outputLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {logExponent : ℕ}
    (coarseSeedLoss : ℝ)
    (coarseSeedNormalizationExponent coarseSeedLogExponent : ℕ)
    (rhoRequested : WZ2PaperRequestedScale delta)
    (rhoRequested_eq : rhoRequested.1 = rho)
    (first : PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := coarseSeedLoss)
      (outputLoss := firstLoss) source.shading rhoRequested
      coarseSeedNormalizationExponent coarseSeedLogExponent logExponent)
    (schedule : PureWZ2Node05SameExtremizerSchedule sigma middleLoss)
    (coarse_slope_eq : ∀ coarseGrains : PureWZ2GrainRefinementData
        first.toNode5StickyData.croppedCoarseShading sigma middleLoss,
      coarseGrains.globalGrains.slope = source.globalGrains.slope)
    (firstLoss_le_input : firstLoss ≤ schedule.inputLoss)
    (rho_le_delta₀ : rhoRequested.1 ≤ schedule.delta₀)
    (sqrtRequested : WZ2PaperRequestedScale rhoRequested.1)
    (sqrtRequested_eq : sqrtRequested.1 = Real.sqrt rho)
    (fineSeedLoss : ℝ)
    (reentryNormalizationExponent secondLogExponent : ℕ)
    (continuation : ∀ coarseGrains : PureWZ2GrainRefinementData
        first.toNode5StickyData.croppedCoarseShading sigma middleLoss,
      PureWZ2Node05SecondOwnerContinuation
        (fineSeedLoss := fineSeedLoss)
        (secondLoss := outputLoss)
        (reentryNormalizationExponent := reentryNormalizationExponent)
        (secondLogExponent := secondLogExponent)
        (commonLogExponent := logExponent)
        first.toNode5StickyData coarseGrains sqrtRequested) :
    Nonempty (PureWZ2Node05TwoCallExactMultiplicityWiring
      source rho middleLoss outputLoss logExponent) := by
  rcases pureWZ2Node05Owner_intermediateGrains first.toNode5StickyData
      schedule firstLoss_le_input rho_le_delta₀ with ⟨coarseGrains⟩
  let next := continuation coarseGrains
  have fine : PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := fineSeedLoss)
      (outputLoss := outputLoss) coarseGrains.shading sqrtRequested
      reentryNormalizationExponent secondLogExponent logExponent := by
    exact next.call.output
  exact ⟨PureWZ2Node05TwoCallExactMultiplicityWiring.ofOwnerExactCalls
    firstLoss coarseSeedLoss coarseSeedNormalizationExponent
    coarseSeedLogExponent rhoRequested rhoRequested_eq first coarseGrains
    (coarse_slope_eq coarseGrains)
    sqrtRequested sqrtRequested_eq fineSeedLoss reentryNormalizationExponent
    secondLogExponent fine⟩

/-- A complete first owner stage rooted on the shading of one fixed grain
configuration.  All re-entry and owner-call data are explicit receipts. -/
structure PureWZ2Node05FirstOwnerStage
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (rho middleLoss firstLoss : ℝ)
    (firstOutputLogExponent : ℕ) where
  rootSourceLoss : ℝ
  rootNormalizationLoss : ℝ
  rootSeedLoss : ℝ
  rootNormalizationExponent : ℕ
  rootSeedLogExponent : ℕ
  rootReentry : PureWZ2PropStickyReentryData
    (sigma := sigma) source.shading rootNormalizationExponent
    rootSourceLoss rootNormalizationLoss
  rhoRequested : WZ2PaperRequestedScale delta
  rhoRequested_eq : rhoRequested.1 = rho
  firstInput : PureWZ2CroppedPropStickyUniversalInput
    (outputLoss := rootSeedLoss) rootReentry.toNormalizationData
    rhoRequested rootSeedLogExponent
  firstOwnerCompanion : PureWZ2Node05OwnerReentryCompanion firstInput
  firstCall : PureWZ2Node05OwnerCallReceipt
    firstInput firstLoss firstOutputLogExponent
  firstCompanion_eq : firstCall.companion = firstOwnerCompanion
  schedule : PureWZ2Node05SameExtremizerSchedule sigma middleLoss
  coarse_slope_eq : ∀ coarseGrains : PureWZ2GrainRefinementData
      firstCall.output.toNode5StickyData.croppedCoarseShading sigma middleLoss,
    coarseGrains.globalGrains.slope = source.globalGrains.slope
  firstLoss_le_input : firstLoss ≤ schedule.inputLoss
  rho_le_delta₀ : rhoRequested.1 ≤ schedule.delta₀

namespace PureWZ2Node05FirstOwnerStage

variable
    {sigma inputLoss delta rho middleLoss firstLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {firstOutputLogExponent : ℕ}

/-- The exact first owner output, still carrying its requested scale and all
seed/log indices. -/
noncomputable def first
    (stage : PureWZ2Node05FirstOwnerStage source rho middleLoss firstLoss
      firstOutputLogExponent) :
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := stage.rootSeedLoss)
      (outputLoss := firstLoss) source.shading stage.rhoRequested
      stage.rootNormalizationExponent stage.rootSeedLogExponent
      firstOutputLogExponent :=
  stage.firstCall.output

/-- The same-extremizer schedule restores grains on the actual coarse output
of this stage. -/
theorem coarseGrains_nonempty
    (stage : PureWZ2Node05FirstOwnerStage source rho middleLoss firstLoss
      firstOutputLogExponent) :
    Nonempty (PureWZ2GrainRefinementData
      stage.first.toNode5StickyData.croppedCoarseShading sigma middleLoss) :=
  pureWZ2Node05Owner_intermediateGrains stage.first.toNode5StickyData
    stage.schedule stage.firstLoss_le_input stage.rho_le_delta₀

/-- A canonical choice of the actual intermediate grains furnished by the
first stage. -/
noncomputable def coarseGrains
    (stage : PureWZ2Node05FirstOwnerStage source rho middleLoss firstLoss
      firstOutputLogExponent) :
    PureWZ2GrainRefinementData
      stage.first.toNode5StickyData.croppedCoarseShading sigma middleLoss :=
  Classical.choice stage.coarseGrains_nonempty

/-- The concrete owner call preserves its deterministic coarse family even
after transport to the caller's output log index. -/
theorem first_coarse_family_eq
    (stage : PureWZ2Node05FirstOwnerStage source rho middleLoss firstLoss
      firstOutputLogExponent) :
    stage.first.toNode5StickyData.data.coarse =
      stage.firstInput.deterministicData.coarse := by
  exact (PureWZ2Node05OwnerCallReceipt.transported_coarse_eq
    stage.firstCall.logExponent_eq _).trans rfl

/-- The cropped coarse shading of the concrete owner output is exactly the
shading accompanied by the first owner re-entry receipt. -/
theorem first_coarse_shading_heq
    (stage : PureWZ2Node05FirstOwnerStage source rho middleLoss firstLoss
      firstOutputLogExponent) :
    HEq stage.first.toNode5StickyData.croppedCoarseShading
      stage.firstInput.deterministicData.croppedCoarseShading := by
  exact (PureWZ2Node05OwnerCallReceipt.transported_coarseShading_heq
    stage.firstCall.logExponent_eq _).trans HEq.rfl

/-- The first concrete owner call's exact coarse re-entry, transported only
across its output-log equality to the public coarse shading. -/
noncomputable def coarseAncestor
    (stage : PureWZ2Node05FirstOwnerStage source rho middleLoss firstLoss
      firstOutputLogExponent) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) stage.first.toNode5StickyData.croppedCoarseShading
      stage.rootNormalizationExponent
      stage.firstOwnerCompanion.coarseSourceLoss
      stage.firstOwnerCompanion.coarseNormalizationLoss := by
  rw [← stage.firstCompanion_eq]
  exact transportReentry stage.first_coarse_family_eq.symm
    stage.first_coarse_shading_heq.symm
    stage.firstCall.companion.coarseReentry

end PureWZ2Node05FirstOwnerStage

/-- A second owner stage on the canonical intermediate grains of a completed
first stage.  The second call is indexed by the first call's output log
exponent, so no transport is needed during final assembly. -/
structure PureWZ2Node05SecondOwnerStage
    {sigma inputLoss delta rho middleLoss firstLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {firstOutputLogExponent : ℕ}
    (firstStage : PureWZ2Node05FirstOwnerStage source rho middleLoss firstLoss
      firstOutputLogExponent)
    (outputLoss : ℝ) where
  sqrtRequested : WZ2PaperRequestedScale firstStage.rhoRequested.1
  sqrtRequested_eq : sqrtRequested.1 = Real.sqrt rho
  fineSeedLoss : ℝ
  secondSeedLogExponent : ℕ
  secondInputCompanion : PureWZ2Node05SecondOwnerInputCompanion
    (secondLoss := fineSeedLoss) firstStage.first.toNode5StickyData
    firstStage.coarseGrains sqrtRequested firstStage.rootNormalizationExponent
    secondSeedLogExponent firstStage.firstOwnerCompanion.coarseSourceLoss
    firstStage.firstOwnerCompanion.coarseNormalizationLoss
    firstStage.coarseAncestor
  secondOwnerCompanion :
    PureWZ2Node05OwnerReentryCompanion secondInputCompanion.secondInput
  secondCall : PureWZ2Node05OwnerCallReceipt
    secondInputCompanion.secondInput outputLoss firstOutputLogExponent
  secondCompanion_eq :
    secondCall.companion = secondOwnerCompanion

namespace PureWZ2Node05SecondOwnerStage

variable
    {sigma inputLoss delta rho middleLoss firstLoss outputLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {firstOutputLogExponent : ℕ}
    {firstStage : PureWZ2Node05FirstOwnerStage source rho middleLoss firstLoss
      firstOutputLogExponent}

/-- Assemble both indexed owner calls through the canonical actual grains of
the first stage. -/
noncomputable def assemble
    (secondStage : PureWZ2Node05SecondOwnerStage firstStage outputLoss) :
    PureWZ2Node05TwoCallExactMultiplicityWiring
      source rho middleLoss outputLoss firstOutputLogExponent :=
  PureWZ2Node05TwoCallExactMultiplicityWiring.ofOwnerExactCalls
    firstLoss firstStage.rootSeedLoss firstStage.rootNormalizationExponent
    firstStage.rootSeedLogExponent firstStage.rhoRequested
    firstStage.rhoRequested_eq firstStage.first firstStage.coarseGrains
    (firstStage.coarse_slope_eq firstStage.coarseGrains)
    secondStage.sqrtRequested secondStage.sqrtRequested_eq
    secondStage.fineSeedLoss firstStage.rootNormalizationExponent
    secondStage.secondSeedLogExponent secondStage.secondCall.output

end PureWZ2Node05SecondOwnerStage

end Kakeya.Assouad

end
