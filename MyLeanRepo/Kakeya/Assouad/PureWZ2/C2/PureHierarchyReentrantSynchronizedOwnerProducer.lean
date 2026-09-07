import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantOrdinaryOwnerLossSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05SynchronizedReentryTraceSchedule

/-!
# Exact-current synchronized ordinary owner producer

The public sticky capability and its first kernel output do not contain the
post-sticky Node-5 refinement capability.  This module therefore does not
claim an unconditional ordinary owner producer.  Instead it freezes the
smallest current-indexed receipt which still exposes the missing mathematical
construction, and closes every later dependent connection.

The dependency order is literal:

1. `ambient.seed` is the exact first reentrant kernel output, with the public
   equality also retained as `HEq ambient.seed.data kernelOutput.first`;
2. `ancestor` is identified with the coarse re-entry of that same seed;
3. `coarseGrains` lives on that exact ambient coarse shading and retains the
   supplied current slope;
4. the synchronized selection is made once by the regularized re-entry-trace
   theorem;
5. the quantitative overlay and second owner call are indexed by precisely
   that selected witness;
6. the existing synchronized hierarchy receipt is assembled without
   reselecting any family, shading, or owner.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The exact first-owner overlay on the supplied kernel output.

This is the first irreducible production boundary.  It asks for the actual
universal input, companion, and owner call, not merely an arbitrary public
`PureWZ2Node5StickyData`.  The two heterogeneous equalities pin the resulting
ambient datum to `kernelOutput.first`, while `ancestor_eq` pins the ancestor
to the re-entry carried by the same owner companion. -/
structure PureWZ2HierarchyReentrantFirstOverlayReceipt
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    (kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer) where
  firstInput : PureWZ2CroppedPropStickyUniversalInput
    (outputLoss := lossSchedule.ownerSchedule.stickyLoss)
    current.reentry.toNormalizationData kernelOutput.requested
      kernelOutput.firstSeedLogExponent
  firstCompanion : PureWZ2Node05OwnerReentryCompanion firstInput
  firstCall : PureWZ2Node05OwnerCallReceipt firstInput
    lossSchedule.ownerSchedule.stickyLoss capability.logExponent
  first_companion_eq : firstCall.companion = firstCompanion
  ambient : PureWZ2Node5StickyData
    (sigma := sigma)
    (outputLoss := lossSchedule.ownerSchedule.stickyLoss)
    current.grain.shading kernelOutput.requested capability.logExponent
  ambient_eq : ambient = firstCall.output.toNode5StickyData
  first_reentrant_eq :
    HEq firstCompanion.toReentrant kernelOutput.firstReentrant
  first_data_eq : HEq ambient.seed.data kernelOutput.first
  ancestor : PureWZ2PropStickyReentryData
    (sigma := sigma) ambient.croppedCoarseShading
    ambient.seedNormalizationExponent ambient.seed.coarseSourceLoss
      ambient.seed.coarseNormalizationLoss
  ancestor_eq : HEq ancestor firstCompanion.toReentrant.coarseReentry

/-- The exact current-slope grain refinement on one produced first overlay.

This is the second irreducible production boundary.  It is indexed by the
supplied `current` and by one exact first-overlay receipt, rather than by an
arbitrary family/shading callback. -/
structure PureWZ2HierarchyReentrantCurrentCoarseGrainReceipt
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    (firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
      (current := current) kernelOutput) where
  grainLoss : ℝ
  coarseGrains : PureWZ2GrainRefinementData
    firstOverlay.ambient.croppedCoarseShading sigma grainLoss
  coarse_slope_eq :
    coarseGrains.globalGrains.slope =
      current.grain.globalGrains.slope

/-- Exact-current input to the synchronized selection theorem.

The first overlay and current-slope coarse grain are explicit dependent
receipts.  The remaining fields are scalar absorptions for the regularized
re-entry-trace theorem; no family or shading can be reselected here. -/
structure PureWZ2HierarchyReentrantSynchronizedOwnerSelectionPrefix
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    (kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer) where
  firstOverlay : PureWZ2HierarchyReentrantFirstOverlayReceipt
    (current := current) kernelOutput
  currentCoarseGrain : PureWZ2HierarchyReentrantCurrentCoarseGrainReceipt
    firstOverlay
  inputEta : ℝ
  outputEta : ℝ
  structuralBudget : ℝ
  epsilon : ℝ
  croppedMassFraction : ENNReal
  traceSchedule : PureWZ2ReentryTraceFloorSchedule
    sigma lossSchedule.middleLoss structuralBudget
  delta_le_traceSchedule :
    kernelOutput.requested.1 ≤ traceSchedule.delta₀
  sourceLoss_le_traceCeiling :
    firstOverlay.ambient.seed.coarseSourceLoss ≤
      traceSchedule.traceSourceCeiling
  epsilon_pos : 0 < epsilon
  densitySeparation :
    Kakeya.realRpowENN kernelOutput.requested.1 outputEta ≤
      (1 / 2 : ENNReal) *
        Kakeya.realRpowENN kernelOutput.requested.1 inputEta
  inputDensityAbsorption :
    Kakeya.realRpowENN kernelOutput.requested.1 inputEta ≤
      (100 : ENNReal)⁻¹ *
        firstOverlay.ancestor.geometry.ordinaryDensity *
          Kakeya.realRpowENN kernelOutput.requested.1
            currentCoarseGrain.grainLoss
  croppedMassAbsorption :
    croppedMassFraction ≤
      (100 : ENNReal)⁻¹ *
        firstOverlay.ancestor.geometry.ordinaryDensity
  roundingAbsorption :
    ENNReal.ofReal
          (Real.rpow kernelOutput.requested.1 (-epsilon)) *
        Kakeya.realRpowENN kernelOutput.requested.1
          (-lossSchedule.ownerSchedule.stickyLoss) ≤
      Kakeya.realRpowENN kernelOutput.requested.1
        (-traceSchedule.densityLoss)
  restrictionAbsorption :
    wz2PaperPureNearbyRestrictionConstant
        (Kakeya.realRpowENN kernelOutput.requested.1
          (-lossSchedule.ownerSchedule.stickyLoss))
        (Kakeya.realRpowENN kernelOutput.requested.1 inputEta *
          Kakeya.deltaTubeVolume kernelOutput.requested.1)
        (pureWZ2SpatialCellDegreeConstant epsilon
          (pureWZ2Node05AmbientCoarseIdentityRefinement
            firstOverlay.ambient).selected.family.card)
        (pureWZ2SpatialCellRegularizationLoss epsilon
            (pureWZ2Node05AmbientCoarseIdentityRefinement
              firstOverlay.ambient).selected.family.card *
          Kakeya.deltaTubeVolume kernelOutput.requested.1) ≤
      Kakeya.realRpowENN kernelOutput.requested.1
        (-traceSchedule.densityLoss)
  cardinalityAbsorption :
    Kakeya.realRpowENN kernelOutput.requested.1 outputEta *
        pureWZ2SpatialCellRegularizationLoss epsilon
          (pureWZ2Node05AmbientCoarseIdentityRefinement
            firstOverlay.ambient).selected.family.card ≤
      Kakeya.realRpowENN kernelOutput.requested.1 inputEta
  grainLoss_le_density :
    currentCoarseGrain.grainLoss ≤ traceSchedule.densityLoss
  densityAbsorption :
    (13824 : ENNReal) *
        Kakeya.realRpowENN kernelOutput.requested.1
          traceSchedule.densityLoss ≤
      Kakeya.realRpowENN kernelOutput.requested.1 outputEta
  topLevelAbsorption :
    ((Kakeya.realRpowENN kernelOutput.requested.1 outputEta)⁻¹ * 1) *
        Kakeya.realRpowENN kernelOutput.requested.1
          (-currentCoarseGrain.grainLoss) ≤
      Kakeya.realRpowENN kernelOutput.requested.1
        (-lossSchedule.middleLoss)
  normalizationLoss_le :
    firstOverlay.ambient.seed.coarseNormalizationLoss ≤
      lossSchedule.middleLoss
  retainedMassAbsorption :
    pureWZ2SpatialCellRegularizationLoss epsilon
          (pureWZ2Node05AmbientCoarseIdentityRefinement
            firstOverlay.ambient).selected.family.card *
        wz2PaperPureRefinementFraction kernelOutput.requested.1
          firstOverlay.ambient.seedNormalizationExponent ≤
      ((100 : ENNReal)⁻¹ *
          firstOverlay.ancestor.geometry.ordinaryDensity *
            Kakeya.realRpowENN kernelOutput.requested.1
              currentCoarseGrain.grainLoss) *
        wz2PaperPureRefinementFraction kernelOutput.requested.1
          firstOverlay.ambient.seedNormalizationExponent
  densityBudget :
    Kakeya.realRpowENN kernelOutput.requested.1
          firstOverlay.ambient.seed.coarseSourceLoss / 2 ≤
      Kakeya.realRpowENN kernelOutput.requested.1 outputEta

namespace PureWZ2HierarchyReentrantSynchronizedOwnerSelectionPrefix

variable
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}

/-- The regularized theorem selects one synchronized owner on the exact
ambient/ancestor/coarse-grain chain. -/
theorem selection_nonempty
    (selectionInput :
      PureWZ2HierarchyReentrantSynchronizedOwnerSelectionPrefix
        (current := current) kernelOutput) :
    Nonempty (PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := selectionInput.outputEta)
      (selectedLoss := lossSchedule.middleLoss)
      (selectedNormalizationExponent :=
        selectionInput.firstOverlay.ambient.seedNormalizationExponent)
      selectionInput.firstOverlay.ambient
        selectionInput.firstOverlay.ancestor
        selectionInput.currentCoarseGrain.coarseGrains
        selectionInput.croppedMassFraction) := by
  apply
    exists_pureWZ2Node05SynchronizedOwnerSelection_of_regularized_reentryTraceSchedule
      selectionInput.firstOverlay.ambient
      selectionInput.firstOverlay.ancestor
      selectionInput.currentCoarseGrain.coarseGrains selectionInput.inputEta
      selectionInput.outputEta lossSchedule.middleLoss
      selectionInput.structuralBudget selectionInput.epsilon
      selectionInput.firstOverlay.ambient.seedNormalizationExponent
      selectionInput.croppedMassFraction selectionInput.traceSchedule
      selectionInput.delta_le_traceSchedule
      selectionInput.sourceLoss_le_traceCeiling
      selectionInput.firstOverlay.ambient.coarse_extremal.cwa_nearby_scales
      selectionInput.epsilon_pos selectionInput.densitySeparation
      selectionInput.inputDensityAbsorption
      selectionInput.croppedMassAbsorption selectionInput.roundingAbsorption
      selectionInput.restrictionAbsorption
      selectionInput.cardinalityAbsorption
      selectionInput.grainLoss_le_density selectionInput.densityAbsorption
      selectionInput.topLevelAbsorption selectionInput.normalizationLoss_le
      selectionInput.retainedMassAbsorption selectionInput.densityBudget

/-- The unique selection consumed below.  This choice is made from the
regularized theorem above; it is not supplied by a family-valued callback. -/
noncomputable def selection
    (selectionInput :
      PureWZ2HierarchyReentrantSynchronizedOwnerSelectionPrefix
        (current := current) kernelOutput) :
    PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := selectionInput.outputEta)
      (selectedLoss := lossSchedule.middleLoss)
      (selectedNormalizationExponent :=
        selectionInput.firstOverlay.ambient.seedNormalizationExponent)
      selectionInput.firstOverlay.ambient
        selectionInput.firstOverlay.ancestor
        selectionInput.currentCoarseGrain.coarseGrains
        selectionInput.croppedMassFraction :=
  Classical.choice selectionInput.selection_nonempty

end PureWZ2HierarchyReentrantSynchronizedOwnerSelectionPrefix

/-- Quantitative data after the one canonical synchronized selection.

Both fields are indexed by `selectionInput.selection`, so this receipt cannot answer
queries about arbitrary grains, families, or selected cores. -/
structure PureWZ2HierarchyReentrantSynchronizedOwnerPostSelectionReceipt
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}
    (selectionInput :
      PureWZ2HierarchyReentrantSynchronizedOwnerSelectionPrefix
        (current := current) kernelOutput) where
  overlayQuantitative :
    PureWZ2Node05SynchronizedOverlayQuantitativeReceipt
      selectionInput.firstOverlay.ambient
        selectionInput.firstOverlay.ancestor
        selectionInput.currentCoarseGrain.coarseGrains
        selectionInput.croppedMassFraction
        selectionInput.selection capability.logExponent
  seedLoss : ℝ
  secondSeedLogExponent : ℕ
  second : PureWZ2Node05SynchronizedSecondOwnerCall
    (seedLoss := seedLoss)
    (outputLoss := lossSchedule.ownerSchedule.stickyLoss)
    (secondSeedLogExponent := secondSeedLogExponent)
    (outputLogExponent := capability.logExponent)
    selectionInput.firstOverlay.ambient
      selectionInput.firstOverlay.ancestor
      selectionInput.currentCoarseGrain.coarseGrains
      selectionInput.croppedMassFraction
      selectionInput.selection kernelOutput.sqrtRequested

/-- The sole current-indexed mathematical leaf left by this module.  It
contains one exact first ambient construction and only the quantitative
receipts on the one synchronized witness selected from it. -/
structure PureWZ2HierarchyReentrantSynchronizedOwnerCurrentLeaf
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    (kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer) where
  selectionInput :
    PureWZ2HierarchyReentrantSynchronizedOwnerSelectionPrefix
      (current := current) kernelOutput
  post :
    PureWZ2HierarchyReentrantSynchronizedOwnerPostSelectionReceipt
      selectionInput

namespace PureWZ2HierarchyReentrantSynchronizedOwnerCurrentLeaf

variable
    {sigma inputLoss delta outputLoss sourceLossCeiling targetRho : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {lossSchedule :
      PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
        outputLoss sourceLossCeiling}
    {outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
      delta targetRho lossSchedule.ownerSchedule.stickyLoss outputLoss}
    {kernelOutput : PureWZ2HierarchyReentrantOrdinaryKernelOutput
      (current := current) lossSchedule.ownerSchedule outer}

/-- Complete all deterministic wiring after the exact-current leaf. -/
noncomputable def toSynchronizedOwnerReceipt
    (leaf : PureWZ2HierarchyReentrantSynchronizedOwnerCurrentLeaf
      (current := current) kernelOutput) :
    PureWZ2HierarchyReentrantOrdinarySynchronizedOwnerReceipt
      (current := current) kernelOutput := by
  let stage : PureWZ2Node05SynchronizedTwoCallStage
      (seedLoss := leaf.post.seedLoss)
      (outputLoss := lossSchedule.ownerSchedule.stickyLoss)
      (firstLogExponent := capability.logExponent)
      (secondSeedLogExponent := leaf.post.secondSeedLogExponent)
      current.grain leaf.selectionInput.firstOverlay.ambient
        leaf.selectionInput.firstOverlay.ancestor
        leaf.selectionInput.currentCoarseGrain.coarseGrains
        leaf.selectionInput.croppedMassFraction
        leaf.selectionInput.selection kernelOutput.sqrtRequested :=
    { rho := kernelOutput.requested.1
      rho_eq := rfl
      sqrt_eq := kernelOutput.sqrtRequested_val
      firstReceipt := leaf.post.overlayQuantitative.toOverlayReceipt
      coarse_slope_eq :=
        leaf.selectionInput.currentCoarseGrain.coarse_slope_eq
      second := leaf.post.second }
  exact
    { ambientLoss := lossSchedule.ownerSchedule.stickyLoss
      sourceLoss :=
        leaf.selectionInput.firstOverlay.ambient.seed.coarseSourceLoss
      normalizationLoss :=
        leaf.selectionInput.firstOverlay.ambient.seed.coarseNormalizationLoss
      grainLoss := leaf.selectionInput.currentCoarseGrain.grainLoss
      outputEta := leaf.selectionInput.outputEta
      seedLoss := leaf.post.seedLoss
      ambientLogExponent := capability.logExponent
      ancestorNormalizationExponent :=
        leaf.selectionInput.firstOverlay.ambient.seedNormalizationExponent
      selectedNormalizationExponent :=
        leaf.selectionInput.firstOverlay.ambient.seedNormalizationExponent
      secondSeedLogExponent := leaf.post.secondSeedLogExponent
      ambient := leaf.selectionInput.firstOverlay.ambient
      first_data_eq := leaf.selectionInput.firstOverlay.first_data_eq
      ancestor := leaf.selectionInput.firstOverlay.ancestor
      coarseGrains := leaf.selectionInput.currentCoarseGrain.coarseGrains
      croppedMassFraction := leaf.selectionInput.croppedMassFraction
      selection := leaf.selectionInput.selection
      stage := stage }

end PureWZ2HierarchyReentrantSynchronizedOwnerCurrentLeaf

/-- Production target for the exact first ambient owner call.

This target cannot be discharged from `PureWZ2PropStickyCapability`: that
structure exposes public sticky outputs and the re-entry kernel, but no
`PureWZ2CroppedPropStickyUniversalInput`, owner companion, or owner-call
receipt on `kernelOutput.first`. -/
def PureWZ2HierarchyReentrantFirstOverlayAt
    (capability : PureWZ2PropStickyCapability) (sigma : ℝ) : Prop :=
  ∀ {outputLoss sourceLossCeiling : ℝ},
    ∀ lossSchedule :
        PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
          outputLoss sourceLossCeiling,
      ∀ inputLoss : ℝ,
        0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ,
            0 < delta → delta ≤ lossSchedule.ownerSchedule.delta₀ →
              ∀ current : PureWZ2ReentrantGrainSource sigma inputLoss delta
                  capability.normalizationExponent,
                ∀ targetRho : ℝ,
                  delta ≤ targetRho → targetRho ≤ 1 →
                    Real.rpow delta (1 - outputLoss) ≤ targetRho →
                      targetRho ≤ Real.rpow delta outputLoss →
                        ∀ outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
                            delta targetRho
                            lossSchedule.ownerSchedule.stickyLoss outputLoss,
                          ∀ kernelOutput :
                              PureWZ2HierarchyReentrantOrdinaryKernelOutput
                                (current := current)
                                lossSchedule.ownerSchedule outer,
                            Nonempty
                              (PureWZ2HierarchyReentrantFirstOverlayReceipt
                                (current := current) kernelOutput)

/-- Production target for a current-slope coarse grain on the exact first
overlay.

The input is one first-overlay receipt, not an arbitrary family/shading.
Existing `restrict` lemmas do not prove this target: they preserve one tube
family, while `current.grain` is indexed at `delta` and the required ambient
coarse shading is indexed at `kernelOutput.requested.1`. -/
def PureWZ2HierarchyReentrantCurrentCoarseGrainAt
    (capability : PureWZ2PropStickyCapability) (sigma : ℝ) : Prop :=
  ∀ {outputLoss sourceLossCeiling : ℝ},
    ∀ lossSchedule :
        PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
          outputLoss sourceLossCeiling,
      ∀ inputLoss : ℝ,
        0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ,
            0 < delta → delta ≤ lossSchedule.ownerSchedule.delta₀ →
              ∀ current : PureWZ2ReentrantGrainSource sigma inputLoss delta
                  capability.normalizationExponent,
                ∀ targetRho : ℝ,
                  delta ≤ targetRho → targetRho ≤ 1 →
                    Real.rpow delta (1 - outputLoss) ≤ targetRho →
                      targetRho ≤ Real.rpow delta outputLoss →
                        ∀ outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
                            delta targetRho
                            lossSchedule.ownerSchedule.stickyLoss outputLoss,
                          ∀ kernelOutput :
                              PureWZ2HierarchyReentrantOrdinaryKernelOutput
                                (current := current)
                                lossSchedule.ownerSchedule outer,
                            ∀ firstOverlay :
                                PureWZ2HierarchyReentrantFirstOverlayReceipt
                                  (current := current) kernelOutput,
                              Nonempty
                                (PureWZ2HierarchyReentrantCurrentCoarseGrainReceipt
                                  firstOverlay)

/-- Exact quantifier order of the remaining synchronized continuation after
the first-overlay and current-coarse-grain boundaries have been made
explicit.

This is intentionally not named as the final producer: neither the public
sticky capability nor `kernelOutput` supplies this receipt. -/
def PureWZ2HierarchyReentrantSynchronizedOwnerCurrentLeafAt
    (capability : PureWZ2PropStickyCapability) (sigma : ℝ) : Prop :=
  ∀ {outputLoss sourceLossCeiling : ℝ},
    ∀ lossSchedule :
        PureWZ2HierarchyReentrantOrdinaryOwnerLossSchedule capability sigma
          outputLoss sourceLossCeiling,
      ∀ inputLoss : ℝ,
        0 < inputLoss → inputLoss ≤ sourceLossCeiling →
          ∀ delta : ℝ,
            0 < delta → delta ≤ lossSchedule.ownerSchedule.delta₀ →
              ∀ current : PureWZ2ReentrantGrainSource sigma inputLoss delta
                  capability.normalizationExponent,
                ∀ targetRho : ℝ,
                  delta ≤ targetRho → targetRho ≤ 1 →
                    Real.rpow delta (1 - outputLoss) ≤ targetRho →
                      targetRho ≤ Real.rpow delta outputLoss →
                        ∀ outer : PureWZ2SourceHorizontalFlexibleOuterScaleData
                            delta targetRho
                            lossSchedule.ownerSchedule.stickyLoss outputLoss,
                          ∀ kernelOutput :
                              PureWZ2HierarchyReentrantOrdinaryKernelOutput
                                (current := current)
                                lossSchedule.ownerSchedule outer,
                            Nonempty
                              (PureWZ2HierarchyReentrantSynchronizedOwnerCurrentLeaf
                                (current := current) kernelOutput)

/-- Once the exact-current leaf is supplied, the requested synchronized
producer follows with no further mathematical callback or reselection. -/
theorem
    pureWZ2_reentrantOrdinaryPreScheduledSynchronizedOwnerProducer_of_currentLeaf
    {capability : PureWZ2PropStickyCapability} {sigma : ℝ}
    (leaf :
      PureWZ2HierarchyReentrantSynchronizedOwnerCurrentLeafAt
        capability sigma) :
    PureWZ2HierarchyReentrantOrdinaryPreScheduledSynchronizedOwnerProducerAt
      capability sigma := by
  intro outputLoss sourceLossCeiling lossSchedule inputLoss hinput
    hinputCeiling delta hdelta hdeltaSmall current targetRho hdeltaRho
    hrhoOne hrhoLower hrhoUpper outer kernelOutput
  rcases leaf lossSchedule inputLoss hinput hinputCeiling delta hdelta
      hdeltaSmall current targetRho hdeltaRho hrhoOne hrhoLower hrhoUpper outer
      kernelOutput with ⟨currentLeaf⟩
  exact ⟨currentLeaf.toSynchronizedOwnerReceipt⟩

end Kakeya.Assouad

end
