import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05SynchronizedOwnerSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05OwnerTwoCallAssembly

/-!
# Dependent second owner call after synchronized post-grain pruning

The old second-owner companion is indexed by the unchanged coarse family.
Synchronized pruning genuinely changes that family, so this module packages a
new second universal input directly on the selected re-entry normalization.
It then combines the repackaged first owner output, the selected grain
configuration, and the concrete second owner call without equality transport.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The second owner input and exact call, both indexed by the selected-family
re-entry furnished by one synchronized owner selection. -/
structure PureWZ2Node05SynchronizedSecondOwnerCall
    {delta sigma ambientLoss sourceLoss normalizationLoss grainLoss outputEta
      selectedLoss seedLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent ancestorNormalizationExponent
      selectedNormalizationExponent secondSeedLogExponent
      outputLogExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss)
    (coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss)
    (croppedMassFraction : ENNReal)
    (selection : PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient ancestor coarseGrains croppedMassFraction)
    (sqrtRequested : WZ2PaperRequestedScale rhoRequested.1) where
  input : PureWZ2CroppedPropStickyUniversalInput
    (outputLoss := seedLoss) selection.selectedReentry.toNormalizationData
    sqrtRequested secondSeedLogExponent
  ownerCompanion : PureWZ2Node05OwnerReentryCompanion input
  call : PureWZ2Node05OwnerCallReceipt input outputLoss outputLogExponent
  companion_eq : call.companion = ownerCompanion

namespace PureWZ2Node05SynchronizedSecondOwnerCall

variable
    {delta sigma ambientLoss sourceLoss normalizationLoss grainLoss outputEta
      selectedLoss seedLoss outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent ancestorNormalizationExponent
      selectedNormalizationExponent secondSeedLogExponent
      outputLogExponent : ℕ}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      sourceShading rhoRequested ambientLogExponent}
    {ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss}
    {coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss}
    {croppedMassFraction : ENNReal}
    {selection : PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient ancestor coarseGrains croppedMassFraction}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}

/-- The concrete second owner output on the exact selected post-grain
shading. -/
noncomputable def output
    (second : PureWZ2Node05SynchronizedSecondOwnerCall
      (seedLoss := seedLoss) (outputLoss := outputLoss)
      (secondSeedLogExponent := secondSeedLogExponent)
      (outputLogExponent := outputLogExponent)
      ambient ancestor coarseGrains croppedMassFraction selection
      sqrtRequested) :
    PureWZ2Node05ExactMultiplicityPostRefinementData
      (sigma := sigma) (seedLoss := seedLoss) (outputLoss := outputLoss)
      selection.overlay sqrtRequested selectedNormalizationExponent
      secondSeedLogExponent outputLogExponent :=
  second.call.output

end PureWZ2Node05SynchronizedSecondOwnerCall

/-- A complete synchronized two-call stage.  The first call is repackaged on
the selected coarse family and complete fine parent fibers; the second call
uses the selected re-entry normalization on exactly that coarse shading. -/
structure PureWZ2Node05SynchronizedTwoCallStage
    {delta sigma inputLoss ambientLoss sourceLoss normalizationLoss grainLoss outputEta
      selectedLoss seedLoss outputLoss : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent firstLogExponent ancestorNormalizationExponent
      selectedNormalizationExponent secondSeedLogExponent : ℕ}
    (ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      source.shading rhoRequested ambientLogExponent)
    (ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss)
    (coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss)
    (croppedMassFraction : ENNReal)
    (selection : PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient ancestor coarseGrains croppedMassFraction)
    (sqrtRequested : WZ2PaperRequestedScale rhoRequested.1) where
  rho : ℝ
  rho_eq : rhoRequested.1 = rho
  sqrt_eq : sqrtRequested.1 = Real.sqrt rho
  firstReceipt : PureWZ2Node05CompleteParentOverlayReceipt
    (outputLoss := selectedLoss) ambient selection.selectedCoarse
    selection.pullback selection.overlay firstLogExponent
  coarse_slope_eq :
    coarseGrains.globalGrains.slope = source.globalGrains.slope
  second : PureWZ2Node05SynchronizedSecondOwnerCall
    (seedLoss := seedLoss) (outputLoss := outputLoss)
    (secondSeedLogExponent := secondSeedLogExponent)
    (outputLogExponent := firstLogExponent)
    ambient ancestor coarseGrains croppedMassFraction selection sqrtRequested

namespace PureWZ2Node05SynchronizedTwoCallStage

variable
    {delta sigma inputLoss ambientLoss sourceLoss normalizationLoss grainLoss outputEta
      selectedLoss seedLoss outputLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {ambientLogExponent firstLogExponent ancestorNormalizationExponent
      selectedNormalizationExponent secondSeedLogExponent : ℕ}
    {ambient : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := ambientLoss)
      source.shading rhoRequested ambientLogExponent}
    {ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) ambient.croppedCoarseShading
      ancestorNormalizationExponent sourceLoss normalizationLoss}
    {coarseGrains : PureWZ2GrainRefinementData
      ambient.croppedCoarseShading sigma grainLoss}
    {croppedMassFraction : ENNReal}
    {selection : PureWZ2Node05SynchronizedOwnerSelection
      (outputEta := outputEta) (selectedLoss := selectedLoss)
      (selectedNormalizationExponent := selectedNormalizationExponent)
      ambient ancestor coarseGrains croppedMassFraction}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}

/-- Project the synchronized dependent owner calls to the existing two-scale
consumer interface. -/
noncomputable def toOneScaleTwoScaleStickyData
    (stage : PureWZ2Node05SynchronizedTwoCallStage
      (seedLoss := seedLoss) (outputLoss := outputLoss)
      (firstLogExponent := firstLogExponent)
      (secondSeedLogExponent := secondSeedLogExponent)
      source ambient ancestor coarseGrains croppedMassFraction
      selection sqrtRequested) :
    PureWZ2OneScaleTwoScaleStickyData source stage.rho
      selectedLoss outputLoss firstLogExponent where
  coarseLoss := selectedLoss
  rhoRequested := rhoRequested
  rhoRequested_eq := stage.rho_eq
  coarse := stage.firstReceipt.toNode5StickyData
  coarseGrains := selection.receipt.toIdentityGrainRefinementData
  coarse_slope_eq := by
    change coarseGrains.globalGrains.slope = source.globalGrains.slope
    exact stage.coarse_slope_eq
  sqrtRequested := sqrtRequested
  sqrtRequested_eq := stage.rho_eq ▸ stage.sqrt_eq
  fine := stage.second.output.toNode5StickyData

end PureWZ2Node05SynchronizedTwoCallStage

end Kakeya.Assouad

end
