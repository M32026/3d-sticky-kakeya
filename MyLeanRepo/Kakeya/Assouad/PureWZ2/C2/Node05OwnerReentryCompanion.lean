import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedPropStickyUniversalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropStickyReentry

/-!
# Exact re-entry companion for the deterministic owner assembly

This module adds an explicit coarse re-entry receipt to one existing
`PureWZ2CroppedPropStickyUniversalInput`.  The receipt is indexed by the exact
cropped coarse shading returned by `sameFamilyOwnerUniversalData`; no coarse
re-entry theorem is derived here.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2CroppedPropStickyUniversalInput

/-- The deterministic data selected by an existing universal owner input. -/
noncomputable abbrev deterministicData
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent logExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (input : PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := outputLoss) normalized callerRequested logExponent) :
    PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      normalized.croppedRefined callerRequested logExponent :=
  WZ2PaperOwnerParentSelectedData.sameFamilyOwnerUniversalData
    normalized input.actualNearby input.quotient input.support
    input.coordinateCount input.regularized input.merged
    input.scales input.scheduled input.sameFamily input.scaleSeparation
    input.fixedBalancing input.owner input.data logExponent input.witness

end PureWZ2CroppedPropStickyUniversalInput

/--
The numerical coarse-loss ledger and exact coarse re-entry receipt accompanying
one deterministic same-family owner output.

The final field is deliberately an input.  Thus this structure records, but
does not claim to produce, coarse re-entry.
-/
structure PureWZ2Node05OwnerReentryCompanion
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent logExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    (input : PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := outputLoss) normalized callerRequested logExponent) where
  coarseSourceLoss : ℝ
  coarseNormalizationLoss : ℝ
  coarseSourceLoss_pos : 0 < coarseSourceLoss
  coarseNormalizationLoss_pos : 0 < coarseNormalizationLoss
  coarseSourceLoss_budget : 3 * coarseSourceLoss ≤ outputLoss
  coarseNormalizationLoss_eq :
    coarseNormalizationLoss = (7 / 2 : ℝ) * coarseSourceLoss
  coarseReentry :
    PureWZ2PropStickyReentryData
      (sigma := sigma) input.deterministicData.croppedCoarseShading
      normalizationExponent coarseSourceLoss coarseNormalizationLoss

namespace PureWZ2Node05OwnerReentryCompanion

variable
    {delta sigma sourceLoss normalizationLoss outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent logExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {callerRequested : WZ2PaperRequestedScale delta}
    {input : PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := outputLoss) normalized callerRequested logExponent}

/-- Forget the companion wrapper while retaining its exact deterministic data. -/
noncomputable def toReentrant
    (companion : PureWZ2Node05OwnerReentryCompanion input) :
    PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      normalized.croppedRefined callerRequested normalizationExponent
      logExponent where
  data := input.deterministicData
  coarseSourceLoss := companion.coarseSourceLoss
  coarseNormalizationLoss := companion.coarseNormalizationLoss
  coarseSourceLoss_pos := companion.coarseSourceLoss_pos
  coarseNormalizationLoss_pos := companion.coarseNormalizationLoss_pos
  coarseSourceLoss_budget := companion.coarseSourceLoss_budget
  coarseNormalizationLoss_eq := companion.coarseNormalizationLoss_eq
  coarseReentry := companion.coarseReentry

@[simp] theorem toReentrant_data
    (companion : PureWZ2Node05OwnerReentryCompanion input) :
    companion.toReentrant.data = input.deterministicData := rfl

@[simp] theorem toReentrant_refined
    (companion : PureWZ2Node05OwnerReentryCompanion input) :
    companion.toReentrant.data.refined = input.data.finalFineShading := rfl

@[simp] theorem toReentrant_coarse
    (companion : PureWZ2Node05OwnerReentryCompanion input) :
    companion.toReentrant.data.coarse = input.data.selectedPacked.family := rfl

@[simp] theorem toReentrant_balanced
    (companion : PureWZ2Node05OwnerReentryCompanion input) :
    companion.toReentrant.data.balanced =
      input.data.toGenericOwnerSelectedData.publicBalanced
        input.sameFamily.pullback.section6Cover.fine_line_class
        input.sameFamily.pullback.section6Cover.coarse_line_class
        input.sameFamily.pullback.section6Cover.coarse_essentially_distinct := rfl

end PureWZ2Node05OwnerReentryCompanion

end Kakeya.Assouad

end
