import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05PostGrainReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyRefinementData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedPropStickyUniversalAssembly

/-!
# Explicit second owner input on the intermediate grain shading

This companion records the inputs needed to make a second owner call after an
actual intermediate grain refinement.  The re-entry is constructed canonically
from a quantitative post-grain trace receipt; the second universal input is
still an explicit producer receipt.

The dependent indices make the three relevant shadings definitionally equal,
without any equality transport:
the re-entry shading is `coarseGrains.shading`, its normalization retains that
same cropped refinement, and the second universal input consumes precisely that
normalization at `sqrtRequested`.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The canonical post-grain receipt and second universal owner input on the actual
grain refinement of the first call's cropped coarse shading.

The ancestor is an index of the structure, so the canonical receipt cannot
silently change the first call's coarse re-entry provenance.
-/
structure PureWZ2Node05SecondOwnerInputCompanion
    {delta sigma firstLoss middleLoss secondLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {firstLogExponent : ℕ}
    (first : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := firstLoss)
      sourceShading rhoRequested firstLogExponent)
    (coarseGrains : PureWZ2GrainRefinementData
      first.croppedCoarseShading sigma middleLoss)
    (sqrtRequested : WZ2PaperRequestedScale rhoRequested.1)
    (reentryNormalizationExponent secondLogExponent : ℕ)
    (reentrySourceLoss ancestorNormalizationLoss : ℝ)
    (ancestor :
    PureWZ2PropStickyReentryData
      (sigma := sigma) first.croppedCoarseShading
      reentryNormalizationExponent reentrySourceLoss
      ancestorNormalizationLoss) where
  producerInput :
    PureWZ2Node05CanonicalPostGrainProducerInput
      (pureWZ2Node05PostGrainIdentityRefinement first.croppedCoarseShading)
      ancestor coarseGrains
  secondInput :
    PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := secondLoss)
      producerInput.toCanonicalReceipt.toReentryData.toNormalizationData
      sqrtRequested secondLogExponent

namespace PureWZ2Node05SecondOwnerInputCompanion

variable
    {delta sigma firstLoss middleLoss secondLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {rhoRequested : WZ2PaperRequestedScale delta}
    {firstLogExponent reentryNormalizationExponent secondLogExponent : ℕ}
    {first : PureWZ2Node5StickyData
      (sigma := sigma) (outputLoss := firstLoss)
      sourceShading rhoRequested firstLogExponent}
    {coarseGrains : PureWZ2GrainRefinementData
      first.croppedCoarseShading sigma middleLoss}
    {sqrtRequested : WZ2PaperRequestedScale rhoRequested.1}
    {reentrySourceLoss ancestorNormalizationLoss : ℝ}
    {ancestor : PureWZ2PropStickyReentryData
      (sigma := sigma) first.croppedCoarseShading
      reentryNormalizationExponent reentrySourceLoss
      ancestorNormalizationLoss}

/-- The full canonical receipt generated from the minimal quantitative input. -/
noncomputable abbrev canonicalReceipt
    (companion : PureWZ2Node05SecondOwnerInputCompanion
      (secondLoss := secondLoss) first coarseGrains sqrtRequested
      reentryNormalizationExponent secondLogExponent
      reentrySourceLoss ancestorNormalizationLoss ancestor) :=
  companion.producerInput.toCanonicalReceipt

/-- The second re-entry constructed from the canonical post-grain trace. -/
noncomputable abbrev reentry
    (companion : PureWZ2Node05SecondOwnerInputCompanion
      (secondLoss := secondLoss) first coarseGrains sqrtRequested
      reentryNormalizationExponent secondLogExponent
      reentrySourceLoss ancestorNormalizationLoss ancestor) :=
  companion.canonicalReceipt.toReentryData

/-- The normalization determined by the canonical post-grain re-entry. -/
noncomputable abbrev normalization
    (companion : PureWZ2Node05SecondOwnerInputCompanion
      (secondLoss := secondLoss) first coarseGrains sqrtRequested
      reentryNormalizationExponent secondLogExponent
      reentrySourceLoss ancestorNormalizationLoss ancestor) :=
  companion.reentry.toNormalizationData

/-- Package the minimal quantitative producer input and its dependent universal
owner input. -/
noncomputable def ofProducerInput
    (producerInput : PureWZ2Node05CanonicalPostGrainProducerInput
      (pureWZ2Node05PostGrainIdentityRefinement first.croppedCoarseShading)
      ancestor coarseGrains)
    (secondInput : PureWZ2CroppedPropStickyUniversalInput
      (outputLoss := secondLoss)
      producerInput.toCanonicalReceipt.toReentryData.toNormalizationData
      sqrtRequested secondLogExponent) :
    PureWZ2Node05SecondOwnerInputCompanion
      (secondLoss := secondLoss) first coarseGrains sqrtRequested
      reentryNormalizationExponent secondLogExponent
      reentrySourceLoss ancestorNormalizationLoss ancestor where
  producerInput := producerInput
  secondInput := secondInput

@[simp] theorem normalization_croppedRefined
    (companion : PureWZ2Node05SecondOwnerInputCompanion
      (secondLoss := secondLoss) first coarseGrains sqrtRequested
      reentryNormalizationExponent secondLogExponent
      reentrySourceLoss ancestorNormalizationLoss ancestor) :
    companion.normalization.croppedRefined = coarseGrains.shading := rfl

end PureWZ2Node05SecondOwnerInputCompanion

end Kakeya.Assouad

end
