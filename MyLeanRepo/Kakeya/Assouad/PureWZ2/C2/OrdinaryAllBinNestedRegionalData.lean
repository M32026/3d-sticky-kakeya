import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinNestedRegionalPreparation

/-!
# Nested ordinary regional data

The completed dependent family keeps every source block, source bin, and
retained nested coarse bin on one provenance chain.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- The new regional witness indexed by every source-regularized block and,
inside each block, by every source global bin and every retained nested coarse
global bin.  All finite choices are stored dependently, so a rich-height lift
cannot be paired with a different companion, parent class, or source slice. -/
structure PureWZ2OrdinaryAllBinNestedRegionalData
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta finalLoss
      theoremEta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
    (companions : PureWZ2OrdinaryAllBinOuterPopularCompanionData carriers) where
  parentData : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2BalancedSafeOuterPopularCoarseParentData
      (companions.companions.companion block.1)
      (carriers.carrier block.1).outerPopular
      (companions.envelopes.envelope block.1)
  weightClass : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2BalancedSafeOuterPopularCoarseParentWeightClassData
      (companions.companions.companion block.1)
      (carriers.carrier block.1).outerPopular
      (companions.envelopes.envelope block.1) (parentData block)
  weightRestriction : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2BalancedSafeOuterPopularCoarseParentWeightRestrictionData
      (companions.companions.companion block.1)
      (carriers.carrier block.1).outerPopular
      (companions.envelopes.envelope block.1) (parentData block)
      (weightClass block)
  sourceWindow : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2BalancedSafeOuterPopularCoarseCellRestrictionSourceWindowData
      (weightRestriction block).restriction
  sourceBins : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2BalancedSafeOuterPopularCoarseSourceGlobalBinFamilyData
      (parentData := parentData block)
      (weightRestriction block).restriction (sourceWindow block)
  family : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2BalancedSafeOuterPopularCoarseNestedBlockRichFamilyData
      (normalEta := normalEta) (finalLoss := finalLoss)
      (theoremEta := theoremEta) (volumeLoss := volumeLoss)
      (weightRestriction block) (sourceWindow block) (sourceBins block)

end Kakeya.Assouad

end
