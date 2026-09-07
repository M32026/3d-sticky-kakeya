import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryAllBinScalarSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderProducer

/-!
# Scheduled ordinary all-bin selection

This module combines the two source-independent thresholds used before the
dependent all-bin family is inspected.  It returns one genuine-coarse good
bin over every source-relative regularized block.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The complete ordinary all-bin prefix through one graph-good coarse bin
over every source-relative regularized block. -/
structure PureWZ2OrdinaryAllBinSelectedData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (volumeLoss : ℝ) where
  safe : PureWZ2BalancedSafeBlockFamilyData prepared
  carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe
  allBins : PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers
  coarseBins :
    PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins
  selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
    (volumeLoss := volumeLoss) coarseBins

/-- Select all regularized-block bins using only thresholds fixed before the
runtime family and its block witnesses. -/
theorem PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData.selectGoodCoarseBinsScheduled
    {sigma sourceLossCeiling coarseLossCeiling stickyLoss volumeLoss
      outerLoss inputLoss delta rho middleLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    {allBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers}
    (coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins)
    (scalar : PureWZ2OrdinaryAllBinScalarThreshold sigma
      sourceLossCeiling coarseLossCeiling stickyLoss volumeLoss outerLoss)
    (houterLoss : 0 < outerLoss)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hcoarseLossNonneg : 0 ≤ twoScale.coarseLoss)
    (hcoarseLossCeiling : twoScale.coarseLoss ≤ coarseLossCeiling)
    (hdeltaSmall : delta ≤ scalar.delta₀)
    (hrho : 0 < rho)
    (hrhoOuterSmall : rho ≤
      Classical.choose
        (pureWZ2_sourceWindowHeightBins_power_schedule
          (extraLoss := outerLoss) houterLoss))
    (hrhoPower : rho ≤ Real.rpow delta stickyLoss) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
        (volumeLoss := volumeLoss) coarseBins) := by
  apply coarseBins.selectGoodCoarseBinsOfThreshold scalar
    hinputNonneg hinputCeiling hcoarseLossNonneg hcoarseLossCeiling
    hdeltaSmall hrho
  · rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  · exact hrhoPower
  · intro block
    exact
      carriers.outer_bins_power_bound houterLoss hrho hrhoOuterSmall block

/-- Construct the entire all-bin selection prefix without exposing a
pointwise maximal-bin goodness assumption. -/
theorem PureWZ2SourceCarrierPreparation.ordinaryAllBinSelected
    {sigma sourceLossCeiling coarseLossCeiling stickyLoss volumeLoss
      outerLoss inputLoss delta rho middleLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (scalar : PureWZ2OrdinaryAllBinScalarThreshold sigma
      sourceLossCeiling coarseLossCeiling stickyLoss volumeLoss outerLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hmargin : 4 * rho ≤ Real.sqrt rho)
    (hCge :
      (4 : ENNReal) ≤ Kakeya.realRpowENN rho (-middleLoss))
    (hendpoint :
      ENNReal.ofReal
          ((2 * (28 * twoScale.sqrtRequested.1) / rho + 2) ^ sigma *
            4 ^ (1 - sigma)) ≤
        Kakeya.realRpowENN rho (-middleLoss))
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (houterLoss : 0 < outerLoss)
    (hinputNonneg : 0 ≤ inputLoss)
    (hinputCeiling : inputLoss ≤ sourceLossCeiling)
    (hcoarseLossNonneg : 0 ≤ twoScale.coarseLoss)
    (hcoarseLossCeiling : twoScale.coarseLoss ≤ coarseLossCeiling)
    (hdeltaSmall : delta ≤ scalar.delta₀)
    (hrho : 0 < rho)
    (hrhoOuterSmall : rho ≤
      Classical.choose
        (pureWZ2_sourceWindowHeightBins_power_schedule
          (extraLoss := outerLoss) houterLoss))
    (hrhoPower : rho ≤ Real.rpow delta stickyLoss) :
    Nonempty (PureWZ2OrdinaryAllBinSelectedData prepared volumeLoss) := by
  rcases prepared.balancedSafeBlockFamily hmargin with ⟨safe⟩
  rcases safe.ordinaryPaperOrderCarriers with ⟨carriers⟩
  rcases carriers.prepareAllGlobalBins hbridge hgraphOne hheightAbsorb with
    ⟨allBins⟩
  rcases allBins.prepareAllCoarseGlobalBins hsigma hsigmaOne hCge hendpoint
      hbridge hgraphOne hheightAbsorb with ⟨coarseBins⟩
  rcases coarseBins.selectGoodCoarseBinsScheduled scalar houterLoss
      hinputNonneg hinputCeiling hcoarseLossNonneg hcoarseLossCeiling
      hdeltaSmall hrho hrhoOuterSmall hrhoPower with ⟨selected⟩
  exact ⟨{
    safe := safe
    carriers := carriers
    allBins := allBins
    coarseBins := coarseBins
    selected := selected
  }⟩

end Kakeya.Assouad

end
