import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderGlobalBinCoarseFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderBlockRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalRelativeMassBudget

/-!
# Ordinary all-global-bin families over every source block

This is the dependent two-dimensional carrier required by the paper order.
The outer index is the genuine source block; the inner index is a nonempty
global-bin fibre of that block's one exact Fubini slice.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Every safe source block, with all of its global-bin preparations. -/
structure PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe) where
  binFamily : ∀ block : {block // block ∈ safe.blocks},
    PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData
      (carriers.carrier block)

/-- Construct the two-dimensional preparation family without selecting a
good bin. -/
theorem PureWZ2OrdinaryPaperOrderAllBlockCarrierData.prepareAllGlobalBins
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    (carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers) := by
  have hfamily : ∀ block : {block // block ∈ safe.blocks},
      Nonempty (PureWZ2OrdinaryPaperOrderGlobalBinPreparationFamilyData
        (carriers.carrier block)) := fun block =>
    (carriers.carrier block).prepareAllGlobalBins
      hbridge hgraphOne hheightAbsorb
  exact ⟨{ binFamily := fun block => Classical.choice (hfamily block) }⟩

/-- For each source-relative regularized block, choose the good global-bin
family obtained from that block's own aggregate graph-shadow estimate. -/
structure PureWZ2OrdinaryPaperOrderRegularizedGoodBinData
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (allBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers) where
  good : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2OrdinaryPaperOrderGoodGlobalBinFamilyData
      (allBins.binFamily block.1) volumeLoss

/-- Perform the per-block good-bin selection from honest fiberwise aggregate
budgets.  The hypothesis is intentionally dependent on the block and its own
global-bin family. -/
theorem PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData.selectGoodBinsPerRegularizedBlock
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (allBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers)
    (hbad : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      2 *
          (((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss)) ≤
        ∑ bin : {bin // bin ∈
            (allBins.binFamily block.1).line.globalBins},
          volume ((allBins.binFamily block.1).prep bin).shadow.union) :
    Nonempty (PureWZ2OrdinaryPaperOrderRegularizedGoodBinData
      (volumeLoss := volumeLoss) allBins) := by
  have hgood : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      Nonempty (PureWZ2OrdinaryPaperOrderGoodGlobalBinFamilyData
        (allBins.binFamily block.1) volumeLoss) := fun block =>
    (allBins.binFamily block.1).selectGoodGlobalBins (hbad block)
  exact ⟨{ good := fun block => Classical.choice (hgood block) }⟩

/-- The unique bin chosen for a retained source block, after good-bin
selection. -/
def PureWZ2OrdinaryPaperOrderRegularizedGoodBinData.chosenBin
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
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
    (selected : PureWZ2OrdinaryPaperOrderRegularizedGoodBinData
      (volumeLoss := volumeLoss) allBins)
    (block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}) :
    {bin // bin ∈ (allBins.binFamily block.1).line.globalBins} :=
  (selected.good block).chosenBin

/-- The chosen bin over each retained block has the exact ready-graph volume
floor. -/
theorem PureWZ2OrdinaryPaperOrderRegularizedGoodBinData.chosenBin_volume_lower
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
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
    (selected : PureWZ2OrdinaryPaperOrderRegularizedGoodBinData
      (volumeLoss := volumeLoss) allBins)
    (block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}) :
    Kakeya.realRpowENN
        ((allBins.binFamily block.1).prep (selected.chosenBin block)).graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume ((allBins.binFamily block.1).prep
        (selected.chosenBin block)).shadow.union :=
  (selected.good block).chosenBin_volume_lower

/-- Genuine-coarse graph preparations for all global bins in every retained
source block. -/
structure PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (allBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers) where
  coarseFamily : ∀ block : {block // block ∈ safe.blocks},
    PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData
      (allBins.binFamily block)

/-- Construct the all-block genuine-coarse family without re-choosing the
underlying source block or its global-bin fibres. -/
theorem PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData.prepareAllCoarseGlobalBins
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {safe : PureWZ2BalancedSafeBlockFamilyData prepared}
    {carriers : PureWZ2OrdinaryPaperOrderAllBlockCarrierData safe}
    (allBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinPreparationData carriers)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCge :
      (4 : ENNReal) ≤ Kakeya.realRpowENN rho (-middleLoss))
    (hendpoint :
      ENNReal.ofReal
          ((2 * (28 * twoScale.sqrtRequested.1) / rho + 2) ^ sigma *
            4 ^ (1 - sigma)) ≤
        Kakeya.realRpowENN rho (-middleLoss))
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins) := by
  have hcoarse : ∀ block : {block // block ∈ safe.blocks},
      Nonempty
        (PureWZ2OrdinaryPaperOrderGlobalBinCoarsePreparationFamilyData
          (allBins.binFamily block)) := fun block =>
    (allBins.binFamily block).prepareAllCoarseGlobalBins
      hsigma hsigmaOne hCge hendpoint hbridge hgraphOne hheightAbsorb
  exact ⟨{
    coarseFamily := fun block => Classical.choice (hcoarse block)
  }⟩

/-- One graph-good genuine-coarse bin in every source-regularized block. -/
structure PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
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
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins) where
  good : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
    PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData
      (coarseBins.coarseFamily block.1) volumeLoss

/-- Select one genuine-coarse graph-good bin in every regularized source
block from the corresponding scaled aggregate budget. -/
theorem PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData.selectGoodCoarseBinsPerRegularizedBlock
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
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
    (hscaled : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      let family := allBins.binFamily block.1
      (2 * ((family.line.globalBins.card : ENNReal) *
          Kakeya.realRpowENN (256 * rho)
            (1 + sigma / 2 + volumeLoss))) *
          pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤
        (carriers.carrier block.1).outerPopular.popularWindow.volumeSupply *
          twoScale.fine.balanced.cellMass) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
        (volumeLoss := volumeLoss) coarseBins) := by
  have hgood : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      Nonempty (PureWZ2OrdinaryPaperOrderGoodCoarseGlobalBinFamilyData
        (coarseBins.coarseFamily block.1) volumeLoss) := fun block =>
    (coarseBins.coarseFamily block.1).selectGoodCoarseGlobalBins
      (hscaled block)
  exact ⟨{ good := fun block => Classical.choice (hgood block) }⟩

/-- The canonical genuine-coarse bin attached to a source-regularized block. -/
def PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData.chosenBin
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
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
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    (selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins)
    (block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}) :
    {bin // bin ∈ (allBins.binFamily block.1).line.globalBins} :=
  (selected.good block).chosenBin

/-- The chosen bin has the genuine-coarse ready-volume floor. -/
theorem PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData.chosenBin_volume_lower
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
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
    {coarseBins :
      PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData allBins}
    (selected : PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
      (volumeLoss := volumeLoss) coarseBins)
    (block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe}) :
    Kakeya.realRpowENN
        ((coarseBins.coarseFamily block.1).prep
          (selected.chosenBin block)).graphScale
        (1 + sigma / 2 + volumeLoss) ≤
      volume ((coarseBins.coarseFamily block.1).prep
        (selected.chosenBin block)).shadow.union :=
  (selected.good block).chosenBin_volume_lower

/-- Convert the source-relative block floor and the outer height-popularity
retention into the scaled per-block budget consumed by the all-bin
genuine-coarse selector.  The remaining hypothesis is purely numerical: it
contains both finite pigeonhole costs on the left and the canonical
source-block threshold on the right. -/
theorem PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData.scaled_budget_of_regularizedBlock
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
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
    (block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe})
    (hpower :
      ((2 * (carriers.carrier block.1).outerPopular.popular.bins :
          ENNReal) *
          ((2 * (((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
              Kakeya.realRpowENN (256 * rho)
                (1 + sigma / 2 + volumeLoss))) *
            pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta)) ≤
        pureWZ2OrdinaryPaperOrderBlockThreshold
            (volume prepared.shadow.union) rho *
          twoScale.fine.balanced.cellMass) :
    let family := allBins.binFamily block.1
    (2 * ((family.line.globalBins.card : ENNReal) *
        Kakeya.realRpowENN (256 * rho)
          (1 + sigma / 2 + volumeLoss))) *
        pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta ≤
      (carriers.carrier block.1).outerPopular.popularWindow.volumeSupply *
        twoScale.fine.balanced.cellMass := by
  dsimp only
  let outerCost : ENNReal :=
    (2 * (carriers.carrier block.1).outerPopular.popular.bins : ℕ)
  let graphCost : ENNReal :=
    (2 * (((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
      Kakeya.realRpowENN (256 * rho)
        (1 + sigma / 2 + volumeLoss))) *
      pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta
  have hblockFloor :=
    pureWZ2OrdinaryPaperOrderRegularizedBlock_volume_lower block.2
  have hblockToPopular :
      pureWZ2OrdinaryPaperOrderBlockThreshold
          (volume prepared.shadow.union) rho ≤
        outerCost *
          (carriers.carrier block.1).outerPopular.popularWindow.volumeSupply := by
    calc
      pureWZ2OrdinaryPaperOrderBlockThreshold
            (volume prepared.shadow.union) rho ≤
          volume (safe.blockWindow block.1).shading.union := hblockFloor
      _ = volume (safe.blockWindow block.1).window.shading.union := by
        rw [(safe.blockWindow block.1).window_shading]
      _ ≤ outerCost *
          (carriers.carrier block.1).outerPopular.popularWindow.volumeSupply := by
        simpa [outerCost] using
          (carriers.carrier block.1).outerPopular.source_volume_retention
  have houterPos : 0 < outerCost := by
    have hbinsPos : 0 <
        (carriers.carrier block.1).outerPopular.popular.bins := by
      rw [(carriers.carrier block.1).outerPopular.popular.bins_eq]
      omega
    dsimp only [outerCost]
    exact_mod_cast Nat.mul_pos (by omega) hbinsPos
  have houterTop : outerCost ≠ ⊤ := by
    dsimp only [outerCost]
    exact ENNReal.natCast_ne_top _
  apply (ENNReal.mul_le_mul_iff_right houterPos.ne' houterTop).mp
  calc
    outerCost * graphCost ≤
        pureWZ2OrdinaryPaperOrderBlockThreshold
            (volume prepared.shadow.union) rho *
          twoScale.fine.balanced.cellMass := by
      simpa [outerCost, graphCost] using hpower
    _ ≤ (outerCost *
          (carriers.carrier block.1).outerPopular.popularWindow.volumeSupply) *
        twoScale.fine.balanced.cellMass := by gcongr
    _ = outerCost *
        ((carriers.carrier block.1).outerPopular.popularWindow.volumeSupply *
          twoScale.fine.balanced.cellMass) := by ring

/-- The fully dependent per-block selector with only a numerical power budget
left at the boundary. -/
theorem PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData.selectGoodCoarseBinsOfPowerBudget
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss : ℝ}
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
    (hpower : ∀ block :
      {block // block ∈ pureWZ2OrdinaryPaperOrderRegularizedBlocks safe},
      ((2 * (carriers.carrier block.1).outerPopular.popular.bins :
          ENNReal) *
          ((2 * (((allBins.binFamily block.1).line.globalBins.card : ENNReal) *
              Kakeya.realRpowENN (256 * rho)
                (1 + sigma / 2 + volumeLoss))) *
            pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta)) ≤
        pureWZ2OrdinaryPaperOrderBlockThreshold
            (volume prepared.shadow.union) rho *
          twoScale.fine.balanced.cellMass) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
        (volumeLoss := volumeLoss) coarseBins) :=
  coarseBins.selectGoodCoarseBinsPerRegularizedBlock fun block =>
    coarseBins.scaled_budget_of_regularizedBlock block (hpower block)

/-- The canonical regularized-block threshold times the second balanced cell
mass has a source-independent power lower bound.  This is the structural
input for the remaining scalar schedule. -/
theorem PureWZ2SourceCarrierPreparation.regularized_block_supply_power_lower
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    (32 : ENNReal)⁻¹ *
        (Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
          Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) *
          Kakeya.realRpowENN rho (1 / 2 : ℝ) *
          Kakeya.realRpowENN twoScale.rhoRequested.1
            (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)) ≤
      pureWZ2OrdinaryPaperOrderBlockThreshold
          (volume prepared.shadow.union) rho *
        twoScale.fine.balanced.cellMass := by
  let sourcePower :=
    Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
      Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss)
  let root : ENNReal := ENNReal.ofReal (Real.sqrt rho)
  let secondPower :=
    Kakeya.realRpowENN twoScale.rhoRequested.1
      (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)
  let sourceVolume := volume prepared.shadow.union
  let fineMass := twoScale.fine.balanced.cellMass
  let denom := ENNReal.ofReal (2 + rho + Real.sqrt rho)
  have hrho : 0 < rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.coarseGrains.extremal.delta_pos
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hsource : sourcePower ≤ sourceVolume := by
    simpa [sourcePower, sourceVolume] using
      prepared.pullback_volume_relative_lower
  have hsecond : secondPower ≤ fineMass := by
    simpa [secondPower, fineMass] using twoScale.second_source_floor_power
  have hroot : root = Kakeya.realRpowENN rho (1 / 2 : ℝ) := by
    simp [root, Kakeya.realRpowENN, Real.sqrt_eq_rpow]
  have hdenomReal : 2 + rho + Real.sqrt rho ≤ 4 := by
    have hsqrtOne : Real.sqrt rho ≤ 1 := Real.sqrt_le_one.mpr hrhoOne
    linarith
  have hdenom : denom ≤ 4 := by
    simpa [denom] using ENNReal.ofReal_le_ofReal hdenomReal
  have hwindow : (4 : ENNReal)⁻¹ * (sourceVolume * root) ≤
      pureWZ2SourceHorizontalWindowSupply sourceVolume rho := by
    calc
      (4 : ENNReal)⁻¹ * (sourceVolume * root) =
          sourceVolume * root / 4 := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ sourceVolume * root / denom := ENNReal.div_le_div_left hdenom _
      _ = pureWZ2SourceHorizontalWindowSupply sourceVolume rho := by
        rfl
  have hwindowSource : (4 : ENNReal)⁻¹ * (sourcePower * root) ≤
      pureWZ2SourceHorizontalWindowSupply sourceVolume rho := by
    calc
      (4 : ENNReal)⁻¹ * (sourcePower * root) ≤
          (4 : ENNReal)⁻¹ * (sourceVolume * root) := by
        gcongr
      _ ≤ pureWZ2SourceHorizontalWindowSupply sourceVolume rho := hwindow
  have hconstant : (32 : ENNReal)⁻¹ =
      (8 : ENNReal)⁻¹ * (4 : ENNReal)⁻¹ := by
    rw [show (32 : ENNReal) = 8 * 4 by norm_num]
    exact ENNReal.mul_inv (by simp) (by simp)
  calc
    (32 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
            Kakeya.realRpowENN rho (stickyLoss + twoScale.coarseLoss) *
            Kakeya.realRpowENN rho (1 / 2 : ℝ) *
            Kakeya.realRpowENN twoScale.rhoRequested.1
              (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)) =
        (8 : ENNReal)⁻¹ *
          ((4 : ENNReal)⁻¹ * (sourcePower * root)) * secondPower := by
      rw [hconstant, hroot]
      simp only [sourcePower, secondPower]
      ac_rfl
    _ ≤ (8 : ENNReal)⁻¹ *
        pureWZ2SourceHorizontalWindowSupply sourceVolume rho * fineMass := by
      gcongr
    _ = pureWZ2OrdinaryPaperOrderBlockThreshold sourceVolume rho *
        fineMass := by
      rfl

/-- Reduce the dependent per-block all-bin budget to one source-independent
scalar inequality.  The two finite pigeonhole costs are bounded separately,
while the right side is the canonical regularized-block supply floor. -/
theorem PureWZ2OrdinaryPaperOrderAllGlobalBinCoarsePreparationData.selectGoodCoarseBinsOfScalarBudget
    {sigma inputLoss delta rho middleLoss stickyLoss volumeLoss outerLoss : ℝ}
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
    (houter : ∀ block : {block // block ∈ safe.blocks},
      (2 * (carriers.carrier block).outerPopular.popular.bins : ENNReal) ≤
        Kakeya.realRpowENN (256 * rho) (-outerLoss))
    (hscalar :
      Kakeya.realRpowENN (256 * rho) (-outerLoss) *
          (2 * (pureWZ2OrdinaryAllBinCoarseVolumeConstant *
            Kakeya.realRpowENN delta (sigma - inputLoss) *
            Kakeya.realRpowENN rho 1) *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss)) ≤
        (32 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
            Kakeya.realRpowENN rho
              (stickyLoss + twoScale.coarseLoss) *
            Kakeya.realRpowENN rho (1 / 2 : ℝ) *
            Kakeya.realRpowENN twoScale.rhoRequested.1
              (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))) :
    Nonempty
      (PureWZ2OrdinaryPaperOrderRegularizedGoodCoarseBinData
        (volumeLoss := volumeLoss) coarseBins) := by
  apply coarseBins.selectGoodCoarseBinsOfPowerBudget
  intro block
  let line := (allBins.binFamily block.1).line
  have hcountCost :=
    PureWZ2SourceHorizontalFixedBinData.global_bin_count_mul_coarseCost_upper
      line.toFixedBinData
    (by
      rw [← twoScale.rhoRequested_eq]
      exact twoScale.rhoRequested.property.2)
  calc
    ((2 * (carriers.carrier block.1).outerPopular.popular.bins :
          ENNReal) *
          ((2 * ((line.globalBins.card : ENNReal) *
              Kakeya.realRpowENN (256 * rho)
                (1 + sigma / 2 + volumeLoss))) *
            pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta)) ≤
        Kakeya.realRpowENN (256 * rho) (-outerLoss) *
          (2 * (pureWZ2OrdinaryAllBinCoarseVolumeConstant *
            Kakeya.realRpowENN delta (sigma - inputLoss) *
            Kakeya.realRpowENN rho 1) *
            Kakeya.realRpowENN (256 * rho)
              (1 + sigma / 2 + volumeLoss)) := by
      calc
        _ ≤ Kakeya.realRpowENN (256 * rho) (-outerLoss) *
            ((2 * ((line.globalBins.card : ENNReal) *
                Kakeya.realRpowENN (256 * rho)
                  (1 + sigma / 2 + volumeLoss))) *
              pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta) := by
          exact mul_le_mul_right' (houter block.1) _
        _ = Kakeya.realRpowENN (256 * rho) (-outerLoss) *
            (2 * ((line.globalBins.card : ENNReal) *
              pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta) *
              Kakeya.realRpowENN (256 * rho)
                (1 + sigma / 2 + volumeLoss)) := by
          ring
        _ ≤ _ := by
          apply mul_le_mul_left'
          calc
            2 * ((line.globalBins.card : ENNReal) *
                  pureWZ2OrdinaryAllBinCoarseVolumeCost rho delta) *
                Kakeya.realRpowENN (256 * rho)
                  (1 + sigma / 2 + volumeLoss) ≤
              2 * (pureWZ2OrdinaryAllBinCoarseVolumeConstant *
                  Kakeya.realRpowENN delta (sigma - inputLoss) *
                  Kakeya.realRpowENN rho 1) *
                Kakeya.realRpowENN (256 * rho)
                  (1 + sigma / 2 + volumeLoss) := by
              gcongr
            _ = _ := rfl
    _ ≤ (32 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta (sigma + twoScale.coarseLoss) *
            Kakeya.realRpowENN rho
              (stickyLoss + twoScale.coarseLoss) *
            Kakeya.realRpowENN rho (1 / 2 : ℝ) *
            Kakeya.realRpowENN twoScale.rhoRequested.1
              (3 / 2 + sigma / 2 + 3 * stickyLoss / 2)) := hscalar
    _ ≤ pureWZ2OrdinaryPaperOrderBlockThreshold
          (volume prepared.shadow.union) rho *
        twoScale.fine.balanced.cellMass :=
      prepared.regularized_block_supply_power_lower

end Kakeya.Assouad

end
