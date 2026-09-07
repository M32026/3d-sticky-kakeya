import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularFullParentLocalBins

/-!
# Paper-order local bins on the terminal outer-popular graph

The compatibility name below now denotes the paper-order construction: full
balanced parents are used only to certify the source normal, while every
cell counted by the local-bin package remains an actual cell of the localized
outer-popular shadow.
-/

noncomputable section

namespace Kakeya.Assouad

abbrev PureWZ2TerminalPopularLocalCellData
    {sigma inputLoss delta stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    (graphParents : PureWZ2TerminalPopularGraphParentData prep) :=
  PureWZ2TerminalPopularFullParentLocalBinData (eta := eta) graphParents

theorem PureWZ2TerminalPopularGraphParentData.localCells
    {sigma inputLoss delta stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    {restrictedPrepared :
      PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
    {line : PureWZ2HorizontalFixedBinCore
      restrictedPrepared.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
    {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
    {selectedCarrier :
      PureWZ2TerminalPopularSelectedParentCarrierData selection}
    {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
    {localized : PureWZ2TerminalPopularLocalizedPieceData
      (selectedCarrier := selectedCarrier) sources}
    {prep : PureWZ2TerminalPopularGraphPreparation localized}
    (graphParents : PureWZ2TerminalPopularGraphParentData prep)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCpower : 10 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-eta))
    (hPlanarSmall : 32 * Real.rpow delta eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt delta ≤ 1)
    (habsorb : Real.rpow delta (1 - 4 * eta / sigma) ≤
      Real.sqrt delta / 14)
    (htransferSmall : 1000 * Real.sqrt delta ≤ 1)
    (hsourceVolume :
      (512 : ENNReal) * Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 + eta) ≤
        terminal.sticky.balanced.cellMass) :
    Nonempty (PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents) :=
  graphParents.fullParentLocalBins hbridge hsigma hsigmaOne heta hetaSigma
    hCpower hPlanarSmall hrootSmall20 habsorb htransferSmall hsourceVolume

end Kakeya.Assouad

end
