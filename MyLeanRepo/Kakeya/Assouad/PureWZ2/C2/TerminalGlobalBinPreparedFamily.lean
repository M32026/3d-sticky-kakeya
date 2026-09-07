import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalGlobalBinFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactPreparedGraph

/-!
# Sharp terminal graphs on every global-bin fibre

The paper's terminal locally-linear step must not discard all but one global
AD bin. This module runs the carrier and local-grain preparation on every
nonempty bin of the common Fubini slice. It deliberately stops before the
ready-graph volume hypothesis: a small bin need not satisfy the same pointwise
power lower bound as the sum of all bins.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Per-bin terminal graph data through the sharp localized geometry stage. -/
structure PureWZ2TerminalGlobalBinPreparedFamily
    {sigma inputLoss delta stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    (family : PureWZ2TerminalGlobalBinParentFamily line) where
  localCells : ∀ bin,
    PureWZ2TerminalExactLocalCellData
      (eta := eta) (family.graphParents bin)
  preparedGraph : ∀ bin,
    PureWZ2TerminalExactPreparedGraphData (localCells bin)
  sharp : ∀ bin,
    PureWZ2TerminalExactSharpGeometry (preparedGraph bin)

/-- Complete all per-bin graph geometry up to the point where a quantitative
volume certificate is needed. No largest-bin cardinality estimate is used. -/
theorem PureWZ2TerminalGlobalBinParentFamily.prepareAllBins
    {sigma inputLoss delta stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    (family : PureWZ2TerminalGlobalBinParentFamily line)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCpower : 10 * Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-eta))
    (hPlanarSmall : 32 * Real.rpow delta eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt delta ≤ 1)
    (habsorb : Real.rpow delta (1 - 4 * eta / sigma) ≤
      Real.sqrt delta / 14)
    (hsourceVolume :
      (512 * (2 * 512 * 57) : ENNReal) *
          Kakeya.realRpowENN delta (3 / 2 + sigma / 2 + eta) ≤
        terminal.sticky.balanced.cellMass) :
    Nonempty (PureWZ2TerminalGlobalBinPreparedFamily
      (eta := eta) family) := by
  let localCells : ∀ bin,
      PureWZ2TerminalExactLocalCellData
        (eta := eta) (family.graphParents bin) := fun bin =>
    Classical.choice ((family.graphParents bin).localCells
      hsigma hsigmaOne heta hetaSigma hCpower hPlanarSmall
      hrootSmall20 habsorb hsourceVolume)
  let preparedGraph : ∀ bin,
      PureWZ2TerminalExactPreparedGraphData (localCells bin) := fun bin =>
    Classical.choice ((localCells bin).prepareGraph)
  let sharp : ∀ bin,
      PureWZ2TerminalExactSharpGeometry (preparedGraph bin) := fun bin =>
    Classical.choice ((preparedGraph bin).toSharpGeometry)
  exact ⟨{
    localCells := localCells
    preparedGraph := preparedGraph
    sharp := sharp
  }⟩

end Kakeya.Assouad

end
