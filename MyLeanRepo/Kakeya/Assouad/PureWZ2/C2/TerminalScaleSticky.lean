import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OneScaleTwoScaleSticky

/-!
# Single sticky decomposition for the exact terminal Lemma-23 scale

At the terminal Corollary-26 level the Lemma-23 scale is the source tube
radius `delta`.  The public sticky theorem cannot be called at `rho = delta`:
its Lemma-24 window has lower endpoint `delta^(1-epsilon)`.  The paper needs
only the coarse `sqrt delta` geometry at this endpoint.  We therefore retain
the original grain configuration as the Lemma-23 carrier and apply sticky
exactly once, at `sqrt delta`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Provenance-preserving terminal-scale decomposition. -/
structure PureWZ2TerminalScaleStickyData
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (stickyLoss : ℝ) (logExponent : ℕ) where
  sqrtRequested : WZ2PaperRequestedScale delta
  sqrtRequested_eq : sqrtRequested.1 = Real.sqrt delta
  sticky : PureWZ2TerminalStickyCore
    (sigma := sigma) (outputLoss := stickyLoss)
    source.shading sqrtRequested logExponent

/--
The second call in an ordinary two-scale sticky witness is literally a
terminal sticky decomposition of the intermediate grain configuration.

This adapter changes no family, shading, requested scale, or sticky output.
It is the provenance-preserving entry point for reusing the terminal
block--parent weighted construction inside an ordinary hierarchy step.
-/
noncomputable def PureWZ2OneScaleTwoScaleStickyData.toTerminalScaleStickyData
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent) :
    PureWZ2TerminalScaleStickyData
      (data.coarseGrains.toQuantitativeGrainConfiguration
        data.coarseGrains_slope_bound) stickyLoss logExponent where
  sqrtRequested := data.sqrtRequested
  sqrtRequested_eq := data.sqrtRequested_eq.trans
    (congrArg Real.sqrt data.rhoRequested_eq.symm)
  sticky := data.fine.toTerminalStickyCore

@[simp] theorem PureWZ2OneScaleTwoScaleStickyData.toTerminalScaleStickyData_sticky
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent) :
    data.toTerminalScaleStickyData.sticky = data.fine.toTerminalStickyCore := rfl

end Kakeya.Assouad
