import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalPopularCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalResiduePreparation

/-!
# Install the outer-popular carrier in the ordinary graph preparation

This is the type-safe form of the pre-graph source-volume restriction in WZ
Lemma 5.5.  The full residue shadow remains available for the already proved
fixed-line and local-grain estimates, while every exact-slice graph cell is
chosen from the outer-popular carrier.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Replace only the graph carrier of an existing ordinary preparation by the
outer-popular graph shadow.  Re-running `prepare` is essential: it rebuilds
the exact global slice package and graph local grains on the restricted
carrier, while retaining the full ambient shadow for the geometric bounds. -/
theorem PureWZ2SourceHorizontalFixedBinPopularCarrierData.installInPreparationFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho)}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    (carrier : PureWZ2SourceHorizontalFixedBinPopularCarrierData outerPopular retained)
    (base : PureWZ2SourceHorizontalFixedBinResiduePreparation retained)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2SourceHorizontalFixedBinResiduePreparation
      (retained.withPopularGraphFixedBin carrier)) := by
  exact (retained.withPopularGraphFixedBin carrier).prepareFixedBin hbridge
    (by rw [← base.graphScale_eq]; exact base.graphScale_one)
    (by rw [← base.graphScale_eq]; exact base.graphScale_two_root_bound)

/-- Compatibility wrapper for maximal-bin outer-popular preparation. -/
theorem PureWZ2SourceHorizontalPopularCarrierData.installInPreparation
    {sigma inputLoss delta rho middleLoss stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {sourceWindow : PureWZ2SourceCarrierWindow prepared}
    {outerPopular : PureWZ2SourceWindowHeightPopularData
      sourceWindow (256 * rho)}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    (carrier : PureWZ2SourceHorizontalPopularCarrierData outerPopular retained)
    (base : PureWZ2SourceHorizontalResiduePreparation retained)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2SourceHorizontalResiduePreparation
      (retained.withPopularGraph carrier)) :=
  carrier.installInPreparationFixedBin base hbridge

end Kakeya.Assouad

end
