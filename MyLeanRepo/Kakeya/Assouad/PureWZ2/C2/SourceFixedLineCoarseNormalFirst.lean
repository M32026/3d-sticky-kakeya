import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderCarrier
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalNormalFirst

/-!
# Original normal tilt on the genuine coarse Lemma-23 carrier

The strong second-stage sources and their normals retain the original fine
provenance.  Their global comparison is now made against the genuine coarse
carrier equipped with the original interval slope.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

theorem PureWZ2SourceFixedBinCoarsePreparationData.normalFirstFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue}
    {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData
      carrier fineWitnesses.coarseWitnesses}
    (prep : PureWZ2SourceFixedBinCoarsePreparationData original)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-eta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-eta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (habsorb :
      Real.rpow (4 * rho) (1 - 4 * eta / sigma) ≤
        Real.sqrt (4 * rho) / 14) :
    Nonempty
      (PureWZ2SourceHorizontalFixedBinNormalFirstCertificate
        (eta := eta) fineWitnesses) := by
  apply PureWZ2SourceHorizontalFixedBinFineWitnessData.normalFirstOfGlobalFixedBin
    fineWitnesses
    carrier.shading.union source.globalGrains.slope
    source.globalGrains.slope_bound
  · intro z hz
    exact original.original_slope_exactADFixedBin z hz
  · intro parent hparent point hpoint
    rw [carrier.union_eq, carrier.selectedRegion_eq]
    exact ⟨hpoint.1, Set.mem_iUnion₂.mpr
      ⟨parent, hparent, hpoint.2⟩⟩
  · exact hbridge
  · exact hsigma
  · exact hsigmaOne
  · exact heta
  · exact hetaSigma
  · exact hcertificateOne
  · exact hsourceFloor
  · exact hlocalPower
  · exact hglobalPower
  · exact hPlanarSmall
  · exact hrootSmall20
  · exact habsorb

/-- Backwards-compatible maximal-bin constructor for the first normal tilt. -/
theorem PureWZ2SourceFixedLineCoarsePreparationData.normalFirst
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData
      carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    (prep : PureWZ2SourceFixedLineCoarsePreparationData original)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-eta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-eta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (habsorb :
      Real.rpow (4 * rho) (1 - 4 * eta / sigma) ≤
        Real.sqrt (4 * rho) / 14) :
    Nonempty
      (PureWZ2SourceHorizontalNormalFirstCertificate
        (eta := eta) carriers.fineWitnesses) :=
  PureWZ2SourceFixedBinCoarsePreparationData.normalFirstFixedBin prep
    hbridge hsigma hsigmaOne heta hetaSigma
    hcertificateOne hsourceFloor hlocalPower hglobalPower hPlanarSmall
    hrootSmall20 habsorb

end Kakeya.Assouad

end
