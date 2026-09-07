import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedPreparedPackage

/-!
# Edge cardinality from quantitative WZ1 Lemma 23 bounds

This module is the purely finite final step of the Lemma 23 counting
argument.  It consumes:

* a lower bound for the selected actual cell count;
* upper bounds for occupied y-layers and heights;
* upper bounds for the local and localized global scalar bins; and
* one parameter-budget inequality with no graph-cardinality premise.

The closed four-cycle abundance inequality then gives the requested lower
bound for the actual normalized edge set.
-/

namespace Kakeya.Assouad

noncomputable section

/--
Convert the quantitative cell/layer/bin bounds into an edge-cardinality lower
bound.

The `hbudget` premise is the isolated exponent-and-constant absorption
obligation.  It contains no reference to the edge set.
-/
theorem WZ1Lemma23LocalizedPreparedPackage.edge_cardinality_from_bounds
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    {localized :
      WZ1Lemma23LocalizedGlobalBinPackage windowed.global}
    {residue :
      WZ1Lemma23YResiduePackage windowed.global}
    {localBins :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C windowed.global.cells}
    (package :
      WZ1Lemma23LocalizedPreparedPackage
        windowed localized residue localBins)
    (cellLower yLayerUpper localBinUpper
      heightUpper globalBinUpper target : ℝ)
    (hcellLower : 0 ≤ cellLower)
    (hyLayerUpper : 0 < yLayerUpper)
    (hlocalBinUpper : 0 < localBinUpper)
    (hheightUpper : 0 < heightUpper)
    (hglobalBinUpper : 0 < globalBinUpper)
    (hcells :
      cellLower ≤ (residue.cells.card : ℝ))
    (hyLayers :
      ((wz1Lemma23SnappedYLayers residue.cells).card : ℝ) ≤
        yLayerUpper)
    (hlocalBins :
      (package.selectedLocal.localBinBound : ℝ) ≤
        localBinUpper)
    (hheights :
      ((wz1Lemma23SnappedHeights residue.cells).card : ℝ) ≤
        heightUpper)
    (hglobalBins :
      (localized.globalBinBound : ℝ) ≤
        globalBinUpper)
    (hbudget :
      target *
          ((yLayerUpper * localBinUpper) ^ 2 *
            (heightUpper ^ 2 * globalBinUpper) *
            (heightUpper * globalBinUpper) * 16) ≤
        cellLower ^ 4) :
    target ≤ (package.normalized.H.card : ℝ) := by
  have habundance :
      (residue.cells.card : ℝ) ^ 4 ≤
        (((wz1Lemma23SnappedYLayers residue.cells).card : ℝ) *
            (package.selectedLocal.localBinBound : ℝ)) ^ 2 *
          (((wz1Lemma23SnappedHeights residue.cells).card : ℝ) ^ 2 *
            (localized.globalBinBound : ℝ)) *
          (((wz1Lemma23SnappedHeights residue.cells).card : ℝ) *
            (localized.globalBinBound : ℝ)) *
          16 * (package.normalized.H.card : ℝ) := by
    exact_mod_cast package.abundance
  have hcellPower :
      cellLower ^ 4 ≤ (residue.cells.card : ℝ) ^ 4 := by
    gcongr
  let actualDenominator : ℝ :=
    (((wz1Lemma23SnappedYLayers residue.cells).card : ℝ) *
        (package.selectedLocal.localBinBound : ℝ)) ^ 2 *
      (((wz1Lemma23SnappedHeights residue.cells).card : ℝ) ^ 2 *
        (localized.globalBinBound : ℝ)) *
      (((wz1Lemma23SnappedHeights residue.cells).card : ℝ) *
        (localized.globalBinBound : ℝ)) * 16
  let upperDenominator : ℝ :=
    (yLayerUpper * localBinUpper) ^ 2 *
      (heightUpper ^ 2 * globalBinUpper) *
      (heightUpper * globalBinUpper) * 16
  have hactual :
      (residue.cells.card : ℝ) ^ 4 ≤
        actualDenominator * (package.normalized.H.card : ℝ) := by
    simpa [actualDenominator, mul_assoc] using habundance
  have hdenominator :
      actualDenominator ≤ upperDenominator := by
    dsimp only [actualDenominator, upperDenominator]
    gcongr
  have hHnonneg :
      0 ≤ (package.normalized.H.card : ℝ) := by positivity
  have hactualUpper :
      actualDenominator * (package.normalized.H.card : ℝ) ≤
        upperDenominator * (package.normalized.H.card : ℝ) := by
    gcongr
  have hmain :
      target * upperDenominator ≤
        upperDenominator * (package.normalized.H.card : ℝ) :=
    hbudget.trans
      (hcellPower.trans (hactual.trans hactualUpper))
  have hupperPos : 0 < upperDenominator := by
    dsimp only [upperDenominator]
    positivity
  nlinarith

end

end Kakeya.Assouad
