import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseCarrierBlocks
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineSharpGeometry

/-!
# Dependent coarse-horizontal pipeline on one Lemma-24 slab

Every witness remains on the actual first-sticky coarse grain configuration.
The record ends immediately before the common-endpoint ready graph, so all
remaining premises are numerical.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2CoarseHorizontalPipelineData
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent) where
  prepared : PureWZ2Lemma23PreparedCoarse twoScale
  window : PureWZ2Lemma23WindowedCoarse prepared
  line : PureWZ2HorizontalFixedLineData window
  parents : PureWZ2HorizontalFixedLineParentData line
  selection : PureWZ2HorizontalFixedLineYSelection parents
  residue : PureWZ2HorizontalFixedLineYResidueData selection
  residueShading : PureWZ2HorizontalFixedLineResidueShadingData residue
  prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading
  graphParents : PureWZ2HorizontalFixedLineGraphParentData prep
  sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading
  fullGrains : PureWZ2HorizontalFixedLineResidueFullGrainFamily
    (eta := eta) sources prep
  graph : WZ1Lemma23WindowedPreparedGraph prep.windowed
  heightFiberCost_eq : graph.residue.heightFiberCost = 2
  extraCost_le_log : graph.residue.extraCost ≤
    Nat.log 2 prep.windowed.global.cells.card + 1
  sharp : PureWZ2HorizontalFixedLineSharpGeometry graph

theorem PureWZ2Lemma23WindowedCoarse.coarseHorizontalPipelineWithWindow
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (window : PureWZ2Lemma23WindowedCoarse prepared)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hgraphOne : 256 * twoScale.rhoRequested.1 ≤ 1)
    (hheightAbsorb :
      256 * twoScale.rhoRequested.1 +
          2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hsourceAbsorb :
      (512 : ENNReal) *
          Kakeya.realRpowENN (256 * twoScale.rhoRequested.1)
            (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN twoScale.rhoRequested.1
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hconstantPower :
      10 * Kakeya.realRpowENN
          twoScale.rhoRequested.1 (-middleLoss) ≤
        Kakeya.realRpowENN
          (256 * twoScale.rhoRequested.1) (-eta))
    (hPlanarSmall :
      32 * Real.rpow (256 * twoScale.rhoRequested.1) eta ≤ 1)
    (hrootSmall20 :
      20 * Real.sqrt (256 * twoScale.rhoRequested.1) ≤ 1)
    (habsorb :
      Real.rpow (256 * twoScale.rhoRequested.1)
          (1 - 4 * eta / sigma) ≤
        Real.sqrt (256 * twoScale.rhoRequested.1) / 14) :
    ∃ pipeline : PureWZ2CoarseHorizontalPipelineData
        (eta := eta) twoScale,
      pipeline.window.left = window.left ∧
        pipeline.window.volumeSupply = window.volumeSupply := by
  have hwindowVolume : 0 < MeasureTheory.volume window.shading.union :=
    window.volumeSupply_pos.trans_le window.volume_lower
  rcases window.selectHorizontalFixedLine hwindowVolume with ⟨line⟩
  rcases line.toParents with ⟨parents⟩
  rcases parents.selectOnePerY with ⟨selection⟩
  rcases selection.selectResidue with ⟨residue⟩
  rcases residue.retainShading with ⟨residueShading⟩
  rcases residueShading.prepare hbridge hgraphOne hheightAbsorb with ⟨prep⟩
  rcases prep.graphParents with ⟨graphParents⟩
  rcases residueShading.sources with ⟨sources⟩
  have hsourceAbsorb' :
      (512 : ENNReal) *
          Kakeya.realRpowENN prep.graphScale
            (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN twoScale.rhoRequested.1
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2) := by
    simpa [prep.graphScale_eq] using hsourceAbsorb
  have hconstantPower' :
      10 * Kakeya.realRpowENN
          twoScale.rhoRequested.1 (-middleLoss) ≤
        Kakeya.realRpowENN prep.graphScale (-eta) := by
    simpa [prep.graphScale_eq] using hconstantPower
  rcases sources.fullGrains prep hsourceAbsorb' hconstantPower' with
    ⟨fullGrains⟩
  rcases graphParents.preparedGraph sources fullGrains hsigma hsigmaOne
      heta hetaSigma hconstantPower'
      (by simpa [prep.graphScale_eq] using hPlanarSmall)
      (by simpa [prep.graphScale_eq] using hrootSmall20)
      (by simpa [prep.graphScale_eq] using habsorb) with
    ⟨graph, hheightFiberCost, hextraCost⟩
  rcases graph.toPureSharpGeometry
      (eta := eta) (graphParents := graphParents)
      (sources := sources) (fullGrains := fullGrains) with ⟨sharp⟩
  let pipeline : PureWZ2CoarseHorizontalPipelineData
      (eta := eta) twoScale := {
    prepared := prepared
    window := window
    line := line
    parents := parents
    selection := selection
    residue := residue
    residueShading := residueShading
    prep := prep
    graphParents := graphParents
    sources := sources
    fullGrains := fullGrains
    graph := graph
    heightFiberCost_eq := hheightFiberCost
    extraCost_le_log := hextraCost
    sharp := sharp
  }
  exact ⟨pipeline, rfl, rfl⟩

/-- Compatibility view when the caller does not need the supplied-window
provenance equations. -/
theorem PureWZ2Lemma23WindowedCoarse.coarseHorizontalPipeline
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (window : PureWZ2Lemma23WindowedCoarse prepared)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hgraphOne : 256 * twoScale.rhoRequested.1 ≤ 1)
    (hheightAbsorb :
      256 * twoScale.rhoRequested.1 +
          2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1)
    (hsourceAbsorb :
      (512 : ENNReal) *
          Kakeya.realRpowENN (256 * twoScale.rhoRequested.1)
            (3 / 2 + sigma / 2 + eta) ≤
        Kakeya.realRpowENN twoScale.rhoRequested.1
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hconstantPower :
      10 * Kakeya.realRpowENN
          twoScale.rhoRequested.1 (-middleLoss) ≤
        Kakeya.realRpowENN
          (256 * twoScale.rhoRequested.1) (-eta))
    (hPlanarSmall :
      32 * Real.rpow (256 * twoScale.rhoRequested.1) eta ≤ 1)
    (hrootSmall20 :
      20 * Real.sqrt (256 * twoScale.rhoRequested.1) ≤ 1)
    (habsorb :
      Real.rpow (256 * twoScale.rhoRequested.1)
          (1 - 4 * eta / sigma) ≤
        Real.sqrt (256 * twoScale.rhoRequested.1) / 14) :
    Nonempty (PureWZ2CoarseHorizontalPipelineData
      (eta := eta) twoScale) := by
  rcases window.coarseHorizontalPipelineWithWindow hbridge hsigma hsigmaOne
      heta hetaSigma hgraphOne hheightAbsorb hsourceAbsorb hconstantPower
      hPlanarSmall hrootSmall20 habsorb with ⟨pipeline, _⟩
  exact ⟨pipeline⟩

end Kakeya.Assouad
