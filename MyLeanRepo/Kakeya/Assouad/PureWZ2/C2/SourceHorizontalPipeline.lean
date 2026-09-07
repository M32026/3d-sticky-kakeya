import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalOneScaleAssembly

/-!
# Dependent source-horizontal Pure one-scale pipeline

All graph, parent, shading, and grain witnesses are retained in one record.
No coarse carrier is identified with the original source carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure PureWZ2SourceHorizontalPipelineData
    {sigma inputLoss delta rho middleLoss outputLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent) where
  pullback : PureWZ2TwoScaleCellPullbackData twoScale
  prepared : PureWZ2SourceCarrierPreparation pullback
  window : PureWZ2SourceCarrierWindow prepared
  line : PureWZ2SourceHorizontalFixedLineData window
  parents : PureWZ2SourceHorizontalParentData line
  selection : PureWZ2SourceHorizontalYSelection parents
  residue : PureWZ2SourceHorizontalYResidueData selection
  retained : PureWZ2SourceHorizontalResidueShadingData residue
  prep : PureWZ2SourceHorizontalResiduePreparation retained
  shadow_union : prep.shadow.union = retained.shading.union
  graphParents : PureWZ2SourceHorizontalGraphParentData prep
  fineWitnesses : PureWZ2SourceHorizontalFineWitnessData retained
  normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate
    (eta := normalEta) fineWitnesses
  heightPopular : PureWZ2SourceHorizontalHeightPopularShadow
    retained prep.shadow prep.graphScale
  popularSource : PureWZ2SourceHorizontalPopularResidueData heightPopular
  rawResidue : WZ1Lemma23YResiduePackage prep.windowed.global
  rawResidue_eq : rawResidue = popularSource.residue
  popularResidue : WZ1Lemma23HeightPopularResidueData rawResidue
  graph : WZ1Lemma23WindowedPreparedGraph prep.windowed
  graph_residue_eq : graph.residue = popularResidue.residue
  heightFiberCost_eq : graph.residue.heightFiberCost = 2
  extraCost_eq : graph.residue.extraCost =
    2 * heightPopular.bins *
      (Nat.log 2 rawResidue.cells.card + 1)
  volumeCost_eq : graph.residue.volumeCost =
    wz1Lemma23YStride prep.graphScale * graph.residue.extraCost
  sharp : PureWZ2SourceHorizontalSharpGeometry graph

/-- Continue the dependent source-horizontal construction from one supplied
positive complete-cell window. -/
theorem PureWZ2SourceCarrierWindow.sourceHorizontalPipelineWithExactWindow
    {sigma inputLoss delta rho middleLoss outputLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta) (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * outputLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (habsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    ∃ pipeline : PureWZ2SourceHorizontalPipelineData
        (normalEta := normalEta) twoScale,
      pipeline.window.left = window.left ∧
        pipeline.window.shading.union = window.shading.union ∧
          pipeline.window.volumeSupply = window.volumeSupply := by
  have hwindowVolume : 0 < MeasureTheory.volume window.shading.union := by
    exact window.volumeSupply_pos.trans_le window.volume_lower
  rcases window.selectHorizontalFixedLine hwindowVolume with ⟨line⟩
  rcases line.toParents with ⟨parents⟩
  rcases parents.selectOnePerY with ⟨selection⟩
  rcases selection.selectResidue with ⟨residue⟩
  rcases residue.retainSourceShading with ⟨retained, hretainedShadow⟩
  rcases retained.prepare hbridge hgraphOne hheightAbsorb with ⟨prep⟩
  have hprepShadow : prep.shadow.union = retained.shading.union := by
    rw [prep.shadow_eq, hretainedShadow]
  rcases prep.graphParents with ⟨graphParents⟩
  rcases retained.fineWitnesses with ⟨fineWitnesses⟩
  rcases fineWitnesses.normalFirst hbridge hsigma hsigmaOne
      hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor
      hlocalPower hglobalPower hPlanarSmall hrootSmall20 habsorb with
    ⟨normalFirst⟩
  have hshadowVolume : 0 < MeasureTheory.volume prep.shadow.union := by
    rw [hprepShadow]
    have hselected : 0 < (residue.selected.card : ENNReal) := by
      exact_mod_cast residue.selected_nonempty.card_pos
    exact (ENNReal.mul_pos hselected.ne'
      twoScale.coarse.balanced.cellMass_pos.ne').trans_le retained.volume_lower
  rcases graphParents.preparedGraph fineWitnesses normalFirst hshadowVolume with
    ⟨rawResidue, heightPopular, popularSource, popularResidue, graph,
      hrawResidue, hgraphResidue, hheightFiberCost, hextraCost, hvolumeCost⟩
  rcases graph.toSourceSharpGeometry with ⟨sharp⟩
  let pipeline : PureWZ2SourceHorizontalPipelineData
      (normalEta := normalEta) twoScale := {
    pullback := pullback
    prepared := prepared
    window := window
    line := line
    parents := parents
    selection := selection
    residue := residue
    retained := retained
    prep := prep
    shadow_union := hprepShadow
    graphParents := graphParents
    fineWitnesses := fineWitnesses
    normalFirst := normalFirst
    heightPopular := heightPopular
    popularSource := popularSource
    rawResidue := rawResidue
    rawResidue_eq := hrawResidue
    popularResidue := popularResidue
    graph := graph
    graph_residue_eq := hgraphResidue
    heightFiberCost_eq := hheightFiberCost
    extraCost_eq := hextraCost
    volumeCost_eq := hvolumeCost
    sharp := sharp
  }
  exact ⟨pipeline, rfl, rfl, rfl⟩

/-- Compatibility form exposing only the two scalar window fields. -/
theorem PureWZ2SourceCarrierWindow.sourceHorizontalPipelineWithWindow
    {sigma inputLoss delta rho middleLoss outputLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta) (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * outputLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (habsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    ∃ pipeline : PureWZ2SourceHorizontalPipelineData
        (normalEta := normalEta) twoScale,
      pipeline.window.left = window.left ∧
        pipeline.window.volumeSupply = window.volumeSupply := by
  rcases window.sourceHorizontalPipelineWithExactWindow hbridge
      hsigma hsigmaOne hnormalEta hnormalEtaSigma hcertificateOne
      hsourceFloor hlocalPower hglobalPower hPlanarSmall hrootSmall20
      habsorb hgraphOne hheightAbsorb with
    ⟨pipeline, hleft, _hshading, hsupply⟩
  exact ⟨pipeline, hleft, hsupply⟩

/-- Compatibility view without the explicit caller-window equality. -/
theorem PureWZ2SourceCarrierWindow.sourceHorizontalPipeline
    {sigma inputLoss delta rho middleLoss outputLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta) (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * outputLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (habsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2SourceHorizontalPipelineData
      (normalEta := normalEta) twoScale) := by
  rcases window.sourceHorizontalPipelineWithWindow hbridge hsigma hsigmaOne
      hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor
      hlocalPower hglobalPower hPlanarSmall hrootSmall20 habsorb
      hgraphOne hheightAbsorb with ⟨pipeline, _⟩
  exact ⟨pipeline⟩

/-- Select the maximal complete-cell window and run the dependent local
pipeline. -/
theorem PureWZ2OneScaleTwoScaleStickyData.sourceHorizontalPipeline
    {sigma inputLoss delta rho middleLoss outputLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta) (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * outputLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (habsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2SourceHorizontalPipelineData
      (normalEta := normalEta) twoScale) := by
  rcases twoScale.pullbackSelectedCells with ⟨pullback⟩
  rcases pullback.prepareSourceCarrier hbridge with ⟨prepared⟩
  rcases prepared.selectWindow with ⟨window⟩
  exact window.sourceHorizontalPipeline hbridge hsigma hsigmaOne
    hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor
    hlocalPower hglobalPower hPlanarSmall hrootSmall20 habsorb
    hgraphOne hheightAbsorb

end Kakeya.Assouad
