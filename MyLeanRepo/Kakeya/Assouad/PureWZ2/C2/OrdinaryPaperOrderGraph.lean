import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.OrdinaryPaperOrderPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalNormalFirst
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalPreparedGraph
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalSharpGeometry

/-!
# The ordinary Lemma-23 graph after pre-graph popularity

This is the graph-facing continuation of `OrdinaryPaperOrderPreparation`.
The second height popularity below is the internal `Z_popular` step of Lemma
23; it is distinct from the source-volume popularity performed before the
fixed-line selection.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

structure PureWZ2OrdinaryPaperOrderGraphData
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    (prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers) where
  normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate
    (eta := normalEta) prepared.fineWitnesses
  heightPopular : PureWZ2SourceHorizontalHeightPopularShadow
    prepared.graphRetained prepared.prep.shadow prepared.prep.graphScale
  popularSource : PureWZ2SourceHorizontalPopularResidueData heightPopular
  rawResidue : WZ1Lemma23YResiduePackage prepared.prep.windowed.global
  rawResidue_eq : rawResidue = popularSource.residue
  popularResidue : WZ1Lemma23HeightPopularResidueData rawResidue
  graph : WZ1Lemma23WindowedPreparedGraph prepared.prep.windowed
  graph_residue_eq : graph.residue = popularResidue.residue
  heightFiberCost_eq : graph.residue.heightFiberCost = 2
  extraCost_eq : graph.residue.extraCost =
    2 * heightPopular.bins *
      (Nat.log 2 rawResidue.cells.card + 1)
  volumeCost_eq : graph.residue.volumeCost =
    wz1Lemma23YStride prepared.prep.graphScale * graph.residue.extraCost
  sharp : PureWZ2SourceHorizontalSharpGeometry graph

/-- Run the finite graph on the already outer-popular source shadow. -/
theorem PureWZ2OrdinaryPaperOrderPreparationData.buildGraph
    {sigma inputLoss delta rho middleLoss stickyLoss normalEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    (prepared : PureWZ2OrdinaryPaperOrderPreparationData carriers)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hnormalEta : 0 < normalEta) (hnormalEtaSigma : 4 * normalEta < sigma)
    (hcertificateOne : 4 * rho ≤ 1)
    (hsourceFloor :
      Kakeya.realRpowENN (4 * rho)
          (3 / 2 + sigma / 2 + normalEta) ≤
        Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + 3 * stickyLoss / 2))
    (hlocalPower :
      160 * Kakeya.realRpowENN delta (-inputLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hglobalPower :
      10 * Kakeya.realRpowENN rho (-middleLoss) ≤
        Kakeya.realRpowENN (4 * rho) (-normalEta))
    (hPlanarSmall : 32 * Real.rpow (4 * rho) normalEta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt (4 * rho) ≤ 1)
    (hlocalizationAbsorb :
      Real.rpow (4 * rho) (1 - 4 * normalEta / sigma) ≤
        Real.sqrt (4 * rho) / 14)
    (hshadowVolume : 0 < volume prepared.prep.shadow.union) :
    Nonempty (PureWZ2OrdinaryPaperOrderGraphData
      (normalEta := normalEta) prepared) := by
  rcases prepared.fineWitnesses.normalFirst hbridge hsigma hsigmaOne
      hnormalEta hnormalEtaSigma hcertificateOne hsourceFloor
      hlocalPower hglobalPower hPlanarSmall hrootSmall20
      hlocalizationAbsorb with ⟨normalFirst⟩
  rcases prepared.graphParents.preparedGraph prepared.fineWitnesses
      normalFirst hshadowVolume with
    ⟨rawResidue, heightPopular, popularSource, popularResidue, graph,
      hrawResidue, hgraphResidue, hheightFiberCost, hextraCost, hvolumeCost⟩
  rcases graph.toSourceSharpGeometry with ⟨sharp⟩
  exact ⟨{
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
  }⟩

end Kakeya.Assouad

end
