import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineCoarsePreparedGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedPreparedGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedGlobalBinPackage

/-!
# Sharp localized geometry on the genuine coarse graph

The localized global-bin estimate uses the original source slope and the
fixed line selected before passing to the first-sticky coarse carrier.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2SourceFixedBinCoarseSharpGeometry
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale} {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared} {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line} {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection} {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue} {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate (eta := eta) fineWitnesses}
    (preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst) where
  localized : WZ1Lemma23LocalizedGlobalBinPackage prep.windowed.global
  sharp : WZ1Lemma23LocalizedPreparedPackage prep.windowed localized
    preparedGraph.graph.residue preparedGraph.graph.localBins
  geometry : WZ1Lemma23LocalizedPreparedGeometry sharp

abbrev PureWZ2SourceFixedLineCoarseSharpGeometry
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate (eta := eta) carriers.fineWitnesses}
    (preparedGraph : PureWZ2SourceFixedLineCoarsePreparedGraphData graphParents normalFirst) : Type :=
  PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph

/-- Attach the sharp localized global-bin bound and all closed geometric
Theorem-22 inputs to the genuine-coarse prepared graph. -/
theorem PureWZ2SourceFixedBinCoarsePreparedGraphData.toSharpGeometryFixedBin
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss stickyLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale} {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared} {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line} {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection} {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {carrier : PureWZ2SourceFixedBinCoarseCarrierData residue} {fineWitnesses : PureWZ2SourceHorizontalFixedBinFineWitnessData retained}
    {original : PureWZ2SourceFixedBinCoarseOriginalSlopeData carrier fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedBinCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedBinCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalFixedBinNormalFirstCertificate (eta := eta) fineWitnesses}
    (preparedGraph : PureWZ2SourceFixedBinCoarsePreparedGraphData
      graphParents normalFirst) :
    Nonempty (PureWZ2SourceFixedBinCoarseSharpGeometry preparedGraph) := by
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hcarrier : point ∈ carrier.shading.union := by
      exact prep.shadow_union_subset hpoint
    have hbox := shading_union_subset_axisBox
      (carrier.subshading.union_subset hcarrier)
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hCtop :
      (10 * Kakeya.realRpowENN rho (-middleLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  rcases wz1_lemma23_localized_global_bin_package_of_coord_of_exact
      prep.windowed.global prep.graphScale_one hcoord prep.exactAD hCtop
      prep.localization.center prep.localization.localization with
    ⟨localized, _⟩
  rcases wz1_lemma23_localized_prepared_package prep.windowed localized
      preparedGraph.graph.residue preparedGraph.graph.localBins with
    ⟨sharp⟩
  rcases wz1_lemma23_localized_prepared_geometry_of_coord
      prep.graphScale_one hcoord sharp with ⟨geometry⟩
  exact ⟨{ localized := localized, sharp := sharp, geometry := geometry }⟩

/-- Backwards-compatible maximal-bin constructor for sharp geometry. -/
theorem PureWZ2SourceFixedLineCoarsePreparedGraphData.toSharpGeometry
    {sigma inputLoss delta rho middleLoss stickyLoss eta : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss stickyLoss logExponent}
    {carriers : PureWZ2OrdinaryPaperOrderCarrierData twoScale}
    {original : PureWZ2SourceFixedLineCoarseOriginalSlopeData carriers.coarseCarrier carriers.fineWitnesses.coarseWitnesses}
    {prep : PureWZ2SourceFixedLineCoarsePreparationData original}
    {graphParents : PureWZ2SourceFixedLineCoarseGraphParentData prep}
    {normalFirst : PureWZ2SourceHorizontalNormalFirstCertificate (eta := eta) carriers.fineWitnesses}
    (preparedGraph : PureWZ2SourceFixedLineCoarsePreparedGraphData graphParents normalFirst) :
    Nonempty (PureWZ2SourceFixedLineCoarseSharpGeometry preparedGraph) :=
  PureWZ2SourceFixedBinCoarsePreparedGraphData.toSharpGeometryFixedBin preparedGraph

end Kakeya.Assouad

end
