import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalPreparedGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedPreparedGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedGlobalBinPackage

/-!
# Sharp localized geometry on the source-slope residue graph
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2SourceHorizontalFixedBinSharpGeometry
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalFixedBinResiduePreparation retained}
    (graph : WZ1Lemma23WindowedPreparedGraph prep.windowed) where
  localized : WZ1Lemma23LocalizedGlobalBinPackage prep.windowed.global
  sharp : WZ1Lemma23LocalizedPreparedPackage
    prep.windowed localized graph.residue graph.localBins
  geometry : WZ1Lemma23LocalizedPreparedGeometry sharp

theorem WZ1Lemma23WindowedPreparedGraph.toSourceSharpGeometryFixedBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedBinData window}
    {parents : PureWZ2SourceHorizontalFixedBinParentData line}
    {selection : PureWZ2SourceHorizontalFixedBinYSelection parents}
    {residue : PureWZ2SourceHorizontalFixedBinYResidueData selection}
    {retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalFixedBinResiduePreparation retained}
    (graph : WZ1Lemma23WindowedPreparedGraph prep.windowed) :
    Nonempty (PureWZ2SourceHorizontalFixedBinSharpGeometry graph) := by
  have hcoord :
      ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpaper : point ∈ retained.shading.union := by
      exact prep.shadow_union_subset hpoint
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hCtop :
      (10 * Kakeya.realRpowENN delta (-inputLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  rcases wz1_lemma23_localized_global_bin_package_of_coord_of_exact
      prep.windowed.global prep.graphScale_one hcoord prep.exactAD
      hCtop prep.localization.center prep.localization.localization with
    ⟨localized, _⟩
  rcases wz1_lemma23_localized_prepared_package
      prep.windowed localized graph.residue graph.localBins with ⟨sharp⟩
  rcases wz1_lemma23_localized_prepared_geometry_of_coord
      prep.graphScale_one hcoord sharp with ⟨geometry⟩
  exact ⟨{ localized := localized, sharp := sharp, geometry := geometry }⟩


/-- Backwards-compatible sharp geometry on the maximal global bin. -/
abbrev PureWZ2SourceHorizontalSharpGeometry
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    (graph : WZ1Lemma23WindowedPreparedGraph prep.windowed) :=
  PureWZ2SourceHorizontalFixedBinSharpGeometry graph

/-- Compatibility wrapper for the former maximal-bin sharp-geometry API. -/
theorem WZ1Lemma23WindowedPreparedGraph.toSourceSharpGeometry
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    {prep : PureWZ2SourceHorizontalResiduePreparation retained}
    (graph : WZ1Lemma23WindowedPreparedGraph prep.windowed) :
    Nonempty (PureWZ2SourceHorizontalSharpGeometry graph) :=
  WZ1Lemma23WindowedPreparedGraph.toSourceSharpGeometryFixedBin graph

end Kakeya.Assouad
