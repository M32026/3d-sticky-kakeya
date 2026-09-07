import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLinePreparedGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedPreparedGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedGlobalBinPackage

/-!
# Sharp localized geometry for the Pure fixed-line graph
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2HorizontalFixedLineSharpGeometry
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading : PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    (graph : WZ1Lemma23WindowedPreparedGraph prep.windowed) where
  localized : WZ1Lemma23LocalizedGlobalBinPackage prep.windowed.global
  sharp : WZ1Lemma23LocalizedPreparedPackage
    prep.windowed localized graph.residue graph.localBins
  geometry : WZ1Lemma23LocalizedPreparedGeometry sharp

theorem WZ1Lemma23WindowedPreparedGraph.toPureSharpGeometry
    {sigma inputLoss delta rho middleLoss outputLoss eta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    {residueShading : PureWZ2HorizontalFixedLineResidueShadingData residue}
    {prep : PureWZ2HorizontalFixedLineResiduePreparation residueShading}
    {graphParents : PureWZ2HorizontalFixedLineGraphParentData prep}
    {sources : PureWZ2HorizontalFixedLineResidueSourceFamily residueShading}
    {fullGrains : PureWZ2HorizontalFixedLineResidueFullGrainFamily
      (eta := eta) sources prep}
    (graph : WZ1Lemma23WindowedPreparedGraph prep.windowed) :
    Nonempty (PureWZ2HorizontalFixedLineSharpGeometry graph) := by
  have hcoord :
      ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpaper : point ∈ residueShading.shading.union := by
      rwa [prep.shadow_union] at hpoint
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  rcases wz1_lemma23_localized_global_bin_package_of_coord_of_exact
      prep.windowed.global prep.graphScale_one hcoord prep.exactAD
      (ENNReal.mul_ne_top (by norm_num)
        (by simp [Kakeya.realRpowENN]))
      prep.localization.center prep.localization.localization with
    ⟨localized, _⟩
  rcases wz1_lemma23_localized_prepared_package
      prep.windowed localized graph.residue graph.localBins with ⟨sharp⟩
  rcases wz1_lemma23_localized_prepared_geometry_of_coord
      prep.graphScale_one hcoord sharp with ⟨geometry⟩
  exact ⟨{ localized := localized, sharp := sharp, geometry := geometry }⟩

end Kakeya.Assouad
