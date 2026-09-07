import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceFixedLineLocalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GeometricInput

/-!
# Source-slope Lemma-23 preparation on the final residue carrier

The paper shading remains a subshading of the original `delta`-tube family.
Its ordinary shadow, local plane map, and global slope are therefore all
constructed from the same source configuration.  Only the graph grid is
coarsened to side `256 * rho`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

structure PureWZ2SourceHorizontalFixedBinResiduePreparation
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
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue) where
  graphScale : ℝ := 256 * rho
  graphScale_eq : graphScale = 256 * rho
  graphScale_pos : 0 < graphScale
  graphScale_one : graphScale ≤ 1
  graphScale_sqrt :
    Real.sqrt graphScale = 16 * twoScale.sqrtRequested.1
  graphScale_two_root_bound :
    graphScale + 2 * twoScale.sqrtRequested.1 ≤
      16 * twoScale.sqrtRequested.1
  sourceScale_le_graphScale : delta ≤ graphScale
  rho_le_graphScale : rho ≤ graphScale
  localPaper : PureWZ2LocalGrainData retained.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  localPaper_planeMap_eq :
    ∀ point : {point : Point3 // point ∈ retained.shading.union},
      localPaper.planeMap point = source.localGrains.planeMap
        ⟨point, retained.subshading.union_subset point.property⟩
  globalPaper : PureWZ2LipschitzGlobalGrainData retained.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  globalPaper_slope_eq : globalPaper.slope = source.globalGrains.slope
  ambientShadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily retained.shading source.extremal.delta_pos) :=
    pureWZ2ActiveCellShading retained.shading source.extremal.delta_pos
  ambientShadow_union : ambientShadow.union = retained.shading.union
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily retained.shading source.extremal.delta_pos) :=
    retained.graphShadow
  shadow_eq : shadow = retained.graphShadow
  shadow_sub_ambient : IsSubshading shadow ambientShadow
  shadow_union_subset : shadow.union ⊆ retained.shading.union
  ambientLocalGrains : WZ1LocalGrainData ambientShadow sigma
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  localGrains : WZ1LocalGrainData shadow sigma
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  ambientPlaneMap_eq_on_paper :
    ∀ point : {point : Point3 // point ∈ ambientShadow.union},
      ambientLocalGrains.planeMap point = localPaper.planeMap
        ⟨point, by simpa [ambientShadow_union] using point.property⟩
  planeMap_eq_on_paper :
    ∀ point : {point : Point3 // point ∈ shadow.union},
      localGrains.planeMap point = localPaper.planeMap
        ⟨point, shadow_union_subset point.property⟩
  planeMap_vertical_bound :
    ∀ point ∈ ambientShadow.union,
      |ambientLocalGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  windowed : WZ1Lemma23WindowedGlobalSlicePackage
    (delta := delta) (rho := graphScale) (sigma := sigma) shadow
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  sourceSlope_eq :
    windowed.global.sourceSlope = source.globalGrains.slope
  fixed_line_localization :
    ∀ point ∈ ambientShadow.union,
      |inner ℝ point
          (globalGrainDirection
            (windowed.global.sourceSlope (point (2 : Fin 3)))) -
        line.lineLevel| ≤ 14 * twoScale.sqrtRequested.1
  exactAD :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (windowed.global.sourceSlope z))
          (horizontalSlice shadow.union z))
        graphScale (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss))
  localization : WZ1Lemma23GlobalLocalizationInput windowed.global

lemma PureWZ2SourceHorizontalFixedBinResiduePreparation.activeCells_subset_ambientFixedBin
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
    (prep : PureWZ2SourceHorizontalFixedBinResiduePreparation retained) :
    wz1Lemma23ActiveCells prep.shadow prep.graphScale prep.graphScale_pos ⊆
      wz1Lemma23ActiveCells prep.ambientShadow prep.graphScale prep.graphScale_pos := by
  intro cell hcell
  rw [wz1Lemma23_mem_active_iff] at hcell ⊢
  refine ⟨hcell.1, ?_⟩
  rcases hcell.2 with ⟨point, hpoint⟩
  exact ⟨point, prep.shadow_sub_ambient.union_subset hpoint.1, hpoint.2⟩

theorem PureWZ2SourceHorizontalFixedBinResidueShadingData.prepareFixedBin
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
    (retained : PureWZ2SourceHorizontalFixedBinResidueShadingData residue)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2SourceHorizontalFixedBinResiduePreparation retained) := by
  let root := twoScale.sqrtRequested.1
  let graphScale := 256 * rho
  let C := Kakeya.realRpowENN delta (-inputLoss)
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrho : 0 < rho := hdelta.trans_le hdeltaRho
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hroot : 0 < root := twoScale.fine.coarse_extremal.delta_pos
  have hgraph : 0 < graphScale := by positivity
  have hrhoGraph : rho ≤ graphScale := by
    dsimp only [graphScale]
    nlinarith [hrho]
  have hdeltaGraph : delta ≤ graphScale := hdeltaRho.trans hrhoGraph
  have hsqrtRho : root = Real.sqrt rho := twoScale.sqrtRequested_eq
  have hsqrtGraph : Real.sqrt graphScale = 16 * root := by
    rw [show graphScale = 256 * rho by rfl, Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt (256 : ℝ) = 16 by norm_num, ← hsqrtRho]
  have hCtop : C ≠ ⊤ := by simp [C, Kakeya.realRpowENN]
  let localPaper : PureWZ2LocalGrainData retained.shading sigma C :=
    source.localGrains.restrictWithConstant retained.subshading le_rfl hCtop
  let restrictedGlobal :
      PureWZ2LipschitzGlobalGrainData retained.shading sigma C :=
    source.globalGrains.toPureWZ2LipschitzGlobalGrainData.restrict
      retained.subshading le_rfl hCtop
  let globalPaper :
      PureWZ2BoundedLipschitzGlobalGrainData retained.shading sigma C :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound restrictedGlobal <| by
      intro z hz
      exact source.globalGrains.slope_bound z hz
  have hglobalSlope : globalPaper.slope = source.globalGrains.slope := rfl
  let ambientShadow := pureWZ2ActiveCellShading retained.shading hdelta
  have hambientUnion : ambientShadow.union = retained.shading.union :=
    pureWZ2ActiveCellShading_union retained.shading hdelta retained.whole_cells
  let shadow := retained.graphShadow
  have hshadowSub : IsSubshading shadow ambientShadow := by
    simpa [shadow, ambientShadow] using retained.graphShadow_sub
  have hshadowUnion : shadow.union ⊆ retained.shading.union := by
    simpa [shadow] using retained.graphShadow_union_subset
  let ambientLocalGrains :=
    localPaper.toActiveCellShadow hdelta retained.whole_cells hbridge
  let localGrains : WZ1LocalGrainData shadow sigma (10 * C) :=
    restrictAndWeakenLocalGrains hshadowSub (by rfl) ambientLocalGrains
  have hplaneMapEq :
      ∀ point : {point : Point3 // point ∈ retained.shading.union},
        ambientLocalGrains.planeMap point = localPaper.planeMap point := by
    intro point
    exact (Classical.choose_spec localPaper.exists_ambient_extension).2 point
  have hverticalPaper :
      ∀ point : {point : Point3 // point ∈ retained.shading.union},
        |localPaper.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, retained.subshading.union_subset point.property⟩
  have hvertical :
      ∀ point ∈ ambientShadow.union,
        |ambientLocalGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 :=
    localPaper.toActiveCellShadow_vertical_bound
      hdelta retained.whole_cells hbridge hverticalPaper
  have hball : shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hpaper : point ∈ retained.shading.union := hshadowUnion hpoint
    have hnorm := norm_le_two_of_mem_paperShading hpaper
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord :
      ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpaper : point ∈ retained.shading.union := hshadowUnion hpoint
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hexact :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (globalPaper.slope z))
            (horizontalSlice shadow.union z))
          delta (1 - sigma) (10 * C) := by
    intro z hz
    apply (globalPaper.activeCellShadow_exactAD
      hdelta retained.whole_cells hbridge globalPaper.slope_bound z hz).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point, ⟨hshadowSub.union_subset hpoint.1, hpoint.2⟩, rfl⟩
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      shadow hgraph hdeltaGraph hgraphOne hball hcoord
      globalPaper.slope globalPaper.slope_lipschitz
      globalPaper.slope_bound (10 * C)
      (ENNReal.mul_ne_top (by norm_num) hCtop) hexact with
    ⟨global, hsourceSlope⟩
  let left :=
    (retained.commonParentHeight : ℝ) * root - graphScale / 2
  have hactiveWindow :
      WZ1Lemma23ActiveCellHeightWindow shadow global.rho_pos := by
    refine ⟨left, ?_⟩
    intro idx hidx
    have hactive := (wz1Lemma23_mem_active_iff shadow hgraph idx).mp hidx
    rcases hactive.2 with ⟨point, hpointShadow, hpointIndex⟩
    have hpointPaper : point ∈ retained.shading.union :=
      hshadowUnion hpointShadow
    have hheight := retained.union_height point hpointPaper
    have hcenter :=
      ((wz1_lemma23_snapped_cell_geometry
          graphScale hgraph hgraphOne).2.1 idx point hpointIndex).1
        (2 : Fin 3)
    have hcenterEq :
        (wz1Lemma23SnappedPoint graphScale idx) (2 : Fin 3) =
          (wz1Lemma23CellCenter graphScale idx) (2 : Fin 3) := rfl
    rw [hcenterEq, abs_le] at hcenter
    have hcenterLower :
        point (2 : Fin 3) - graphScale / 2 ≤
          (wz1Lemma23CellCenter graphScale idx) (2 : Fin 3) := by
      linarith [hcenter.2]
    have hcenterUpper :
        (wz1Lemma23CellCenter graphScale idx) (2 : Fin 3) ≤
          point (2 : Fin 3) + graphScale / 2 := by
      linarith [hcenter.1]
    constructor
    · dsimp only [left]
      linarith [hheight.1]
    · dsimp only [left]
      rw [hsqrtGraph]
      have habsorb : graphScale + root ≤ 16 * root := by
        have hstrong : graphScale + 2 * root ≤ 16 * root := by
          simpa [graphScale, root] using hheightAbsorb
        linarith [hroot]
      linarith [hheight.2]
  let windowedPackage :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := graphScale) (sigma := sigma)
        shadow (10 * C) :=
    { global := global
      active_height_window := hactiveWindow }
  have hlocalization :
      WZ1Lemma23GlobalLocalizationInput windowedPackage.global := by
    refine ⟨fun _ => line.lineLevel, ?_⟩
    intro heightIndex hheightIndex
    rintro value ⟨point, hpoint, rfl⟩
    have hpaper : point ∈ retained.shading.union :=
      hshadowUnion hpoint.1
    have hbound := retained.fixed_line_localizationFixedBin point hpaper
    rw [hpoint.2] at hbound
    rw [Metric.mem_closedBall, Real.dist_eq, hsqrtGraph]
    change
      |inner ℝ point
          (globalGrainDirection
            (global.sourceSlope (global.selectedHeight heightIndex))) -
        line.lineLevel| ≤ 16 * root
    rw [hsourceSlope, hglobalSlope]
    exact hbound.trans (by nlinarith [hroot])
  have hfixedLine :
      ∀ point ∈ ambientShadow.union,
        |inner ℝ point
            (globalGrainDirection
              (global.sourceSlope (point (2 : Fin 3)))) -
          line.lineLevel| ≤ 14 * root := by
    intro point hpoint
    have hpaper : point ∈ retained.shading.union := by
      rwa [hambientUnion] at hpoint
    have hbound := retained.fixed_line_localizationFixedBin point hpaper
    rw [hsourceSlope, hglobalSlope]
    exact hbound
  have hexactGraph :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (global.sourceSlope z))
            (horizontalSlice shadow.union z))
          graphScale (1 - sigma) (10 * C) := by
    intro z hz
    rw [hsourceSlope]
    exact (hexact z hz).coarsen_scale hgraph hdeltaGraph hgraphOne
  exact ⟨{
    graphScale := graphScale
    graphScale_eq := rfl
    graphScale_pos := hgraph
    graphScale_one := hgraphOne
    graphScale_sqrt := hsqrtGraph
    graphScale_two_root_bound := by
      simpa [graphScale, root] using hheightAbsorb
    sourceScale_le_graphScale := hdeltaGraph
    rho_le_graphScale := hrhoGraph
    localPaper := localPaper
    localPaper_planeMap_eq := by
      intro point
      rfl
    globalPaper := globalPaper
    globalPaper_slope_eq := hglobalSlope
    ambientShadow := ambientShadow
    ambientShadow_union := hambientUnion
    shadow := shadow
    shadow_eq := rfl
    shadow_sub_ambient := hshadowSub
    shadow_union_subset := hshadowUnion
    ambientLocalGrains := ambientLocalGrains
    localGrains := localGrains
    ambientPlaneMap_eq_on_paper := by
      intro point
      simpa only using hplaneMapEq
        ⟨point, by simpa [hambientUnion] using point.property⟩
    planeMap_eq_on_paper := by
      intro point
      exact hplaneMapEq ⟨point, hshadowUnion point.property⟩
    planeMap_vertical_bound := hvertical
    windowed := windowedPackage
    sourceSlope_eq := hsourceSlope.trans hglobalSlope
    fixed_line_localization := hfixedLine
    exactAD := hexactGraph
    localization := hlocalization
  }⟩

/-- Backwards-compatible graph preparation on the maximal global bin. -/
abbrev PureWZ2SourceHorizontalResiduePreparation
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (retained : PureWZ2SourceHorizontalResidueShadingData residue) :=
  PureWZ2SourceHorizontalFixedBinResiduePreparation retained

/-- Compatibility name for the maximal-bin active-cell inclusion. -/
lemma PureWZ2SourceHorizontalResiduePreparation.activeCells_subset_ambient
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    {retained : PureWZ2SourceHorizontalResidueShadingData residue}
    (prep : PureWZ2SourceHorizontalResiduePreparation retained) :
    wz1Lemma23ActiveCells prep.shadow prep.graphScale prep.graphScale_pos ⊆
      wz1Lemma23ActiveCells prep.ambientShadow prep.graphScale prep.graphScale_pos :=
  prep.activeCells_subset_ambientFixedBin

/-- Compatibility wrapper for the former maximal-bin preparation API. -/
theorem PureWZ2SourceHorizontalResidueShadingData.prepare
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {line : PureWZ2SourceHorizontalFixedLineData window}
    {parents : PureWZ2SourceHorizontalParentData line}
    {selection : PureWZ2SourceHorizontalYSelection parents}
    {residue : PureWZ2SourceHorizontalYResidueData selection}
    (retained : PureWZ2SourceHorizontalResidueShadingData residue)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * rho ≤ 1)
    (hheightAbsorb :
      256 * rho + 2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2SourceHorizontalResiduePreparation retained) :=
  retained.prepareFixedBin hbridge hgraphOne hheightAbsorb

end Kakeya.Assouad
