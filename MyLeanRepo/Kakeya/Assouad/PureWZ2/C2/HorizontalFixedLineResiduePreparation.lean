import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLineResidueSources
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.FixedLineLocalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GeometricInput

/-!
# Same-carrier Lemma-23 preparation on the fixed-line residue shading
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

structure PureWZ2HorizontalFixedLineResiduePreparation
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    (residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue) where
  graphScale : ℝ := 256 * twoScale.rhoRequested.1
  graphScale_eq : graphScale = 256 * twoScale.rhoRequested.1
  graphScale_pos : 0 < graphScale
  graphScale_one : graphScale ≤ 1
  graphScale_sqrt :
    Real.sqrt graphScale = 16 * twoScale.sqrtRequested.1
  graphScale_two_root_bound :
    graphScale + 2 * twoScale.sqrtRequested.1 ≤
      16 * twoScale.sqrtRequested.1
  base_le_graphScale : twoScale.rhoRequested.1 ≤ graphScale
  localPaper :
    PureWZ2LocalGrainData residueShading.shading sigma
      (Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss))
  globalPaper :
    PureWZ2LipschitzGlobalGrainData residueShading.shading sigma
      (Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss))
  globalPaper_slope_eq :
    globalPaper.slope = twoScale.coarseGrains.globalGrains.slope
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily residueShading.shading
      twoScale.coarseGrains.extremal.delta_pos) :=
    pureWZ2ActiveCellShading residueShading.shading
      twoScale.coarseGrains.extremal.delta_pos
  shadow_union : shadow.union = residueShading.shading.union
  localGrains :
    WZ1LocalGrainData shadow sigma
      (10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss))
  planeMap_eq_on_paper :
    ∀ point : {point : Point3 // point ∈ residueShading.shading.union},
      localGrains.planeMap point = localPaper.planeMap point
  planeMap_vertical_bound :
    ∀ point ∈ shadow.union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  windowed :
    WZ1Lemma23WindowedGlobalSlicePackage
      (delta := twoScale.rhoRequested.1)
      (rho := graphScale) (sigma := sigma) shadow
      (10 * Kakeya.realRpowENN
        twoScale.rhoRequested.1 (-middleLoss))
  sourceSlope_eq :
    windowed.global.sourceSlope =
      twoScale.coarseGrains.globalGrains.slope
  fixed_line_localization :
    ∀ point ∈ shadow.union,
      |inner ℝ point
          (globalGrainDirection
            (windowed.global.sourceSlope (point (2 : Fin 3)))) -
        line.lineLevel| ≤
      14 * twoScale.sqrtRequested.1
  exactAD :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection
          (globalGrainDirection (windowed.global.sourceSlope z))
          (horizontalSlice shadow.union z))
        graphScale (1 - sigma)
        (10 * Kakeya.realRpowENN
          twoScale.rhoRequested.1 (-middleLoss))
  localization : WZ1Lemma23GlobalLocalizationInput windowed.global

theorem PureWZ2HorizontalFixedLineResidueShadingData.prepare
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    {windowed : PureWZ2Lemma23WindowedCoarse prepared}
    {line : PureWZ2HorizontalFixedLineData windowed}
    {parents : PureWZ2HorizontalFixedLineParentData line}
    {selection : PureWZ2HorizontalFixedLineYSelection parents}
    {residue : PureWZ2HorizontalFixedLineYResidueData selection}
    (residueShading :
      PureWZ2HorizontalFixedLineResidueShadingData residue)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * twoScale.rhoRequested.1 ≤ 1)
    (hheightAbsorb :
      256 * twoScale.rhoRequested.1 +
          2 * twoScale.sqrtRequested.1 ≤
        16 * twoScale.sqrtRequested.1) :
    Nonempty (PureWZ2HorizontalFixedLineResiduePreparation residueShading) := by
  let base := twoScale.rhoRequested.1
  let root := twoScale.sqrtRequested.1
  let graphScale := 256 * base
  let C := Kakeya.realRpowENN base (-middleLoss)
  have hbase : 0 < base := twoScale.coarseGrains.extremal.delta_pos
  have hbaseOne : base ≤ 1 := twoScale.rhoRequested.property.2
  have hroot : 0 < root := twoScale.fine.coarse_extremal.delta_pos
  have hgraph : 0 < graphScale := by positivity
  have hbaseGraph : base ≤ graphScale := by
    dsimp only [graphScale]
    nlinarith [hbase]
  have hsqrtBase : root = Real.sqrt base := by
    calc
      root = Real.sqrt rho := twoScale.sqrtRequested_eq
      _ = Real.sqrt base := by
        congr 1
        exact twoScale.rhoRequested_eq.symm
  have hsqrtGraph : Real.sqrt graphScale = 16 * root := by
    rw [show graphScale = 256 * base by rfl, Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt (256 : ℝ) = 16 by norm_num, ← hsqrtBase]
  have hCtop : C ≠ ⊤ := by
    simp [C, Kakeya.realRpowENN]
  let localPaper :
      PureWZ2LocalGrainData residueShading.shading sigma C :=
    twoScale.coarseGrains.localGrains.restrictWithConstant
      residueShading.subshading le_rfl hCtop
  let restrictedGlobal :
      PureWZ2LipschitzGlobalGrainData residueShading.shading sigma C :=
    twoScale.coarseGrains.globalGrains.restrict
      residueShading.subshading le_rfl hCtop
  let globalPaper : PureWZ2BoundedLipschitzGlobalGrainData
      residueShading.shading sigma C :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound restrictedGlobal <| by
      intro z hz
      change |twoScale.coarseGrains.globalGrains.slope z| ≤ 3
      exact twoScale.coarseGrains_slope_bound z hz
  have hglobalSlope :
      globalPaper.slope = twoScale.coarseGrains.globalGrains.slope := rfl
  let shadow := pureWZ2ActiveCellShading residueShading.shading hbase
  have hunion : shadow.union = residueShading.shading.union :=
    pureWZ2ActiveCellShading_union
      residueShading.shading hbase residueShading.whole_cells
  let localGrains :=
    localPaper.toActiveCellShadow hbase residueShading.whole_cells hbridge
  have hplaneMapEq :
      ∀ point : {point : Point3 // point ∈ residueShading.shading.union},
        localGrains.planeMap point = localPaper.planeMap point := by
    intro point
    exact
      (Classical.choose_spec localPaper.exists_ambient_extension).2 point
  have hverticalPaper :
      ∀ point : {point : Point3 // point ∈ residueShading.shading.union},
        |localPaper.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact twoScale.coarseGrains.planeMap_vertical_bound
      ⟨point, residueShading.subshading.union_subset point.property⟩
  have hvertical :
      ∀ point ∈ shadow.union,
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 :=
    localPaper.toActiveCellShadow_vertical_bound
      hbase residueShading.whole_cells hbridge hverticalPaper
  have hball : shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hpaper : point ∈ residueShading.shading.union := by
      rwa [hunion] at hpoint
    have hnorm := norm_le_two_of_mem_paperShading hpaper
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord :
      ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpaper : point ∈ residueShading.shading.union := by
      rwa [hunion] at hpoint
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
          base (1 - sigma) (10 * C) :=
    globalPaper.activeCellShadow_exactAD
      hbase residueShading.whole_cells hbridge globalPaper.slope_bound
  rcases
      wz1_lemma23_global_slice_package_of_exact_paper_window
        shadow hgraph hbaseGraph hgraphOne hball hcoord
        globalPaper.slope globalPaper.slope_lipschitz
        globalPaper.slope_bound (10 * C)
        (ENNReal.mul_ne_top (by norm_num) hCtop) hexact with
    ⟨global, hsourceSlope⟩
  let left :=
    (residueShading.commonParentHeight : ℝ) * root - graphScale / 2
  have hactiveWindow :
      WZ1Lemma23ActiveCellHeightWindow shadow global.rho_pos := by
    refine ⟨left, ?_⟩
    intro idx hidx
    have hactive := (wz1Lemma23_mem_active_iff shadow hgraph idx).mp hidx
    rcases hactive.2 with ⟨point, hpointShadow, hpointIndex⟩
    have hpointPaper : point ∈ residueShading.shading.union := by
      rwa [← hunion]
    have hheight := residueShading.union_height point hpointPaper
    have hcenter :=
      ((wz1_lemma23_snapped_cell_geometry
          graphScale hgraph hgraphOne).2.1 idx point hpointIndex).1
        (2 : Fin 3)
    have hcenterEq :
        (wz1Lemma23SnappedPoint graphScale idx) (2 : Fin 3) =
          (wz1Lemma23CellCenter graphScale idx) (2 : Fin 3) := rfl
    rw [hcenterEq]
    rw [abs_le] at hcenter
    have hcenterLower :
        (wz1Lemma23CellCenter graphScale idx) (2 : Fin 3) ≥
          point (2 : Fin 3) - graphScale / 2 := by
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
          simpa [graphScale, base, root] using hheightAbsorb
        linarith [hroot]
      linarith [hheight.2]
  let windowedPackage :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := base) (rho := graphScale) (sigma := sigma)
        shadow (10 * C) :=
    { global := global
      active_height_window := hactiveWindow }
  rcases parents.retainShading with ⟨fullRetained⟩
  have hresidueSubFull :
      residueShading.shading.union ⊆ fullRetained.shading.union := by
    intro point hpoint
    rw [residueShading.union_eq] at hpoint
    rw [fullRetained.union_eq]
    refine ⟨hpoint.1, ?_⟩
    rw [residueShading.selectedRegion_eq] at hpoint
    rw [fullRetained.selectedRegion_eq]
    rcases Set.mem_iUnion₂.mp hpoint.2 with ⟨parent, hparent, hpointParent⟩
    exact Set.mem_iUnion₂.mpr
      ⟨parent,
        selection.selected_subset (residue.selected_subset hparent),
        hpointParent⟩
  have hlocalization :
      WZ1Lemma23GlobalLocalizationInput windowedPackage.global := by
    refine ⟨fun _ => line.lineLevel, ?_⟩
    intro heightIndex hheightIndex
    rintro value ⟨point, hpoint, rfl⟩
    have hshadowPoint : point ∈ shadow.union := hpoint.1
    have hresiduePoint : point ∈ residueShading.shading.union := by
      rwa [hunion] at hshadowPoint
    have hfullPoint : point ∈ fullRetained.shading.union :=
      hresidueSubFull hresiduePoint
    have hbound := fullRetained.fixed_line_localization point hfullPoint
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
      ∀ point ∈ shadow.union,
        |inner ℝ point
            (globalGrainDirection
              (global.sourceSlope (point (2 : Fin 3)))) -
          line.lineLevel| ≤ 14 * root := by
    intro point hpoint
    have hresiduePoint : point ∈ residueShading.shading.union := by
      rwa [hunion] at hpoint
    have hfullPoint : point ∈ fullRetained.shading.union :=
      hresidueSubFull hresiduePoint
    have hbound := fullRetained.fixed_line_localization point hfullPoint
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
    exact (hexact z hz).coarsen_scale hgraph hbaseGraph hgraphOne
  exact
    ⟨{ graphScale := graphScale
       graphScale_eq := rfl
       graphScale_pos := hgraph
       graphScale_one := hgraphOne
       graphScale_sqrt := hsqrtGraph
       graphScale_two_root_bound := by
         simpa [graphScale, base, root] using hheightAbsorb
       base_le_graphScale := hbaseGraph
       localPaper := localPaper
       globalPaper := globalPaper
       globalPaper_slope_eq := hglobalSlope
       shadow := shadow
       shadow_union := hunion
       localGrains := localGrains
       planeMap_eq_on_paper := hplaneMapEq
       planeMap_vertical_bound := hvertical
       fixed_line_localization := hfixedLine
       windowed := windowedPackage
       sourceSlope_eq := hsourceSlope.trans hglobalSlope
       exactAD := hexactGraph
       localization := hlocalization }⟩

end Kakeya.Assouad
