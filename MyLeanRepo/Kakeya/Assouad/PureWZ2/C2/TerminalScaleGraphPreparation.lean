import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleRetainedShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GeometricInput

/-!
# Graph-scale preparation on the terminal source carrier

The final paper shading remains on the original side-`delta` tube family.  We
only coarsen the auxiliary Lemma-23 graph grid to side `256 * delta`.  The
global slope, local plane map, fixed line, and exact AD certificates all come
from the same retained source configuration.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The complete terminal residue lies near the one fixed source-slope line. -/
theorem PureWZ2TerminalBinRetainedShadingData.fixed_line_localization
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    (retained : PureWZ2TerminalBinRetainedShadingData residue) :
    ∀ point ∈ retained.shading.union,
      |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) -
        line.lineLevel| ≤ 14 * terminal.sqrtRequested.1 := by
  let root := terminal.sqrtRequested.1
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hdeltaOne : delta ≤ 1 := source.extremal.delta_le_one
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hdeltaRoot : delta ≤ root := by
    rw [show root = Real.sqrt delta by exact terminal.sqrtRequested_eq]
    nlinarith [Real.sqrt_nonneg delta, Real.sq_sqrt hdelta.le, hdeltaOne]
  intro point hpoint
  have hregion : point ∈ retained.selectedRegion := by
    rw [retained.union_eq] at hpoint
    exact hpoint.2
  rw [retained.selectedRegion_eq] at hregion
  rcases Set.mem_iUnion₂.mp hregion with
    ⟨parent, hparent, hpointParent⟩
  rcases selection.selected_hit parent (residue.selected_subset hparent) with
    ⟨cell, hcell, hcellParent⟩
  let representative := line.representative cell
  have hrepresentativeParent : representative ∈ wz1PaperGridCube root parent := by
    have hmem := parents.representative_mem_parent cell hcell
    rwa [hcellParent] at hmem
  rw [wz1PaperGridCube_eq_Ico hroot parent] at hpointParent
  rw [wz1PaperGridCube_eq_Ico hroot parent] at hrepresentativeParent
  rcases hpointParent with
    ⟨hpoint0Lower, hpoint0Upper, hpoint1Lower, hpoint1Upper,
      hpoint2Lower, hpoint2Upper⟩
  rcases hrepresentativeParent with
    ⟨hrep0Lower, hrep0Upper, hrep1Lower, hrep1Upper,
      hrep2Lower, hrep2Upper⟩
  have hcoord0 : |point 0 - representative 0| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hcoord1 : |point 1 - representative 1| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hcoord2 : |point 2 - representative 2| ≤ root := by
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hpointSource : point ∈ source.shading.union :=
    retained.subshading.union_subset hpoint
  have hpointBox := shading_union_subset_axisBox hpointSource
  have hpoint1 : |point 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpointBox.2.1
  have hpointHeight : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [Kakeya.Streamlined.axisBox, abs_le] using hpointBox.2.2
  have hrepresentativeHeight :
      representative (2 : Fin 3) = line.lineHeight :=
    line.representative_height cell hcell
  have hslopeDifference :
      |source.globalGrains.slope (point (2 : Fin 3)) -
          source.globalGrains.slope line.lineHeight| ≤ root := by
    have hlip := source.globalGrains.slope_lipschitz.dist_le_mul
      (point (2 : Fin 3)) hpointHeight line.lineHeight line.lineHeight_mem
    simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hlip
    exact hlip.trans (by
      rw [← hrepresentativeHeight]
      exact hcoord2)
  have hslopeLine : |source.globalGrains.slope line.lineHeight| ≤ 3 :=
    source.globalGrains.slope_bound line.lineHeight line.lineHeight_mem
  have hprojectionDifference :
      |inner ℝ point
            (globalGrainDirection
              (source.globalGrains.slope (point (2 : Fin 3)))) -
          inner ℝ representative
            (globalGrainDirection
              (source.globalGrains.slope line.lineHeight))| ≤ 5 * root := by
    have hformula :
        inner ℝ point
              (globalGrainDirection
                (source.globalGrains.slope (point (2 : Fin 3)))) -
            inner ℝ representative
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight)) =
          (point 0 - representative 0) +
            source.globalGrains.slope line.lineHeight *
              (point 1 - representative 1) +
            (source.globalGrains.slope (point (2 : Fin 3)) -
              source.globalGrains.slope line.lineHeight) * point 1 := by
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      ring
    rw [hformula]
    calc
      |(point 0 - representative 0) +
          source.globalGrains.slope line.lineHeight *
            (point 1 - representative 1) +
          (source.globalGrains.slope (point (2 : Fin 3)) -
            source.globalGrains.slope line.lineHeight) * point 1|
          ≤ |point 0 - representative 0| +
              |source.globalGrains.slope line.lineHeight| *
                |point 1 - representative 1| +
              |source.globalGrains.slope (point (2 : Fin 3)) -
                source.globalGrains.slope line.lineHeight| * |point 1| := by
            calc
              _ ≤ |(point 0 - representative 0) +
                    source.globalGrains.slope line.lineHeight *
                      (point 1 - representative 1)| +
                    |(source.globalGrains.slope (point (2 : Fin 3)) -
                      source.globalGrains.slope line.lineHeight) * point 1| :=
                abs_add_le _ _
              _ ≤ (|point 0 - representative 0| +
                    |source.globalGrains.slope line.lineHeight *
                      (point 1 - representative 1)|) +
                    |(source.globalGrains.slope (point (2 : Fin 3)) -
                      source.globalGrains.slope line.lineHeight) * point 1| := by
                gcongr
                exact abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ root + 3 * root + root * 1 := by gcongr
      _ = 5 * root := by ring
  have hrepresentativeNear := line.heavy_representative_near_line cell hcell
  calc
    |inner ℝ point
          (globalGrainDirection
            (source.globalGrains.slope (point (2 : Fin 3)))) -
        line.lineLevel|
        ≤ |inner ℝ point
              (globalGrainDirection
                (source.globalGrains.slope (point (2 : Fin 3)))) -
            inner ℝ representative
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight))| +
          |inner ℝ representative
              (globalGrainDirection
                (source.globalGrains.slope line.lineHeight)) -
            line.lineLevel| := by
          have := abs_add_le
            (inner ℝ point
                (globalGrainDirection
                  (source.globalGrains.slope (point (2 : Fin 3)))) -
              inner ℝ representative
                (globalGrainDirection
                  (source.globalGrains.slope line.lineHeight)))
            (inner ℝ representative
                (globalGrainDirection
                  (source.globalGrains.slope line.lineHeight)) - line.lineLevel)
          simpa only [sub_add_sub_cancel] using this
    _ ≤ 5 * root + 9 * delta := by gcongr
    _ ≤ 14 * root := by linarith

structure PureWZ2TerminalGraphPreparation
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    (retained : PureWZ2TerminalRetainedShadingData residue) where
  graphScale : ℝ := 256 * delta
  graphScale_eq : graphScale = 256 * delta
  graphScale_pos : 0 < graphScale
  graphScale_one : graphScale ≤ 1
  graphScale_sqrt : Real.sqrt graphScale = 16 * terminal.sqrtRequested.1
  graphScale_two_root_bound :
    graphScale + 2 * terminal.sqrtRequested.1 ≤
      16 * terminal.sqrtRequested.1
  sourceScale_le_graphScale : delta ≤ graphScale
  localPaper : PureWZ2LocalGrainData retained.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  localPaper_planeMap_eq :
    ∀ point : {point : Point3 // point ∈ retained.shading.union},
      localPaper.planeMap point = source.localGrains.planeMap
        ⟨point, retained.subshading.union_subset point.property⟩
  globalPaper : PureWZ2LipschitzGlobalGrainData retained.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  globalPaper_slope_eq : globalPaper.slope = source.globalGrains.slope
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily retained.shading source.extremal.delta_pos) :=
    pureWZ2ActiveCellShading retained.shading source.extremal.delta_pos
  shadow_union : shadow.union = retained.shading.union
  localGrains : WZ1LocalGrainData shadow sigma
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  planeMap_eq_on_paper :
    ∀ point : {point : Point3 // point ∈ retained.shading.union},
      localGrains.planeMap point = localPaper.planeMap point
  planeMap_vertical_bound :
    ∀ point ∈ shadow.union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  windowed : WZ1Lemma23WindowedGlobalSlicePackage
    (delta := delta) (rho := graphScale) (sigma := sigma) shadow
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  sourceSlope_eq : windowed.global.sourceSlope = source.globalGrains.slope
  fixed_line_localization :
    ∀ point ∈ shadow.union,
      |inner ℝ point
          (globalGrainDirection
            (windowed.global.sourceSlope (point (2 : Fin 3)))) -
        line.lineLevel| ≤ 14 * terminal.sqrtRequested.1
  exactAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    IsADSet1
      (scalarProjection
        (globalGrainDirection (windowed.global.sourceSlope z))
        (horizontalSlice shadow.union z))
      graphScale (1 - sigma)
      (10 * Kakeya.realRpowENN delta (-inputLoss))
  localization : WZ1Lemma23GlobalLocalizationInput windowed.global

theorem PureWZ2TerminalRetainedShadingData.prepareGraph
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    (retained : PureWZ2TerminalRetainedShadingData residue)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hgraphOne : 256 * delta ≤ 1)
    (hheightAbsorb :
      256 * delta + 2 * terminal.sqrtRequested.1 ≤
        16 * terminal.sqrtRequested.1) :
    Nonempty (PureWZ2TerminalGraphPreparation retained) := by
  let root := terminal.sqrtRequested.1
  let graphScale := 256 * delta
  let C := Kakeya.realRpowENN delta (-inputLoss)
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hroot : 0 < root := terminal.sticky.coarse_extremal.delta_pos
  have hgraph : 0 < graphScale := by positivity
  have hdeltaGraph : delta ≤ graphScale := by
    dsimp only [graphScale]
    nlinarith [hdelta]
  have hsqrtGraph : Real.sqrt graphScale = 16 * root := by
    rw [show graphScale = 256 * delta by rfl, Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt (256 : ℝ) = 16 by norm_num,
      ← terminal.sqrtRequested_eq]
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
  let shadow := pureWZ2ActiveCellShading retained.shading hdelta
  have hunion : shadow.union = retained.shading.union :=
    pureWZ2ActiveCellShading_union retained.shading hdelta retained.whole_cells
  let localGrains :=
    localPaper.toActiveCellShadow hdelta retained.whole_cells hbridge
  have hplaneMapEq :
      ∀ point : {point : Point3 // point ∈ retained.shading.union},
        localGrains.planeMap point = localPaper.planeMap point := by
    intro point
    exact (Classical.choose_spec localPaper.exists_ambient_extension).2 point
  have hverticalPaper :
      ∀ point : {point : Point3 // point ∈ retained.shading.union},
        |localPaper.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, retained.subshading.union_subset point.property⟩
  have hvertical :
      ∀ point ∈ shadow.union,
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 :=
    localPaper.toActiveCellShadow_vertical_bound
      hdelta retained.whole_cells hbridge hverticalPaper
  have hball : shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hpaper : point ∈ retained.shading.union := by rwa [hunion] at hpoint
    have hnorm := norm_le_two_of_mem_paperShading hpaper
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord : ∀ point ∈ shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpaper : point ∈ retained.shading.union := by rwa [hunion] at hpoint
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (globalPaper.slope z))
          (horizontalSlice shadow.union z))
        delta (1 - sigma) (10 * C) :=
    globalPaper.activeCellShadow_exactAD
      hdelta retained.whole_cells hbridge globalPaper.slope_bound
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      shadow hgraph hdeltaGraph hgraphOne hball hcoord
      globalPaper.slope globalPaper.slope_lipschitz
      globalPaper.slope_bound (10 * C)
      (ENNReal.mul_ne_top (by norm_num) hCtop) hexact with
    ⟨global, hsourceSlope⟩
  let left := (retained.commonParentHeight : ℝ) * root - graphScale / 2
  have hactiveWindow :
      WZ1Lemma23ActiveCellHeightWindow shadow global.rho_pos := by
    refine ⟨left, ?_⟩
    intro idx hidx
    have hactive := (wz1Lemma23_mem_active_iff shadow hgraph idx).mp hidx
    rcases hactive.2 with ⟨point, hpointShadow, hpointIndex⟩
    have hpointPaper : point ∈ retained.shading.union := by rwa [← hunion]
    have hheight := retained.union_height point hpointPaper
    have hcenter :=
      ((wz1_lemma23_snapped_cell_geometry graphScale hgraph hgraphOne).2.1
        idx point hpointIndex).1 (2 : Fin 3)
    rw [show (wz1Lemma23SnappedPoint graphScale idx) (2 : Fin 3) =
      (wz1Lemma23CellCenter graphScale idx) (2 : Fin 3) by rfl, abs_le]
      at hcenter
    constructor
    · dsimp only [left]
      linarith [hheight.1, hcenter.2]
    · dsimp only [left]
      rw [hsqrtGraph]
      have habsorb : graphScale + root ≤ 16 * root := by
        have hstrong : graphScale + 2 * root ≤ 16 * root := by
          simpa [graphScale, root] using hheightAbsorb
        linarith [hroot]
      linarith [hheight.2, hcenter.1]
  let windowedPackage : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := graphScale) (sigma := sigma)
      shadow (10 * C) :=
    { global := global
      active_height_window := hactiveWindow }
  have hlocalization : WZ1Lemma23GlobalLocalizationInput windowedPackage.global := by
    refine ⟨fun _ => line.lineLevel, ?_⟩
    intro heightIndex hheightIndex
    rintro value ⟨point, hpoint, rfl⟩
    have hpaper : point ∈ retained.shading.union := by
      rw [← hunion]
      exact hpoint.1
    have hbound := retained.fixed_line_localization point hpaper
    rw [hpoint.2] at hbound
    rw [Metric.mem_closedBall, Real.dist_eq, hsqrtGraph]
    change |inner ℝ point
        (globalGrainDirection
          (global.sourceSlope (global.selectedHeight heightIndex))) -
      line.lineLevel| ≤ 16 * root
    rw [hsourceSlope, hglobalSlope]
    exact hbound.trans (by nlinarith [hroot])
  have hfixedLine : ∀ point ∈ shadow.union,
      |inner ℝ point
          (globalGrainDirection
            (global.sourceSlope (point (2 : Fin 3)))) - line.lineLevel| ≤
        14 * root := by
    intro point hpoint
    have hpaper : point ∈ retained.shading.union := by rwa [hunion] at hpoint
    have hbound := retained.fixed_line_localization point hpaper
    rw [hsourceSlope, hglobalSlope]
    exact hbound
  have hexactGraph : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (global.sourceSlope z))
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
    localPaper := localPaper
    localPaper_planeMap_eq := by intro point; rfl
    globalPaper := globalPaper
    globalPaper_slope_eq := hglobalSlope
    shadow := shadow
    shadow_union := hunion
    localGrains := localGrains
    planeMap_eq_on_paper := hplaneMapEq
    planeMap_vertical_bound := hvertical
    windowed := windowedPackage
    sourceSlope_eq := hsourceSlope.trans hglobalSlope
    fixed_line_localization := hfixedLine
    exactAD := hexactGraph
    localization := hlocalization
  }⟩

end Kakeya.Assouad
