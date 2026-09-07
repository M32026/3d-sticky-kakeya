import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TwoScaleCellPullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedGlobalPackage
import MyLeanRepo.Kakeya.Assouad.WZ1.HeightWindowPigeonhole

/-!
# Source-slope Lemma-23 carrier after the two-scale cell pullback

The paper carrier stays on the original `delta` family.  The selected region
comes from the second sticky `rho` cells, but both the global slope and local
plane map are restrictions of the original source grain configuration.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

structure PureWZ2SourceCarrierPreparation
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale) where
  shadow : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily pullback.shading source.extremal.delta_pos) :=
    pureWZ2ActiveCellShading pullback.shading source.extremal.delta_pos
  shadow_union : shadow.union = pullback.shading.union
  localPaper : PureWZ2LocalGrainData pullback.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  globalPaper : PureWZ2BoundedLipschitzGlobalGrainData pullback.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  globalPaper_slope_eq : globalPaper.slope = source.globalGrains.slope
  localGrains : WZ1LocalGrainData shadow sigma
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  planeMap_eq_on_paper :
    ∀ point : {point : Point3 // point ∈ pullback.shading.union},
      localGrains.planeMap point = localPaper.planeMap point
  planeMap_vertical_bound :
    ∀ point ∈ shadow.union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  exactAD_delta :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice shadow.union z))
        delta (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss))
  exactAD :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice shadow.union z))
        rho (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss))

theorem PureWZ2TwoScaleCellPullbackData.prepareSourceCarrier
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    (pullback : PureWZ2TwoScaleCellPullbackData twoScale)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2SourceCarrierPreparation pullback) := by
  let C := Kakeya.realRpowENN delta (-inputLoss)
  have hCtop : C ≠ ⊤ := by simp [C, Kakeya.realRpowENN]
  let localPaper := source.localGrains.restrictWithConstant
    pullback.subshading le_rfl hCtop
  let restrictedGlobal :=
    source.globalGrains.toPureWZ2LipschitzGlobalGrainData.restrict
      pullback.subshading le_rfl hCtop
  let globalPaper :=
    PureWZ2BoundedLipschitzGlobalGrainData.ofSlopeBound restrictedGlobal <| by
      intro z hz
      exact source.globalGrains.slope_bound z hz
  let shadow := pureWZ2ActiveCellShading
    pullback.shading source.extremal.delta_pos
  have hunion : shadow.union = pullback.shading.union :=
    pureWZ2ActiveCellShading_union pullback.shading
      source.extremal.delta_pos pullback.whole_cells
  let localGrains := localPaper.toActiveCellShadow
    source.extremal.delta_pos pullback.whole_cells hbridge
  have hplane :
      ∀ point : {point : Point3 // point ∈ pullback.shading.union},
        localGrains.planeMap point = localPaper.planeMap point := by
    intro point
    exact (Classical.choose_spec localPaper.exists_ambient_extension).2 point
  have hverticalPaper :
      ∀ point : {point : Point3 // point ∈ pullback.shading.union},
        |localPaper.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, pullback.subshading.union_subset point.property⟩
  have hvertical :
      ∀ point ∈ shadow.union,
        |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 :=
    localPaper.toActiveCellShadow_vertical_bound
      source.extremal.delta_pos pullback.whole_cells hbridge hverticalPaper
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrho : 0 < rho := source.extremal.delta_pos.trans_le hdeltaRho
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hexactDelta :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          delta (1 - sigma) (10 * C) := by
    intro z hz
    have h := globalPaper.activeCellShadow_exactAD
      source.extremal.delta_pos pullback.whole_cells hbridge
      globalPaper.slope_bound z hz
    rwa [show globalPaper.slope = source.globalGrains.slope by rfl] at h
  have hexact :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice shadow.union z))
          rho (1 - sigma) (10 * C) := by
    intro z hz
    exact (hexactDelta z hz).coarsen_scale hrho hdeltaRho hrhoOne
  exact ⟨{
    shadow := shadow
    shadow_union := hunion
    localPaper := localPaper
    globalPaper := globalPaper
    globalPaper_slope_eq := rfl
    localGrains := localGrains
    planeMap_eq_on_paper := hplane
    planeMap_vertical_bound := hvertical
    exactAD_delta := by simpa [C] using hexactDelta
    exactAD := by simpa [C] using hexact
  }⟩

structure PureWZ2SourceCarrierWindow
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) where
  left : ℝ
  shading : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily pullback.shading source.extremal.delta_pos)
  subshading : IsSubshading shading prepared.shadow
  windowed : WZ1Lemma23WindowedGlobalSlicePackage
    (delta := delta) (rho := rho) (sigma := sigma) shading
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  sourceSlope_eq : windowed.global.sourceSlope = source.globalGrains.slope
  active_cell_window :
    ∀ cell ∈ wz1Lemma23ActiveCells shading rho
        (source.extremal.delta_pos.trans_le (by
          rw [← twoScale.rhoRequested_eq]
          exact twoScale.rhoRequested.property.1)),
      (wz1Lemma23SnappedPoint rho cell) (2 : Fin 3) ∈
        Set.Icc left (left + Real.sqrt rho)
  union_height_window :
    ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈ Set.Ico
        (left - rho) (left + Real.sqrt rho + rho)
  volumeSupply : ENNReal
  volumeSupply_pos : 0 < volumeSupply
  volumeSupply_ne_top : volumeSupply ≠ ⊤
  volume_lower : volumeSupply ≤ MeasureTheory.volume shading.union

/--
Package an arbitrary positive whole-cell source block whose active cell
centers lie in one paper `sqrt rho` height window.  The exact-slice global
package and source-slope provenance are reconstructed by restriction from the
prepared carrier.
-/
theorem PureWZ2SourceCarrierPreparation.ofSubshading
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (left : ℝ)
    (shading : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily pullback.shading
        source.extremal.delta_pos))
    (hsub : IsSubshading shading prepared.shadow)
    (hactive :
      ∀ cell ∈ wz1Lemma23ActiveCells shading rho
          (source.extremal.delta_pos.trans_le (by
            rw [← twoScale.rhoRequested_eq]
            exact twoScale.rhoRequested.property.1)),
        (wz1Lemma23SnappedPoint rho cell) (2 : Fin 3) ∈
          Set.Icc left (left + Real.sqrt rho))
    (volumeSupply : ENNReal)
    (hvolumeSupply : 0 < volumeSupply)
    (hvolumeSupplyTop : volumeSupply ≠ ⊤)
    (hvolume : volumeSupply ≤ MeasureTheory.volume shading.union) :
    ∃ window : PureWZ2SourceCarrierWindow prepared,
      window.left = left ∧
        window.shading = shading ∧
          window.volumeSupply = volumeSupply := by
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrho : 0 < rho := source.extremal.delta_pos.trans_le hdeltaRho
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hunionSub : shading.union ⊆ prepared.shadow.union :=
    hsub.union_subset
  have hball : shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared := hunionSub hpoint
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hsource := pullback.subshading.union_subset hpull
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord :
      ∀ point ∈ shading.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hprepared := hunionSub hpoint
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hbox := shading_union_subset_axisBox hpull
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hCtop :
      (10 * Kakeya.realRpowENN delta (-inputLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN])
  have hexact :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection (source.globalGrains.slope z))
            (horizontalSlice shading.union z))
          delta (1 - sigma)
          (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    intro z hz
    apply (prepared.exactAD_delta z hz).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point, ⟨hunionSub hpoint.1, hpoint.2⟩, rfl⟩
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      shading hrho hdeltaRho hrhoOne hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound
      (10 * Kakeya.realRpowENN delta (-inputLoss)) hCtop hexact with
    ⟨global, hslope⟩
  let windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading
      (10 * Kakeya.realRpowENN delta (-inputLoss)) :=
    { global := global
      active_height_window := ⟨left, hactive⟩ }
  have hunionHeight :
      ∀ point ∈ shading.union,
        point (2 : Fin 3) ∈ Set.Ico
          (left - rho) (left + Real.sqrt rho + rho) := by
    intro point hpoint
    have hactiveCell := wz1Lemma23_index_mem_active_two hrho hball hpoint
    have hcenterWindow := hactive _ hactiveCell
    have hpointCenter :=
      ((wz1_lemma23_snapped_cell_geometry rho hrho hrhoOne).2.1
        (wz1Lemma23CellIndex rho point) point rfl).1 (2 : Fin 3)
    rw [abs_le] at hpointCenter
    exact ⟨by linarith [hcenterWindow.1, hpointCenter.2],
      by linarith [hcenterWindow.2, hpointCenter.1]⟩
  let result : PureWZ2SourceCarrierWindow prepared := {
    left := left
    shading := shading
    subshading := hsub
    windowed := windowed
    sourceSlope_eq := by simpa [windowed] using hslope
    active_cell_window := hactive
    union_height_window := hunionHeight
    volumeSupply := volumeSupply
    volumeSupply_pos := hvolumeSupply
    volumeSupply_ne_top := hvolumeSupplyTop
    volume_lower := hvolume
  }
  exact ⟨result, rfl, rfl, rfl⟩

/--
Construct one caller-supplied complete-cell height window.

Unlike `selectWindow`, this constructor makes no maximal-window assertion.
The caller supplies the exact local volume floor used by the graph budget; a
multi-window Lemma-24 assembly can therefore run the local pipeline on every
positive parity block without assigning the global pigeonhole bound to each
block separately.
-/
theorem PureWZ2SourceCarrierPreparation.windowAt
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback)
    (left : ℝ) (volumeSupply : ENNReal)
    (hvolumeSupply : 0 < volumeSupply)
    (hvolumeSupplyTop : volumeSupply ≠ ⊤)
    (hvolume :
      volumeSupply ≤ MeasureTheory.volume
        (prepared.shadow.union ∩
          wz1Lemma23CellHeightWindowSet rho
            (source.extremal.delta_pos.trans_le (by
              rw [← twoScale.rhoRequested_eq]
              exact twoScale.rhoRequested.property.1)) left)) :
    Nonempty (PureWZ2SourceCarrierWindow prepared) := by
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrho : 0 < rho := source.extremal.delta_pos.trans_le hdeltaRho
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hball : prepared.shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hpoint
    have hsource := pullback.subshading.union_subset hpull
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord :
      ∀ point ∈ prepared.shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hpoint
    have hbox := shading_union_subset_axisBox hpull
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hCtop :
      (10 * Kakeya.realRpowENN delta (-inputLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN])
  rcases wz1_lemma23_windowed_global_slice_package_of_exact_paper_window
      prepared.shadow hrho hdeltaRho hrhoOne hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound
      (10 * Kakeya.realRpowENN delta (-inputLoss)) hCtop
      (by
        intro z hz
        exact prepared.exactAD_delta z hz) left with
    ⟨shading, windowed, hshading, hsub, hslope⟩
  have hunion : shading.union = prepared.shadow.union ∩
      wz1Lemma23CellHeightWindowSet rho hrho left := by
    rw [hshading]
    ext point
    constructor
    · rintro ⟨index, hpoint⟩
      exact ⟨⟨index, hpoint.1⟩, hpoint.2⟩
    · rintro ⟨⟨index, hpoint⟩, hwindow⟩
      exact ⟨index, hpoint, hwindow⟩
  exact ⟨{
    left := left
    shading := shading
    subshading := hsub
    windowed := windowed
    sourceSlope_eq := hslope
    active_cell_window := by
      intro cell hcell
      rw [wz1Lemma23_mem_active_iff] at hcell
      rcases hcell.2 with ⟨point, hpointShading, hpointCell⟩
      have hpointWindow : point ∈
          wz1Lemma23CellHeightWindowSet rho hrho left := by
        rw [hunion] at hpointShading
        exact hpointShading.2
      rcases Set.mem_iUnion₂.mp hpointWindow with
        ⟨selectedCell, hselectedCell, hpointSelected⟩
      have heq : selectedCell = cell := hpointSelected.symm.trans hpointCell
      rw [heq] at hselectedCell
      exact (Finset.mem_filter.mp hselectedCell).2
    union_height_window := by
      intro point hpoint
      have hwindow :
          point ∈ wz1Lemma23CellHeightWindowSet rho hrho left := by
        rw [hunion] at hpoint
        exact hpoint.2
      rcases Set.mem_iUnion₂.mp hwindow with
        ⟨cell, hcell, hpointCell⟩
      have hcenterWindow := (Finset.mem_filter.mp hcell).2
      have hcellIndex : wz1Lemma23CellIndex rho point = cell := by
        simpa [wz1Lemma23Cell, wz1Lemma23CellIndex, rhoGridIndex, gridSide]
          using hpointCell
      have hpointCenter :=
        ((wz1_lemma23_snapped_cell_geometry rho hrho hrhoOne).2.1
          cell point hcellIndex).1 (2 : Fin 3)
      rw [abs_le] at hpointCenter
      exact ⟨by linarith [hcenterWindow.1, hpointCenter.2],
        by linarith [hcenterWindow.2, hpointCenter.1]⟩
    volumeSupply := volumeSupply
    volumeSupply_pos := hvolumeSupply
    volumeSupply_ne_top := hvolumeSupplyTop
    volume_lower := by rw [hunion]; exact hvolume
  }⟩

theorem PureWZ2SourceCarrierPreparation.selectWindow
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    (prepared : PureWZ2SourceCarrierPreparation pullback) :
    Nonempty (PureWZ2SourceCarrierWindow prepared) := by
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrho : 0 < rho := source.extremal.delta_pos.trans_le hdeltaRho
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hball : prepared.shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hpoint
    have hsource := pullback.subshading.union_subset hpull
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord :
      ∀ point ∈ prepared.shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hpoint
    have hbox := shading_union_subset_axisBox hpull
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hheight : ∀ point ∈ prepared.shadow.union,
      |point (2 : Fin 3)| ≤ 1 := fun point hpoint => hcoord point hpoint 2
  rcases height_window_pigeonhole_tight_of_paper_window
      prepared.shadow hrho hrhoOne hball hheight with ⟨left, hvolume⟩
  have hCtop :
      (10 * Kakeya.realRpowENN delta (-inputLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN])
  rcases wz1_lemma23_windowed_global_slice_package_of_exact_paper_window
      prepared.shadow hrho hdeltaRho hrhoOne hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound
      (10 * Kakeya.realRpowENN delta (-inputLoss)) hCtop
      (by
        intro z hz
        exact prepared.exactAD_delta z hz) left with
    ⟨shading, windowed, hshading, hsub, hslope⟩
  have hunion : shading.union = prepared.shadow.union ∩
      wz1Lemma23CellHeightWindowSet rho hrho left := by
    rw [hshading]
    ext point
    constructor
    · rintro ⟨index, hpoint⟩
      exact ⟨⟨index, hpoint.1⟩, hpoint.2⟩
    · rintro ⟨⟨index, hpoint⟩, hwindow⟩
      exact ⟨index, hpoint, hwindow⟩
  have hpullbackVolume :
      0 < MeasureTheory.volume pullback.shading.union := by
    rw [pullback.volume_eq]
    have hselectedNonempty : pullback.selectedCells.Nonempty := by
      by_contra hempty
      have hcells : pullback.selectedCells = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hempty
      have hselectedCount := pullback.selected_count_mul_coarse_volume
      rw [hcells] at hselectedCount
      simp only [Finset.card_empty, Nat.cast_zero, zero_mul] at hselectedCount
      have hfinePositive :
          0 < MeasureTheory.volume twoScale.fine.refined.union :=
        (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos
            twoScale.coarseGrains.extremal.delta_pos _)).trans_le
          twoScale.fine.refined_volume_lower
      rw [← hselectedCount] at hfinePositive
      exact (lt_irrefl 0) hfinePositive
    have hcardPositive :
        0 < (pullback.selectedCells.card : ENNReal) := by
      exact_mod_cast hselectedNonempty.card_pos
    exact ENNReal.mul_pos hcardPositive.ne'
      twoScale.coarse.balanced.cellMass_pos.ne'
  have hpreparedVolume :
      0 < MeasureTheory.volume prepared.shadow.union := by
    rwa [prepared.shadow_union]
  exact ⟨{
    left := left
    shading := shading
    subshading := hsub
    windowed := windowed
    sourceSlope_eq := hslope
    active_cell_window := by
      intro cell hcell
      rw [wz1Lemma23_mem_active_iff] at hcell
      rcases hcell.2 with ⟨point, hpointShading, hpointCell⟩
      have hpointWindow : point ∈
          wz1Lemma23CellHeightWindowSet rho hrho left := by
        rw [hunion] at hpointShading
        exact hpointShading.2
      rcases Set.mem_iUnion₂.mp hpointWindow with
        ⟨selectedCell, hselectedCell, hpointSelected⟩
      have heq : selectedCell = cell := hpointSelected.symm.trans hpointCell
      rw [heq] at hselectedCell
      exact (Finset.mem_filter.mp hselectedCell).2
    union_height_window := by
      intro point hpoint
      have hwindow :
          point ∈ wz1Lemma23CellHeightWindowSet rho hrho left := by
        rw [hunion] at hpoint
        exact hpoint.2
      rcases Set.mem_iUnion₂.mp hwindow with
        ⟨cell, hcell, hpointCell⟩
      have hcenterWindow := (Finset.mem_filter.mp hcell).2
      have hcellIndex : wz1Lemma23CellIndex rho point = cell := by
        simpa [wz1Lemma23Cell, wz1Lemma23CellIndex, rhoGridIndex, gridSide]
          using hpointCell
      have hpointCenter :=
        ((wz1_lemma23_snapped_cell_geometry rho hrho hrhoOne).2.1
          cell point hcellIndex).1 (2 : Fin 3)
      rw [abs_le] at hpointCenter
      exact ⟨by linarith [hcenterWindow.1, hpointCenter.2],
        by linarith [hcenterWindow.2, hpointCenter.1]⟩
    volumeSupply :=
      MeasureTheory.volume prepared.shadow.union *
          ENNReal.ofReal (Real.sqrt rho) /
        ENNReal.ofReal (2 + rho + Real.sqrt rho)
    volumeSupply_pos := by
      exact ENNReal.div_pos
        (ENNReal.mul_pos hpreparedVolume.ne'
          (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hrho)).ne').ne'
        ENNReal.ofReal_ne_top
    volumeSupply_ne_top := by
      apply ENNReal.div_ne_top
      · apply ENNReal.mul_ne_top
        · exact ne_top_of_le_ne_top
            Metric.isBounded_closedBall.measure_lt_top.ne
            (MeasureTheory.measure_mono hball)
        · exact ENNReal.ofReal_ne_top
      · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    volume_lower := by rw [hunion]; exact hvolume
  }⟩

end Kakeya.Assouad
