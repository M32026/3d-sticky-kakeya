import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularCarrierBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.FixedLineCore

/-!
# Lemma-23 data on the outer-popular terminal carrier

The source-volume popularity step at the terminal scale produces a genuine
paper shading on the original source family, but that shading is not a union
of complete source cells.  Consequently it must be passed to Lemma 23 through
the equal-union partial-cell shadow, rather than through the whole-cell shadow
used by the earlier terminal implementation.

This module records that paper-faithful interface.  In particular, the fixed
horizontal line selected below is selected from the outer-popular carrier
itself.  No discarded height is restored.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Local and global grain data, together with the exact-slice window, on the
equal-union partial-cell shadow of the outer-popular source carrier. -/
structure PureWZ2TerminalPopularPreparedWindowData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    (carrier : PureWZ2TerminalPopularSourceCarrierData heightData) where
  localPaper : PureWZ2LocalGrainData carrier.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  globalPaper : PureWZ2LipschitzGlobalGrainData carrier.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  globalPaper_slope_eq : globalPaper.slope = source.globalGrains.slope
  localGrains : WZ1LocalGrainData
    (pureWZ2PartialActiveCellShading
      carrier.shading source.extremal.delta_pos) sigma
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  planeMap_vertical_bound :
    ∀ point ∈ (pureWZ2PartialActiveCellShading
        carrier.shading source.extremal.delta_pos).union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  windowed : WZ1Lemma23WindowedGlobalSlicePackage
    (delta := delta) (rho := delta) (sigma := sigma)
    (pureWZ2PartialActiveCellShading
      carrier.shading source.extremal.delta_pos)
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  sourceSlope_eq : windowed.global.sourceSlope = source.globalGrains.slope
  active_cell_window :
    ∀ cell ∈ wz1Lemma23ActiveCells
        (pureWZ2PartialActiveCellShading
          carrier.shading source.extremal.delta_pos) delta
        source.extremal.delta_pos,
      (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3) ∈
        Set.Icc heightData.graphWindow.left
          (heightData.graphWindow.left + Real.sqrt delta)
  exactAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    IsADSet1
      (scalarProjection
        (globalGrainDirection (source.globalGrains.slope z))
        (horizontalSlice (pureWZ2PartialActiveCellShading
          carrier.shading source.extremal.delta_pos).union z))
      delta (1 - sigma)
      (10 * Kakeya.realRpowENN delta (-inputLoss))
  volumeSupply : ENNReal := heightData.graphWindow.volumeSupply
  volumeSupply_pos : 0 < volumeSupply
  volume_lower : volumeSupply ≤ volume
    (pureWZ2PartialActiveCellShading
      carrier.shading source.extremal.delta_pos).union
  union_height_window : ∀ point ∈
      (pureWZ2PartialActiveCellShading
        carrier.shading source.extremal.delta_pos).union,
    point (2 : Fin 3) ∈ Set.Ico
      (heightData.graphWindow.left - delta)
      (heightData.graphWindow.left + Real.sqrt delta + delta)

/-- Rebuild the exact-slice data on the outer-popular original-family carrier.
The partial-cell conversion is essential: the carrier is intentionally not
asserted to be cubical. -/
theorem PureWZ2TerminalPopularSourceCarrierData.prepareWindow
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    (carrier : PureWZ2TerminalPopularSourceCarrierData heightData)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2TerminalPopularPreparedWindowData carrier) := by
  let C := Kakeya.realRpowENN delta (-inputLoss)
  have hCtop : C ≠ ⊤ := by
    simp [C, Kakeya.realRpowENN]
  let localPaper : PureWZ2LocalGrainData carrier.shading sigma C :=
    source.localGrains.restrictWithConstant carrier.subshading le_rfl hCtop
  let globalPaper : PureWZ2BoundedLipschitzGlobalGrainData
      carrier.shading sigma C :=
    source.globalGrains.restrict carrier.subshading le_rfl hCtop
  let partialShadow := pureWZ2PartialActiveCellShading
    carrier.shading source.extremal.delta_pos
  let localGrains : WZ1LocalGrainData partialShadow sigma (10 * C) :=
    localPaper.toPartialActiveCellShadow source.extremal.delta_pos hbridge
  have hverticalPaper :
      ∀ point : {point : Point3 // point ∈ carrier.shading.union},
        |localPaper.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, carrier.subshading.union_subset point.property⟩
  have hvertical : ∀ point ∈ partialShadow.union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 :=
    localPaper.toPartialActiveCellShadow_vertical_bound
      source.extremal.delta_pos hbridge hverticalPaper
  have hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice partialShadow.union z))
        delta (1 - sigma) (10 * C) := by
    intro z hz
    have h := globalPaper.partialActiveCellShadow_exactAD
      source.extremal.delta_pos hbridge globalPaper.slope_bound z hz
    change IsADSet1
      (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
        (horizontalSlice partialShadow.union z))
      delta (1 - sigma) (10 * C) at h
    exact h
  have hball : partialShadow.union ⊆
      Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hcarrier : point ∈ carrier.shading.union := by
      rw [show partialShadow.union = carrier.shading.union by
        exact pureWZ2PartialActiveCellShading_union
          carrier.shading source.extremal.delta_pos] at hpoint
      exact hpoint
    have hsource := carrier.subshading.union_subset hcarrier
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord : ∀ point ∈ partialShadow.union,
      ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hcarrier : point ∈ carrier.shading.union := by
      rw [show partialShadow.union = carrier.shading.union by
        exact pureWZ2PartialActiveCellShading_union
          carrier.shading source.extremal.delta_pos] at hpoint
      exact hpoint
    have hsource := carrier.subshading.union_subset hcarrier
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hactive :
      ∀ cell ∈ wz1Lemma23ActiveCells partialShadow delta
          source.extremal.delta_pos,
        (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3) ∈
          Set.Icc heightData.graphWindow.left
            (heightData.graphWindow.left + Real.sqrt delta) := by
    intro cell hcell
    apply heightData.graphWindow.active_cell_window cell
    rw [wz1Lemma23_mem_active_iff] at hcell ⊢
    refine ⟨hcell.1, ?_⟩
    rcases hcell.2 with ⟨point, hpoint, hpointCell⟩
    have hcarrier : point ∈ carrier.shading.union := by
      simpa [partialShadow, pureWZ2PartialActiveCellShading_union] using hpoint
    have hgraph : point ∈ heightData.graphWindow.shading.union := by
      rw [← carrier.union_eq]
      exact hcarrier
    exact ⟨point, hgraph, hpointCell⟩
  have hunionHeight : ∀ point ∈ partialShadow.union,
      point (2 : Fin 3) ∈ Set.Ico
        (heightData.graphWindow.left - delta)
        (heightData.graphWindow.left + Real.sqrt delta + delta) := by
    intro point hpoint
    apply heightData.graphWindow.union_height_window point
    rw [← carrier.union_eq]
    rw [← show partialShadow.union = carrier.shading.union by
      exact pureWZ2PartialActiveCellShading_union
        carrier.shading source.extremal.delta_pos]
    exact hpoint
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      partialShadow source.extremal.delta_pos le_rfl
      source.extremal.delta_le_one hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound (10 * C)
      (ENNReal.mul_ne_top (by norm_num) hCtop) hexact with
    ⟨global, hslope⟩
  let windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := delta) (sigma := sigma) partialShadow
      (10 * C) :=
    { global := global
      active_height_window := ⟨heightData.graphWindow.left, hactive⟩ }
  have hvolumePos : 0 < volume partialShadow.union := by
    rw [show partialShadow.union = carrier.shading.union by
      exact pureWZ2PartialActiveCellShading_union
        carrier.shading source.extremal.delta_pos, carrier.volume_eq]
    exact heightData.graphWindow.volumeSupply_pos.trans_le
      heightData.graphWindow.volume_lower
  have hvolume : heightData.graphWindow.volumeSupply ≤
      volume partialShadow.union := by
    rw [show partialShadow.union = carrier.shading.union by
      exact pureWZ2PartialActiveCellShading_union
        carrier.shading source.extremal.delta_pos, carrier.volume_eq]
    exact heightData.graphWindow.volume_lower
  exact ⟨{
    localPaper := localPaper
    globalPaper := globalPaper
    globalPaper_slope_eq := rfl
    localGrains := localGrains
    planeMap_vertical_bound := hvertical
    windowed := windowed
    sourceSlope_eq := by simpa [windowed] using hslope
    active_cell_window := hactive
    exactAD := by simpa [C] using hexact
    volumeSupply := heightData.graphWindow.volumeSupply
    volumeSupply_pos := heightData.graphWindow.volumeSupply_pos
    volume_lower := hvolume
    union_height_window := hunionHeight }⟩

/-- Select the Fubini line and its global-bin fibre from the outer-popular
carrier itself.  Every chosen representative therefore has genuine
outer-popular provenance. -/
theorem PureWZ2TerminalPopularPreparedWindowData.selectHorizontalFixedLine
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    (data : PureWZ2TerminalPopularPreparedWindowData carrier) :
    Nonempty (PureWZ2HorizontalFixedLineCore
      data.windowed source.globalGrains.slope) := by
  have hcoord : ∀ point ∈ (pureWZ2PartialActiveCellShading
      carrier.shading source.extremal.delta_pos).union,
      ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hcarrier : point ∈ carrier.shading.union := by
      rw [pureWZ2PartialActiveCellShading_union
        carrier.shading source.extremal.delta_pos] at hpoint
      exact hpoint
    have hsource := carrier.subshading.union_subset hcarrier
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  exact pureWZ2_selectHorizontalFixedLineCore
    data.windowed source.globalGrains.slope
    source.extremal.delta_pos le_rfl source.extremal.delta_le_one
    data.sourceSlope_eq hcoord heightData.graphWindow.left
    data.union_height_window data.exactAD
    (data.volumeSupply_pos.trans_le data.volume_lower)

/-- Every exact-slice representative selected from the rebuilt window is an
actual point of the outer-popular source carrier. -/
theorem PureWZ2TerminalPopularPreparedWindowData.representative_mem_carrier
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    (data : PureWZ2TerminalPopularPreparedWindowData carrier)
    (line : PureWZ2HorizontalFixedBinCore
      data.windowed source.globalGrains.slope)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ line.heavyCells) :
    line.representative cell ∈ carrier.shading.union := by
  have hshadow := line.representative_mem cell hcell
  simpa [pureWZ2PartialActiveCellShading_union] using hshadow

/-- The selected line can use only outer-popular height labels.  This is the
precise provenance certificate needed before any per-bin parent geometry is
constructed. -/
theorem PureWZ2TerminalPopularPreparedWindowData.heavy_height_mem
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    (data : PureWZ2TerminalPopularPreparedWindowData carrier)
    (line : PureWZ2HorizontalFixedBinCore
      data.windowed source.globalGrains.slope)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ line.heavyCells) :
    cell.2.2 ∈ heightData.popular.heightIndices := by
  have hrepresentative : line.representative cell ∈ carrier.shading.union :=
    data.representative_mem_carrier line cell hcell
  have hheightRegion : line.representative cell ∈
      heightData.popular.heightRegion :=
    carrier.height_region hrepresentative
  rw [heightData.popular.heightRegion_eq] at hheightRegion
  rcases Set.mem_iUnion₂.mp hheightRegion with
    ⟨heightIndex, hheightIndex, hslab⟩
  have hfloor := (wz1Lemma23_mem_heightSlab_iff
    source.extremal.delta_pos heightIndex (line.representative cell)).mp hslab
  have hcellHeight := congrArg
    (fun index : ℤ × ℤ × ℤ => index.2.2)
    (line.representative_index cell hcell)
  have hfloorCell :
      Int.floor
          (line.representative cell (2 : Fin 3) /
            gridSide (delta / 2)) = cell.2.2 := by
    simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using hcellHeight
  have : cell.2.2 = heightIndex := hfloorCell.symm.trans hfloor
  rwa [this]

end Kakeya.Assouad

end
