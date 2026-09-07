import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScalePreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.FixedLineCore
import MyLeanRepo.Kakeya.Assouad.WZ1.HeightWindowPigeonhole

/-!
# Complete-cell terminal height window

Select one `sqrt delta` height window on the equal-union active-cell shadow.
The exact retained-volume lower bound and the root source slope stay attached
to the same windowed shading.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The graph-facing data of a terminal height window.  Unlike
`PureWZ2TerminalCertifiedWindow`, this interface does not require a lower
bound against the canonical global window average, so it remains valid after
the paper's height-popularity restriction. -/
structure PureWZ2TerminalGraphWindow
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) where
  left : ℝ
  shading : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily terminalSource.shading
      terminalSource.delta_pos)
  subshading : IsSubshading shading prepared.shadow
  windowed : WZ1Lemma23WindowedGlobalSlicePackage
    (delta := delta) (rho := delta) (sigma := sigma) shading
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  sourceSlope_eq : windowed.global.sourceSlope = source.globalGrains.slope
  active_cell_window :
    ∀ cell ∈ wz1Lemma23ActiveCells shading delta
        terminalSource.delta_pos,
      (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3) ∈
        Set.Icc left (left + Real.sqrt delta)
  volumeSupply : ENNReal
  volumeSupply_pos : 0 < volumeSupply
  volume_lower : volumeSupply ≤ MeasureTheory.volume shading.union
  union_height_window :
    ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈ Set.Ico
        (left - delta) (left + Real.sqrt delta + delta)

structure PureWZ2TerminalCertifiedWindow
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) where
  left : ℝ
  shading : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily terminalSource.shading
      terminalSource.delta_pos)
  subshading : IsSubshading shading prepared.shadow
  windowed : WZ1Lemma23WindowedGlobalSlicePackage
    (delta := delta) (rho := delta) (sigma := sigma) shading
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  sourceSlope_eq : windowed.global.sourceSlope = source.globalGrains.slope
  active_cell_window :
    ∀ cell ∈ wz1Lemma23ActiveCells shading delta
        terminalSource.delta_pos,
      (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3) ∈
        Set.Icc left (left + Real.sqrt delta)
  volumeSupply : ENNReal
  volumeSupply_pos : 0 < volumeSupply
  volumeSupply_ne_top : volumeSupply ≠ ⊤
  minimum_supply :
    (4 : ENNReal)⁻¹ *
        (MeasureTheory.volume prepared.shadow.union *
          ENNReal.ofReal (Real.sqrt delta) /
          ENNReal.ofReal (2 + delta + Real.sqrt delta)) ≤
      volumeSupply
  volume_lower :
    volumeSupply ≤ MeasureTheory.volume shading.union
  union_height_window :
    ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈ Set.Ico
        (left - delta) (left + Real.sqrt delta + delta)

/-- Forget the canonical-average certificate of a selected terminal window. -/
def PureWZ2TerminalCertifiedWindow.toGraphWindow
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalCertifiedWindow prepared) :
    PureWZ2TerminalGraphWindow prepared where
  left := window.left
  shading := window.shading
  subshading := window.subshading
  windowed := window.windowed
  sourceSlope_eq := window.sourceSlope_eq
  active_cell_window := window.active_cell_window
  volumeSupply := window.volumeSupply
  volumeSupply_pos := window.volumeSupply_pos
  volume_lower := window.volume_lower
  union_height_window := window.union_height_window

/-- The common terminal-chain window interface.  The initial selector returns
a `PureWZ2TerminalCertifiedWindow`; after height popularity the same chain is
run on a window without the obsolete global-average certificate. -/
abbrev PureWZ2TerminalWindow
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :=
  PureWZ2TerminalGraphWindow prepared

theorem PureWZ2TerminalLemma23Prepared.selectWindow
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource) :
    Nonempty (PureWZ2TerminalCertifiedWindow prepared) := by
  have hdelta : 0 < delta := terminalSource.delta_pos
  have hdeltaOne : delta ≤ 1 := terminalSource.delta_le_one
  have hball : prepared.shadow.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hpaper : point ∈ terminalSource.shading.union := by
      rwa [prepared.shadow_union] at hpoint
    have hnorm := norm_le_two_of_mem_paperShading hpaper
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hheight :
      ∀ point ∈ prepared.shadow.union, |point (2 : Fin 3)| ≤ 1 := by
    intro point hpoint
    have hpaper : point ∈ terminalSource.shading.union := by
      rwa [prepared.shadow_union] at hpoint
    have hbox := shading_union_subset_axisBox hpaper
    simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
  rcases height_window_pigeonhole_tight_of_paper_window
      prepared.shadow hdelta hdeltaOne hball hheight with
    ⟨left, hvolume⟩
  have hcoord :
      ∀ point ∈ prepared.shadow.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpaper : point ∈ terminalSource.shading.union := by
      rwa [prepared.shadow_union] at hpoint
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hCtop :
      (10 * Kakeya.realRpowENN delta (-inputLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN])
  rcases wz1_lemma23_windowed_global_slice_package_of_exact_paper_window
      prepared.shadow hdelta le_rfl hdeltaOne hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound
      (10 * Kakeya.realRpowENN delta (-inputLoss)) hCtop prepared.exactAD left with
    ⟨shading, windowed, hshading, hsub, hslope⟩
  have hunion : shading.union = prepared.shadow.union ∩
      wz1Lemma23CellHeightWindowSet delta hdelta left := by
    rw [hshading]
    ext point
    constructor
    · rintro ⟨index, hpoint⟩
      exact ⟨⟨index, hpoint.1⟩, hpoint.2⟩
    · rintro ⟨⟨index, hpoint⟩, hwindow⟩
      exact ⟨index, hpoint, hwindow⟩
  let volumeSupply :=
    MeasureTheory.volume prepared.shadow.union *
        ENNReal.ofReal (Real.sqrt delta) /
      ENNReal.ofReal (2 + delta + Real.sqrt delta)
  have hpreparedVolume : 0 < MeasureTheory.volume prepared.shadow.union := by
    rw [prepared.shadow_union]
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos terminalSource.delta_pos _)).trans_le
      terminalSource.volume_lower
  have hvolumeSupplyPos : 0 < volumeSupply := by
    dsimp only [volumeSupply]
    exact ENNReal.div_pos
      (ENNReal.mul_pos hpreparedVolume.ne'
        (ENNReal.ofReal_pos.mpr
          (Real.sqrt_pos.mpr terminalSource.delta_pos)).ne').ne'
      ENNReal.ofReal_ne_top
  have hvolumeSupplyTop : volumeSupply ≠ ⊤ := by
    dsimp only [volumeSupply]
    apply ENNReal.div_ne_top
    · exact ENNReal.mul_ne_top
        (ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
          (MeasureTheory.measure_mono hball)) ENNReal.ofReal_ne_top
    · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hunionHeight :
      ∀ point ∈ shading.union,
        point (2 : Fin 3) ∈ Set.Ico
          (left - delta) (left + Real.sqrt delta + delta) := by
    intro point hpoint
    have hpointRestricted : point ∈
        (wz1Lemma23RestrictShadingToCellHeightWindow
          prepared.shadow hdelta left).union := by
      rw [← hshading]
      exact hpoint
    rcases hpointRestricted with ⟨index, hpointCarrier⟩
    have hpointWindow : point ∈
        wz1Lemma23CellHeightWindowSet delta hdelta left :=
      hpointCarrier.2
    rcases Set.mem_iUnion₂.mp hpointWindow with
      ⟨windowCell, hwindowCell, hpointCell⟩
    have hcenterWindow := (Finset.mem_filter.mp hwindowCell).2
    have hpointCenter :=
      ((wz1_lemma23_snapped_cell_geometry delta hdelta hdeltaOne).2.1
        windowCell point hpointCell).1 (2 : Fin 3)
    rw [abs_le] at hpointCenter
    exact ⟨by linarith [hcenterWindow.1, hpointCenter.2],
      by linarith [hcenterWindow.2, hpointCenter.1]⟩
  exact ⟨{
    left := left
    shading := shading
    subshading := hsub
    windowed := windowed
    sourceSlope_eq := hslope
    active_cell_window := by
      intro cell hcell
      rcases (wz1Lemma23_mem_active_iff shading hdelta cell).mp hcell with
        ⟨_hbounded, point, hpoint, hpointCell⟩
      have hpointRestricted : point ∈
          (wz1Lemma23RestrictShadingToCellHeightWindow
            prepared.shadow hdelta left).union := by
        rwa [← hshading]
      rcases hpointRestricted with ⟨index, hpointCarrier⟩
      have hpointWindow : point ∈
          wz1Lemma23CellHeightWindowSet delta hdelta left :=
        hpointCarrier.2
      rcases Set.mem_iUnion₂.mp hpointWindow with
        ⟨windowCell, hwindowCell, hpointWindowCell⟩
      have hwindowIndex : wz1Lemma23CellIndex delta point = windowCell :=
        hpointWindowCell
      have hcellEq : windowCell = cell := hwindowIndex.symm.trans hpointCell
      simpa [hcellEq] using (Finset.mem_filter.mp hwindowCell).2
    volumeSupply := volumeSupply
    volumeSupply_pos := hvolumeSupplyPos
    volumeSupply_ne_top := hvolumeSupplyTop
    minimum_supply := by
      dsimp only [volumeSupply]
      have hquarter : (4 : ENNReal)⁻¹ ≤ 1 := by norm_num
      calc
        (4 : ENNReal)⁻¹ *
              (MeasureTheory.volume prepared.shadow.union *
                ENNReal.ofReal (Real.sqrt delta) /
                ENNReal.ofReal (2 + delta + Real.sqrt delta)) ≤
            1 * (MeasureTheory.volume prepared.shadow.union *
                ENNReal.ofReal (Real.sqrt delta) /
                ENNReal.ofReal (2 + delta + Real.sqrt delta)) := by gcongr
        _ = _ := one_mul _
    volume_lower := by rwa [hunion]
    union_height_window := hunionHeight
  }⟩

/-- Package an arbitrary positive terminal subwindow with its true local
volume supply.  The lower bound is deliberately relative to the canonical
global average, so every downstream exact-volume schedule remains uniform. -/
theorem PureWZ2TerminalLemma23Prepared.windowOfSubshading
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    (prepared : PureWZ2TerminalLemma23Prepared terminalSource)
    (left : ℝ)
    (shading : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily terminalSource.shading
        terminalSource.delta_pos))
    (hsub : IsSubshading shading prepared.shadow)
    (hactive : ∀ cell ∈ wz1Lemma23ActiveCells shading delta
        terminalSource.delta_pos,
      (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3) ∈
        Set.Icc left (left + Real.sqrt delta))
    (volumeSupply : ENNReal)
    (hvolumeSupply : 0 < volumeSupply)
    (hvolumeSupplyTop : volumeSupply ≠ ⊤)
    (hminimum :
      (4 : ENNReal)⁻¹ *
          (MeasureTheory.volume prepared.shadow.union *
            ENNReal.ofReal (Real.sqrt delta) /
            ENNReal.ofReal (2 + delta + Real.sqrt delta)) ≤
        volumeSupply)
    (hvolume : volumeSupply ≤ MeasureTheory.volume shading.union) :
    ∃ window : PureWZ2TerminalCertifiedWindow prepared,
      window.left = left ∧ window.shading = shading ∧
        window.volumeSupply = volumeSupply := by
  have hdelta : 0 < delta := terminalSource.delta_pos
  have hdeltaOne : delta ≤ 1 := terminalSource.delta_le_one
  have hball : shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared := hsub.union_subset hpoint
    have hpaper : point ∈ terminalSource.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hnorm := norm_le_two_of_mem_paperShading hpaper
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord : ∀ point ∈ shading.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hprepared := hsub.union_subset hpoint
    have hpaper : point ∈ terminalSource.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hCtop :
      (10 * Kakeya.realRpowENN delta (-inputLoss) : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by simp [Kakeya.realRpowENN])
  have hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice shading.union z))
        delta (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    intro z hz
    apply (prepared.exactAD z hz).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point, ⟨hsub.union_subset hpoint.1, hpoint.2⟩, rfl⟩
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      shading hdelta le_rfl hdeltaOne hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound
      (10 * Kakeya.realRpowENN delta (-inputLoss)) hCtop hexact with
    ⟨global, hslope⟩
  let windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := delta) (sigma := sigma) shading
      (10 * Kakeya.realRpowENN delta (-inputLoss)) :=
    { global := global
      active_height_window := ⟨left, hactive⟩ }
  have hunionHeight : ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈ Set.Ico
        (left - delta) (left + Real.sqrt delta + delta) := by
    intro point hpoint
    have hcell := wz1Lemma23_index_mem_active_two hdelta hball hpoint
    have hcenter := hactive _ hcell
    have hpointCenter :=
      ((wz1_lemma23_snapped_cell_geometry delta hdelta hdeltaOne).2.1
        (wz1Lemma23CellIndex delta point) point rfl).1 (2 : Fin 3)
    rw [abs_le] at hpointCenter
    exact ⟨by linarith [hcenter.1, hpointCenter.2],
      by linarith [hcenter.2, hpointCenter.1]⟩
  let result : PureWZ2TerminalCertifiedWindow prepared :=
    { left := left
      shading := shading
      subshading := hsub
      windowed := windowed
      sourceSlope_eq := by simpa [windowed] using hslope
      active_cell_window := hactive
      volumeSupply := volumeSupply
      volumeSupply_pos := hvolumeSupply
      volumeSupply_ne_top := hvolumeSupplyTop
      minimum_supply := hminimum
      volume_lower := hvolume
      union_height_window := hunionHeight }
  exact ⟨result, rfl, rfl, rfl⟩

/-- Select the genuine fixed horizontal source line on the terminal window. -/
theorem PureWZ2TerminalGraphWindow.selectHorizontalFixedLine
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalGraphWindow prepared) :
    Nonempty (PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope) := by
  have hcoord : ∀ point ∈ window.shading.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hprepared := window.subshading.union_subset hpoint
    have hpaper : point ∈ terminalSource.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hbox := shading_union_subset_axisBox hpaper
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice window.shading.union z))
        delta (1 - sigma)
        (10 * Kakeya.realRpowENN delta (-inputLoss)) := by
    intro z hz
    apply (prepared.exactAD z hz).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point, ⟨window.subshading.union_subset hpoint.1, hpoint.2⟩, rfl⟩
  have hvolume : 0 < MeasureTheory.volume window.shading.union := by
    have hsourceVolume : 0 < MeasureTheory.volume prepared.shadow.union := by
      rw [prepared.shadow_union]
      exact (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos terminalSource.delta_pos _)).trans_le
        terminalSource.volume_lower
    have hroot : 0 < ENNReal.ofReal (Real.sqrt delta) :=
      ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr terminalSource.delta_pos)
    have hdenomTop : ENNReal.ofReal
        (2 + delta + Real.sqrt delta) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hleft : 0 < MeasureTheory.volume prepared.shadow.union *
          ENNReal.ofReal (Real.sqrt delta) /
        ENNReal.ofReal (2 + delta + Real.sqrt delta) :=
      ENNReal.div_pos
        (ENNReal.mul_pos hsourceVolume.ne' hroot.ne').ne' hdenomTop
    exact window.volumeSupply_pos.trans_le window.volume_lower
  exact pureWZ2_selectHorizontalFixedLineCore
    window.windowed source.globalGrains.slope
    terminalSource.delta_pos le_rfl terminalSource.delta_le_one
    window.sourceSlope_eq hcoord window.left window.union_height_window
    hexact hvolume

end Kakeya.Assouad
