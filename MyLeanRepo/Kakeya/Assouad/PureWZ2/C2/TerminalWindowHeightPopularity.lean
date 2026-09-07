import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleWindow
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HeightVolumePopularity

/-!
# Terminal height popularity before fixed-line selection

The terminal endpoint of the Corollary-5.6 construction must first retain a
dyadically popular family of genuine three-dimensional height slabs.  Only
after that restriction may the auxiliary exact-slice graph select a fixed
horizontal line.

`PureWZ2TerminalGraphWindow` is the graph-facing part of a terminal window.
Unlike `PureWZ2TerminalCertifiedWindow`, it deliberately has no lower bound
against the canonical global window average: a height-popularity restriction
pays an explicit logarithmic loss instead.  The latter is recorded by
`PureWZ2TerminalWindowHeightPopularData.source_volume_retention`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Package any positive terminal subshading carrying the inherited active
cell-height window as a graph-facing terminal window. -/
theorem PureWZ2TerminalLemma23Prepared.graphWindowOfSubshading
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
    (hvolume : volumeSupply ≤ volume shading.union) :
    ∃ graphWindow : PureWZ2TerminalGraphWindow prepared,
      graphWindow.left = left ∧ graphWindow.shading = shading ∧
        graphWindow.volumeSupply = volumeSupply := by
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
    ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
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
  let graphWindow : PureWZ2TerminalGraphWindow prepared := {
    left := left
    shading := shading
    subshading := hsub
    windowed := windowed
    sourceSlope_eq := by simpa [windowed] using hslope
    active_cell_window := hactive
    volumeSupply := volumeSupply
    volumeSupply_pos := hvolumeSupply
    volume_lower := hvolume
    union_height_window := hunionHeight }
  exact ⟨graphWindow, rfl, rfl, rfl⟩

/-- Genuine union-volume popularity on a terminal window, before selecting a
fixed line.  Every cell of the rebuilt exact-slice package has one of the
selected popular height labels. -/
structure PureWZ2TerminalWindowHeightPopularData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalWindow prepared) where
  popular : PureWZ2HeightVolumePopularData window.shading delta
  graphWindow : PureWZ2TerminalGraphWindow prepared
  graphWindow_left : graphWindow.left = window.left
  graphWindow_shading : graphWindow.shading = popular.shading
  graphWindow_supply : graphWindow.volumeSupply = volume popular.shading.union
  graphWindow_carrier_eq : ∀ index, graphWindow.shading.carrier index =
    window.shading.carrier index ∩ popular.heightRegion
  graph_cells_popular_height :
    ∀ cell ∈ graphWindow.windowed.global.cells,
      cell.2.2 ∈ popular.heightIndices
  source_volume_retention :
    volume window.shading.union ≤
      (2 * popular.bins : ℕ) * graphWindow.volumeSupply

/-- Select source-volume-popular terminal heights and rebuild the auxiliary
global-slice package on exactly that restricted carrier. -/
theorem PureWZ2TerminalWindow.heightPopularBeforeFixedLine
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    (window : PureWZ2TerminalWindow prepared) :
    Nonempty (PureWZ2TerminalWindowHeightPopularData window) := by
  have hdelta : 0 < delta := terminalSource.delta_pos
  have hball : window.shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared := window.subshading.union_subset hpoint
    have hpaper : point ∈ terminalSource.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hnorm := norm_le_two_of_mem_paperShading hpaper
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hvolumePos : 0 < volume window.shading.union :=
    window.volumeSupply_pos.trans_le window.volume_lower
  have hvolumeTop : volume window.shading.union ≠ ⊤ :=
    ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  rcases pureWZ2_heightVolumePopularity window.shading delta hdelta
      hball hvolumePos hvolumeTop with ⟨popular⟩
  have hpopularPos : 0 < volume popular.shading.union := by
    rcases popular.heightIndices_nonempty with ⟨heightIndex, hheightIndex⟩
    apply popular.layerMass_pos.trans_le
    calc
      popular.layerMass ≤ volume (window.shading.union ∩
          wz1Lemma23HeightSlab delta heightIndex) :=
        (popular.layer_volume_band heightIndex hheightIndex).1
      _ ≤ ∑ selectedHeight ∈ popular.heightIndices,
          volume (window.shading.union ∩
            wz1Lemma23HeightSlab delta selectedHeight) :=
        Finset.single_le_sum
          (f := fun selectedHeight => volume (window.shading.union ∩
            wz1Lemma23HeightSlab delta selectedHeight))
          (fun _ _ => bot_le) hheightIndex
      _ = volume popular.shading.union := popular.volume_eq_sum.symm
  have hsubPrepared : IsSubshading popular.shading prepared.shadow :=
    fun index => (popular.subshading index).trans (window.subshading index)
  have hactive : ∀ cell ∈ wz1Lemma23ActiveCells popular.shading delta hdelta,
      (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3) ∈
        Set.Icc window.left (window.left + Real.sqrt delta) := by
    intro cell hcell
    apply window.active_cell_window cell
    rw [wz1Lemma23_mem_active_iff] at hcell ⊢
    refine ⟨hcell.1, ?_⟩
    rcases hcell.2 with ⟨point, hpoint, hpointCell⟩
    exact ⟨point, popular.subshading.union_subset hpoint, hpointCell⟩
  rcases prepared.graphWindowOfSubshading window.left popular.shading
      hsubPrepared hactive (volume popular.shading.union) hpopularPos le_rfl with
    ⟨graphWindow, hgraphLeft, hgraphShading, hgraphSupply⟩
  have hcellsPopular : ∀ cell ∈ graphWindow.windowed.global.cells,
      cell.2.2 ∈ popular.heightIndices := by
    intro cell hcell
    have hcellActive := graphWindow.windowed.global.cells_active hcell
    rcases (wz1Lemma23_mem_active_iff graphWindow.shading hdelta cell).mp
        hcellActive with ⟨_hbounded, point, hpoint, hpointIndex⟩
    have hpointPopular : point ∈ popular.shading.union := by
      rw [← hgraphShading]
      exact hpoint
    rw [popular.union_eq] at hpointPopular
    rw [popular.heightRegion_eq] at hpointPopular
    rcases Set.mem_iUnion₂.mp hpointPopular.2 with
      ⟨heightIndex, hheightIndex, hpointSlab⟩
    have hfloor :=
      (wz1Lemma23_mem_heightSlab_iff hdelta heightIndex point).mp hpointSlab
    have hcellHeight : cell.2.2 = heightIndex := by
      have hindex := congrArg (fun index : ℤ × ℤ × ℤ => index.2.2)
        hpointIndex
      have hindex' :
          Int.floor (point (2 : Fin 3) / gridSide (delta / 2)) = cell.2.2 := by
        simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex] using hindex
      exact hindex'.symm.trans hfloor
    rwa [hcellHeight]
  have hretention : volume window.shading.union ≤
      (2 * popular.bins : ℕ) * graphWindow.volumeSupply := by
    have h := (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp
      popular.retained_volume
    calc
      volume window.shading.union ≤
          (popular.bins : ENNReal) * volume popular.shading.union * 2 := h
      _ = ((2 * popular.bins : ℕ) : ENNReal) *
          volume popular.shading.union := by
        push_cast
        ring
      _ = (2 * popular.bins : ℕ) * graphWindow.volumeSupply := by
        rw [hgraphSupply]
  exact ⟨{
    popular := popular
    graphWindow := graphWindow
    graphWindow_left := hgraphLeft
    graphWindow_shading := hgraphShading
    graphWindow_supply := hgraphSupply
    graphWindow_carrier_eq := by
      intro index
      rw [hgraphShading]
      exact popular.carrier_eq index
    graph_cells_popular_height := hcellsPopular
    source_volume_retention := hretention }⟩

end Kakeya.Assouad
