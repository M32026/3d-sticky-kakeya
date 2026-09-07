import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HeightVolumePopularity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCarrierPreparation

/-!
# Full-source height popularity before fixed-line selection

The continuous popular slabs are first selected using genuine union volume.
We then retain every complete source `delta`-cell that meets those slabs.
This whole-cell envelope contains the volume-popular shading and can be
repackaged as a standard source window for the existing auxiliary graph.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceWindowHeightPopularData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (graphScale : ℝ) where
  popular : PureWZ2HeightVolumePopularData window.shading graphScale
  popularWindow : PureWZ2SourceCarrierWindow prepared
  popularWindow_left : popularWindow.left = window.left
  popularWindow_shading : popularWindow.shading = popular.shading
  popularWindow_supply :
    popularWindow.volumeSupply = volume popular.shading.union
  heightCells : Finset (ℤ × ℤ × ℤ) :=
    (wz1PaperActiveCells source.shading source.extremal.delta_pos).filter
      fun cell => (wz1PaperGridCube delta cell ∩ popular.heightRegion).Nonempty
  heightCells_eq : heightCells =
    (wz1PaperActiveCells source.shading source.extremal.delta_pos).filter
      fun cell => (wz1PaperGridCube delta cell ∩ popular.heightRegion).Nonempty
  region : Set Point3 :=
    ⋃ cell ∈ heightCells, wz1PaperGridCube delta cell
  region_eq : region =
    ⋃ cell ∈ heightCells, wz1PaperGridCube delta cell
  region_measurable : MeasurableSet region
  shading : Kakeya.Streamlined.TubeShading
    (pureWZ2ActiveCellFamily pullback.shading source.extremal.delta_pos)
  carrier_eq : ∀ index, shading.carrier index =
    window.shading.carrier index ∩ region
  subshading_window : IsSubshading shading window.shading
  subshading_prepared : IsSubshading shading prepared.shadow
  popular_subset : popular.shading.union ⊆ shading.union
  volume_lower : volume popular.shading.union ≤ volume shading.union
  volume_pos : 0 < volume shading.union
  volume_ne_top : volume shading.union ≠ ⊤
  windowed : PureWZ2SourceCarrierWindow prepared
  windowed_left : windowed.left = window.left
  windowed_shading : windowed.shading = shading
  windowed_supply : windowed.volumeSupply = volume shading.union

theorem PureWZ2SourceCarrierWindow.heightPopularWholeCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (graphScale : ℝ) (hgraphScale : 0 < graphScale) :
    Nonempty (PureWZ2SourceWindowHeightPopularData window graphScale) := by
  have hball : window.shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hprepared := window.subshading.union_subset hpoint
    have hpull : point ∈ pullback.shading.union := by
      rwa [prepared.shadow_union] at hprepared
    have hsource := pullback.subshading.union_subset hpull
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hvolumePos : 0 < volume window.shading.union :=
    window.volumeSupply_pos.trans_le window.volume_lower
  have hvolumeTop : volume window.shading.union ≠ ⊤ :=
    ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  rcases pureWZ2_heightVolumePopularity window.shading graphScale
      hgraphScale hball hvolumePos hvolumeTop with ⟨popular⟩
  have hpopularSubPrepared : IsSubshading popular.shading prepared.shadow :=
    fun index => (popular.subshading index).trans (window.subshading index)
  have hpopularPos : 0 < volume popular.shading.union := by
    rcases popular.heightIndices_nonempty with ⟨heightIndex, hheightIndex⟩
    apply popular.layerMass_pos.trans_le
    calc
      popular.layerMass ≤ volume (window.shading.union ∩
          wz1Lemma23HeightSlab graphScale heightIndex) :=
        (popular.layer_volume_band heightIndex hheightIndex).1
      _ ≤ ∑ selectedHeight ∈ popular.heightIndices,
          volume (window.shading.union ∩
            wz1Lemma23HeightSlab graphScale selectedHeight) :=
        Finset.single_le_sum
          (f := fun selectedHeight => volume (window.shading.union ∩
            wz1Lemma23HeightSlab graphScale selectedHeight))
          (fun _ _ => bot_le) hheightIndex
      _ = volume popular.shading.union := popular.volume_eq_sum.symm
  have hpopularTop : volume popular.shading.union ≠ ⊤ :=
    ne_top_of_le_ne_top hvolumeTop
      (measure_mono popular.subshading.union_subset)
  have hpopularActive :
      ∀ cell ∈ wz1Lemma23ActiveCells popular.shading rho
          (source.extremal.delta_pos.trans_le (by
            rw [← twoScale.rhoRequested_eq]
            exact twoScale.rhoRequested.property.1)),
        (wz1Lemma23SnappedPoint rho cell) (2 : Fin 3) ∈
          Set.Icc window.left (window.left + Real.sqrt rho) := by
    intro cell hcell
    apply window.active_cell_window cell
    rw [wz1Lemma23_mem_active_iff] at hcell ⊢
    refine ⟨hcell.1, ?_⟩
    rcases hcell.2 with ⟨point, hpoint, hpointCell⟩
    exact ⟨point, popular.subshading.union_subset hpoint, hpointCell⟩
  rcases prepared.ofSubshading window.left popular.shading
      hpopularSubPrepared hpopularActive (volume popular.shading.union)
      hpopularPos hpopularTop le_rfl with
    ⟨popularWindow, hpopularLeft, hpopularShading, hpopularSupply⟩
  let heightCells :=
    (wz1PaperActiveCells source.shading source.extremal.delta_pos).filter
      fun cell => (wz1PaperGridCube delta cell ∩ popular.heightRegion).Nonempty
  let region : Set Point3 :=
    ⋃ cell ∈ heightCells, wz1PaperGridCube delta cell
  have hregionMeas : MeasurableSet region :=
    MeasurableSet.biUnion heightCells.finite_toSet.countable
      (fun cell _ => wz1PaperGridCube_measurable cell)
  let shading : Kakeya.Streamlined.TubeShading
      (pureWZ2ActiveCellFamily pullback.shading source.extremal.delta_pos) :=
    { carrier := fun index => window.shading.carrier index ∩ region
      measurable_carrier := fun index =>
        (window.shading.measurable_carrier index).inter hregionMeas
      subset_body := fun index => Set.inter_subset_left.trans
        (window.shading.subset_body index) }
  have hsubWindow : IsSubshading shading window.shading :=
    fun _ => Set.inter_subset_left
  have hsubPrepared : IsSubshading shading prepared.shadow :=
    fun index => (hsubWindow index).trans (window.subshading index)
  have hpopularSubset : popular.shading.union ⊆ shading.union := by
    intro point hpoint
    rw [popular.union_eq] at hpoint
    rcases hpoint.1 with ⟨index, hpointWindow⟩
    have hpull : point ∈ pullback.shading.union := by
      have hprepared : point ∈ prepared.shadow.union :=
        window.subshading.union_subset ⟨index, hpointWindow⟩
      rwa [prepared.shadow_union] at hprepared
    have hsource : point ∈ source.shading.union :=
      pullback.subshading.union_subset hpull
    rw [source.cubical.union_eq_activeCells source.extremal.delta_pos] at hsource
    rcases Set.mem_iUnion₂.mp hsource with ⟨cell, hcell, hpointCell⟩
    have hheightCell : cell ∈ heightCells := by
      apply Finset.mem_filter.mpr
      exact ⟨hcell, ⟨point, hpointCell, hpoint.2⟩⟩
    exact ⟨index, hpointWindow, Set.mem_iUnion₂.mpr
      ⟨cell, hheightCell, hpointCell⟩⟩
  have hvolumeLower : volume popular.shading.union ≤ volume shading.union :=
    measure_mono hpopularSubset
  have hshadingPos : 0 < volume shading.union := by
    rcases popular.heightIndices_nonempty with ⟨heightIndex, hheightIndex⟩
    apply popular.layerMass_pos.trans_le
    calc
      popular.layerMass ≤ volume (window.shading.union ∩
          wz1Lemma23HeightSlab graphScale heightIndex) :=
        (popular.layer_volume_band heightIndex hheightIndex).1
      _ ≤ ∑ selectedHeight ∈ popular.heightIndices,
          volume (window.shading.union ∩
            wz1Lemma23HeightSlab graphScale selectedHeight) :=
        Finset.single_le_sum
          (f := fun selectedHeight => volume (window.shading.union ∩
            wz1Lemma23HeightSlab graphScale selectedHeight))
          (fun _ _ => bot_le) hheightIndex
      _ = volume popular.shading.union := popular.volume_eq_sum.symm
      _ ≤ volume shading.union := hvolumeLower
  have hshadingTop : volume shading.union ≠ ⊤ :=
    ne_top_of_le_ne_top hvolumeTop (measure_mono hsubWindow.union_subset)
  have hactive :
      ∀ cell ∈ wz1Lemma23ActiveCells shading rho
          (source.extremal.delta_pos.trans_le (by
            rw [← twoScale.rhoRequested_eq]
            exact twoScale.rhoRequested.property.1)),
        (wz1Lemma23SnappedPoint rho cell) (2 : Fin 3) ∈
          Set.Icc window.left (window.left + Real.sqrt rho) := by
    intro cell hcell
    apply window.active_cell_window cell
    rw [wz1Lemma23_mem_active_iff] at hcell ⊢
    refine ⟨hcell.1, ?_⟩
    rcases hcell.2 with ⟨point, hpoint, hpointCell⟩
    exact ⟨point, hsubWindow.union_subset hpoint, hpointCell⟩
  rcases prepared.ofSubshading window.left shading hsubPrepared hactive
      (volume shading.union) hshadingPos hshadingTop le_rfl with
    ⟨windowed, hleft, hshading, hsupply⟩
  exact ⟨{
    popular := popular
    popularWindow := popularWindow
    popularWindow_left := hpopularLeft
    popularWindow_shading := hpopularShading
    popularWindow_supply := hpopularSupply
    heightCells := heightCells
    heightCells_eq := rfl
    region := region
    region_eq := rfl
    region_measurable := hregionMeas
    shading := shading
    carrier_eq := fun _ => rfl
    subshading_window := hsubWindow
    subshading_prepared := hsubPrepared
    popular_subset := hpopularSubset
    volume_lower := hvolumeLower
    volume_pos := hshadingPos
    volume_ne_top := hshadingTop
    windowed := windowed
    windowed_left := hleft
    windowed_shading := hshading
    windowed_supply := hsupply
  }⟩

/-- The logarithmic loss paid by the paper's pre-graph height popularity.
This is the ordinary-scale counterpart of
`PureWZ2TerminalWindowHeightPopularData.source_volume_retention`. -/
theorem PureWZ2SourceWindowHeightPopularData.source_volume_retention
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {graphScale : ℝ}
    (data : PureWZ2SourceWindowHeightPopularData window graphScale) :
    volume window.shading.union ≤
      (2 * data.popular.bins : ℕ) * data.popularWindow.volumeSupply := by
  have h := (ENNReal.div_le_iff (by norm_num) (by norm_num)).mp
    data.popular.retained_volume
  calc
    volume window.shading.union ≤
        (data.popular.bins : ENNReal) *
          volume data.popular.shading.union * 2 := h
    _ = ((2 * data.popular.bins : ℕ) : ENNReal) *
        volume data.popular.shading.union := by
      push_cast
      ring
    _ = (2 * data.popular.bins : ℕ) *
        data.popularWindow.volumeSupply := by
      rw [data.popularWindow_supply]

/-- The same pre-graph retention bound for the complete-cell envelope used by
the finite graph. -/
theorem PureWZ2SourceWindowHeightPopularData.source_volume_retention_windowed
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {graphScale : ℝ}
    (data : PureWZ2SourceWindowHeightPopularData window graphScale) :
    volume window.shading.union ≤
      (2 * data.popular.bins : ℕ) * data.windowed.volumeSupply := by
  calc
    volume window.shading.union ≤
        (2 * data.popular.bins : ℕ) *
          data.popularWindow.volumeSupply :=
      data.source_volume_retention
    _ = (2 * data.popular.bins : ℕ) *
        volume data.popular.shading.union := by
      rw [data.popularWindow_supply]
    _ ≤ (2 * data.popular.bins : ℕ) * volume data.shading.union := by
      exact mul_le_mul_left' data.volume_lower _
    _ = (2 * data.popular.bins : ℕ) * data.windowed.volumeSupply := by
      rw [data.windowed_supply]

/-- Every point of the complete source-cell envelope is within one source
cell diameter of the height region which generated the envelope. -/
theorem PureWZ2SourceWindowHeightPopularData.shading_point_near_height_region
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {graphScale : ℝ}
    (data : PureWZ2SourceWindowHeightPopularData window graphScale) :
    ∀ point ∈ data.shading.union,
      ∃ anchor ∈ data.popular.heightRegion,
        dist point anchor < 2 * delta := by
  intro point hpoint
  rcases hpoint with ⟨index, hpointCarrier⟩
  rw [data.carrier_eq] at hpointCarrier
  have hregion := hpointCarrier.2
  rw [data.region_eq] at hregion
  rcases Set.mem_iUnion₂.mp hregion with
    ⟨cell, hcell, hpointCell⟩
  rw [data.heightCells_eq] at hcell
  rcases (Finset.mem_filter.mp hcell).2 with
    ⟨anchor, hanchorCell, hanchorHeight⟩
  exact ⟨anchor, hanchorHeight,
    wz1_paper_grid_cube_diameter_lt_two_rho
      source.extremal.delta_pos hpointCell hanchorCell⟩

/-- The height envelope preserves union-level complete source cells whenever
its input window does.  This is the form needed by the same-block graph
volume argument; it makes no carrier-index identification. -/
theorem PureWZ2SourceWindowHeightPopularData.shading_union_whole_cells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    {graphScale : ℝ}
    (data : PureWZ2SourceWindowHeightPopularData window graphScale)
    (hwindow : ∀ point, point ∈ window.shading.union →
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        window.shading.union) :
    ∀ point, point ∈ data.shading.union →
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        data.shading.union := by
  intro point hpoint other hother
  rcases hpoint with ⟨index, hpointCarrier⟩
  rw [data.carrier_eq] at hpointCarrier
  have hotherWindow : other ∈ window.shading.union :=
    hwindow point ⟨index, hpointCarrier.1⟩ hother
  have hpointRegion := hpointCarrier.2
  rw [data.region_eq] at hpointRegion
  rcases Set.mem_iUnion₂.mp hpointRegion with
    ⟨cell, hcell, hpointCell⟩
  have hcellEq :
      wz1PaperGridIndex delta point = cell :=
    (mem_wz1PaperGridCube delta cell point).mp hpointCell
  rcases hotherWindow with ⟨otherIndex, hotherCarrier⟩
  refine ⟨otherIndex, ?_⟩
  rw [data.carrier_eq]
  refine ⟨hotherCarrier, ?_⟩
  rw [data.region_eq]
  exact Set.mem_iUnion₂.mpr ⟨cell, hcell, by rwa [← hcellEq]⟩

end Kakeya.Assouad
