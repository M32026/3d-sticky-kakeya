import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularParentWeightClass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.ActiveCellShadowGrains

/-!
# Outer-popular carrier restricted to a regularized parent class

The restriction is performed before the terminal fixed line is selected.  It
keeps the original source-family indices, the exact outer-popular carrier, and
the common multiplicity band.  Its partial-cell shadow has the same union and
is the carrier on which the new fixed line is selected.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2TerminalPopularParentRestrictionData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    (weightClass : PureWZ2TerminalPopularParentWeightClassData carrier) where
  shading : WZ1PaperTubeShading source.family
  carrier_eq : ∀ index, shading.carrier index =
    carrier.shading.carrier index ∩ weightClass.selectedRegion
  subshading_carrier : PureWZ2PaperIsSubshading shading carrier.shading
  subshading_source : PureWZ2PaperIsSubshading shading source.shading
  union_eq : shading.union =
    carrier.shading.union ∩ weightClass.selectedRegion
  volume_eq : volume shading.union = weightClass.selectedWeight
  volume_pos : 0 < volume shading.union
  retained_volume : volume carrier.shading.union ≤
    2 * weightClass.bins * volume shading.union
  height_region : shading.union ⊆ heightData.popular.heightRegion
  constant_multiplicity : shading.HasConstantMultiplicity
    terminalSource.multiplicity (2 * terminalSource.multiplicity)

noncomputable def PureWZ2TerminalPopularParentWeightClassData.restrictCarrier
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    (weightClass : PureWZ2TerminalPopularParentWeightClassData carrier) :
    PureWZ2TerminalPopularParentRestrictionData weightClass := by
  let shading : WZ1PaperTubeShading source.family :=
    { carrier := fun index =>
        carrier.shading.carrier index ∩ weightClass.selectedRegion
      measurable_carrier := fun index =>
        (carrier.shading.measurable_carrier index).inter
          weightClass.selectedRegion_measurable
      subset_body := fun index => Set.inter_subset_left.trans
        (carrier.shading.subset_body index) }
  have hunion : shading.union =
      carrier.shading.union ∩ weightClass.selectedRegion := by
    ext point
    constructor
    · rintro ⟨index, hcarrier, hregion⟩
      exact ⟨⟨index, hcarrier⟩, hregion⟩
    · rintro ⟨⟨index, hcarrier⟩, hregion⟩
      exact ⟨index, hcarrier, hregion⟩
  have hsubCarrier : PureWZ2PaperIsSubshading shading carrier.shading :=
    fun _ => Set.inter_subset_left
  have hsubSource : PureWZ2PaperIsSubshading shading source.shading :=
    fun index => (hsubCarrier index).trans (carrier.subshading index)
  have hconstant : shading.HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity) := by
    intro point hpoint
    have hmultiplicity : shading.pointMultiplicity point =
        carrier.shading.pointMultiplicity point := by
      unfold Kakeya.Streamlined.Shading.pointMultiplicity
      congr 1
      ext index
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.1
      · intro hcarrier
        have hrestricted :
            point ∈ carrier.shading.union ∩ weightClass.selectedRegion := by
          rw [← hunion]
          exact hpoint
        exact ⟨hcarrier, hrestricted.2⟩
    rw [hmultiplicity]
    exact carrier.constant_multiplicity point
      (hsubCarrier.union_subset hpoint)
  have hvolume : volume shading.union = weightClass.selectedWeight := by
    rw [hunion, ← weightClass.selectedWeight_eq]
  exact {
    shading := shading
    carrier_eq := fun _ => rfl
    subshading_carrier := hsubCarrier
    subshading_source := hsubSource
    union_eq := hunion
    volume_eq := hvolume
    volume_pos := by rw [hvolume]; exact weightClass.selectedWeight_pos
    retained_volume := by rw [hvolume]; exact weightClass.retained_volume
    height_region := hsubCarrier.union_subset.trans carrier.height_region
    constant_multiplicity := hconstant
  }

/-- Local/global grains and exact-slice data rebuilt on the pre-line
parent-weight restriction. -/
structure PureWZ2TerminalPopularParentRestrictedPreparedData
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    (restricted : PureWZ2TerminalPopularParentRestrictionData weightClass) where
  localPaper : PureWZ2LocalGrainData restricted.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  globalPaper : PureWZ2LipschitzGlobalGrainData restricted.shading sigma
    (Kakeya.realRpowENN delta (-inputLoss))
  globalPaper_slope_eq : globalPaper.slope = source.globalGrains.slope
  localGrains : WZ1LocalGrainData
    (pureWZ2PartialActiveCellShading
      restricted.shading source.extremal.delta_pos) sigma
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  planeMap_vertical_bound :
    ∀ point ∈ (pureWZ2PartialActiveCellShading
        restricted.shading source.extremal.delta_pos).union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2
  windowed : WZ1Lemma23WindowedGlobalSlicePackage
    (delta := delta) (rho := delta) (sigma := sigma)
    (pureWZ2PartialActiveCellShading
      restricted.shading source.extremal.delta_pos)
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  sourceSlope_eq : windowed.global.sourceSlope = source.globalGrains.slope
  active_cell_window :
    ∀ cell ∈ wz1Lemma23ActiveCells
        (pureWZ2PartialActiveCellShading
          restricted.shading source.extremal.delta_pos) delta
        source.extremal.delta_pos,
      (wz1Lemma23SnappedPoint delta cell) (2 : Fin 3) ∈
        Set.Icc heightData.graphWindow.left
          (heightData.graphWindow.left + Real.sqrt delta)
  exactAD : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    IsADSet1
      (scalarProjection
        (globalGrainDirection (source.globalGrains.slope z))
        (horizontalSlice (pureWZ2PartialActiveCellShading
          restricted.shading source.extremal.delta_pos).union z))
      delta (1 - sigma)
      (10 * Kakeya.realRpowENN delta (-inputLoss))
  volumeSupply : ENNReal := volume restricted.shading.union
  volumeSupply_pos : 0 < volumeSupply
  volume_eq : volumeSupply = volume
    (pureWZ2PartialActiveCellShading
      restricted.shading source.extremal.delta_pos).union
  union_height_window : ∀ point ∈
      (pureWZ2PartialActiveCellShading
        restricted.shading source.extremal.delta_pos).union,
    point (2 : Fin 3) ∈ Set.Ico
      (heightData.graphWindow.left - delta)
      (heightData.graphWindow.left + Real.sqrt delta + delta)

theorem PureWZ2TerminalPopularParentRestrictionData.prepareWindow
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    (restricted : PureWZ2TerminalPopularParentRestrictionData weightClass)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2TerminalPopularParentRestrictedPreparedData restricted) := by
  let C := Kakeya.realRpowENN delta (-inputLoss)
  have hCtop : C ≠ ⊤ := by simp [C, Kakeya.realRpowENN]
  let localPaper : PureWZ2LocalGrainData restricted.shading sigma C :=
    source.localGrains.restrictWithConstant
      restricted.subshading_source le_rfl hCtop
  let globalPaper : PureWZ2BoundedLipschitzGlobalGrainData
      restricted.shading sigma C :=
    source.globalGrains.restrict restricted.subshading_source le_rfl hCtop
  let localGrains : WZ1LocalGrainData
      (pureWZ2PartialActiveCellShading restricted.shading
        source.extremal.delta_pos) sigma (10 * C) :=
    localPaper.toPartialActiveCellShadow source.extremal.delta_pos hbridge
  have hverticalPaper :
      ∀ point : {point : Point3 // point ∈ restricted.shading.union},
        |localPaper.planeMap point (2 : Fin 3)| ≤ 1 / 2 := by
    intro point
    exact source.planeMap_vertical_bound
      ⟨point, restricted.subshading_source.union_subset point.property⟩
  have hverticalRaw : ∀ point ∈
      (pureWZ2PartialActiveCellShading
        restricted.shading source.extremal.delta_pos).union,
      |localGrains.planeMap point (2 : Fin 3)| ≤ 1 / 2 :=
    localPaper.toPartialActiveCellShadow_vertical_bound
      source.extremal.delta_pos hbridge hverticalPaper
  have hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
          (horizontalSlice (pureWZ2PartialActiveCellShading
            restricted.shading source.extremal.delta_pos).union z))
        delta (1 - sigma) (10 * C) := by
    intro z hz
    have h := globalPaper.partialActiveCellShadow_exactAD
      source.extremal.delta_pos hbridge globalPaper.slope_bound z hz
    rw [show globalPaper.slope = source.globalGrains.slope by rfl] at h
    change IsADSet1
      (scalarProjection (globalGrainDirection (source.globalGrains.slope z))
        (horizontalSlice (pureWZ2PartialActiveCellShading
          restricted.shading source.extremal.delta_pos).union z))
      delta (1 - sigma) (10 * C) at h
    exact h
  have hball : (pureWZ2PartialActiveCellShading restricted.shading
      source.extremal.delta_pos).union ⊆
      Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hsource : point ∈ source.shading.union := by
      rw [pureWZ2PartialActiveCellShading_union] at hpoint
      exact restricted.subshading_source.union_subset hpoint
    have hnorm := norm_le_two_of_mem_paperShading hsource
    simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
  have hcoord : ∀ point ∈
      (pureWZ2PartialActiveCellShading restricted.shading
        source.extremal.delta_pos).union,
      ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hsource : point ∈ source.shading.union := by
      rw [pureWZ2PartialActiveCellShading_union] at hpoint
      exact restricted.subshading_source.union_subset hpoint
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hactive :
      ∀ cell ∈ wz1Lemma23ActiveCells
          (pureWZ2PartialActiveCellShading restricted.shading
            source.extremal.delta_pos) delta
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
      rw [pureWZ2PartialActiveCellShading_union] at hpoint
      exact restricted.subshading_carrier.union_subset hpoint
    have hgraph : point ∈ heightData.graphWindow.shading.union := by
      rw [← carrier.union_eq]
      exact hcarrier
    exact ⟨point, hgraph, hpointCell⟩
  have hunionHeight : ∀ point ∈
      (pureWZ2PartialActiveCellShading restricted.shading
        source.extremal.delta_pos).union,
      point (2 : Fin 3) ∈ Set.Ico
        (heightData.graphWindow.left - delta)
        (heightData.graphWindow.left + Real.sqrt delta + delta) := by
    intro point hpoint
    apply heightData.graphWindow.union_height_window point
    have hcarrier : point ∈ carrier.shading.union := by
      rw [pureWZ2PartialActiveCellShading_union] at hpoint
      exact restricted.subshading_carrier.union_subset hpoint
    rw [← carrier.union_eq]
    exact hcarrier
  rcases wz1_lemma23_global_slice_package_of_exact_paper_window
      (pureWZ2PartialActiveCellShading restricted.shading
        source.extremal.delta_pos) source.extremal.delta_pos le_rfl
      source.extremal.delta_le_one hball hcoord
      source.globalGrains.slope source.globalGrains.slope_lipschitz
      source.globalGrains.slope_bound (10 * C)
      (ENNReal.mul_ne_top (by norm_num) hCtop) hexact with
    ⟨global, hslope⟩
  let windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := delta) (sigma := sigma)
      (pureWZ2PartialActiveCellShading restricted.shading
        source.extremal.delta_pos) (10 * C) :=
    { global := global
      active_height_window := ⟨heightData.graphWindow.left, hactive⟩ }
  exact ⟨{
    localPaper := localPaper
    globalPaper := globalPaper
    globalPaper_slope_eq := rfl
    localGrains := localGrains
    planeMap_vertical_bound := hverticalRaw
    windowed := windowed
    sourceSlope_eq := by simpa [windowed] using hslope
    active_cell_window := hactive
    exactAD := by simpa [C] using hexact
    volumeSupply := volume restricted.shading.union
    volumeSupply_pos := restricted.volume_pos
    volume_eq := by rw [pureWZ2PartialActiveCellShading_union]
    union_height_window := hunionHeight
  }⟩

theorem PureWZ2TerminalPopularParentRestrictedPreparedData.selectHorizontalFixedLine
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {heightData : PureWZ2TerminalWindowHeightPopularData window}
    {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
    {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
    {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
    (data : PureWZ2TerminalPopularParentRestrictedPreparedData restricted) :
    Nonempty (PureWZ2HorizontalFixedLineCore
      data.windowed source.globalGrains.slope) := by
  exact pureWZ2_selectHorizontalFixedLineCore
    data.windowed source.globalGrains.slope
    source.extremal.delta_pos le_rfl source.extremal.delta_le_one
    data.sourceSlope_eq (by
      intro point hpoint coordinate
      have hsource : point ∈ source.shading.union := by
        rw [pureWZ2PartialActiveCellShading_union] at hpoint
        exact restricted.subshading_source.union_subset hpoint
      have hbox := shading_union_subset_axisBox hsource
      simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
      norm_num at hbox
      fin_cases coordinate <;> tauto)
    heightData.graphWindow.left data.union_height_window data.exactAD
    (by rw [← data.volume_eq]; exact data.volumeSupply_pos)

end Kakeya.Assouad

end
