import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCarrierPreparation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLine
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ExactSliceGlobalBins

/-!
# Genuine horizontal fixed line on the source-slope pullback carrier
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

structure PureWZ2SourceHorizontalFixedLineData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared) where
  rho_pos : 0 < rho
  lineHeight : ℝ
  lineHeight_mem : lineHeight ∈ Set.Icc (-1 : ℝ) 1
  sliceCells : Finset (ℤ × ℤ × ℤ)
  sliceCells_eq : sliceCells =
    wz1Lemma23ExactSliceCells window.shading delta
      source.extremal.delta_pos lineHeight
  slice_area_lower :
    MeasureTheory.volume window.shading.union /
        ENNReal.ofReal (Real.sqrt rho + 2 * rho) ≤
      MeasureTheory.volume
        (wz1Lemma23PlanarSlice window.shading.union lineHeight)
  sliceCells_nonempty : sliceCells.Nonempty
  globalBins : Finset ℤ
  globalBins_eq : globalBins = sliceCells.image fun cell =>
    Int.floor (wz1Lemma23GlobalCoordinate
      window.windowed.global.extendedSlope
      (wz1Lemma23CellCenter delta cell) / delta)
  global_bin_count :
    (globalBins.card : ENNReal) ≤
      132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
        Kakeya.realRpowENN (1 / delta) (1 - sigma)
  lineBin : ℤ
  lineBin_mem : lineBin ∈ globalBins
  heavyCells : Finset (ℤ × ℤ × ℤ)
  heavyCells_eq : heavyCells = sliceCells.filter fun cell =>
    Int.floor (wz1Lemma23GlobalCoordinate
      window.windowed.global.extendedSlope
      (wz1Lemma23CellCenter delta cell) / delta) = lineBin
  heavyCells_subset : heavyCells ⊆ sliceCells
  heavyCells_nonempty : heavyCells.Nonempty
  heavy_cell_count : sliceCells.card ≤ globalBins.card * heavyCells.card
  representative : (ℤ × ℤ × ℤ) → Point3
  representative_eq :
    ∀ cell (hcell : cell ∈ heavyCells), representative cell =
      wz1Lemma23LiftSlicePoint lineHeight
        (wz1Lemma23ExactSliceRepresentative window.shading
          source.extremal.delta_pos lineHeight
          ⟨cell, by simpa [sliceCells_eq] using heavyCells_subset hcell⟩)
  representative_mem :
    ∀ cell ∈ heavyCells, representative cell ∈ window.shading.union
  representative_height :
    ∀ cell ∈ heavyCells, representative cell (2 : Fin 3) = lineHeight
  representative_index :
    ∀ cell ∈ heavyCells, wz1Lemma23CellIndex delta (representative cell) = cell
  lineCell : ℤ × ℤ × ℤ
  lineCell_mem : lineCell ∈ heavyCells
  lineAnchor : Point3
  lineAnchor_eq : lineAnchor = representative lineCell
  lineAnchor_mem : lineAnchor ∈ window.shading.union
  lineAnchor_height : lineAnchor (2 : Fin 3) = lineHeight
  lineLevel : ℝ
  lineLevel_eq : lineLevel = inner ℝ lineAnchor
    (globalGrainDirection (source.globalGrains.slope lineHeight))
  heavy_representative_near_line :
    ∀ cell (hcell : cell ∈ heavyCells),
      let point := representative cell
      |inner ℝ point
          (globalGrainDirection (source.globalGrains.slope lineHeight)) -
        lineLevel| ≤ 9 * delta

theorem PureWZ2SourceCarrierWindow.selectHorizontalFixedLine
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    (window : PureWZ2SourceCarrierWindow prepared)
    (hvolume : 0 < MeasureTheory.volume window.shading.union) :
    Nonempty (PureWZ2SourceHorizontalFixedLineData window) := by
  have hdeltaRho : delta ≤ rho := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.1
  have hrho : 0 < rho := source.extremal.delta_pos.trans_le hdeltaRho
  have hrhoOne : rho ≤ 1 := by
    rw [← twoScale.rhoRequested_eq]
    exact twoScale.rhoRequested.property.2
  have hunionSub : window.shading.union ⊆ prepared.shadow.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, window.subshading index hpoint⟩
  have hcoord : ∀ point ∈ window.shading.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpull : point ∈ pullback.shading.union := by
      rw [← prepared.shadow_union]
      exact hunionSub hpoint
    have hbox := shading_union_subset_axisBox hpull
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hheight : ∀ point ∈ window.shading.union,
      |point (2 : Fin 3)| ≤ 1 := fun point hp => hcoord point hp 2
  have hmeas := measurableSet_shading_union window.shading
  have hfinite : MeasureTheory.volume window.shading.union ≠ ⊤ := by
    have hbox : window.shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
      intro point hpoint
      have hpull : point ∈ pullback.shading.union := by
        rw [← prepared.shadow_union]
        exact hunionSub hpoint
      have hsource := pullback.subshading.union_subset hpull
      have hnorm := norm_le_two_of_mem_paperShading hsource
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    exact ne_top_of_le_ne_top (Metric.isBounded_closedBall.measure_lt_top).ne
      (MeasureTheory.measure_mono hbox)
  let slabLeft := window.left - rho
  let slabRight := window.left + Real.sqrt rho + rho
  have hslab : window.shading.union ⊆
      {point : Point3 | point (2 : Fin 3) ∈ Set.Ico slabLeft slabRight} := by
    intro point hpoint
    exact window.union_height_window point hpoint
  have hslabLength : slabRight - slabLeft = Real.sqrt rho + 2 * rho := by
    dsimp only [slabLeft, slabRight]; ring
  have hslabNondegenerate : slabLeft < slabRight := by
    dsimp only [slabLeft, slabRight]
    nlinarith [Real.sqrt_pos.mpr hrho]
  rcases wz1_lemma23_exists_good_height_in_slab
      hmeas hfinite hslabNondegenerate with
    ⟨lineHeight, _, hsliceRaw⟩
  have hinter : window.shading.union ∩
      {point : Point3 | point (2 : Fin 3) ∈ Set.Ico slabLeft slabRight} =
      window.shading.union := Set.inter_eq_left.mpr hslab
  have hsliceArea : MeasureTheory.volume window.shading.union /
        ENNReal.ofReal (Real.sqrt rho + 2 * rho) ≤
      MeasureTheory.volume
        (wz1Lemma23PlanarSlice window.shading.union lineHeight) := by
    rw [hinter, hslabLength] at hsliceRaw
    exact hsliceRaw
  have hlineHeight : lineHeight ∈ Set.Icc (-1 : ℝ) 1 := by
    have hnonzero : MeasureTheory.volume
        (wz1Lemma23PlanarSlice window.shading.union lineHeight) ≠ 0 := by
      intro hzero
      rw [hzero] at hsliceArea
      have hpos : 0 < MeasureTheory.volume window.shading.union /
          ENNReal.ofReal (Real.sqrt rho + 2 * rho) :=
        ENNReal.div_pos hvolume.ne' ENNReal.ofReal_ne_top
      exact (not_le_of_gt hpos) hsliceArea
    have hsliceNonempty :
        (wz1Lemma23PlanarSlice window.shading.union lineHeight).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hnonzero
      exact hnonzero (by simp)
    rcases hsliceNonempty with ⟨point, hpoint⟩
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    simpa [point3] using abs_le.mp
      (hheight (point3 (point 0) (point 1) lineHeight) hlift)
  let sliceCells := wz1Lemma23ExactSliceCells window.shading delta
    source.extremal.delta_pos lineHeight
  have hsliceCells : sliceCells.Nonempty := by
    by_contra hempty
    have hzero : MeasureTheory.volume
        (wz1Lemma23PlanarSlice window.shading.union lineHeight) = 0 := by
      have hcover := wz1_lemma23_exactSlice_area_le_two window.shading
        source.extremal.delta_pos
        (by
          intro point hp
          have hpull : point ∈ pullback.shading.union := by
            rw [← prepared.shadow_union]
            exact hunionSub hp
          have hsource := pullback.subshading.union_subset hpull
          have hnorm := norm_le_two_of_mem_paperShading hsource
          simpa [Metric.mem_closedBall, dist_zero_right] using hnorm) lineHeight
      have hemptyEq : sliceCells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      simpa [sliceCells, hemptyEq] using hcover
    have hpos : 0 < MeasureTheory.volume window.shading.union /
        ENNReal.ofReal (Real.sqrt rho + 2 * rho) :=
      ENNReal.div_pos hvolume.ne' ENNReal.ofReal_ne_top
    rw [hzero] at hsliceArea
    exact (not_le_of_gt hpos) hsliceArea
  let label : (ℤ × ℤ × ℤ) → ℤ := fun cell => Int.floor
    (wz1Lemma23GlobalCoordinate window.windowed.global.extendedSlope
      (wz1Lemma23CellCenter delta cell) / delta)
  let globalBins := sliceCells.image label
  rcases finset_exists_max_fiber_with_product_bound sliceCells label hsliceCells with
    ⟨lineBin, hlineBin, hheavyCount, hheavyNonempty⟩
  let heavyCells := sliceCells.filter fun cell => label cell = lineBin
  have hslopeEq : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      window.windowed.global.extendedSlope z = source.globalGrains.slope z := by
    intro z hz
    rw [window.windowed.global.extendedSlope_eq z hz, window.sourceSlope_eq]
  have hglobalBinCount : (globalBins.card : ENNReal) ≤
      132 * (10 * Kakeya.realRpowENN delta (-inputLoss)) *
        Kakeya.realRpowENN (1 / delta) (1 - sigma) := by
    have hbins := wz1_lemma23_exactSlice_global_bin_count_of_exact_paper_window
      window.shading source.extremal.delta_pos le_rfl
      source.extremal.delta_le_one hcoord
      source.globalGrains.slope window.windowed.global.extendedSlope
      window.windowed.global.extendedSlope_lipschitz
      window.windowed.global.extendedSlope_bounded hslopeEq
      (by
        intro z hz
        exact (prepared.exactAD_delta z hz).mono (by
          rintro value ⟨point, hp, rfl⟩
          exact ⟨point, ⟨hunionSub hp.1, hp.2⟩, rfl⟩)) lineHeight
    simpa [globalBins, sliceCells, label, wz1Lemma23ExactSliceGlobalValues,
      wz1Lemma23ScalarBins, Finset.image_image, Function.comp_def] using hbins
  let lineCell := Classical.choose hheavyNonempty
  have hlineCell : lineCell ∈ heavyCells := Classical.choose_spec hheavyNonempty
  have hheavySubset : heavyCells ⊆ sliceCells := Finset.filter_subset _ _
  let representative (cell : ℤ × ℤ × ℤ) : Point3 :=
    if hcell : cell ∈ heavyCells then
      wz1Lemma23LiftSlicePoint lineHeight
        (wz1Lemma23ExactSliceRepresentative window.shading
          source.extremal.delta_pos lineHeight
          ⟨cell, hheavySubset hcell⟩) else 0
  have hrepEq : ∀ cell (hcell : cell ∈ heavyCells), representative cell =
      wz1Lemma23LiftSlicePoint lineHeight
        (wz1Lemma23ExactSliceRepresentative window.shading
          source.extremal.delta_pos lineHeight
          ⟨cell, hheavySubset hcell⟩) := by
    intro cell hcell; simp [representative, hcell]
  have hrepMem : ∀ cell (hcell : cell ∈ heavyCells),
      representative cell ∈ window.shading.union := by
    intro cell hcell
    rw [hrepEq cell hcell]
    exact wz1Lemma23ExactSliceRepresentative_mem_union window.shading
      source.extremal.delta_pos
      lineHeight ⟨cell, hheavySubset hcell⟩
  have hrepHeight : ∀ cell (hcell : cell ∈ heavyCells),
      representative cell (2 : Fin 3) = lineHeight := by
    intro cell hcell
    rw [hrepEq cell hcell]
    simp [wz1Lemma23LiftSlicePoint, point3]
  have hrepIndex : ∀ cell (hcell : cell ∈ heavyCells),
      wz1Lemma23CellIndex delta (representative cell) = cell := by
    intro cell hcell
    rw [hrepEq cell hcell]
    exact wz1Lemma23ExactSliceRepresentative_index window.shading
      source.extremal.delta_pos
      lineHeight ⟨cell, hheavySubset hcell⟩
  let lineAnchor := representative lineCell
  let lineLevel := inner ℝ lineAnchor
    (globalGrainDirection (source.globalGrains.slope lineHeight))
  have hnear : ∀ cell (hcell : cell ∈ heavyCells),
      |inner ℝ (representative cell)
          (globalGrainDirection (source.globalGrains.slope lineHeight)) -
        lineLevel| ≤ 9 * delta := by
    intro cell hcell
    let point := representative cell
    let anchor := lineAnchor
    let coordinate : Point3 → ℝ := fun p =>
      wz1Lemma23GlobalCoordinate window.windowed.global.extendedSlope p
    have hpHeight := hrepHeight cell hcell
    have haHeight := hrepHeight lineCell hlineCell
    have hpIndex := hrepIndex cell hcell
    have haIndex := hrepIndex lineCell hlineCell
    have hpSnap := wz1Lemma23_globalCoordinate_snap_of_coord_bound
      source.extremal.delta_pos source.extremal.delta_le_one
      window.windowed.global.extendedSlope
      window.windowed.global.extendedSlope_lipschitz
      window.windowed.global.extendedSlope_bounded point
      (hcoord point (hrepMem cell hcell))
    have haSnap := wz1Lemma23_globalCoordinate_snap_of_coord_bound
      source.extremal.delta_pos source.extremal.delta_le_one
      window.windowed.global.extendedSlope
      window.windowed.global.extendedSlope_lipschitz
      window.windowed.global.extendedSlope_bounded anchor
      (hcoord anchor (hrepMem lineCell hlineCell))
    have hcenter : |coordinate (wz1Lemma23CellCenter delta cell) -
        coordinate (wz1Lemma23CellCenter delta lineCell)| < delta := by
      apply wz1Lemma23_abs_sub_lt_of_floor_div_eq source.extremal.delta_pos
      simpa [label, coordinate] using
        (Finset.mem_filter.mp hcell).2.trans
          (Finset.mem_filter.mp hlineCell).2.symm
    have hpCoord : coordinate point = inner ℝ point
        (globalGrainDirection (source.globalGrains.slope lineHeight)) := by
      simp only [coordinate, wz1Lemma23GlobalCoordinate]
      rw [hpHeight, hslopeEq lineHeight hlineHeight]
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    have haCoord : coordinate anchor = lineLevel := by
      change coordinate lineAnchor = lineLevel
      dsimp only [lineLevel]
      simp only [coordinate, wz1Lemma23GlobalCoordinate]
      rw [haHeight, hslopeEq lineHeight hlineHeight]
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    have hpSnapEq : wz1Lemma23Snap delta point =
        wz1Lemma23CellCenter delta cell := by
      change wz1Lemma23Snap delta (representative cell) = _
      simp [wz1Lemma23Snap, hpIndex]
    have haSnapEq : wz1Lemma23Snap delta anchor =
        wz1Lemma23CellCenter delta lineCell := by
      change wz1Lemma23Snap delta (representative lineCell) = _
      simp [wz1Lemma23Snap, haIndex]
    rw [hpSnapEq] at hpSnap
    rw [haSnapEq] at haSnap
    rw [← hpCoord, ← haCoord]
    have htriangle := abs_sub_le (coordinate point)
      (coordinate (wz1Lemma23CellCenter delta cell))
      (coordinate anchor)
    have htriangle2 := abs_sub_le
      (coordinate (wz1Lemma23CellCenter delta cell))
      (coordinate (wz1Lemma23CellCenter delta lineCell))
      (coordinate anchor)
    have hpointBound :
        |coordinate point - coordinate (wz1Lemma23CellCenter delta cell)| ≤
          4 * delta := by simpa [coordinate] using hpSnap
    have hanchorBound :
        |coordinate (wz1Lemma23CellCenter delta lineCell) - coordinate anchor| ≤
          4 * delta := by simpa [coordinate, abs_sub_comm] using haSnap
    exact htriangle.trans (by
      linarith [htriangle2, hpointBound, hanchorBound, hcenter.le])
  exact ⟨{
    rho_pos := hrho
    lineHeight := lineHeight
    lineHeight_mem := hlineHeight
    sliceCells := sliceCells
    sliceCells_eq := rfl
    slice_area_lower := hsliceArea
    sliceCells_nonempty := hsliceCells
    globalBins := globalBins
    globalBins_eq := rfl
    global_bin_count := hglobalBinCount
    lineBin := lineBin
    lineBin_mem := hlineBin
    heavyCells := heavyCells
    heavyCells_eq := rfl
    heavyCells_subset := hheavySubset
    heavyCells_nonempty := hheavyNonempty
    heavy_cell_count := hheavyCount
    representative := representative
    representative_eq := hrepEq
    representative_mem := hrepMem
    representative_height := hrepHeight
    representative_index := hrepIndex
    lineCell := lineCell
    lineCell_mem := hlineCell
    lineAnchor := lineAnchor
    lineAnchor_eq := rfl
    lineAnchor_mem := hrepMem lineCell hlineCell
    lineAnchor_height := hrepHeight lineCell hlineCell
    lineLevel := lineLevel
    lineLevel_eq := rfl
    heavy_representative_near_line := hnear
  }⟩

end Kakeya.Assouad
