import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.CoarseGlobalPreparation
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ExactSliceGlobalBins

/-!
# Horizontal fixed global line from one genuine high slice

The second sticky parent is a vertical coarse tube and is not the fixed line
used in WZ Lemma 23.  This module makes the paper selection literally: first
choose a high-area exact horizontal slice of the retained coarse carrier,
then choose a largest occupied global-projection `rho`-bin on that slice.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- A largest fiber of a map on a nonempty finset carries the average share. -/
lemma finset_exists_max_fiber_with_product_bound
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (cells : Finset α) (label : α → β)
    (hcells : cells.Nonempty) :
    ∃ value ∈ cells.image label,
      cells.card ≤
        (cells.image label).card *
          (cells.filter fun cell => label cell = value).card ∧
      (cells.filter fun cell => label cell = value).Nonempty := by
  let values := cells.image label
  let fiber (value : β) := cells.filter fun cell => label cell = value
  have hvalues : values.Nonempty := hcells.image label
  rcases Finset.exists_max_image values (fun value => (fiber value).card) hvalues with
    ⟨value, hvalue, hmax⟩
  have hmaps : Set.MapsTo label (cells : Set α) (values : Set β) :=
    fun cell hcell => Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
  have hsum : cells.card = ∑ other ∈ values, (fiber other).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hbound :
      cells.card ≤ values.card * (fiber value).card := by
    calc
      cells.card = ∑ other ∈ values, (fiber other).card := hsum
      _ ≤ ∑ _other ∈ values, (fiber value).card := by
        exact Finset.sum_le_sum fun other hother => hmax other hother
      _ = values.card * (fiber value).card := by
        simp [Finset.sum_const]
  have hfiber : (fiber value).Nonempty := by
    rcases Finset.mem_image.mp hvalue with ⟨cell, hcell, hlabel⟩
    exact ⟨cell, Finset.mem_filter.mpr ⟨hcell, hlabel⟩⟩
  exact ⟨value, hvalue, hbound, hfiber⟩

/--
The genuine horizontal line selected from a high exact slice and a largest
global AD bin.  Only the exact-slice representatives in the selected bin are
asserted to lie near the line; no vertical sticky parent is reinterpreted as
this horizontal object.
-/
structure PureWZ2HorizontalFixedLineData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (windowed : PureWZ2Lemma23WindowedCoarse prepared) where
  lineHeight : ℝ
  lineHeight_mem : lineHeight ∈ Set.Icc (-1 : ℝ) 1
  sliceCells : Finset (ℤ × ℤ × ℤ)
  sliceCells_eq :
    sliceCells =
      wz1Lemma23ExactSliceCells windowed.shading
        twoScale.rhoRequested.1
        twoScale.coarseGrains.extremal.delta_pos lineHeight
  slice_area_lower :
    MeasureTheory.volume windowed.shading.union /
        ENNReal.ofReal
          (Real.sqrt twoScale.rhoRequested.1 +
            2 * twoScale.rhoRequested.1) ≤
      MeasureTheory.volume
        (wz1Lemma23PlanarSlice windowed.shading.union lineHeight)
  sliceCells_nonempty : sliceCells.Nonempty
  globalBins : Finset ℤ
  globalBins_eq :
    globalBins = sliceCells.image fun cell =>
      Int.floor
        (wz1Lemma23GlobalCoordinate
            windowed.windowed.global.extendedSlope
            (wz1Lemma23CellCenter twoScale.rhoRequested.1 cell) /
          twoScale.rhoRequested.1)
  global_bin_count :
    (globalBins.card : ENNReal) ≤
      132 *
        (10 * Kakeya.realRpowENN
          twoScale.rhoRequested.1 (-middleLoss)) *
        Kakeya.realRpowENN
          (1 / twoScale.rhoRequested.1) (1 - sigma)
  lineBin : ℤ
  lineBin_mem : lineBin ∈ globalBins
  heavyCells : Finset (ℤ × ℤ × ℤ)
  heavyCells_eq :
    heavyCells = sliceCells.filter fun cell =>
      Int.floor
        (wz1Lemma23GlobalCoordinate
            windowed.windowed.global.extendedSlope
            (wz1Lemma23CellCenter twoScale.rhoRequested.1 cell) /
          twoScale.rhoRequested.1) = lineBin
  heavyCells_subset : heavyCells ⊆ sliceCells
  heavyCells_nonempty : heavyCells.Nonempty
  heavy_cell_count :
    sliceCells.card ≤ globalBins.card * heavyCells.card
  representative : (ℤ × ℤ × ℤ) → Point3
  representative_eq :
    ∀ cell (hcell : cell ∈ heavyCells),
      representative cell =
        wz1Lemma23LiftSlicePoint lineHeight
          (wz1Lemma23ExactSliceRepresentative windowed.shading
            twoScale.coarseGrains.extremal.delta_pos lineHeight
            ⟨cell, by
              simpa [sliceCells_eq] using heavyCells_subset hcell⟩)
  representative_mem :
    ∀ cell ∈ heavyCells, representative cell ∈ windowed.shading.union
  representative_height :
    ∀ cell ∈ heavyCells,
      representative cell (2 : Fin 3) = lineHeight
  representative_index :
    ∀ cell ∈ heavyCells,
      wz1Lemma23CellIndex twoScale.rhoRequested.1
        (representative cell) = cell
  lineCell : ℤ × ℤ × ℤ
  lineCell_mem : lineCell ∈ heavyCells
  lineAnchor : Point3
  lineAnchor_eq :
    lineAnchor = representative lineCell
  lineAnchor_mem : lineAnchor ∈ windowed.shading.union
  lineAnchor_height : lineAnchor (2 : Fin 3) = lineHeight
  lineLevel : ℝ
  lineLevel_eq :
    lineLevel =
      inner ℝ lineAnchor
        (globalGrainDirection
          (twoScale.coarseGrains.globalGrains.slope lineHeight))
  heavy_representative_near_line :
    ∀ cell (hcell : cell ∈ heavyCells),
      let point := representative cell
      |inner ℝ point
          (globalGrainDirection
            (twoScale.coarseGrains.globalGrains.slope lineHeight)) -
        lineLevel| ≤ 9 * twoScale.rhoRequested.1

/-- Select the paper's horizontal fixed line on the genuine coarse carrier. -/
theorem PureWZ2Lemma23WindowedCoarse.selectHorizontalFixedLine
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale :
      PureWZ2OneScaleTwoScaleStickyData
        source rho middleLoss outputLoss logExponent}
    {prepared : PureWZ2Lemma23PreparedCoarse twoScale}
    (windowed : PureWZ2Lemma23WindowedCoarse prepared)
    (hvolume : 0 < MeasureTheory.volume windowed.shading.union) :
    Nonempty (PureWZ2HorizontalFixedLineData windowed) := by
  let scale := twoScale.rhoRequested.1
  have hscale : 0 < scale := twoScale.coarseGrains.extremal.delta_pos
  have hscaleOne : scale ≤ 1 := twoScale.rhoRequested.property.2
  have hunionSub : windowed.shading.union ⊆ prepared.shadow.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, windowed.subshading index hpoint⟩
  have hcoord :
      ∀ point ∈ windowed.shading.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hfine : point ∈ twoScale.fine.refined.union := by
      rw [← prepared.shadow_union]
      exact hunionSub hpoint
    rcases hfine with ⟨index, hindex⟩
    have hsource : point ∈ twoScale.coarseGrains.shading.union :=
      ⟨twoScale.fine.selected.embedding index,
        twoScale.fine.subshading index hindex⟩
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hheight :
      ∀ point ∈ windowed.shading.union,
        |point (2 : Fin 3)| ≤ 1 :=
    fun point hpoint => hcoord point hpoint 2
  have hmeas : MeasurableSet windowed.shading.union :=
    measurableSet_shading_union windowed.shading
  have hfinite : MeasureTheory.volume windowed.shading.union ≠ ⊤ := by
    have hbox :
        windowed.shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
      intro point hpoint
      have hfine : point ∈ twoScale.fine.refined.union := by
        rw [← prepared.shadow_union]
        exact hunionSub hpoint
      rcases hfine with ⟨index, hindex⟩
      have hsource : point ∈ twoScale.coarseGrains.shading.union :=
        ⟨twoScale.fine.selected.embedding index,
          twoScale.fine.subshading index hindex⟩
      have hnorm := norm_le_two_of_mem_paperShading hsource
      simpa [Metric.mem_closedBall, dist_zero_right] using hnorm
    exact ne_top_of_le_ne_top
      (Metric.isBounded_closedBall.measure_lt_top).ne
      (MeasureTheory.measure_mono hbox)
  let slabLeft := windowed.left - scale
  let slabRight := windowed.left + Real.sqrt scale + scale
  have hslab :
      windowed.shading.union ⊆
        {point : Point3 | point (2 : Fin 3) ∈ Set.Ico slabLeft slabRight} := by
    intro point hpoint
    simpa [slabLeft, slabRight, scale] using
      windowed.union_height_window point hpoint
  have hslabLength :
      slabRight - slabLeft = Real.sqrt scale + 2 * scale := by
    dsimp only [slabLeft, slabRight]
    ring
  have hslabNondegenerate : slabLeft < slabRight := by
    rw [sub_lt_iff_lt_add, show slabRight + scale =
      windowed.left + Real.sqrt scale + 2 * scale by
        dsimp only [slabRight]; ring]
    have hsqrt : 0 < Real.sqrt scale := Real.sqrt_pos.mpr hscale
    linarith
  rcases
      wz1_lemma23_exists_good_height_in_slab
        hmeas hfinite hslabNondegenerate with
    ⟨lineHeight, hlineHeightSlab, hsliceAreaRaw⟩
  have hinter :
      windowed.shading.union ∩
          {point : Point3 | point (2 : Fin 3) ∈ Set.Ico slabLeft slabRight} =
        windowed.shading.union := by
    exact Set.inter_eq_left.mpr hslab
  have hsliceArea :
      MeasureTheory.volume windowed.shading.union /
          ENNReal.ofReal (Real.sqrt scale + 2 * scale) ≤
        MeasureTheory.volume
          (wz1Lemma23PlanarSlice windowed.shading.union lineHeight) := by
    rw [hinter, hslabLength] at hsliceAreaRaw
    exact hsliceAreaRaw
  have hlineHeight : lineHeight ∈ Set.Icc (-1 : ℝ) 1 := by
    have hnonzero :
        MeasureTheory.volume
            (wz1Lemma23PlanarSlice windowed.shading.union lineHeight) ≠ 0 := by
      intro hzero
      rw [hzero] at hsliceArea
      have hpositive :
          0 < MeasureTheory.volume windowed.shading.union /
            ENNReal.ofReal (Real.sqrt scale + 2 * scale) :=
        ENNReal.div_pos hvolume.ne' ENNReal.ofReal_ne_top
      exact (not_le_of_gt hpositive) hsliceArea
    have hsliceNonempty :
        (wz1Lemma23PlanarSlice windowed.shading.union lineHeight).Nonempty := by
      by_contra hempty
      have hemptyEq := Set.not_nonempty_iff_eq_empty.mp hempty
      rw [hemptyEq] at hnonzero
      exact hnonzero (by simp)
    rcases hsliceNonempty with ⟨point, hpoint⟩
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have hcoordHeight := hheight
      (point3 (point 0) (point 1) lineHeight) hlift
    simpa [point3] using abs_le.mp hcoordHeight
  let sliceCells :=
    wz1Lemma23ExactSliceCells windowed.shading scale hscale lineHeight
  have hsliceCells : sliceCells.Nonempty := by
    by_contra hempty
    have hzero :
        MeasureTheory.volume
            (wz1Lemma23PlanarSlice windowed.shading.union lineHeight) = 0 := by
      have hcover := wz1_lemma23_exactSlice_area_le_two
        windowed.shading hscale
        (by
          intro point hpoint
          have hfine : point ∈ twoScale.fine.refined.union := by
            rw [← prepared.shadow_union]
            exact hunionSub hpoint
          rcases hfine with ⟨index, hindex⟩
          have hsource : point ∈ twoScale.coarseGrains.shading.union :=
            ⟨twoScale.fine.selected.embedding index,
              twoScale.fine.subshading index hindex⟩
          have hnorm := norm_le_two_of_mem_paperShading hsource
          simpa [Metric.mem_closedBall, dist_zero_right] using hnorm)
        lineHeight
      have hcellsEmpty : sliceCells = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hempty
      simpa [sliceCells, hcellsEmpty] using hcover
    have hhalf :
        0 < MeasureTheory.volume windowed.shading.union /
          ENNReal.ofReal (Real.sqrt scale + 2 * scale) :=
      ENNReal.div_pos hvolume.ne' ENNReal.ofReal_ne_top
    rw [hzero] at hsliceArea
    exact (not_le_of_gt hhalf) hsliceArea
  let label : (ℤ × ℤ × ℤ) → ℤ := fun cell =>
    Int.floor
      (wz1Lemma23GlobalCoordinate
          windowed.windowed.global.extendedSlope
          (wz1Lemma23CellCenter scale cell) / scale)
  let globalBins := sliceCells.image label
  rcases finset_exists_max_fiber_with_product_bound
      sliceCells label hsliceCells with
    ⟨lineBin, hlineBin, hheavyCount, hheavyNonempty⟩
  let heavyCells := sliceCells.filter fun cell => label cell = lineBin
  have hglobalAD :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        IsADSet1
          (scalarProjection
            (globalGrainDirection
              (twoScale.coarseGrains.globalGrains.slope z))
            (horizontalSlice windowed.shading.union z))
          scale (1 - sigma)
          (10 * Kakeya.realRpowENN scale (-middleLoss)) := by
    intro z hz
    exact (prepared.exactAD z hz).mono (by
      rintro value ⟨point, hpoint, rfl⟩
      exact ⟨point, ⟨hunionSub hpoint.1, hpoint.2⟩, rfl⟩)
  have hslopeEq :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        windowed.windowed.global.extendedSlope z =
          twoScale.coarseGrains.globalGrains.slope z := by
    intro z hz
    rw [windowed.windowed.global.extendedSlope_eq z hz,
      windowed.sourceSlope_eq]
  have hglobalBinCount :
      (globalBins.card : ENNReal) ≤
        132 * (10 * Kakeya.realRpowENN scale (-middleLoss)) *
          Kakeya.realRpowENN (1 / scale) (1 - sigma) := by
    have hbins :=
      wz1_lemma23_exactSlice_global_bin_count_of_exact_paper_window
        windowed.shading hscale le_rfl hscaleOne hcoord
        twoScale.coarseGrains.globalGrains.slope
        windowed.windowed.global.extendedSlope
        windowed.windowed.global.extendedSlope_lipschitz
        windowed.windowed.global.extendedSlope_bounded
        hslopeEq hglobalAD lineHeight
    simpa [globalBins, sliceCells, label,
      wz1Lemma23ExactSliceGlobalValues, wz1Lemma23ScalarBins,
      Finset.image_image, Function.comp_def] using hbins
  let lineCell := Classical.choose hheavyNonempty
  have hlineCell : lineCell ∈ heavyCells :=
    Classical.choose_spec hheavyNonempty
  have hheavySubset : heavyCells ⊆ sliceCells :=
    Finset.filter_subset _ _
  let representative (cell : ℤ × ℤ × ℤ) : Point3 :=
    if hcell : cell ∈ heavyCells then
      wz1Lemma23LiftSlicePoint lineHeight
        (wz1Lemma23ExactSliceRepresentative windowed.shading hscale lineHeight
          ⟨cell, hheavySubset hcell⟩)
    else 0
  have hrepresentativeEq :
      ∀ cell (hcell : cell ∈ heavyCells),
        representative cell =
          wz1Lemma23LiftSlicePoint lineHeight
            (wz1Lemma23ExactSliceRepresentative windowed.shading hscale lineHeight
              ⟨cell, hheavySubset hcell⟩) := by
    intro cell hcell
    simp [representative, hcell]
  let lineAnchor := representative lineCell
  have hrepresentativeMem :
      ∀ cell (hcell : cell ∈ heavyCells),
        representative cell ∈ windowed.shading.union := by
    intro cell hcell
    rw [hrepresentativeEq cell hcell]
    exact wz1Lemma23ExactSliceRepresentative_mem_union
      windowed.shading hscale lineHeight ⟨cell, hheavySubset hcell⟩
  have hrepresentativeHeight :
      ∀ cell (hcell : cell ∈ heavyCells),
        representative cell (2 : Fin 3) = lineHeight := by
    intro cell hcell
    rw [hrepresentativeEq cell hcell]
    simp [wz1Lemma23LiftSlicePoint, point3]
  have hrepresentativeIndex :
      ∀ cell (hcell : cell ∈ heavyCells),
        wz1Lemma23CellIndex scale (representative cell) = cell := by
    intro cell hcell
    rw [hrepresentativeEq cell hcell]
    exact wz1Lemma23ExactSliceRepresentative_index
      windowed.shading hscale lineHeight ⟨cell, hheavySubset hcell⟩
  let lineLevel :=
    inner ℝ lineAnchor
      (globalGrainDirection
        (twoScale.coarseGrains.globalGrains.slope lineHeight))
  have hnear :
      ∀ cell (hcell : cell ∈ heavyCells),
        |inner ℝ (representative cell)
              (globalGrainDirection
                (twoScale.coarseGrains.globalGrains.slope lineHeight)) -
            lineLevel| ≤ 9 * scale := by
    intro cell hcell
    let point := representative cell
    let anchor := lineAnchor
    let coordinate : Point3 → ℝ := fun p =>
      wz1Lemma23GlobalCoordinate
        windowed.windowed.global.extendedSlope p
    have hpointHeight : point (2 : Fin 3) = lineHeight :=
      hrepresentativeHeight cell hcell
    have hanchorHeight : anchor (2 : Fin 3) = lineHeight :=
      hrepresentativeHeight lineCell hlineCell
    have hpointIndex : wz1Lemma23CellIndex scale point = cell := by
      exact hrepresentativeIndex cell hcell
    have hanchorIndex : wz1Lemma23CellIndex scale anchor = lineCell := by
      exact hrepresentativeIndex lineCell hlineCell
    have hsnapPoint :
        wz1Lemma23Snap scale point = wz1Lemma23CellCenter scale cell := by
      simp [wz1Lemma23Snap, hpointIndex]
    have hsnapAnchor :
        wz1Lemma23Snap scale anchor = wz1Lemma23CellCenter scale lineCell := by
      simp [wz1Lemma23Snap, hanchorIndex]
    have hpointSnap :=
      wz1Lemma23_globalCoordinate_snap_of_coord_bound
        hscale hscaleOne windowed.windowed.global.extendedSlope
        windowed.windowed.global.extendedSlope_lipschitz
        windowed.windowed.global.extendedSlope_bounded point
        (hcoord point (hrepresentativeMem cell hcell))
    have hanchorSnap :=
      wz1Lemma23_globalCoordinate_snap_of_coord_bound
        hscale hscaleOne windowed.windowed.global.extendedSlope
        windowed.windowed.global.extendedSlope_lipschitz
        windowed.windowed.global.extendedSlope_bounded anchor
        (hcoord anchor (hrepresentativeMem lineCell hlineCell))
    have hcellBin : label cell = lineBin :=
      (Finset.mem_filter.mp hcell).2
    have hlineCellBin : label lineCell = lineBin :=
      (Finset.mem_filter.mp hlineCell).2
    have hcenter :
        |coordinate (wz1Lemma23CellCenter scale cell) -
            coordinate (wz1Lemma23CellCenter scale lineCell)| < scale := by
      apply wz1Lemma23_abs_sub_lt_of_floor_div_eq hscale
      simpa [label, coordinate] using hcellBin.trans hlineCellBin.symm
    have hcoordinatePoint :
        coordinate point =
          inner ℝ point
            (globalGrainDirection
              (twoScale.coarseGrains.globalGrains.slope lineHeight)) := by
      simp only [coordinate, wz1Lemma23GlobalCoordinate]
      rw [hpointHeight, hslopeEq lineHeight hlineHeight]
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    have hcoordinateAnchor :
        coordinate anchor = lineLevel := by
      change coordinate lineAnchor = lineLevel
      dsimp only [lineLevel]
      simp only [coordinate, wz1Lemma23GlobalCoordinate]
      rw [hanchorHeight, hslopeEq lineHeight hlineHeight]
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    have htriangle :
        |coordinate point - coordinate anchor| ≤
          |coordinate point - coordinate (wz1Lemma23CellCenter scale cell)| +
            |coordinate (wz1Lemma23CellCenter scale cell) -
              coordinate (wz1Lemma23CellCenter scale lineCell)| +
            |coordinate (wz1Lemma23CellCenter scale lineCell) -
              coordinate anchor| := by
      calc
        |coordinate point - coordinate anchor| =
            |(coordinate point - coordinate (wz1Lemma23CellCenter scale cell)) +
              (coordinate (wz1Lemma23CellCenter scale cell) -
                coordinate (wz1Lemma23CellCenter scale lineCell)) +
              (coordinate (wz1Lemma23CellCenter scale lineCell) -
                coordinate anchor)| := by ring_nf
        _ ≤
            |(coordinate point - coordinate (wz1Lemma23CellCenter scale cell)) +
              (coordinate (wz1Lemma23CellCenter scale cell) -
                coordinate (wz1Lemma23CellCenter scale lineCell))| +
              |coordinate (wz1Lemma23CellCenter scale lineCell) -
                coordinate anchor| := abs_add_le _ _
        _ ≤
            |coordinate point - coordinate (wz1Lemma23CellCenter scale cell)| +
              |coordinate (wz1Lemma23CellCenter scale cell) -
                coordinate (wz1Lemma23CellCenter scale lineCell)| +
              |coordinate (wz1Lemma23CellCenter scale lineCell) -
                coordinate anchor| := by
          gcongr
          exact abs_add_le _ _
    rw [hsnapPoint] at hpointSnap
    rw [hsnapAnchor] at hanchorSnap
    rw [← hcoordinatePoint, ← hcoordinateAnchor]
    exact htriangle.trans (by
      have hcenterLe :
          |coordinate (wz1Lemma23CellCenter scale cell) -
            coordinate (wz1Lemma23CellCenter scale lineCell)| ≤ scale :=
        hcenter.le
      have hanchorReverse :
          |coordinate (wz1Lemma23CellCenter scale lineCell) - coordinate anchor| ≤
            4 * scale := by
        simpa [coordinate, abs_sub_comm] using hanchorSnap
      have hpointBound :
          |coordinate point - coordinate (wz1Lemma23CellCenter scale cell)| ≤
            4 * scale := by
        simpa [coordinate] using hpointSnap
      linarith)
  exact
    ⟨{ lineHeight := lineHeight
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
       representative_eq := hrepresentativeEq
       representative_mem := hrepresentativeMem
       representative_height := hrepresentativeHeight
       representative_index := hrepresentativeIndex
       lineCell := lineCell
       lineCell_mem := hlineCell
       lineAnchor := lineAnchor
       lineAnchor_eq := rfl
       lineAnchor_mem := hrepresentativeMem lineCell hlineCell
       lineAnchor_height := hrepresentativeHeight lineCell hlineCell
       lineLevel := lineLevel
       lineLevel_eq := rfl
       heavy_representative_near_line := hnear }⟩

end Kakeya.Assouad
