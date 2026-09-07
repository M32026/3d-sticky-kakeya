import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceHorizontalFixedLine

/-!
# All global-bin fibres on one source-horizontal slice

The ordinary source-horizontal fixed line uses exact `delta`-scale slice
cells inside a `sqrt rho` source window.  This file records every nonempty
global-bin fibre of that exact slice, without importing the carrier-generic
`PureWZ2HorizontalFixedBinCore`, whose slice grid is at scale `rho`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- One nonempty source-horizontal global-bin fibre on the exact
`delta`-scale Fubini slice.  It deliberately omits the largest-fibre
cardinality estimate. -/
structure PureWZ2SourceHorizontalFixedBinData
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
    volume window.shading.union /
        ENNReal.ofReal (Real.sqrt rho + 2 * rho) ≤
      volume (wz1Lemma23PlanarSlice window.shading.union lineHeight)
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
      |inner ℝ (representative cell)
          (globalGrainDirection (source.globalGrains.slope lineHeight)) -
        lineLevel| ≤ 9 * delta

/-- Forget only the maximal-fibre cardinality inequality. -/
abbrev PureWZ2SourceHorizontalFixedLineData.toFixedBinData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window) :
    PureWZ2SourceHorizontalFixedBinData window :=
  { rho_pos := line.rho_pos
    lineHeight := line.lineHeight
    lineHeight_mem := line.lineHeight_mem
    sliceCells := line.sliceCells
    sliceCells_eq := line.sliceCells_eq
    slice_area_lower := line.slice_area_lower
    sliceCells_nonempty := line.sliceCells_nonempty
    globalBins := line.globalBins
    globalBins_eq := line.globalBins_eq
    global_bin_count := line.global_bin_count
    lineBin := line.lineBin
    lineBin_mem := line.lineBin_mem
    heavyCells := line.heavyCells
    heavyCells_eq := line.heavyCells_eq
    heavyCells_subset := line.heavyCells_subset
    heavyCells_nonempty := line.heavyCells_nonempty
    representative := line.representative
    representative_eq := line.representative_eq
    representative_mem := line.representative_mem
    representative_height := line.representative_height
    representative_index := line.representative_index
    lineCell := line.lineCell
    lineCell_mem := line.lineCell_mem
    lineAnchor := line.lineAnchor
    lineAnchor_eq := line.lineAnchor_eq
    lineAnchor_mem := line.lineAnchor_mem
    lineAnchor_height := line.lineAnchor_height
    lineLevel := line.lineLevel
    lineLevel_eq := line.lineLevel_eq
    heavy_representative_near_line := line.heavy_representative_near_line }

instance PureWZ2SourceHorizontalFixedLineData.instCoeFixedBinData
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared} :
    Coe (PureWZ2SourceHorizontalFixedLineData window)
      (PureWZ2SourceHorizontalFixedBinData window) :=
  ⟨PureWZ2SourceHorizontalFixedLineData.toFixedBinData⟩

def pureWZ2SourceHorizontalGlobalBinLabel
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    (cell : ℤ × ℤ × ℤ) : ℤ :=
  Int.floor (wz1Lemma23GlobalCoordinate window.windowed.global.extendedSlope
    (wz1Lemma23CellCenter delta cell) / delta)

def pureWZ2SourceHorizontalGlobalBinCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    (bin : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  line.sliceCells.filter fun cell =>
    pureWZ2SourceHorizontalGlobalBinLabel line cell = bin

theorem pureWZ2SourceHorizontalGlobalBinCells_subset
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    (bin : ℤ) :
    pureWZ2SourceHorizontalGlobalBinCells line bin ⊆ line.sliceCells :=
  Finset.filter_subset _ _

theorem pureWZ2SourceHorizontalGlobalBinCells_nonempty
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    {bin : ℤ} (hbin : bin ∈ line.globalBins) :
    (pureWZ2SourceHorizontalGlobalBinCells line bin).Nonempty := by
  rw [line.globalBins_eq] at hbin
  rcases Finset.mem_image.mp hbin with ⟨cell, hcell, hlabel⟩
  refine ⟨cell, Finset.mem_filter.mpr ⟨hcell, ?_⟩⟩
  simpa [pureWZ2SourceHorizontalGlobalBinLabel] using hlabel

theorem pureWZ2SourceHorizontalGlobalBinCells_lineBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window) :
    pureWZ2SourceHorizontalGlobalBinCells line line.lineBin = line.heavyCells := by
  rw [line.heavyCells_eq]
  rfl

theorem PureWZ2SourceHorizontalFixedLineData.card_eq_sum_globalBinCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window) :
    line.sliceCells.card =
      ∑ bin ∈ line.globalBins,
        (pureWZ2SourceHorizontalGlobalBinCells line bin).card := by
  let label : (ℤ × ℤ × ℤ) → ℤ :=
    pureWZ2SourceHorizontalGlobalBinLabel line
  have hmaps : Set.MapsTo label
      (line.sliceCells : Set (ℤ × ℤ × ℤ))
      (line.globalBins : Set ℤ) := by
    intro cell hcell
    rw [line.globalBins_eq]
    exact Finset.mem_image.mpr ⟨cell, hcell, rfl⟩
  simpa [label, pureWZ2SourceHorizontalGlobalBinCells] using
    Finset.card_eq_sum_card_fiberwise hmaps

theorem PureWZ2SourceHorizontalFixedLineData.enncard_eq_sum_globalBinCells
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window) :
    (line.sliceCells.card : ENNReal) =
      ∑ bin ∈ line.globalBins,
        ((pureWZ2SourceHorizontalGlobalBinCells line bin).card : ENNReal) := by
  exact_mod_cast line.card_eq_sum_globalBinCells

theorem PureWZ2SourceHorizontalFixedLineData.coreAtGlobalBin
    {sigma inputLoss delta rho middleLoss outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {twoScale : PureWZ2OneScaleTwoScaleStickyData
      source rho middleLoss outputLoss logExponent}
    {pullback : PureWZ2TwoScaleCellPullbackData twoScale}
    {prepared : PureWZ2SourceCarrierPreparation pullback}
    {window : PureWZ2SourceCarrierWindow prepared}
    (line : PureWZ2SourceHorizontalFixedLineData window)
    (bin : ℤ) (hbin : bin ∈ line.globalBins) :
    ∃ core : PureWZ2SourceHorizontalFixedBinData window,
      core.lineBin = bin ∧
        core.heavyCells = pureWZ2SourceHorizontalGlobalBinCells line bin := by
  let heavyCells := pureWZ2SourceHorizontalGlobalBinCells line bin
  have hheavyNonempty : heavyCells.Nonempty :=
    pureWZ2SourceHorizontalGlobalBinCells_nonempty line hbin
  have hheavySubset : heavyCells ⊆ line.sliceCells :=
    pureWZ2SourceHorizontalGlobalBinCells_subset line bin
  let lineCell := Classical.choose hheavyNonempty
  have hlineCell : lineCell ∈ heavyCells := Classical.choose_spec hheavyNonempty
  let representative (cell : ℤ × ℤ × ℤ) : Point3 :=
    if hcell : cell ∈ heavyCells then
      wz1Lemma23LiftSlicePoint line.lineHeight
        (wz1Lemma23ExactSliceRepresentative window.shading
          source.extremal.delta_pos line.lineHeight ⟨cell, by
            simpa [line.sliceCells_eq] using hheavySubset hcell⟩)
    else 0
  have hrepEq : ∀ cell (hcell : cell ∈ heavyCells), representative cell =
      wz1Lemma23LiftSlicePoint line.lineHeight
        (wz1Lemma23ExactSliceRepresentative window.shading
          source.extremal.delta_pos line.lineHeight ⟨cell, by
            simpa [line.sliceCells_eq] using hheavySubset hcell⟩) := by
    intro cell hcell
    simp [representative, hcell]
  have hrepMem : ∀ cell (hcell : cell ∈ heavyCells),
      representative cell ∈ window.shading.union := by
    intro cell hcell
    rw [hrepEq cell hcell]
    exact wz1Lemma23ExactSliceRepresentative_mem_union window.shading
      source.extremal.delta_pos line.lineHeight ⟨cell, by
        simpa [line.sliceCells_eq] using hheavySubset hcell⟩
  have hrepHeight : ∀ cell (hcell : cell ∈ heavyCells),
      representative cell (2 : Fin 3) = line.lineHeight := by
    intro cell hcell
    rw [hrepEq cell hcell]
    simp [wz1Lemma23LiftSlicePoint, point3]
  have hrepIndex : ∀ cell (hcell : cell ∈ heavyCells),
      wz1Lemma23CellIndex delta (representative cell) = cell := by
    intro cell hcell
    rw [hrepEq cell hcell]
    exact wz1Lemma23ExactSliceRepresentative_index window.shading
      source.extremal.delta_pos line.lineHeight ⟨cell, by
        simpa [line.sliceCells_eq] using hheavySubset hcell⟩
  let lineAnchor := representative lineCell
  let lineLevel := inner ℝ lineAnchor
    (globalGrainDirection (source.globalGrains.slope line.lineHeight))
  have hslopeEq : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      window.windowed.global.extendedSlope z = source.globalGrains.slope z := by
    intro z hz
    rw [window.windowed.global.extendedSlope_eq z hz, window.sourceSlope_eq]
  have hcoord : ∀ point ∈ window.shading.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hpull : point ∈ pullback.shading.union := by
      rw [← prepared.shadow_union]
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨index, window.subshading index hindex⟩
    have hbox := shading_union_subset_axisBox hpull
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  have hnear : ∀ cell (hcell : cell ∈ heavyCells),
      |inner ℝ (representative cell)
          (globalGrainDirection (source.globalGrains.slope line.lineHeight)) -
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
      (hcoord point (by
        rw [show point = representative cell by rfl]
        exact hrepMem cell hcell))
    have haSnap := wz1Lemma23_globalCoordinate_snap_of_coord_bound
      source.extremal.delta_pos source.extremal.delta_le_one
      window.windowed.global.extendedSlope
      window.windowed.global.extendedSlope_lipschitz
      window.windowed.global.extendedSlope_bounded anchor
      (hcoord anchor (by
        rw [show anchor = representative lineCell by rfl]
        exact hrepMem lineCell hlineCell))
    have hcenter : |coordinate (wz1Lemma23CellCenter delta cell) -
        coordinate (wz1Lemma23CellCenter delta lineCell)| < delta := by
      apply wz1Lemma23_abs_sub_lt_of_floor_div_eq source.extremal.delta_pos
      have hcellBin := (Finset.mem_filter.mp hcell).2
      have hlineBin := (Finset.mem_filter.mp hlineCell).2
      simpa [heavyCells, pureWZ2SourceHorizontalGlobalBinCells,
        pureWZ2SourceHorizontalGlobalBinLabel, coordinate] using
        hcellBin.trans hlineBin.symm
    have hpCoord : coordinate point = inner ℝ point
        (globalGrainDirection (source.globalGrains.slope line.lineHeight)) := by
      simp only [coordinate, wz1Lemma23GlobalCoordinate]
      rw [hpHeight, hslopeEq line.lineHeight line.lineHeight_mem]
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    have haCoord : coordinate anchor = lineLevel := by
      change coordinate lineAnchor = lineLevel
      dsimp only [lineLevel]
      simp only [coordinate, wz1Lemma23GlobalCoordinate]
      rw [haHeight, hslopeEq line.lineHeight line.lineHeight_mem]
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
      (coordinate (wz1Lemma23CellCenter delta cell)) (coordinate anchor)
    have htriangle2 := abs_sub_le
      (coordinate (wz1Lemma23CellCenter delta cell))
      (coordinate (wz1Lemma23CellCenter delta lineCell)) (coordinate anchor)
    have hpointBound :
        |coordinate point - coordinate (wz1Lemma23CellCenter delta cell)| ≤
          4 * delta := by
      simpa [coordinate] using hpSnap
    have hanchorBound :
        |coordinate (wz1Lemma23CellCenter delta lineCell) - coordinate anchor| ≤
          4 * delta := by
      simpa [coordinate, abs_sub_comm] using haSnap
    exact htriangle.trans (by
      linarith [htriangle2, hpointBound, hanchorBound, hcenter.le])
  refine ⟨{
    rho_pos := line.rho_pos
    lineHeight := line.lineHeight
    lineHeight_mem := line.lineHeight_mem
    sliceCells := line.sliceCells
    sliceCells_eq := line.sliceCells_eq
    slice_area_lower := line.slice_area_lower
    sliceCells_nonempty := line.sliceCells_nonempty
    globalBins := line.globalBins
    globalBins_eq := line.globalBins_eq
    global_bin_count := line.global_bin_count
    lineBin := bin
    lineBin_mem := hbin
    heavyCells := heavyCells
    heavyCells_eq := rfl
    heavyCells_subset := hheavySubset
    heavyCells_nonempty := hheavyNonempty
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
    heavy_representative_near_line := hnear }, rfl, rfl⟩

end Kakeya.Assouad
