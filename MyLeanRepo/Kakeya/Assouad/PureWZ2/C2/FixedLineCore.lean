import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.HorizontalFixedLine
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ExactSliceGlobalBins

/-!
# Carrier-generic horizontal fixed-line selection

This is the common exact-slice Fubini and largest-global-bin argument used by
the source, coarse, and terminal Pure WZ2 pipelines.  All carrier provenance
is supplied by the caller.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- One nonempty global-bin fibre on a fixed Fubini slice.  No maximality of
the fibre is assumed; terminal endpoint arguments can therefore retain all
bins and sum their contributions. -/
structure PureWZ2HorizontalFixedBinCore
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    (windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C)
    (slope : ℝ → ℝ) where
  rho_pos : 0 < rho
  rho_le_one : rho ≤ 1
  sourceSlope_eq : windowed.global.sourceSlope = slope
  coordinate_bound :
    ∀ point ∈ shading.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1
  lineHeight : ℝ
  lineHeight_mem : lineHeight ∈ Set.Icc (-1 : ℝ) 1
  sliceCells : Finset (ℤ × ℤ × ℤ)
  sliceCells_eq : sliceCells =
    wz1Lemma23ExactSliceCells shading rho rho_pos lineHeight
  slice_area_lower :
    volume shading.union / ENNReal.ofReal (Real.sqrt rho + 2 * rho) ≤
      volume (wz1Lemma23PlanarSlice shading.union lineHeight)
  sliceCells_nonempty : sliceCells.Nonempty
  globalBins : Finset ℤ
  globalBins_eq : globalBins = sliceCells.image fun cell =>
    Int.floor (wz1Lemma23GlobalCoordinate windowed.global.extendedSlope
      (wz1Lemma23CellCenter rho cell) / rho)
  global_bin_count :
    (globalBins.card : ENNReal) ≤
      132 * C * Kakeya.realRpowENN (1 / rho) (1 - sigma)
  lineBin : ℤ
  lineBin_mem : lineBin ∈ globalBins
  heavyCells : Finset (ℤ × ℤ × ℤ)
  heavyCells_eq : heavyCells = sliceCells.filter fun cell =>
    Int.floor (wz1Lemma23GlobalCoordinate windowed.global.extendedSlope
      (wz1Lemma23CellCenter rho cell) / rho) = lineBin
  heavyCells_subset : heavyCells ⊆ sliceCells
  heavyCells_nonempty : heavyCells.Nonempty
  representative : (ℤ × ℤ × ℤ) → Point3
  representative_eq :
    ∀ cell (hcell : cell ∈ heavyCells), representative cell =
      wz1Lemma23LiftSlicePoint lineHeight
        (wz1Lemma23ExactSliceRepresentative shading rho_pos lineHeight
          ⟨cell, by simpa [sliceCells_eq] using heavyCells_subset hcell⟩)
  representative_mem :
    ∀ cell ∈ heavyCells, representative cell ∈ shading.union
  representative_height :
    ∀ cell ∈ heavyCells, representative cell (2 : Fin 3) = lineHeight
  representative_index :
    ∀ cell ∈ heavyCells, wz1Lemma23CellIndex rho (representative cell) = cell
  lineCell : ℤ × ℤ × ℤ
  lineCell_mem : lineCell ∈ heavyCells
  lineAnchor : Point3
  lineAnchor_eq : lineAnchor = representative lineCell
  lineAnchor_mem : lineAnchor ∈ shading.union
  lineAnchor_height : lineAnchor (2 : Fin 3) = lineHeight
  lineLevel : ℝ
  lineLevel_eq : lineLevel = inner ℝ lineAnchor
    (globalGrainDirection (slope lineHeight))
  heavy_representative_near_line :
    ∀ cell (hcell : cell ∈ heavyCells),
      |inner ℝ (representative cell)
          (globalGrainDirection (slope lineHeight)) - lineLevel| ≤ 9 * rho

/-- Backwards-compatible largest-bin view.  The old one-window pipelines use
the additional pigeonhole inequality, while the exact terminal endpoint may
instead range over every `PureWZ2HorizontalFixedBinCore`. -/
structure PureWZ2HorizontalFixedLineCore
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    (windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C)
    (slope : ℝ → ℝ)
    extends PureWZ2HorizontalFixedBinCore windowed slope where
  heavy_cell_count : sliceCells.card ≤ globalBins.card * heavyCells.card

theorem pureWZ2_selectHorizontalFixedLineCore
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    (windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C)
    (slope : ℝ → ℝ)
    (hrho : 0 < rho) (hdeltaRho : delta ≤ rho) (hrhoOne : rho ≤ 1)
    (hslopeEq : windowed.global.sourceSlope = slope)
    (hcoord : ∀ point ∈ shading.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1)
    (left : ℝ)
    (hheight : ∀ point ∈ shading.union,
      point (2 : Fin 3) ∈ Set.Ico
        (left - rho) (left + Real.sqrt rho + rho))
    (hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice shading.union z))
        delta (1 - sigma) C)
    (hvolume : 0 < volume shading.union) :
    Nonempty (PureWZ2HorizontalFixedLineCore windowed slope) := by
  have hmeas := measurableSet_shading_union shading
  have hball : shading.union ⊆ Metric.closedBall (0 : Point3) 2 := by
    intro point hpoint
    have hsq : ‖point‖ ^ 2 ≤ 3 := by
      have h0 : point 0 ^ 2 ≤ 1 := by
        nlinarith [sq_abs (point 0), abs_nonneg (point 0), hcoord point hpoint 0]
      have h1 : point 1 ^ 2 ≤ 1 := by
        nlinarith [sq_abs (point 1), abs_nonneg (point 1), hcoord point hpoint 1]
      have h2 : point 2 ^ 2 ≤ 1 := by
        nlinarith [sq_abs (point 2), abs_nonneg (point 2), hcoord point hpoint 2]
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
      nlinarith
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [norm_nonneg point]
  have hfinite : volume shading.union ≠ ⊤ :=
    ne_top_of_le_ne_top Metric.isBounded_closedBall.measure_lt_top.ne
      (measure_mono hball)
  let slabLeft := left - rho
  let slabRight := left + Real.sqrt rho + rho
  have hslab : shading.union ⊆
      {point : Point3 | point (2 : Fin 3) ∈ Set.Ico slabLeft slabRight} :=
    fun point hpoint => hheight point hpoint
  have hslabLength : slabRight - slabLeft = Real.sqrt rho + 2 * rho := by
    dsimp only [slabLeft, slabRight]
    ring
  have hslabNondegenerate : slabLeft < slabRight := by
    dsimp only [slabLeft, slabRight]
    nlinarith [Real.sqrt_pos.mpr hrho]
  rcases wz1_lemma23_exists_good_height_in_slab
      hmeas hfinite hslabNondegenerate with
    ⟨lineHeight, _, hsliceRaw⟩
  have hinter : shading.union ∩
      {point : Point3 | point (2 : Fin 3) ∈ Set.Ico slabLeft slabRight} =
      shading.union := Set.inter_eq_left.mpr hslab
  have hsliceArea : volume shading.union /
        ENNReal.ofReal (Real.sqrt rho + 2 * rho) ≤
      volume (wz1Lemma23PlanarSlice shading.union lineHeight) := by
    rw [hinter, hslabLength] at hsliceRaw
    exact hsliceRaw
  have hlineHeight : lineHeight ∈ Set.Icc (-1 : ℝ) 1 := by
    have hnonzero : volume
        (wz1Lemma23PlanarSlice shading.union lineHeight) ≠ 0 := by
      intro hzero
      rw [hzero] at hsliceArea
      have hpos : 0 < volume shading.union /
          ENNReal.ofReal (Real.sqrt rho + 2 * rho) :=
        ENNReal.div_pos hvolume.ne' ENNReal.ofReal_ne_top
      exact (not_le_of_gt hpos) hsliceArea
    have hsliceNonempty :
        (wz1Lemma23PlanarSlice shading.union lineHeight).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hnonzero
      exact hnonzero (by simp)
    rcases hsliceNonempty with ⟨point, hpoint⟩
    have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
    have habs := hcoord (point3 (point 0) (point 1) lineHeight) hlift 2
    simpa [point3] using abs_le.mp habs
  let sliceCells := wz1Lemma23ExactSliceCells shading rho hrho lineHeight
  have hsliceCells : sliceCells.Nonempty := by
    by_contra hempty
    have hzero : volume (wz1Lemma23PlanarSlice shading.union lineHeight) = 0 := by
      have hcover := wz1_lemma23_exactSlice_area_le_two
        shading hrho hball lineHeight
      have hemptyEq : sliceCells = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      simpa [sliceCells, hemptyEq] using hcover
    have hpos : 0 < volume shading.union /
        ENNReal.ofReal (Real.sqrt rho + 2 * rho) :=
      ENNReal.div_pos hvolume.ne' ENNReal.ofReal_ne_top
    rw [hzero] at hsliceArea
    exact (not_le_of_gt hpos) hsliceArea
  let label : (ℤ × ℤ × ℤ) → ℤ := fun cell => Int.floor
    (wz1Lemma23GlobalCoordinate windowed.global.extendedSlope
      (wz1Lemma23CellCenter rho cell) / rho)
  let globalBins := sliceCells.image label
  rcases finset_exists_max_fiber_with_product_bound sliceCells label hsliceCells with
    ⟨lineBin, hlineBin, hheavyCount, hheavyNonempty⟩
  let heavyCells := sliceCells.filter fun cell => label cell = lineBin
  have hextendedEq : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      windowed.global.extendedSlope z = slope z := by
    intro z hz
    rw [windowed.global.extendedSlope_eq z hz, hslopeEq]
  have hglobalBinCount : (globalBins.card : ENNReal) ≤
      132 * C * Kakeya.realRpowENN (1 / rho) (1 - sigma) := by
    have hbins := wz1_lemma23_exactSlice_global_bin_count_of_exact_paper_window
      shading hrho hdeltaRho hrhoOne hcoord slope
      windowed.global.extendedSlope windowed.global.extendedSlope_lipschitz
      windowed.global.extendedSlope_bounded hextendedEq hexact lineHeight
    simpa [globalBins, sliceCells, label, wz1Lemma23ExactSliceGlobalValues,
      wz1Lemma23ScalarBins, Finset.image_image, Function.comp_def] using hbins
  let lineCell := Classical.choose hheavyNonempty
  have hlineCell : lineCell ∈ heavyCells := Classical.choose_spec hheavyNonempty
  have hheavySubset : heavyCells ⊆ sliceCells := Finset.filter_subset _ _
  let representative (cell : ℤ × ℤ × ℤ) : Point3 :=
    if hcell : cell ∈ heavyCells then
      wz1Lemma23LiftSlicePoint lineHeight
        (wz1Lemma23ExactSliceRepresentative shading hrho lineHeight
          ⟨cell, hheavySubset hcell⟩) else 0
  have hrepEq : ∀ cell (hcell : cell ∈ heavyCells), representative cell =
      wz1Lemma23LiftSlicePoint lineHeight
        (wz1Lemma23ExactSliceRepresentative shading hrho lineHeight
          ⟨cell, hheavySubset hcell⟩) := by
    intro cell hcell
    simp [representative, hcell]
  have hrepMem : ∀ cell (hcell : cell ∈ heavyCells),
      representative cell ∈ shading.union := by
    intro cell hcell
    rw [hrepEq cell hcell]
    exact wz1Lemma23ExactSliceRepresentative_mem_union shading hrho
      lineHeight ⟨cell, hheavySubset hcell⟩
  have hrepHeight : ∀ cell (hcell : cell ∈ heavyCells),
      representative cell (2 : Fin 3) = lineHeight := by
    intro cell hcell
    rw [hrepEq cell hcell]
    simp [wz1Lemma23LiftSlicePoint, point3]
  have hrepIndex : ∀ cell (hcell : cell ∈ heavyCells),
      wz1Lemma23CellIndex rho (representative cell) = cell := by
    intro cell hcell
    rw [hrepEq cell hcell]
    exact wz1Lemma23ExactSliceRepresentative_index shading hrho
      lineHeight ⟨cell, hheavySubset hcell⟩
  let lineAnchor := representative lineCell
  let lineLevel := inner ℝ lineAnchor
    (globalGrainDirection (slope lineHeight))
  have hnear : ∀ cell (hcell : cell ∈ heavyCells),
      |inner ℝ (representative cell)
          (globalGrainDirection (slope lineHeight)) - lineLevel| ≤ 9 * rho := by
    intro cell hcell
    let coordinate : Point3 → ℝ := fun p =>
      wz1Lemma23GlobalCoordinate windowed.global.extendedSlope p
    have hpHeight := hrepHeight cell hcell
    have haHeight := hrepHeight lineCell hlineCell
    have hpIndex := hrepIndex cell hcell
    have haIndex := hrepIndex lineCell hlineCell
    have hpSnap := wz1Lemma23_globalCoordinate_snap_of_coord_bound hrho hrhoOne
      windowed.global.extendedSlope windowed.global.extendedSlope_lipschitz
      windowed.global.extendedSlope_bounded (representative cell)
      (hcoord _ (hrepMem cell hcell))
    have haSnap := wz1Lemma23_globalCoordinate_snap_of_coord_bound hrho hrhoOne
      windowed.global.extendedSlope windowed.global.extendedSlope_lipschitz
      windowed.global.extendedSlope_bounded lineAnchor
      (hcoord _ (hrepMem lineCell hlineCell))
    have hcenter : |coordinate (wz1Lemma23CellCenter rho cell) -
        coordinate (wz1Lemma23CellCenter rho lineCell)| < rho := by
      apply wz1Lemma23_abs_sub_lt_of_floor_div_eq hrho
      simpa [label, coordinate] using
        (Finset.mem_filter.mp hcell).2.trans
          (Finset.mem_filter.mp hlineCell).2.symm
    have hpCoord : coordinate (representative cell) = inner ℝ (representative cell)
        (globalGrainDirection (slope lineHeight)) := by
      simp only [coordinate, wz1Lemma23GlobalCoordinate]
      rw [hpHeight, hextendedEq lineHeight hlineHeight]
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    have haCoord : coordinate lineAnchor = lineLevel := by
      dsimp only [lineAnchor, lineLevel]
      simp only [coordinate, wz1Lemma23GlobalCoordinate]
      rw [haHeight, hextendedEq lineHeight hlineHeight]
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    have hpSnapEq : wz1Lemma23Snap rho (representative cell) =
        wz1Lemma23CellCenter rho cell := by
      simp [wz1Lemma23Snap, hpIndex]
    have haSnapEq : wz1Lemma23Snap rho lineAnchor =
        wz1Lemma23CellCenter rho lineCell := by
      dsimp only [lineAnchor]
      simp [wz1Lemma23Snap, haIndex]
    rw [hpSnapEq] at hpSnap
    rw [haSnapEq] at haSnap
    rw [← hpCoord, ← haCoord]
    have htriangle := abs_sub_le (coordinate (representative cell))
      (coordinate (wz1Lemma23CellCenter rho cell)) (coordinate lineAnchor)
    have htriangle2 := abs_sub_le
      (coordinate (wz1Lemma23CellCenter rho cell))
      (coordinate (wz1Lemma23CellCenter rho lineCell)) (coordinate lineAnchor)
    have hpointBound :
        |coordinate (representative cell) -
          coordinate (wz1Lemma23CellCenter rho cell)| ≤ 4 * rho := by
      simpa [coordinate] using hpSnap
    have hanchorBound :
        |coordinate (wz1Lemma23CellCenter rho lineCell) -
          coordinate lineAnchor| ≤ 4 * rho := by
      simpa [coordinate, abs_sub_comm] using haSnap
    exact htriangle.trans (by
      linarith [htriangle2, hpointBound, hanchorBound, hcenter.le])
  exact ⟨{
    rho_pos := hrho
    rho_le_one := hrhoOne
    sourceSlope_eq := hslopeEq
    coordinate_bound := hcoord
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
