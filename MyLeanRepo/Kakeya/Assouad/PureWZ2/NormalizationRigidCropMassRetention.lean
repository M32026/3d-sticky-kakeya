import MyLeanRepo.Kakeya.Assouad.PureWZ2.DenseCubicalImageContainment
import MyLeanRepo.Kakeya.Assouad.TubeVolumeRatio

/-!
# Mass retention for a rigid canonical crop

A rigidly framed ordinary tube whose whole carrier stays one grid scale away
from the boundary of the canonical crop box has the following useful
property: every side-`delta` paper grid cell meeting an ordinary source
subshading is contained in the corresponding cropped paper carrier.

The quantitative argument below separates the finitely many source cells
into dense and light cells.  Dense cells lie in
`pureWZ2DenseCubicalization`; the total source mass in the light cells is
controlled by one finite-cover volume bound.  A cover bound of fifty tube
volumes gives one-half retention, and hence the required one-hundredth
retention.

The margin is an explicit theorem parameter, matching the public
`carrier_margin` field of the rigid-frame certificate without importing its
producer.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

private theorem rigidCrop_gridCube_disjoint
    {delta : ℝ}
    {first second : ℤ × ℤ × ℤ}
    (distinct : first ≠ second) :
    Disjoint
      (wz1PaperGridCube delta first)
      (wz1PaperGridCube delta second) := by
  rw [Set.disjoint_left]
  intro point pointFirst pointSecond
  have firstEq :
      wz1PaperGridIndex delta point = first :=
    (mem_wz1PaperGridCube delta first point).mp pointFirst
  have secondEq :
      wz1PaperGridIndex delta point = second :=
    (mem_wz1PaperGridCube delta second point).mp pointSecond
  exact distinct (firstEq.symm.trans secondEq)

theorem rigidCrop_gridIndex_mem_window
    {delta : ℝ}
    (hdelta : 0 < delta)
    {point : Point3}
    (pointBox :
      point ∈ Kakeya.Streamlined.axisBox 2 2 2) :
    wz1PaperGridIndex delta point ∈
      wz1PaperGridIndicesInWindow delta hdelta := by
  let bound : ℤ := ⌈1 / delta⌉ + 1
  have coordinateBound :
      ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
    have boxBounds :
        |point 0| ≤ 1 ∧
          |point 1| ≤ 1 ∧
          |point 2| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using pointBox
    intro coordinate
    fin_cases coordinate <;> tauto
  have floorBound :
      ∀ coordinate : Fin 3,
        -bound ≤ ⌊point coordinate / delta⌋ ∧
          ⌊point coordinate / delta⌋ ≤ bound := by
    intro coordinate
    have absolute := coordinateBound coordinate
    have upper :
        point coordinate / delta ≤ 1 / delta := by
      gcongr
      exact (abs_le.mp absolute).2
    have lower :
        -(1 / delta) ≤ point coordinate / delta := by
      have raw :
          (-1 : ℝ) / delta ≤
            point coordinate / delta := by
        gcongr
        exact (abs_le.mp absolute).1
      simpa only [neg_div] using raw
    constructor
    · have floorLower :
          ⌊-(1 / delta)⌋ ≤
            ⌊point coordinate / delta⌋ :=
        Int.floor_mono lower
      rw [Int.floor_neg] at floorLower
      linarith
    · have floorUpper :
          ⌊point coordinate / delta⌋ ≤
            ⌊1 / delta⌋ :=
        Int.floor_mono upper
      exact floorUpper.trans
        ((Int.floor_le_ceil (1 / delta)).trans (by omega))
  have coordinate0 :
      ⌊point 0 / delta⌋ ∈ Finset.Icc (-bound) bound :=
    Finset.mem_Icc.mpr ⟨(floorBound 0).1, (floorBound 0).2⟩
  have coordinate1 :
      ⌊point 1 / delta⌋ ∈ Finset.Icc (-bound) bound :=
    Finset.mem_Icc.mpr ⟨(floorBound 1).1, (floorBound 1).2⟩
  have coordinate2 :
      ⌊point 2 / delta⌋ ∈ Finset.Icc (-bound) bound :=
    Finset.mem_Icc.mpr ⟨(floorBound 2).1, (floorBound 2).2⟩
  exact
    Finset.mem_product.mpr
      ⟨coordinate0,
        Finset.mem_product.mpr
          ⟨coordinate1, coordinate2⟩⟩

private def rigidCropSourceCells
    (delta : ℝ)
    (hdelta : 0 < delta)
    (source : Set Point3) :
    Finset (ℤ × ℤ × ℤ) :=
  (wz1PaperGridIndicesInWindow delta hdelta).filter fun cell =>
    (source ∩ wz1PaperGridCube delta cell).Nonempty

/--
Every grid cell meeting a source inside a rigid ordinary carrier remains
inside the corresponding cropped paper carrier.
-/
theorem pureWZ2_gridCube_subset_paperCarrier_of_rigid_margin
    {delta : ℝ}
    (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (source : Set Point3)
    (sourceSubset : source ⊆ tube.carrier)
    (carrierMargin :
      ∀ point, point ∈ tube.carrier →
        ∀ coordinate : Fin 3,
          |point coordinate| ≤ 1 - delta)
    {cell : ℤ × ℤ × ℤ}
    (cellMeetsSource :
      (source ∩ wz1PaperGridCube delta cell).Nonempty) :
    wz1PaperGridCube delta cell ⊆
      wz1PaperTubeCarrier tube := by
  rcases cellMeetsSource with
    ⟨sourcePoint, sourcePointMem, sourcePointCell⟩
  have sourcePointTube : sourcePoint ∈ tube.carrier :=
    sourceSubset sourcePointMem
  let segment :=
    Kakeya.unitSegment tube.base tube.direction
  have segmentCompact : IsCompact segment :=
    isCompact_Icc.image
      (continuous_const.add
        (continuous_id.smul continuous_const))
  have sourcePointThickening :
      sourcePoint ∈ Metric.cthickening delta segment :=
    sourcePointTube
  rcases
      exists_dist_le_of_mem_cthickening_closed
        segmentCompact.isClosed hdelta.le sourcePointThickening with
    ⟨axisPoint, ⟨parameter, parameterMem, axisPointEq⟩,
      sourceAxisDistance⟩
  have axisPointLine : axisPoint ∈ tubeAxisLine tube := by
    exact ⟨parameter, axisPointEq.symm⟩
  intro point pointCell
  have pointSourceDistance :
      dist point sourcePoint ≤ delta * Real.sqrt 3 :=
    pureWZ2_same_grid_cell_dist_le
      hdelta sourcePointCell pointCell
  have pointAxisDistance :
      dist point axisPoint ≤ 6 * delta := by
    have sqrtThreeLtTwo : Real.sqrt 3 < 2 :=
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    calc
      dist point axisPoint ≤
          dist point sourcePoint +
            dist sourcePoint axisPoint :=
        dist_triangle _ _ _
      _ ≤ delta * Real.sqrt 3 + delta := by
        gcongr
      _ ≤ 6 * delta := by
        nlinarith
  have pointThickening :
      point ∈
        Metric.cthickening (6 * delta)
          (tubeAxisLine tube) :=
    Metric.mem_cthickening_of_dist_le
      point axisPoint (6 * delta) (tubeAxisLine tube)
      axisPointLine pointAxisDistance
  have coordinateBound :
      ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
    intro coordinate
    have sameCell :=
      pureWZ2_same_grid_cell_coord_lt
        hdelta sourcePointCell pointCell coordinate
    have sourceBound :=
      carrierMargin sourcePoint sourcePointTube coordinate
    calc
      |point coordinate| =
          |sourcePoint coordinate +
            (point coordinate - sourcePoint coordinate)| := by
        congr 1
        ring
      _ ≤
          |sourcePoint coordinate| +
            |point coordinate - sourcePoint coordinate| :=
        abs_add_le _ _
      _ ≤ (1 - delta) + delta := by
        exact add_le_add sourceBound sameCell.le
      _ = 1 := by ring
  refine ⟨pointThickening, ?_⟩
  simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq]
  exact
    ⟨by simpa using coordinateBound 0,
      by simpa using coordinateBound 1,
      by simpa using coordinateBound 2⟩

/--
A finite grid-cell cover with total cube volume at most fifty tube volumes
forces one-half of the source volume into the dense cubicalization.
-/
theorem pureWZ2_denseCubicalization_volume_half_of_rigid_crop_cover
    {delta : ℝ}
    (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (source : Set Point3)
    (sourceMeasurable : MeasurableSet source)
    (sourceSubset : source ⊆ tube.carrier)
    (carrierMargin :
      ∀ point, point ∈ tube.carrier →
        ∀ coordinate : Fin 3,
          |point coordinate| ≤ 1 - delta)
    (coverCells : Finset (ℤ × ℤ × ℤ))
    (sourceCover :
      source ⊆
        ⋃ cell ∈ coverCells,
          wz1PaperGridCube delta cell)
    (coverVolume :
      (∑ cell ∈ coverCells,
          volume (wz1PaperGridCube delta cell)) ≤
        50 * volume tube.carrier) :
    volume source / 2 ≤
      volume (pureWZ2DenseCubicalization tube source) := by
  let activeCells : Finset (ℤ × ℤ × ℤ) :=
    coverCells.filter fun cell =>
      (source ∩ wz1PaperGridCube delta cell).Nonempty
  let threshold : ENNReal :=
    (100 : ENNReal)⁻¹ *
      volume source *
      (volume tube.carrier)⁻¹
  let isHeavy : (ℤ × ℤ × ℤ) → Prop := fun cell =>
    threshold * volume (wz1PaperGridCube delta cell) ≤
      volume (source ∩ wz1PaperGridCube delta cell)
  let heavyCells : Finset (ℤ × ℤ × ℤ) :=
    activeCells.filter isHeavy
  let lightCells : Finset (ℤ × ℤ × ℤ) :=
    activeCells.filter fun cell => ¬ isHeavy cell
  have activeCellsDisjoint :
      Set.PairwiseDisjoint (↑activeCells)
        (fun cell => wz1PaperGridCube delta cell) := by
    intro first _ second _ distinct
    exact rigidCrop_gridCube_disjoint distinct
  have activeTraceDisjoint :
      Set.PairwiseDisjoint (↑activeCells)
        (fun cell =>
          source ∩ wz1PaperGridCube delta cell) := by
    intro first firstMem second secondMem distinct
    exact
      (activeCellsDisjoint
        firstMem secondMem distinct).mono
          Set.inter_subset_right Set.inter_subset_right
  have activeTraceMeasurable :
      ∀ cell ∈ activeCells,
        MeasurableSet
          (source ∩ wz1PaperGridCube delta cell) :=
    fun cell _ =>
      sourceMeasurable.inter
        (wz1PaperGridCube_measurable cell)
  have sourceEq :
      source =
        ⋃ cell ∈ activeCells,
          source ∩ wz1PaperGridCube delta cell := by
    apply Set.Subset.antisymm
    · intro point pointSource
      rcases Set.mem_iUnion₂.mp (sourceCover pointSource) with
        ⟨cell, cellCover, pointCell⟩
      have cellActive : cell ∈ activeCells := by
        exact Finset.mem_filter.mpr
          ⟨cellCover, ⟨point, pointSource, pointCell⟩⟩
      exact Set.mem_iUnion₂.mpr
        ⟨cell, cellActive, pointSource, pointCell⟩
    · intro point pointUnion
      rcases Set.mem_iUnion₂.mp pointUnion with
        ⟨cell, _, pointSource, _⟩
      exact pointSource
  have sourceVolume :
      volume source =
        ∑ cell ∈ activeCells,
          volume
            (source ∩ wz1PaperGridCube delta cell) := by
    calc
      volume source =
          volume
            (⋃ cell ∈ activeCells,
              source ∩ wz1PaperGridCube delta cell) :=
        congrArg volume sourceEq
      _ =
          ∑ cell ∈ activeCells,
            volume
              (source ∩ wz1PaperGridCube delta cell) :=
        MeasureTheory.measure_biUnion_finset
          activeTraceDisjoint activeTraceMeasurable
  have heavySubsetActive : heavyCells ⊆ activeCells := by
    intro cell cellHeavy
    exact (Finset.mem_filter.mp cellHeavy).1
  have lightSubsetActive : lightCells ⊆ activeCells := by
    intro cell cellLight
    exact (Finset.mem_filter.mp cellLight).1
  have heavyCellSubsetDense :
      ∀ cell ∈ heavyCells,
        wz1PaperGridCube delta cell ⊆
          pureWZ2DenseCubicalization tube source := by
    intro cell cellHeavy
    have cellActive :
        cell ∈ activeCells :=
      heavySubsetActive cellHeavy
    have cellMeetsSource :
        (source ∩ wz1PaperGridCube delta cell).Nonempty :=
      (Finset.mem_filter.mp cellActive).2
    have cellPaper :
        wz1PaperGridCube delta cell ⊆
          wz1PaperTubeCarrier tube :=
      pureWZ2_gridCube_subset_paperCarrier_of_rigid_margin
        hdelta tube source sourceSubset carrierMargin
        cellMeetsSource
    have cellDense :
        threshold * volume (wz1PaperGridCube delta cell) ≤
          volume (source ∩ wz1PaperGridCube delta cell) :=
      (Finset.mem_filter.mp cellHeavy).2
    intro point pointCell
    have pointIndex :
        wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp pointCell
    simpa [pureWZ2DenseCubicalization, threshold, pointIndex] using
      And.intro cellPaper cellDense
  have heavyCellsDisjoint :
      Set.PairwiseDisjoint (↑heavyCells)
        (fun cell => wz1PaperGridCube delta cell) := by
    intro first firstMem second secondMem distinct
    exact
      activeCellsDisjoint
        (heavySubsetActive firstMem)
        (heavySubsetActive secondMem) distinct
  have heavyCellsMeasurable :
      ∀ cell ∈ heavyCells,
        MeasurableSet (wz1PaperGridCube delta cell) :=
    fun cell _ => wz1PaperGridCube_measurable cell
  have heavySourceBound :
      (∑ cell ∈ heavyCells,
          volume
            (source ∩ wz1PaperGridCube delta cell)) ≤
        volume (pureWZ2DenseCubicalization tube source) := by
    calc
      (∑ cell ∈ heavyCells,
          volume
            (source ∩ wz1PaperGridCube delta cell)) ≤
          ∑ cell ∈ heavyCells,
            volume (wz1PaperGridCube delta cell) := by
        exact Finset.sum_le_sum fun cell _ =>
          measure_mono Set.inter_subset_right
      _ =
          volume
            (⋃ cell ∈ heavyCells,
              wz1PaperGridCube delta cell) := by
        exact
          (MeasureTheory.measure_biUnion_finset
            heavyCellsDisjoint heavyCellsMeasurable).symm
      _ ≤
          volume
            (pureWZ2DenseCubicalization tube source) := by
        apply measure_mono
        intro point pointUnion
        rcases Set.mem_iUnion₂.mp pointUnion with
          ⟨cell, cellHeavy, pointCell⟩
        exact heavyCellSubsetDense cell cellHeavy pointCell
  have lightCellBound :
      ∀ cell ∈ lightCells,
        volume (source ∩ wz1PaperGridCube delta cell) ≤
          threshold * volume (wz1PaperGridCube delta cell) := by
    intro cell cellLight
    exact
      (not_le.mp
        (Finset.mem_filter.mp cellLight).2).le
  have tubeVolumePos :
      0 < volume tube.carrier :=
    wz2_paper_ordinary_tube_volume_pos tube hdelta
  have tubeVolumeNeTop :
      volume tube.carrier ≠ ⊤ :=
    wz2_paper_ordinary_tube_volume_ne_top tube hdelta
  have inverseCancel :
      (volume tube.carrier)⁻¹ * volume tube.carrier = 1 :=
    ENNReal.inv_mul_cancel
      tubeVolumePos.ne' tubeVolumeNeTop
  have lightSourceBound :
      (∑ cell ∈ lightCells,
          volume
            (source ∩ wz1PaperGridCube delta cell)) ≤
        volume source / 2 := by
    calc
      (∑ cell ∈ lightCells,
          volume
            (source ∩ wz1PaperGridCube delta cell)) ≤
          ∑ cell ∈ lightCells,
            threshold *
              volume (wz1PaperGridCube delta cell) := by
        exact Finset.sum_le_sum fun cell cellLight =>
          lightCellBound cell cellLight
      _ =
          threshold *
            ∑ cell ∈ lightCells,
              volume (wz1PaperGridCube delta cell) := by
        rw [Finset.mul_sum]
      _ ≤
          threshold *
            ∑ cell ∈ coverCells,
              volume (wz1PaperGridCube delta cell) := by
        apply mul_le_mul_left'
        exact Finset.sum_le_sum_of_subset
          (lightSubsetActive.trans fun cell cellActive =>
            (Finset.mem_filter.mp cellActive).1)
      _ ≤
          threshold * (50 * volume tube.carrier) := by
        gcongr
      _ = volume source / 2 := by
        dsimp only [threshold]
        calc
          ((100 : ENNReal)⁻¹ *
              volume source *
              (volume tube.carrier)⁻¹) *
              (50 * volume tube.carrier) =
            ((100 : ENNReal)⁻¹ * 50) *
              volume source *
              ((volume tube.carrier)⁻¹ *
                volume tube.carrier) := by
              ring
          _ = volume source / 2 := by
            rw [inverseCancel]
            have coefficient :
                (100 : ENNReal)⁻¹ * 50 =
                  (2 : ENNReal)⁻¹ := by
              rw [show (100 : ENNReal) = 2 * 50 by norm_num,
                ENNReal.mul_inv (by norm_num) (by norm_num)]
              calc
                ((2 : ENNReal)⁻¹ * (50 : ENNReal)⁻¹) * 50 =
                    (2 : ENNReal)⁻¹ *
                      ((50 : ENNReal)⁻¹ * 50) := by
                  ring
                _ = (2 : ENNReal)⁻¹ := by
                  rw [ENNReal.inv_mul_cancel] <;> norm_num
            rw [coefficient]
            rw [mul_one, div_eq_mul_inv, mul_comm]
  have activeSumSplit :
      (∑ cell ∈ heavyCells,
          volume
            (source ∩ wz1PaperGridCube delta cell)) +
        (∑ cell ∈ lightCells,
          volume
            (source ∩ wz1PaperGridCube delta cell)) =
      ∑ cell ∈ activeCells,
        volume
          (source ∩ wz1PaperGridCube delta cell) := by
    exact
      Finset.sum_filter_add_sum_filter_not
        activeCells isHeavy
        (fun cell =>
          volume
            (source ∩ wz1PaperGridCube delta cell))
  have sourceUpper :
      volume source ≤
        volume (pureWZ2DenseCubicalization tube source) +
          volume source / 2 := by
    calc
      volume source =
          (∑ cell ∈ heavyCells,
              volume
                (source ∩ wz1PaperGridCube delta cell)) +
            (∑ cell ∈ lightCells,
              volume
                (source ∩ wz1PaperGridCube delta cell)) :=
        sourceVolume.trans activeSumSplit.symm
      _ ≤
          volume (pureWZ2DenseCubicalization tube source) +
            volume source / 2 :=
        add_le_add heavySourceBound lightSourceBound
  have sourceVolumeNeTop :
      volume source ≠ ⊤ :=
    ne_top_of_le_ne_top tubeVolumeNeTop
      (measure_mono sourceSubset)
  have sourceHalfNeTop :
      volume source / 2 ≠ ⊤ :=
    ne_top_of_le_ne_top sourceVolumeNeTop
      ENNReal.half_le_self
  apply ENNReal.le_of_add_le_add_right sourceHalfNeTop
  simpa only [ENNReal.add_halves] using sourceUpper

/--
The same finite rigid-crop hypotheses imply the requested one-hundredth
volume retention.
-/
theorem pureWZ2_denseCubicalization_volume_lower_of_rigid_crop_cover
    {delta : ℝ}
    (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (source : Set Point3)
    (sourceMeasurable : MeasurableSet source)
    (sourceSubset : source ⊆ tube.carrier)
    (carrierMargin :
      ∀ point, point ∈ tube.carrier →
        ∀ coordinate : Fin 3,
          |point coordinate| ≤ 1 - delta)
    (coverCells : Finset (ℤ × ℤ × ℤ))
    (sourceCover :
      source ⊆
        ⋃ cell ∈ coverCells,
          wz1PaperGridCube delta cell)
    (coverVolume :
      (∑ cell ∈ coverCells,
          volume (wz1PaperGridCube delta cell)) ≤
        50 * volume tube.carrier) :
    (100 : ENNReal)⁻¹ * volume source ≤
      volume (pureWZ2DenseCubicalization tube source) := by
  calc
    (100 : ENNReal)⁻¹ * volume source ≤
        volume source / 2 := by
      have coefficient :
          (100 : ENNReal)⁻¹ ≤ (2 : ENNReal)⁻¹ := by
        exact ENNReal.inv_le_inv.mpr (by norm_num)
      calc
        (100 : ENNReal)⁻¹ * volume source ≤
            (2 : ENNReal)⁻¹ * volume source := by
          exact mul_le_mul_right' coefficient _
        _ = volume source / 2 := by
          rw [div_eq_mul_inv, mul_comm]
    _ ≤
        volume (pureWZ2DenseCubicalization tube source) :=
      pureWZ2_denseCubicalization_volume_half_of_rigid_crop_cover
        hdelta tube source sourceMeasurable sourceSubset
        carrierMargin coverCells sourceCover coverVolume

/--
The rigid margin automatically supplies the finite source-cell cover and its
volume bound.  Thus, at scales with `3 * delta ≤ 1`, no separate finite-cover
premise is needed.
-/
theorem pureWZ2_denseCubicalization_volume_lower_of_rigid_margin
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : 3 * delta ≤ 1)
    (tube : Kakeya.DeltaTube delta)
    (source : Set Point3)
    (sourceMeasurable : MeasurableSet source)
    (sourceSubset : source ⊆ tube.carrier)
    (carrierMargin :
      ∀ point, point ∈ tube.carrier →
        ∀ coordinate : Fin 3,
          |point coordinate| ≤ 1 - delta) :
    (100 : ENNReal)⁻¹ * volume source ≤
      volume (pureWZ2DenseCubicalization tube source) := by
  let coverCells :=
    rigidCropSourceCells delta hdelta source
  let expandedTube : Kakeya.DeltaTube (3 * delta) :=
    {
      base := tube.base
      direction := tube.direction
      direction_unit := tube.direction_unit
    }
  have sourceCover :
      source ⊆
        ⋃ cell ∈ coverCells,
          wz1PaperGridCube delta cell := by
    intro point pointSource
    have pointTube : point ∈ tube.carrier :=
      sourceSubset pointSource
    have pointBox :
        point ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
      have coordinateBound :
          ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
        intro coordinate
        exact
          (carrierMargin point pointTube coordinate).trans
            (by linarith)
      simpa [Kakeya.Streamlined.axisBox] using
        And.intro (coordinateBound 0)
          (And.intro (coordinateBound 1)
            (coordinateBound 2))
    let cell := wz1PaperGridIndex delta point
    have cellWindow :
        cell ∈ wz1PaperGridIndicesInWindow delta hdelta :=
      rigidCrop_gridIndex_mem_window hdelta pointBox
    have pointCell :
        point ∈ wz1PaperGridCube delta cell :=
      (mem_wz1PaperGridCube delta cell point).mpr rfl
    have cellCover : cell ∈ coverCells := by
      exact Finset.mem_filter.mpr
        ⟨cellWindow, ⟨point, pointSource, pointCell⟩⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, cellCover, pointCell⟩
  have coverCellsDisjoint :
      Set.PairwiseDisjoint (↑coverCells)
        (fun cell => wz1PaperGridCube delta cell) := by
    intro first _ second _ distinct
    exact rigidCrop_gridCube_disjoint distinct
  have coverCellsMeasurable :
      ∀ cell ∈ coverCells,
        MeasurableSet (wz1PaperGridCube delta cell) :=
    fun cell _ => wz1PaperGridCube_measurable cell
  have coverUnionSubset :
      (⋃ cell ∈ coverCells,
        wz1PaperGridCube delta cell) ⊆
          expandedTube.carrier := by
    intro point pointUnion
    rcases Set.mem_iUnion₂.mp pointUnion with
      ⟨cell, cellCover, pointCell⟩
    rcases (Finset.mem_filter.mp cellCover).2 with
      ⟨sourcePoint, sourcePointMem, sourcePointCell⟩
    have sourcePointTube : sourcePoint ∈ tube.carrier :=
      sourceSubset sourcePointMem
    let segment :=
      Kakeya.unitSegment tube.base tube.direction
    have segmentCompact : IsCompact segment :=
      isCompact_Icc.image
        (continuous_const.add
          (continuous_id.smul continuous_const))
    have sourcePointThickening :
        sourcePoint ∈ Metric.cthickening delta segment :=
      sourcePointTube
    rcases
        exists_dist_le_of_mem_cthickening_closed
          segmentCompact.isClosed hdelta.le
          sourcePointThickening with
      ⟨axisPoint, axisPointSegment, sourceAxisDistance⟩
    have pointSourceDistance :
        dist point sourcePoint ≤ delta * Real.sqrt 3 :=
      pureWZ2_same_grid_cell_dist_le
        hdelta sourcePointCell pointCell
    have pointAxisDistance :
        dist point axisPoint ≤ 3 * delta := by
      have sqrtThreeLtTwo : Real.sqrt 3 < 2 :=
        (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
      calc
        dist point axisPoint ≤
            dist point sourcePoint +
              dist sourcePoint axisPoint :=
          dist_triangle _ _ _
        _ ≤ delta * Real.sqrt 3 + delta := by
          gcongr
        _ ≤ 3 * delta := by
          nlinarith
    exact
      Metric.mem_cthickening_of_dist_le
        point axisPoint (3 * delta)
          (Kakeya.unitSegment
            expandedTube.base expandedTube.direction)
        axisPointSegment pointAxisDistance
  have coverSumVolume :
      (∑ cell ∈ coverCells,
          volume (wz1PaperGridCube delta cell)) ≤
        volume expandedTube.carrier := by
    calc
      (∑ cell ∈ coverCells,
          volume (wz1PaperGridCube delta cell)) =
          volume
            (⋃ cell ∈ coverCells,
              wz1PaperGridCube delta cell) := by
        exact
          (MeasureTheory.measure_biUnion_finset
            coverCellsDisjoint coverCellsMeasurable).symm
      _ ≤ volume expandedTube.carrier :=
        measure_mono coverUnionSubset
  have expandedVolume :
      volume expandedTube.carrier ≤
        27 * volume tube.carrier := by
    have raw :=
      deltaTubeVolume_ratio_bound_cylinder
        hdelta (by linarith : delta ≤ 3 * delta)
        hdeltaSmall
    have powerScaling :
        Kakeya.realRpowENN (3 * delta) 2 =
          9 * Kakeya.realRpowENN delta 2 := by
      simp only [Kakeya.realRpowENN]
      have realScaling :
          Real.rpow (3 * delta) 2 =
            9 * Real.rpow delta 2 := by
        calc
          Real.rpow (3 * delta) 2 =
              (3 * delta) ^ 2 := Real.rpow_two _
          _ = 9 * delta ^ 2 := by ring
          _ = 9 * Real.rpow delta 2 := by
            congr 1
            exact (Real.rpow_two delta).symm
      rw [realScaling]
      rw [ENNReal.ofReal_mul
        (by norm_num : (0 : ℝ) ≤ 9)]
      norm_num
    have powerPos :
        0 < Kakeya.realRpowENN delta 2 :=
      ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos hdelta 2)
    have powerNeTop :
        Kakeya.realRpowENN delta 2 ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have tubeVolume :
        volume tube.carrier =
          Kakeya.deltaTubeVolume delta := by
      exact tube_volume_scaling.1 delta tube
    calc
      volume expandedTube.carrier =
          Kakeya.deltaTubeVolume (3 * delta) :=
        tube_volume_scaling.1 _ expandedTube
      _ ≤
          3 * Kakeya.realRpowENN (3 * delta) 2 *
              (Kakeya.realRpowENN delta 2)⁻¹ *
            Kakeya.deltaTubeVolume delta :=
        raw
      _ =
          27 * Kakeya.deltaTubeVolume delta := by
        rw [powerScaling]
        calc
          3 * (9 * Kakeya.realRpowENN delta 2) *
                (Kakeya.realRpowENN delta 2)⁻¹ *
              Kakeya.deltaTubeVolume delta =
              27 *
                (Kakeya.realRpowENN delta 2 *
                  (Kakeya.realRpowENN delta 2)⁻¹) *
                Kakeya.deltaTubeVolume delta := by
            ring
          _ = 27 * Kakeya.deltaTubeVolume delta := by
            rw [ENNReal.mul_inv_cancel
              powerPos.ne' powerNeTop]
            simp
      _ = 27 * volume tube.carrier := by
        rw [tubeVolume]
  have coverVolume :
      (∑ cell ∈ coverCells,
          volume (wz1PaperGridCube delta cell)) ≤
        50 * volume tube.carrier := by
    calc
      (∑ cell ∈ coverCells,
          volume (wz1PaperGridCube delta cell)) ≤
          volume expandedTube.carrier :=
        coverSumVolume
      _ ≤ 27 * volume tube.carrier :=
        expandedVolume
      _ ≤ 50 * volume tube.carrier := by
        gcongr
        norm_num
  exact
    pureWZ2_denseCubicalization_volume_lower_of_rigid_crop_cover
      hdelta tube source sourceMeasurable sourceSubset
      carrierMargin coverCells sourceCover coverVolume

end Kakeya.Assouad

end
