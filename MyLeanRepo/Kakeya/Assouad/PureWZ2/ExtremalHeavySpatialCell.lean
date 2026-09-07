import MyLeanRepo.Kakeya.Assouad.PureWZ2.ExtremalSpatialCellCWAProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers

/-!
# Fixed-grid heavy cells for pure WZ2 extremizers

This module isolates the unconditional geometric part of the spatial-cell
route.  A unit `delta`-tube with `delta <= 1` meets at most `15^3` cells of
the fixed half-open grid of side `1 / 4`.  Consequently every measurable
subcarrier of the tube has one grid cell retaining at least a `1 / 3375`
fraction of its volume.

The selected cell is contained in a closed unit ball around its lower corner.
If the subcarrier has positive volume, the tube base is within distance `3`
of the same corner.  These are the fixed support and base estimates needed by
`PureWZ2SpatialCellPreselectionData`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Side length of the fixed spatial grid. -/
def pureWZ2HeavyCellSide : ℝ := 1 / 4

/-- Midpoint of the distinguished unit segment of a tube. -/
def pureWZ2TubeMidpoint
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) : Point3 :=
  tube.base + (1 / 2 : ℝ) • tube.direction

/--
The fixed `15 × 15 × 15` window of grid cells around the tube midpoint.
-/
def pureWZ2TubeCellWindow
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    Finset (ℤ × ℤ × ℤ) :=
  let midpointCell :=
    wz1PaperGridIndex pureWZ2HeavyCellSide
      (pureWZ2TubeMidpoint tube)
  (Finset.Icc (midpointCell.1 - 7) (midpointCell.1 + 7)).product
    ((Finset.Icc (midpointCell.2.1 - 7) (midpointCell.2.1 + 7)).product
      (Finset.Icc (midpointCell.2.2 - 7) (midpointCell.2.2 + 7)))

/-- The tube-cell window has exactly `15^3 = 3375` cells. -/
theorem pureWZ2TubeCellWindow_card
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    (pureWZ2TubeCellWindow tube).card = 3375 := by
  have interval_card :
      ∀ center : ℤ,
        (Finset.Icc (center - 7) (center + 7)).card = 15 := by
    intro center
    have card_cast :
        ((Finset.Icc (center - 7) (center + 7)).card : ℤ) =
          center + 7 + 1 - (center - 7) :=
      Int.card_Icc_of_le
        (center - 7) (center + 7) (by omega)
    have arithmetic :
        center + 7 + 1 - (center - 7) = (15 : ℤ) := by
      ring
    exact_mod_cast card_cast.trans arithmetic
  simp [pureWZ2TubeCellWindow, interval_card]

/--
Every point of a unit `delta`-tube, for `delta <= 1`, has grid index in the
fixed `15^3` midpoint window.
-/
theorem pureWZ2_gridIndex_mem_tubeCellWindow
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le_one : delta ≤ 1)
    (tube : Kakeya.DeltaTube delta)
    {point : Point3}
    (point_mem : point ∈ tube.carrier) :
    wz1PaperGridIndex pureWZ2HeavyCellSide point ∈
      pureWZ2TubeCellWindow tube := by
  let midpoint := pureWZ2TubeMidpoint tube
  have point_midpoint :
      dist point midpoint ≤ 1 / 2 + delta := by
    simpa [midpoint, pureWZ2TubeMidpoint] using
      tube_subset_midpoint_closedBall delta_pos tube point_mem
  have coordinate_bound :
      ∀ coordinate : Fin 3,
        |point coordinate - midpoint coordinate| ≤ 3 / 2 := by
    intro coordinate
    calc
      |point coordinate - midpoint coordinate| ≤
          dist point midpoint :=
        PiLp.dist_apply_le point midpoint coordinate
      _ ≤ 1 / 2 + delta := point_midpoint
      _ ≤ 3 / 2 := by linarith
  have floor_bound :
      ∀ coordinate : Fin 3,
        |⌊point coordinate / pureWZ2HeavyCellSide⌋ -
            ⌊midpoint coordinate / pureWZ2HeavyCellSide⌋| ≤
          (7 : ℤ) := by
    intro coordinate
    apply wz1_abs_floor_sub_lt_le (N := 7) (by norm_num)
    have scaled :
        |point coordinate / pureWZ2HeavyCellSide -
            midpoint coordinate / pureWZ2HeavyCellSide| =
          4 * |point coordinate - midpoint coordinate| := by
      rw [← sub_div, abs_div]
      norm_num [pureWZ2HeavyCellSide]
      <;> ring
    rw [scaled]
    have scaled_bound :
        4 * |point coordinate - midpoint coordinate| ≤ 6 := by
      nlinarith [coordinate_bound coordinate]
    exact scaled_bound.trans_lt (by norm_num)
  have floor0 := floor_bound (0 : Fin 3)
  have floor1 := floor_bound (1 : Fin 3)
  have floor2 := floor_bound (2 : Fin 3)
  rcases abs_le.mp floor0 with ⟨floor0_lower, floor0_upper⟩
  rcases abs_le.mp floor1 with ⟨floor1_lower, floor1_upper⟩
  rcases abs_le.mp floor2 with ⟨floor2_lower, floor2_upper⟩
  change
    -(7 : ℤ) ≤
      ⌊point 0 / pureWZ2HeavyCellSide⌋ -
        ⌊pureWZ2TubeMidpoint tube 0 /
          pureWZ2HeavyCellSide⌋ at floor0_lower
  change
    ⌊point 0 / pureWZ2HeavyCellSide⌋ -
        ⌊pureWZ2TubeMidpoint tube 0 /
          pureWZ2HeavyCellSide⌋ ≤
      (7 : ℤ) at floor0_upper
  change
    -(7 : ℤ) ≤
      ⌊point 1 / pureWZ2HeavyCellSide⌋ -
        ⌊pureWZ2TubeMidpoint tube 1 /
          pureWZ2HeavyCellSide⌋ at floor1_lower
  change
    ⌊point 1 / pureWZ2HeavyCellSide⌋ -
        ⌊pureWZ2TubeMidpoint tube 1 /
          pureWZ2HeavyCellSide⌋ ≤
      (7 : ℤ) at floor1_upper
  change
    -(7 : ℤ) ≤
      ⌊point 2 / pureWZ2HeavyCellSide⌋ -
        ⌊pureWZ2TubeMidpoint tube 2 /
          pureWZ2HeavyCellSide⌋ at floor2_lower
  change
    ⌊point 2 / pureWZ2HeavyCellSide⌋ -
        ⌊pureWZ2TubeMidpoint tube 2 /
          pureWZ2HeavyCellSide⌋ ≤
      (7 : ℤ) at floor2_upper
  dsimp only [pureWZ2TubeCellWindow]
  apply Finset.mem_product.mpr
  constructor
  · rw [Finset.mem_Icc]
    change
      ⌊pureWZ2TubeMidpoint tube 0 /
            pureWZ2HeavyCellSide⌋ - 7 ≤
          ⌊point 0 / pureWZ2HeavyCellSide⌋ ∧
        ⌊point 0 / pureWZ2HeavyCellSide⌋ ≤
          ⌊pureWZ2TubeMidpoint tube 0 /
              pureWZ2HeavyCellSide⌋ + 7
    omega
  · apply Finset.mem_product.mpr
    constructor
    · rw [Finset.mem_Icc]
      change
        ⌊pureWZ2TubeMidpoint tube 1 /
              pureWZ2HeavyCellSide⌋ - 7 ≤
            ⌊point 1 / pureWZ2HeavyCellSide⌋ ∧
          ⌊point 1 / pureWZ2HeavyCellSide⌋ ≤
            ⌊pureWZ2TubeMidpoint tube 1 /
                pureWZ2HeavyCellSide⌋ + 7
      omega
    · rw [Finset.mem_Icc]
      change
        ⌊pureWZ2TubeMidpoint tube 2 /
              pureWZ2HeavyCellSide⌋ - 7 ≤
            ⌊point 2 / pureWZ2HeavyCellSide⌋ ∧
          ⌊point 2 / pureWZ2HeavyCellSide⌋ ≤
            ⌊pureWZ2TubeMidpoint tube 2 /
                pureWZ2HeavyCellSide⌋ + 7
      omega

/-- The tube carrier is covered by its finite midpoint cell window. -/
theorem pureWZ2_tubeCarrier_subset_cellWindow
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le_one : delta ≤ 1)
    (tube : Kakeya.DeltaTube delta) :
    tube.carrier ⊆
      ⋃ cell ∈ pureWZ2TubeCellWindow tube,
        wz1PaperGridCube pureWZ2HeavyCellSide cell := by
  intro point point_mem
  let cell := wz1PaperGridIndex pureWZ2HeavyCellSide point
  have cell_mem :
      cell ∈ pureWZ2TubeCellWindow tube :=
    pureWZ2_gridIndex_mem_tubeCellWindow
      delta_pos delta_le_one tube point_mem
  exact
    Set.mem_iUnion₂.mpr
      ⟨cell, cell_mem,
        (mem_wz1PaperGridCube _ _ _).mpr rfl⟩

/--
A measurable subcarrier of a tube is the disjoint finite union of its
intersections with the midpoint cell window.
-/
theorem pureWZ2_volume_eq_sum_cellWindow
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le_one : delta ≤ 1)
    (tube : Kakeya.DeltaTube delta)
    (carrier : Set Point3)
    (carrier_measurable : MeasurableSet carrier)
    (carrier_subset : carrier ⊆ tube.carrier) :
    volume carrier =
      ∑ cell ∈ pureWZ2TubeCellWindow tube,
        volume
          (carrier ∩
            wz1PaperGridCube pureWZ2HeavyCellSide cell) := by
  have carrier_eq :
      carrier =
        ⋃ cell ∈ pureWZ2TubeCellWindow tube,
          carrier ∩
            wz1PaperGridCube pureWZ2HeavyCellSide cell := by
    ext point
    constructor
    · intro point_mem
      let cell := wz1PaperGridIndex pureWZ2HeavyCellSide point
      have cell_mem :
          cell ∈ pureWZ2TubeCellWindow tube :=
        pureWZ2_gridIndex_mem_tubeCellWindow
          delta_pos delta_le_one tube
          (carrier_subset point_mem)
      exact
        Set.mem_iUnion₂.mpr
          ⟨cell, cell_mem,
            point_mem,
            (mem_wz1PaperGridCube _ _ _).mpr rfl⟩
    · intro point_mem
      rcases Set.mem_iUnion₂.mp point_mem with
        ⟨cell, _cell_mem, point_mem, _point_cell⟩
      exact point_mem
  have pairwise_disjoint :
      Set.PairwiseDisjoint
        (↑(pureWZ2TubeCellWindow tube) :
          Set (ℤ × ℤ × ℤ))
        (fun cell =>
          carrier ∩
            wz1PaperGridCube pureWZ2HeavyCellSide cell) := by
    intro first first_mem second second_mem distinct
    exact
      (wz1PaperGridCube_disjoint distinct).mono
        Set.inter_subset_right Set.inter_subset_right
  have measurable :
      ∀ cell ∈ pureWZ2TubeCellWindow tube,
        MeasurableSet
          (carrier ∩
            wz1PaperGridCube pureWZ2HeavyCellSide cell) := by
    intro cell _cell_mem
    exact
      carrier_measurable.inter
        (wz1PaperGridCube_measurable cell)
  calc
    volume carrier =
        volume
          (⋃ cell ∈ pureWZ2TubeCellWindow tube,
            carrier ∩
              wz1PaperGridCube pureWZ2HeavyCellSide cell) := by
      exact congrArg volume carrier_eq
    _ =
        ∑ cell ∈ pureWZ2TubeCellWindow tube,
          volume
            (carrier ∩
              wz1PaperGridCube pureWZ2HeavyCellSide cell) :=
      MeasureTheory.measure_biUnion_finset
        pairwise_disjoint measurable

private theorem pureWZ2_exists_heavy_finset
    {Index : Type*}
    [DecidableEq Index]
    (indices : Finset Index)
    (indices_nonempty : indices.Nonempty)
    (weight : Index → ENNReal) :
    ∃ index ∈ indices,
      (indices.card : ENNReal)⁻¹ *
          ∑ candidate ∈ indices, weight candidate ≤
        weight index := by
  rcases
      Finset.exists_max_image
        indices weight indices_nonempty with
    ⟨index, index_mem, maximal⟩
  have sum_upper :
      (∑ candidate ∈ indices, weight candidate) ≤
        (indices.card : ENNReal) * weight index := by
    calc
      (∑ candidate ∈ indices, weight candidate) ≤
          ∑ _candidate ∈ indices, weight index := by
        apply Finset.sum_le_sum
        intro candidate candidate_mem
        exact maximal candidate candidate_mem
      _ = (indices.card : ENNReal) * weight index := by
        simp
  have card_pos : 0 < indices.card :=
    indices_nonempty.card_pos
  have card_ne_zero : (indices.card : ENNReal) ≠ 0 := by
    exact_mod_cast card_pos.ne'
  have card_ne_top : (indices.card : ENNReal) ≠ ⊤ :=
    ENNReal.coe_ne_top
  refine ⟨index, index_mem, ?_⟩
  calc
    (indices.card : ENNReal)⁻¹ *
          ∑ candidate ∈ indices, weight candidate ≤
        (indices.card : ENNReal)⁻¹ *
          ((indices.card : ENNReal) * weight index) := by
      gcongr
    _ = weight index :=
      ENNReal.inv_mul_cancel_left card_ne_zero card_ne_top

/--
Every measurable subcarrier of a unit tube has a heavy fixed grid cell.
-/
theorem pureWZ2_exists_tube_heavyCell
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le_one : delta ≤ 1)
    (tube : Kakeya.DeltaTube delta)
    (carrier : Set Point3)
    (carrier_measurable : MeasurableSet carrier)
    (carrier_subset : carrier ⊆ tube.carrier) :
    ∃ cell ∈ pureWZ2TubeCellWindow tube,
      (3375 : ENNReal)⁻¹ * volume carrier ≤
        volume
          (carrier ∩
            wz1PaperGridCube pureWZ2HeavyCellSide cell) := by
  have window_nonempty :
      (pureWZ2TubeCellWindow tube).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro window_empty
    have card_zero :
        (pureWZ2TubeCellWindow tube).card = 0 := by
      rw [window_empty]
      simp
    rw [pureWZ2TubeCellWindow_card] at card_zero
    omega
  rcases
      pureWZ2_exists_heavy_finset
        (pureWZ2TubeCellWindow tube)
        window_nonempty
        (fun cell =>
          volume
            (carrier ∩
              wz1PaperGridCube pureWZ2HeavyCellSide cell)) with
    ⟨cell, cell_mem, cell_heavy⟩
  refine ⟨cell, cell_mem, ?_⟩
  have volume_partition :=
    pureWZ2_volume_eq_sum_cellWindow
      delta_pos delta_le_one tube carrier
      carrier_measurable carrier_subset
  calc
    (3375 : ENNReal)⁻¹ * volume carrier =
        (3375 : ENNReal)⁻¹ *
          ∑ candidate ∈ pureWZ2TubeCellWindow tube,
            volume
              (carrier ∩
                wz1PaperGridCube
                  pureWZ2HeavyCellSide candidate) := by
      rw [volume_partition]
    _ =
        ((pureWZ2TubeCellWindow tube).card : ENNReal)⁻¹ *
          ∑ candidate ∈ pureWZ2TubeCellWindow tube,
            volume
              (carrier ∩
                wz1PaperGridCube
                  pureWZ2HeavyCellSide candidate) := by
      rw [pureWZ2TubeCellWindow_card]
      norm_num
    _ ≤
        volume
          (carrier ∩
            wz1PaperGridCube pureWZ2HeavyCellSide cell) :=
      cell_heavy

/-- Every fixed side-`1/4` grid cell lies in a unit ball around its corner. -/
theorem pureWZ2_gridCube_subset_corner_closedBall
    (cell : ℤ × ℤ × ℤ) :
    wz1PaperGridCube pureWZ2HeavyCellSide cell ⊆
      Metric.closedBall
        (cellCorner pureWZ2HeavyCellSide cell) 1 := by
  let rho : ℝ := Real.sqrt 3 / 8
  have rho_pos : 0 < rho := by
    dsimp only [rho]
    positivity
  have side_eq : gridSide rho = pureWZ2HeavyCellSide := by
    dsimp only [rho, gridSide, pureWZ2HeavyCellSide]
    have sqrt_ne_zero : Real.sqrt 3 ≠ 0 := by
      positivity
    field_simp [sqrt_ne_zero]
    <;> ring
  have corner_mem :
      cellCorner pureWZ2HeavyCellSide cell ∈
        wz1PaperGridCube pureWZ2HeavyCellSide cell :=
    cellCorner_mem_gridCube (by norm_num [pureWZ2HeavyCellSide]) cell
  intro point point_mem
  have same_index :
      rhoGridIndex rho point =
        rhoGridIndex rho
          (cellCorner pureWZ2HeavyCellSide cell) := by
    have point_index :
        wz1PaperGridIndex pureWZ2HeavyCellSide point = cell :=
      (mem_wz1PaperGridCube _ _ _).mp point_mem
    have corner_index :
        wz1PaperGridIndex pureWZ2HeavyCellSide
          (cellCorner pureWZ2HeavyCellSide cell) = cell :=
      (mem_wz1PaperGridCube _ _ _).mp corner_mem
    simpa [rhoGridIndex, wz1PaperGridIndex, side_eq] using
      point_index.trans corner_index.symm
  have distance_bound :
      dist point (cellCorner pureWZ2HeavyCellSide cell) ≤
        2 * rho :=
    grid_cell_diameter rho_pos same_index
  have sqrt_three_le_two : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num),
      Real.sqrt_nonneg 3]
  change dist point (cellCorner pureWZ2HeavyCellSide cell) ≤ 1
  calc
    dist point (cellCorner pureWZ2HeavyCellSide cell) ≤
        2 * rho := distance_bound
    _ ≤ 1 := by
      dsimp only [rho]
      linarith

/--
The base of a tube is within distance `3` of the corner of every grid cell
meeting its carrier.
-/
theorem pureWZ2_tubeBase_dist_cellCorner
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le_one : delta ≤ 1)
    (tube : Kakeya.DeltaTube delta)
    (cell : ℤ × ℤ × ℤ)
    (cell_meets :
      (tube.carrier ∩
        wz1PaperGridCube pureWZ2HeavyCellSide cell).Nonempty) :
    dist tube.base
        (cellCorner pureWZ2HeavyCellSide cell) ≤ 3 := by
  rcases cell_meets with ⟨point, point_tube, point_cell⟩
  let midpoint := pureWZ2TubeMidpoint tube
  have point_midpoint :
      dist point midpoint ≤ 1 / 2 + delta := by
    simpa [midpoint, pureWZ2TubeMidpoint] using
      tube_subset_midpoint_closedBall delta_pos tube point_tube
  have base_midpoint :
      dist tube.base midpoint = 1 / 2 := by
    rw [dist_eq_norm]
    simp [midpoint, pureWZ2TubeMidpoint,
      norm_smul, tube.direction_unit]
  have base_point :
      dist tube.base point ≤ 2 := by
    calc
      dist tube.base point ≤
          dist tube.base midpoint + dist midpoint point :=
        dist_triangle _ _ _
      _ = 1 / 2 + dist point midpoint := by
        rw [base_midpoint, dist_comm midpoint point]
      _ ≤ 1 / 2 + (1 / 2 + delta) := by
        gcongr
      _ ≤ 2 := by linarith
  have point_corner :
      dist point
          (cellCorner pureWZ2HeavyCellSide cell) ≤ 1 :=
    pureWZ2_gridCube_subset_corner_closedBall cell point_cell
  calc
    dist tube.base (cellCorner pureWZ2HeavyCellSide cell) ≤
        dist tube.base point +
          dist point (cellCorner pureWZ2HeavyCellSide cell) :=
      dist_triangle _ _ _
    _ ≤ 2 + 1 := by gcongr
    _ = 3 := by norm_num

/--
The heavy-cell output simultaneously supplies mass retention, unit-ball
support, and the base-distance estimate.
-/
theorem pureWZ2_exists_tube_heavySpatialCell
    {delta : ℝ}
    (delta_pos : 0 < delta)
    (delta_le_one : delta ≤ 1)
    (tube : Kakeya.DeltaTube delta)
    (carrier : Set Point3)
    (carrier_measurable : MeasurableSet carrier)
    (carrier_subset : carrier ⊆ tube.carrier)
    (carrier_volume_pos : 0 < volume carrier) :
    ∃ cell ∈ pureWZ2TubeCellWindow tube,
      (3375 : ENNReal)⁻¹ * volume carrier ≤
          volume
            (carrier ∩
              wz1PaperGridCube pureWZ2HeavyCellSide cell) ∧
      carrier ∩
          wz1PaperGridCube pureWZ2HeavyCellSide cell ⊆
        Metric.closedBall
          (cellCorner pureWZ2HeavyCellSide cell) 1 ∧
      dist tube.base
          (cellCorner pureWZ2HeavyCellSide cell) ≤ 3 := by
  rcases
      pureWZ2_exists_tube_heavyCell
        delta_pos delta_le_one tube carrier
        carrier_measurable carrier_subset with
    ⟨cell, cell_mem, mass_retention⟩
  have inverse_pos : 0 < (3375 : ENNReal)⁻¹ := by
    exact ENNReal.inv_pos.mpr (by norm_num)
  have local_volume_pos :
      0 <
        volume
          (carrier ∩
            wz1PaperGridCube pureWZ2HeavyCellSide cell) :=
    (ENNReal.mul_pos inverse_pos.ne' carrier_volume_pos.ne').trans_le
      mass_retention
  have local_nonempty :
      (carrier ∩
        wz1PaperGridCube pureWZ2HeavyCellSide cell).Nonempty :=
    MeasureTheory.nonempty_of_measure_ne_zero
      local_volume_pos.ne'
  refine
    ⟨cell, cell_mem, mass_retention, ?_, ?_⟩
  · exact
      Set.Subset.trans Set.inter_subset_right
        (pureWZ2_gridCube_subset_corner_closedBall cell)
  · exact
      pureWZ2_tubeBase_dist_cellCorner
        delta_pos delta_le_one tube cell
        (local_nonempty.mono fun _point point_mem =>
          ⟨carrier_subset point_mem.1, point_mem.2⟩)

/--
Direct specialization to every tube retained by the source per-tube pruning.

This is the exact local input available before grouping tubes by their chosen
heavy cell.  The factor `3375⁻¹` is the only loss.
-/
theorem PureWZ2PerTubeDensityPruningData.exists_heavySpatialCell
    {sigma sourceLoss pruningLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (index : Fin source.family.card)
    (index_mem : index ∈ pruning.indices) :
    ∃ cell ∈
        pureWZ2TubeCellWindow (source.family.tube index),
      (3375 : ENNReal)⁻¹ *
            volume (source.shading.carrier index) ≤
          volume
            (source.shading.carrier index ∩
              wz1PaperGridCube pureWZ2HeavyCellSide cell) ∧
      (3375 : ENNReal)⁻¹ *
            (Kakeya.realRpowENN delta pruningLoss *
              (source.family.tube index).volume) ≤
          volume
            (source.shading.carrier index ∩
              wz1PaperGridCube pureWZ2HeavyCellSide cell) ∧
      source.shading.carrier index ∩
          wz1PaperGridCube pureWZ2HeavyCellSide cell ⊆
        Metric.closedBall
          (cellCorner pureWZ2HeavyCellSide cell) 1 ∧
      dist (source.family.tube index).base
          (cellCorner pureWZ2HeavyCellSide cell) ≤ 3 := by
  let tube := source.family.tube index
  let carrier := source.shading.carrier index
  have density_pos :
      0 < Kakeya.realRpowENN delta pruningLoss := by
    dsimp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos source.extremal.delta_pos _)
  have tube_volume_pos :
      0 < tube.volume := by
    rw [tube_volume_scaling.1 delta tube]
    exact
      (tube_volume_scaling.2.1 delta
        source.extremal.delta_pos
        source.extremal.delta_le_one).1
  have pruning_density :
      Kakeya.realRpowENN delta pruningLoss * tube.volume ≤
        volume carrier := by
    simpa [tube, carrier] using
      pruning.per_tube_density index index_mem
  have carrier_volume_pos : 0 < volume carrier :=
    (ENNReal.mul_pos density_pos.ne' tube_volume_pos.ne').trans_le
      pruning_density
  rcases
      pureWZ2_exists_tube_heavySpatialCell
        source.extremal.delta_pos
        source.extremal.delta_le_one
        tube carrier
        (source.shading.measurable_carrier index)
        (source.shading.subset_body index)
        carrier_volume_pos with
    ⟨cell, cell_mem, cell_mass, cell_support, base_dist⟩
  refine
    ⟨cell, cell_mem, cell_mass, ?_, cell_support, base_dist⟩
  calc
    (3375 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta pruningLoss *
            (source.family.tube index).volume) =
        (3375 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta pruningLoss *
            tube.volume) := by
      rfl
    _ ≤ (3375 : ENNReal)⁻¹ * volume carrier := by
      gcongr
    _ ≤
        volume
          (source.shading.carrier index ∩
            wz1PaperGridCube pureWZ2HeavyCellSide cell) := by
      simpa [carrier] using cell_mass

/--
Choice of one heavy fixed grid cell for each ambient source index.

Only indices in `pruning.indices` are used below.  The default branch makes
the label a total function, which keeps the finite-image aggregation in the
ambient `Fin source.family.card` index type.
-/
noncomputable def PureWZ2PerTubeDensityPruningData.heavyCell
    {sigma sourceLoss pruningLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)
    (index : Fin source.family.card) : ℤ × ℤ × ℤ :=
  if index_mem : index ∈ pruning.indices then
    Classical.choose
      (pruning.exists_heavySpatialCell index index_mem)
  else
    (0, 0, 0)

namespace PureWZ2PerTubeDensityPruningData

variable
    {sigma sourceLoss pruningLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    (pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss)

/-- The chosen label of a retained tube belongs to its finite tube window. -/
theorem heavyCell_mem_window
    (index : Fin source.family.card)
    (index_mem : index ∈ pruning.indices) :
    pruning.heavyCell index ∈
      pureWZ2TubeCellWindow (source.family.tube index) := by
  rw [heavyCell, dif_pos index_mem]
  exact
    (Classical.choose_spec
      (pruning.exists_heavySpatialCell index index_mem)).1

/-- The chosen cell retains `1 / 3375` of the full source carrier mass. -/
theorem heavyCell_full_mass
    (index : Fin source.family.card)
    (index_mem : index ∈ pruning.indices) :
    (3375 : ENNReal)⁻¹ *
          volume (source.shading.carrier index) ≤
      volume
        (source.shading.carrier index ∩
          wz1PaperGridCube pureWZ2HeavyCellSide
            (pruning.heavyCell index)) := by
  rw [heavyCell, dif_pos index_mem]
  exact
    (Classical.choose_spec
      (pruning.exists_heavySpatialCell index index_mem)).2.1

/-- The chosen cell also retains the constant fraction of pruning density. -/
theorem heavyCell_pruning_density
    (index : Fin source.family.card)
    (index_mem : index ∈ pruning.indices) :
    (3375 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta pruningLoss *
            (source.family.tube index).volume) ≤
      volume
        (source.shading.carrier index ∩
          wz1PaperGridCube pureWZ2HeavyCellSide
            (pruning.heavyCell index)) := by
  rw [heavyCell, dif_pos index_mem]
  exact
    (Classical.choose_spec
      (pruning.exists_heavySpatialCell index index_mem)).2.2.1

/-- The chosen local source piece lies in the fixed unit ball of its cell. -/
theorem heavyCell_support
    (index : Fin source.family.card)
    (index_mem : index ∈ pruning.indices) :
    source.shading.carrier index ∩
        wz1PaperGridCube pureWZ2HeavyCellSide
          (pruning.heavyCell index) ⊆
      Metric.closedBall
        (cellCorner pureWZ2HeavyCellSide
          (pruning.heavyCell index)) 1 := by
  rw [heavyCell, dif_pos index_mem]
  exact
    (Classical.choose_spec
      (pruning.exists_heavySpatialCell index index_mem)).2.2.2.1

/-- The source tube base is within distance three of its chosen cell corner. -/
theorem heavyCell_base
    (index : Fin source.family.card)
    (index_mem : index ∈ pruning.indices) :
    dist (source.family.tube index).base
        (cellCorner pureWZ2HeavyCellSide
          (pruning.heavyCell index)) ≤ 3 := by
  rw [heavyCell, dif_pos index_mem]
  exact
    (Classical.choose_spec
      (pruning.exists_heavySpatialCell index index_mem)).2.2.2.2

/-- The finite set of heavy-cell labels actually used by the pruning. -/
def activeCells : Finset (ℤ × ℤ × ℤ) :=
  pruning.indices.image pruning.heavyCell

/-- The local source mass assigned to one heavy cell. -/
def cellWeight (cell : ℤ × ℤ × ℤ) : ENNReal :=
  ∑ index ∈
      pruning.indices.filter fun index =>
        pruning.heavyCell index = cell,
    volume
      (source.shading.carrier index ∩
        wz1PaperGridCube pureWZ2HeavyCellSide cell)

/-- Total mass of all per-tube heavy pieces before grouping equal labels. -/
def retainedLocalMass : ENNReal :=
  ∑ index ∈ pruning.indices,
    volume
      (source.shading.carrier index ∩
        wz1PaperGridCube pureWZ2HeavyCellSide
          (pruning.heavyCell index))

/-- The active heavy-cell set is nonempty. -/
theorem activeCells_nonempty :
    pruning.activeCells.Nonempty :=
  pruning.nonempty.image pruning.heavyCell

/--
Exact finite decomposition of retained local mass by the chosen heavy-cell
label.  No all-space grid count or boundary correction appears here.
-/
theorem sum_cellWeight :
    ∑ cell ∈ pruning.activeCells, pruning.cellWeight cell =
      pruning.retainedLocalMass := by
  let localWeight : Fin source.family.card → ENNReal := fun index =>
    volume
      (source.shading.carrier index ∩
        wz1PaperGridCube pureWZ2HeavyCellSide
          (pruning.heavyCell index))
  have fiberWeight :
      ∀ cell ∈ pruning.activeCells,
        pruning.cellWeight cell =
          ∑ index ∈ pruning.indices with
              pruning.heavyCell index = cell,
            localWeight index := by
    intro cell _cell_mem
    apply Finset.sum_congr rfl
    intro index index_mem
    have label_eq :
        pruning.heavyCell index = cell :=
      (Finset.mem_filter.mp index_mem).2
    simp only [localWeight]
    rw [label_eq]
  calc
    ∑ cell ∈ pruning.activeCells, pruning.cellWeight cell =
        ∑ cell ∈ pruning.activeCells,
          ∑ index ∈ pruning.indices with
              pruning.heavyCell index = cell,
            localWeight index := by
      apply Finset.sum_congr rfl
      intro cell cell_mem
      exact fiberWeight cell cell_mem
    _ =
        ∑ index ∈ pruning.indices with
            pruning.heavyCell index ∈ pruning.activeCells,
          localWeight index :=
      Finset.sum_fiberwise_eq_sum_filter
        pruning.indices pruning.activeCells
        pruning.heavyCell localWeight
    _ = ∑ index ∈ pruning.indices, localWeight index := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro index index_mem index_not_mem
      exfalso
      apply index_not_mem
      rw [Finset.mem_filter]
      exact
        ⟨index_mem,
          Finset.mem_image.mpr
            ⟨index, index_mem, rfl⟩⟩
    _ = pruning.retainedLocalMass := rfl

/-- The retained local pieces keep `1 / 3375` of the pruned source mass. -/
theorem pruned_mass_le_retainedLocalMass :
    (3375 : ENNReal)⁻¹ *
          (selectedTubeShading
            source.shading pruning.indices).mass ≤
      pruning.retainedLocalMass := by
  rw [selectedTubeShading_mass]
  change
    (3375 : ENNReal)⁻¹ *
          (∑ index ∈ pruning.indices,
            volume (source.shading.carrier index)) ≤
      ∑ index ∈ pruning.indices,
        volume
          (source.shading.carrier index ∩
            wz1PaperGridCube pureWZ2HeavyCellSide
              (pruning.heavyCell index))
  rw [Finset.mul_sum]
  exact
    Finset.sum_le_sum fun index index_mem =>
      pruning.heavyCell_full_mass index index_mem

/--
Combining per-tube heavy-cell retention with the original pruning mass
retention loses only the absolute factor `2 * 3375`.
-/
theorem source_mass_le_retainedLocalMass :
    (3375 : ENNReal)⁻¹ * source.shading.mass ≤
      2 * pruning.retainedLocalMass := by
  calc
    (3375 : ENNReal)⁻¹ * source.shading.mass ≤
        (3375 : ENNReal)⁻¹ *
          (2 *
            (selectedTubeShading
              source.shading pruning.indices).mass) := by
      gcongr
      exact pruning.mass_retention
    _ =
        2 *
          ((3375 : ENNReal)⁻¹ *
            (selectedTubeShading
              source.shading pruning.indices).mass) := by
      ring
    _ ≤ 2 * pruning.retainedLocalMass := by
      gcongr
      exact pruning.pruned_mass_le_retainedLocalMass

/--
One active heavy cell retains the average of the exact finite cell weights.
This is the endpoint immediately before the active-cell cardinality bound.
-/
theorem exists_max_cell :
    ∃ cell ∈ pruning.activeCells,
      (pruning.activeCells.card : ENNReal)⁻¹ *
          pruning.retainedLocalMass ≤
        pruning.cellWeight cell := by
  rcases
      pureWZ2_exists_heavy_finset
        pruning.activeCells pruning.activeCells_nonempty
        pruning.cellWeight with
    ⟨cell, cell_mem, cell_heavy⟩
  refine ⟨cell, cell_mem, ?_⟩
  rw [← pruning.sum_cellWeight]
  exact cell_heavy

/--
Equivalent max-cell estimate without division: the exact retained local mass
is at most the number of active labels times one maximal cell weight.
-/
theorem exists_max_cell_mul :
    ∃ cell ∈ pruning.activeCells,
      pruning.retainedLocalMass ≤
        (pruning.activeCells.card : ENNReal) *
          pruning.cellWeight cell := by
  rcases
      Finset.exists_max_image
        pruning.activeCells pruning.cellWeight
        pruning.activeCells_nonempty with
    ⟨cell, cell_mem, maximal⟩
  refine ⟨cell, cell_mem, ?_⟩
  calc
    pruning.retainedLocalMass =
        ∑ candidate ∈ pruning.activeCells,
          pruning.cellWeight candidate := pruning.sum_cellWeight.symm
    _ ≤
        ∑ _candidate ∈ pruning.activeCells,
          pruning.cellWeight cell := by
      apply Finset.sum_le_sum
      intro candidate candidate_mem
      exact maximal candidate candidate_mem
    _ =
        (pruning.activeCells.card : ENNReal) *
          pruning.cellWeight cell := by
      simp

/--
One active cell retains the source mass up to exactly the active-cell count
and the absolute per-tube/pruning factor.
-/
theorem exists_max_cell_source_mass :
    ∃ cell ∈ pruning.activeCells,
      (pruning.activeCells.card : ENNReal)⁻¹ *
            ((3375 : ENNReal)⁻¹ *
              source.shading.mass) ≤
        2 * pruning.cellWeight cell := by
  rcases pruning.exists_max_cell with
    ⟨cell, cell_mem, cell_heavy⟩
  refine ⟨cell, cell_mem, ?_⟩
  calc
    (pruning.activeCells.card : ENNReal)⁻¹ *
          ((3375 : ENNReal)⁻¹ *
            source.shading.mass) ≤
        (pruning.activeCells.card : ENNReal)⁻¹ *
          (2 * pruning.retainedLocalMass) := by
      exact
        mul_le_mul_left'
          pruning.source_mass_le_retainedLocalMass
          (pruning.activeCells.card : ENNReal)⁻¹
    _ =
        2 *
          ((pruning.activeCells.card : ENNReal)⁻¹ *
            pruning.retainedLocalMass) := by
      ring
    _ ≤ 2 * pruning.cellWeight cell := by
      gcongr

/--
The max-cell source-mass estimate in the multiplicative form consumed by a
later active-cell cardinality bound.
-/
theorem exists_max_cell_source_mass_mul :
    ∃ cell ∈ pruning.activeCells,
      source.shading.mass ≤
        ((6750 : ENNReal) *
            (pruning.activeCells.card : ENNReal)) *
          pruning.cellWeight cell := by
  rcases pruning.exists_max_cell_mul with
    ⟨cell, cell_mem, cell_heavy⟩
  have inverse_cancel :
      (3375 : ENNReal) *
          (3375 : ENNReal)⁻¹ =
        1 := by
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  refine ⟨cell, cell_mem, ?_⟩
  calc
    source.shading.mass =
        (3375 : ENNReal) *
          ((3375 : ENNReal)⁻¹ *
            source.shading.mass) := by
      rw [← mul_assoc, inverse_cancel, one_mul]
    _ ≤
        (3375 : ENNReal) *
          (2 * pruning.retainedLocalMass) := by
      exact
        mul_le_mul_left'
          pruning.source_mass_le_retainedLocalMass
          (3375 : ENNReal)
    _ ≤
        (3375 : ENNReal) *
          (2 *
            ((pruning.activeCells.card : ENNReal) *
              pruning.cellWeight cell)) := by
      gcongr
    _ =
        ((6750 : ENNReal) *
            (pruning.activeCells.card : ENNReal)) *
          pruning.cellWeight cell := by
      ring

/--
Thin scalar endpoint for the unfinished aggregation step.

Once a local packing argument bounds the finite active-cell count strongly
enough to absorb `6750 * activeCells.card`, the maximal heavy cell has exactly
the source-mass retention exponent required downstream.
-/
theorem exists_max_cell_source_mass_of_absorption
    (cellLoss : ℝ)
    (absorption :
      ((6750 : ENNReal) *
            (pruning.activeCells.card : ENNReal)) *
          Kakeya.realRpowENN delta cellLoss ≤
        1) :
    ∃ cell ∈ pruning.activeCells,
      Kakeya.realRpowENN delta cellLoss *
          source.shading.mass ≤
        pruning.cellWeight cell := by
  rcases pruning.exists_max_cell_source_mass_mul with
    ⟨cell, cell_mem, source_bound⟩
  refine ⟨cell, cell_mem, ?_⟩
  calc
    Kakeya.realRpowENN delta cellLoss *
          source.shading.mass ≤
        Kakeya.realRpowENN delta cellLoss *
          (((6750 : ENNReal) *
              (pruning.activeCells.card : ENNReal)) *
            pruning.cellWeight cell) := by
      gcongr
    _ =
        (((6750 : ENNReal) *
              (pruning.activeCells.card : ENNReal)) *
            Kakeya.realRpowENN delta cellLoss) *
          pruning.cellWeight cell := by
      ring
    _ ≤ 1 * pruning.cellWeight cell := by
      gcongr
    _ = pruning.cellWeight cell := by
      simp

end PureWZ2PerTubeDensityPruningData

end Kakeya.Assouad

end
