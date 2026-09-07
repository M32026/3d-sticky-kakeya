import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63TwoRichCloseCount
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentHighCovering
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ConstantMultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BodyMassPositivity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63NestedPointCover
import MyLeanRepo.Kakeya.Assouad.WZ1.ShadingPruningMass
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometry
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruning
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperSubfamilyBoundaryMass
import Mathlib.Data.Set.Card.Arithmetic

/-!
# Robust tau localization for Proposition 6.3

This file isolates the paper-faithful core of WZ1 Lemma 17 on the exact
terminal fine family produced by the dependent rich call.  Local fullness is
created by two `tau/2` grid prunings.  The robust close-count is transported
through the genuine two-rich chain and compared with the dyadic multiplicity
selected on that same terminal shading.

Before either `tau/2` grid pruning, whole `delta` cells crossing a grid
boundary are removed.  Consequently the final Property-(P) shading remains
`delta`-cubical and can be lifted through the current-shading re-entry.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

private lemma nine_tenths_add_one_tenth :
    (9 / 10 : ENNReal) + (1 / 10 : ENNReal) = 1 := by
  have hnine : (9 / 10 : ENNReal) = ENNReal.ofReal (9 / 10 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10)]
    norm_num
  have hone : (1 / 10 : ENNReal) = ENNReal.ofReal (1 / 10 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10)]
    norm_num
  rw [hnine, hone, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

private lemma nine_fortieths_eq :
    (9 / 40 : ENNReal) =
      (9 / 10 : ENNReal) * (1 / 4 : ENNReal) := by
  have leftTop : (9 / 40 : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top (by norm_num) (by norm_num)
  have rightTop : (9 / 10 : ENNReal) * (1 / 4 : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
  apply (ENNReal.toReal_eq_toReal_iff' leftTop rightTop).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

private lemma nine_hundredths_eq :
    (9 / 100 : ENNReal) =
      (1 / 10 : ENNReal) * (9 / 10 : ENNReal) := by
  have leftTop : (9 / 100 : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top (by norm_num) (by norm_num)
  have rightTop : (1 / 10 : ENNReal) * (9 / 10 : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
  apply (ENNReal.toReal_eq_toReal_iff' leftTop rightTop).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

private lemma nine_four_hundredths_eq :
    (9 / 400 : ENNReal) =
      (1 / 10 : ENNReal) * (1 / 4 : ENNReal) *
        (9 / 10 : ENNReal) := by
  have leftTop : (9 / 400 : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top (by norm_num) (by norm_num)
  have rightTop :
      (1 / 10 : ENNReal) * (1 / 4 : ENNReal) *
          (9 / 10 : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.div_ne_top (by norm_num) (by norm_num))
        (ENNReal.div_ne_top (by norm_num) (by norm_num)))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
  apply (ENNReal.toReal_eq_toReal_iff' leftTop rightTop).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

/-- The stronger second grid-pruning budget also pays for the first pruning. -/
private lemma grid_pruning_error_first_of_second
    {error mass logFactor : ENNReal}
    (herror : error ≤ (9 / 400 : ENNReal) * (mass / logFactor)) :
    error ≤ (9 / 100 : ENNReal) * (mass / logFactor) := by
  have hconstant : (9 / 400 : ENNReal) ≤ 9 / 100 := by
    have leftTop : (9 / 400 : ENNReal) ≠ ⊤ :=
      ENNReal.div_ne_top (by norm_num) (by norm_num)
    have rightTop : (9 / 100 : ENNReal) ≠ ⊤ :=
      ENNReal.div_ne_top (by norm_num) (by norm_num)
    rw [← ENNReal.toReal_le_toReal leftTop rightTop]
    norm_num [ENNReal.toReal_div]
  exact herror.trans <| mul_le_mul_right' hconstant _

private lemma eighty_one_four_hundredths_eq :
    (81 / 400 : ENNReal) =
      (9 / 40 : ENNReal) * (9 / 10 : ENNReal) := by
  have leftTop : (81 / 400 : ENNReal) ≠ ⊤ :=
    ENNReal.div_ne_top (by norm_num) (by norm_num)
  have rightTop : (9 / 40 : ENNReal) * (9 / 10 : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
  apply (ENNReal.toReal_eq_toReal_iff' leftTop rightTop).mp
  norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]

attribute [local instance] Classical.propDecidable

/-- A radius-`25 * tau` ball meets at most `103^3` cells of the `tau/2`
grid. -/
private lemma gridCellsIntersecting_largeBall_bound
    {tau : ℝ} (htau : 0 < tau) (center : Point3) :
    (gridCellsIntersecting tau
        (Metric.closedBall center (25 * tau))).Finite ∧
      Set.ncard (gridCellsIntersecting tau
        (Metric.closedBall center (25 * tau))) ≤ 103 ^ 3 := by
  have hscale : 0 < tau / 2 := by positivity
  let centerIndex := rhoGridIndex (tau / 2) center
  let first : Finset ℤ :=
    Finset.Icc (centerIndex.1 - 51) (centerIndex.1 + 51)
  let second : Finset ℤ :=
    Finset.Icc (centerIndex.2.1 - 51) (centerIndex.2.1 + 51)
  let third : Finset ℤ :=
    Finset.Icc (centerIndex.2.2 - 51) (centerIndex.2.2 + 51)
  let cells : Finset (ℤ × ℤ × ℤ) := first ×ˢ (second ×ˢ third)
  have firstCard : first.card = 103 := by
    rw [Int.card_Icc]
    have equality : centerIndex.1 + 51 + 1 - (centerIndex.1 - 51) =
        (103 : ℤ) := by omega
    rw [equality]
    rfl
  have secondCard : second.card = 103 := by
    rw [Int.card_Icc]
    have equality : centerIndex.2.1 + 51 + 1 - (centerIndex.2.1 - 51) =
        (103 : ℤ) := by omega
    rw [equality]
    rfl
  have thirdCard : third.card = 103 := by
    rw [Int.card_Icc]
    have equality : centerIndex.2.2 + 51 + 1 - (centerIndex.2.2 - 51) =
        (103 : ℤ) := by omega
    rw [equality]
    rfl
  have cellsCard : cells.card = 103 ^ 3 := by
    rw [Finset.card_product, Finset.card_product, firstCard, secondCard,
      thirdCard]
    norm_num
  have subsetCells : gridCellsIntersecting tau
      (Metric.closedBall center (25 * tau)) ⊆
      (cells : Set (ℤ × ℤ × ℤ)) := by
    intro cell cellMem
    rcases cellMem with ⟨point, pointCell, pointBall⟩
    have distance : dist point center ≤ 25 * tau :=
      Metric.mem_closedBall.mp pointBall
    have coordinateDistance : ∀ coordinate : Fin 3,
        |point coordinate / gridSide (tau / 2) -
          center coordinate / gridSide (tau / 2)| < 51 := by
      intro coordinate
      have sidePositive : 0 < gridSide (tau / 2) := by
        unfold gridSide
        positivity
      have coordinateBound : |point coordinate - center coordinate| ≤
          25 * tau :=
        (PiLp.dist_apply_le point center coordinate).trans distance
      have quotientBound :
          |(point coordinate - center coordinate) / gridSide (tau / 2)| ≤
            (25 * tau) / gridSide (tau / 2) := by
        rw [abs_div, abs_of_pos sidePositive]
        exact div_le_div_of_nonneg_right coordinateBound sidePositive.le
      have ratioBound : (25 * tau) / gridSide (tau / 2) < 51 := by
        unfold gridSide
        have sqrtThreeLtTwo : Real.sqrt 3 < 2 :=
          Real.sqrt_lt' (by norm_num) |>.mpr (by norm_num)
        field_simp [htau.ne']
        nlinarith
      rw [show point coordinate / gridSide (tau / 2) -
          center coordinate / gridSide (tau / 2) =
          (point coordinate - center coordinate) / gridSide (tau / 2) by
            rw [sub_div]]
      exact quotientBound.trans_lt ratioBound
    have pointIndex : rhoGridIndex (tau / 2) point = cell := by
      simpa [gridCell] using pointCell
    have h0 := wz1_abs_floor_sub_lt_le (N := 51) (by norm_num)
      (coordinateDistance 0)
    have h1 := wz1_abs_floor_sub_lt_le (N := 51) (by norm_num)
      (coordinateDistance 1)
    have h2 := wz1_abs_floor_sub_lt_le (N := 51) (by norm_num)
      (coordinateDistance 2)
    have pointIndex0 :
        ⌊point 0 / gridSide (tau / 2)⌋ = cell.1 := by
      simpa [rhoGridIndex, gridIndex] using congrArg Prod.fst pointIndex
    have pointIndex1 :
        ⌊point 1 / gridSide (tau / 2)⌋ = cell.2.1 := by
      simpa [rhoGridIndex, gridIndex] using
        congrArg (fun value => value.2.1) pointIndex
    have pointIndex2 :
        ⌊point 2 / gridSide (tau / 2)⌋ = cell.2.2 := by
      simpa [rhoGridIndex, gridIndex] using
        congrArg (fun value => value.2.2) pointIndex
    change
      |⌊point 0 / gridSide (tau / 2)⌋ -
          ⌊center 0 / gridSide (tau / 2)⌋| ≤ (51 : ℤ) at h0
    change
      |⌊point 1 / gridSide (tau / 2)⌋ -
          ⌊center 1 / gridSide (tau / 2)⌋| ≤ (51 : ℤ) at h1
    change
      |⌊point 2 / gridSide (tau / 2)⌋ -
          ⌊center 2 / gridSide (tau / 2)⌋| ≤ (51 : ℤ) at h2
    rw [pointIndex0] at h0
    rw [pointIndex1] at h1
    rw [pointIndex2] at h2
    have centerIndex0 :
        centerIndex.1 = ⌊center 0 / gridSide (tau / 2)⌋ := by rfl
    have centerIndex1 :
        centerIndex.2.1 = ⌊center 1 / gridSide (tau / 2)⌋ := by rfl
    have centerIndex2 :
        centerIndex.2.2 = ⌊center 2 / gridSide (tau / 2)⌋ := by rfl
    rw [← centerIndex0] at h0
    rw [← centerIndex1] at h1
    rw [← centerIndex2] at h2
    apply Finset.mem_product.mpr
    constructor
    · simp only [first, Finset.mem_Icc]
      rw [abs_le] at h0
      omega
    · apply Finset.mem_product.mpr
      constructor
      · simp only [second, Finset.mem_Icc]
        rw [abs_le] at h1
        omega
      · simp only [third, Finset.mem_Icc]
        rw [abs_le] at h2
        omega
  have finiteCells : (cells : Set (ℤ × ℤ × ℤ)).Finite :=
    cells.finite_toSet
  exact ⟨finiteCells.subset subsetCells,
    (Set.ncard_le_ncard subsetCells finiteCells).trans <| by
      simp [cellsCard]⟩

/-- A cropped paper tube has only one long direction, so it meets
`O(1/tau)` cells of the `tau/2` grid rather than `O(tau^-3)` cells. -/
theorem paperGridCellsIntersecting_carrier_bound
    {delta tau : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (hline : WZ1PaperIsLineClass family)
    (hdelta : 0 < delta) (htau : 0 < tau) (hdeltaTau : delta ≤ tau) :
    ∀ index : Fin family.card,
      (gridCellsIntersecting tau (source.carrier index)).Finite ∧
        Set.ncard (gridCellsIntersecting tau (source.carrier index)) ≤
          (Nat.ceil (4 / tau) + 1) * 103 ^ 3 := by
  intro index
  let axisCenter : ℕ → Point3 := fun step =>
    wz1TubeAxisZeroPoint (family.tube index) +
      (-2 + (step : ℝ) * tau) • wz1PaperDirection (family.tube index)
  have carrierCover : wz1PaperTubeCarrier (family.tube index) ⊆
      ⋃ step ∈ Finset.range (Nat.ceil (4 / tau) + 1),
        Metric.closedBall (axisCenter step) (25 * tau) := by
    intro point pointMem
    have geometry := (wz2_paper_tube_carrier_geometry hdelta
      (family.tube index) (hline index)).2 pointMem
    have coreCompact : IsCompact
        (wz2PaperAxisCoreSegment (family.tube index)) := by
      unfold wz2PaperAxisCoreSegment
      exact isCompact_Icc.image (by fun_prop)
    rcases exists_dist_le_of_mem_cthickening_closed coreCompact.isClosed
        (by positivity : 0 ≤ 24 * delta) geometry with
      ⟨axisPoint, axisPointMem, pointDistance⟩
    rw [wz2PaperAxisCoreSegment_eq] at axisPointMem
    rcases axisPointMem with ⟨parameter, parameterBounds, rfl⟩
    let shifted : ℝ := parameter + 2
    let step : ℕ := Nat.floor (shifted / tau)
    have shiftedNonnegative : 0 ≤ shifted := by
      dsimp only [shifted]
      linarith [parameterBounds.1]
    have stepBound : step ≤ Nat.ceil (4 / tau) := by
      have shiftedUpper : shifted ≤ 4 := by
        dsimp only [shifted]
        linarith [parameterBounds.2]
      have floorLower : (step : ℝ) ≤ shifted / tau :=
        Nat.floor_le (div_nonneg shiftedNonnegative htau.le)
      have quotientUpper : shifted / tau ≤ 4 / tau := by gcongr
      exact_mod_cast floorLower.trans <|
        quotientUpper.trans (Nat.le_ceil (4 / tau))
    have stepMem : step ∈ Finset.range (Nat.ceil (4 / tau) + 1) := by
      simp only [Finset.mem_range]
      omega
    have stepLower : (step : ℝ) * tau ≤ shifted := by
      have bound := mul_le_mul_of_nonneg_right
        (Nat.floor_le (div_nonneg shiftedNonnegative htau.le)) htau.le
      simpa [htau.ne'] using bound
    have stepUpper : shifted < ((step : ℝ) + 1) * tau := by
      have bound := mul_lt_mul_of_pos_right
        (Nat.lt_floor_add_one (shifted / tau)) htau
      calc
        shifted = (shifted / tau) * tau := by field_simp [htau.ne']
        _ < ((step : ℝ) + 1) * tau := bound
    have axisDistance : dist
        (wz1TubeAxisZeroPoint (family.tube index) +
          parameter • wz1PaperDirection (family.tube index))
        (axisCenter step) ≤ tau := by
      rw [paper_axis_dist]
      have difference : parameter - (-2 + (step : ℝ) * tau) =
          shifted - (step : ℝ) * tau := by
        dsimp only [shifted]
        ring
      rw [difference, abs_le]
      constructor <;> linarith
    have pointBall : point ∈ Metric.closedBall (axisCenter step)
        (25 * tau) := by
      rw [Metric.mem_closedBall]
      calc
        dist point (axisCenter step) ≤
            dist point
              (wz1TubeAxisZeroPoint (family.tube index) +
                parameter • wz1PaperDirection (family.tube index)) +
              dist
                (wz1TubeAxisZeroPoint (family.tube index) +
                  parameter • wz1PaperDirection (family.tube index))
                (axisCenter step) := dist_triangle _ _ _
        _ ≤ 24 * delta + tau := add_le_add pointDistance axisDistance
        _ ≤ 25 * tau := by linarith
    exact Set.mem_iUnion₂.mpr ⟨step, stepMem, pointBall⟩
  have cellsSubset : gridCellsIntersecting tau (source.carrier index) ⊆
      ⋃ step ∈ Finset.range (Nat.ceil (4 / tau) + 1),
        gridCellsIntersecting tau
          (Metric.closedBall (axisCenter step) (25 * tau)) := by
    rintro cell ⟨point, pointCell, pointSource⟩
    have pointPaper := source.subset_body index pointSource
    rcases Set.mem_iUnion₂.mp (carrierCover pointPaper) with
      ⟨step, stepMem, pointBall⟩
    exact Set.mem_iUnion₂.mpr
      ⟨step, stepMem, point, pointCell, pointBall⟩
  have finitePiece : ∀ step ∈ Finset.range (Nat.ceil (4 / tau) + 1),
      (gridCellsIntersecting tau
        (Metric.closedBall (axisCenter step) (25 * tau))).Finite := by
    intro step _
    exact (gridCellsIntersecting_largeBall_bound htau (axisCenter step)).1
  have finiteUnion :
      (⋃ step ∈ Finset.range (Nat.ceil (4 / tau) + 1),
        gridCellsIntersecting tau
          (Metric.closedBall (axisCenter step) (25 * tau))).Finite :=
    Set.Finite.biUnion (Finset.range (Nat.ceil (4 / tau) + 1)).finite_toSet
      finitePiece
  refine ⟨finiteUnion.subset cellsSubset, ?_⟩
  calc
    Set.ncard (gridCellsIntersecting tau (source.carrier index)) ≤
        Set.ncard (⋃ step ∈ Finset.range (Nat.ceil (4 / tau) + 1),
          gridCellsIntersecting tau
            (Metric.closedBall (axisCenter step) (25 * tau))) :=
      Set.ncard_le_ncard cellsSubset finiteUnion
    _ ≤ ∑ step ∈ Finset.range (Nat.ceil (4 / tau) + 1),
        Set.ncard (gridCellsIntersecting tau
          (Metric.closedBall (axisCenter step) (25 * tau))) :=
      Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ _step ∈ Finset.range (Nat.ceil (4 / tau) + 1), 103 ^ 3 := by
      apply Finset.sum_le_sum
      intro step _
      exact (gridCellsIntersecting_largeBall_bound htau (axisCenter step)).2
    _ = (Nat.ceil (4 / tau) + 1) * 103 ^ 3 := by
      simp [Finset.sum_const]

/-- A boundary-safe `delta`-cubical shading stays inside one `tau/2` grid
cell whenever two points lie in the same retained `delta` cell. -/
private lemma boundaryPruned_same_gridCell
    {delta tau : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {hdelta : 0 < delta}
    {multiplicityCap : ENNReal}
    (pruning : WZ2PaperBoundaryCellPruningData
      (rho := gridSide (tau / 2)) source hdelta multiplicityCap)
    {point other : Point3}
    (hpoint : point ∈ pruning.pruned.union)
    (hother : other ∈
      wz1PaperGridCube delta (wz1PaperGridIndex delta point)) :
    rhoGridIndex (tau / 2) other = rhoGridIndex (tau / 2) point := by
  rcases hpoint with ⟨index, hpointCarrier⟩
  rw [pruning.pruned_carrier_eq index] at hpointCarrier
  rcases Set.mem_iUnion₂.mp hpointCarrier.2 with
    ⟨fineCell, hfineCell, hpointFineCell⟩
  have hpointIndex : wz1PaperGridIndex delta point = fineCell :=
    (mem_wz1PaperGridCube delta fineCell point).mp hpointFineCell
  have hotherFineCell : other ∈ wz1PaperGridCube delta fineCell := by
    rwa [← hpointIndex]
  have hpointCoarse := pruning.safeFineCell_contained
    fineCell hfineCell hpointFineCell
  have hotherCoarse := pruning.safeFineCell_contained
    fineCell hfineCell hotherFineCell
  exact ((mem_wz1PaperGridCube (gridSide (tau / 2))
    (pruning.coarseParent fineCell) other).mp hotherCoarse).trans
      ((mem_wz1PaperGridCube (gridSide (tau / 2))
        (pruning.coarseParent fineCell) point).mp hpointCoarse).symm

/-- Boundary pruning is a common spatial restriction, so it keeps every
tube membership at each surviving point. -/
private lemma boundaryPruned_pointMultiplicity_eq
    {delta rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {hdelta : 0 < delta}
    {multiplicityCap : ENNReal}
    (pruning : WZ2PaperBoundaryCellPruningData
      (rho := rho) source hdelta multiplicityCap)
    {point : Point3} (hpoint : point ∈ pruning.pruned.union) :
    pruning.pruned.pointMultiplicity point =
      source.pointMultiplicity point := by
  rcases hpoint with ⟨witness, hwitness⟩
  rw [pruning.pruned_carrier_eq witness] at hwitness
  have hsafe := hwitness.2
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro index _
  constructor
  · intro hpruned
    exact pruning.pruned_subshading index hpruned
  · intro hsource
    rw [pruning.pruned_carrier_eq index]
    exact ⟨hsource, hsafe⟩

/-- Grid-cell pruning at `tau/2` preserves the original `delta` cubicality
after boundary-crossing `delta` cells have been removed. -/
private lemma paperGridCellPrune_cubical_of_boundaryPruned
    {delta tau threshold : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {hdelta : 0 < delta}
    {multiplicityCap : ENNReal}
    (pruning : WZ2PaperBoundaryCellPruningData
      (rho := gridSide (tau / 2)) source hdelta multiplicityCap)
    (htau : 0 < tau)
    {input : WZ1PaperTubeShading family}
    (hinputSub : PaperIsSubshading input pruning.pruned)
    (hinputCubical : WZ1PaperIsCubicalShading input) :
    WZ1PaperIsCubicalShading
      (paperGridCellPrune input tau threshold htau) := by
  intro index point hpoint other hother
  rcases hpoint with ⟨cell, hgood, hpointInput, hpointCell⟩
  have hotherInput : other ∈ input.carrier index :=
    hinputCubical index point hpointInput hother
  have hpointSafe : point ∈ pruning.pruned.union :=
    ⟨index, hinputSub index hpointInput⟩
  have hsame := boundaryPruned_same_gridCell pruning hpointSafe hother
  have hcell : rhoGridIndex (tau / 2) point = cell := hpointCell
  exact ⟨cell, hgood, hotherInput, hsame.trans hcell⟩

/-- The explicit aggregate error used by one paper `tau/2` grid pruning. -/
def proposition63TauGridPruningError
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (tau epsilon₁ : ℝ) : ENNReal :=
  (family.card : ENNReal) *
    ((((Nat.ceil (4 / tau) + 1) * 103 ^ 3 : ℕ) : ENNReal) *
      (Kakeya.realRpowENN delta (2 + 2 * epsilon₁) *
        ENNReal.ofReal tau))

/-- The tube-axis grid count is linear in `1 / tau`: after multiplying by
the cell-length factor `tau`, it is bounded by an absolute constant. -/
lemma proposition63_tau_grid_count_mul_tau_le
    {tau : ℝ} (htau : 0 < tau) (htauOne : tau ≤ 1) :
    ((((Nat.ceil (4 / tau) + 1) * 103 ^ 3 : ℕ) : ENNReal) *
        ENNReal.ofReal tau) ≤
      (((6 * 103 ^ 3 : ℕ) : ENNReal)) := by
  let count : ℕ := (Nat.ceil (4 / tau) + 1) * 103 ^ 3
  have hceil : (Nat.ceil (4 / tau) : ℝ) ≤ 4 / tau + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ 4 / tau)).le
  have hmain : ((Nat.ceil (4 / tau) : ℝ) + 1) * tau ≤ 6 := by
    calc
      ((Nat.ceil (4 / tau) : ℝ) + 1) * tau ≤
          (4 / tau + 2) * tau := by
        exact mul_le_mul_of_nonneg_right (by linarith) htau.le
      _ = 4 + 2 * tau := by field_simp [htau.ne']
      _ ≤ 6 := by linarith
  have hreal : (count : ℝ) * tau ≤ 6 * (103 : ℝ) ^ 3 := by
    calc
      (count : ℝ) * tau =
          (((Nat.ceil (4 / tau) : ℝ) + 1) * tau) * (103 : ℝ) ^ 3 := by
        simp only [count, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          Nat.cast_pow]
        ring
      _ ≤ 6 * (103 : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hmain (by positivity)
  rw [show (count : ENNReal) = ENNReal.ofReal (count : ℝ) by simp]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (count : ℝ))]
  calc
    ENNReal.ofReal ((count : ℝ) * tau) ≤
        ENNReal.ofReal (6 * (103 : ℝ) ^ 3) := ENNReal.ofReal_mono hreal
    _ = (((6 * 103 ^ 3 : ℕ) : ENNReal)) := by norm_num

/-- Specialize a family-free scalar grid budget to the exact selected family
of a rich terminal.  This is the cancellation that rules out a cubic
`tau⁻³` loss: only the tube-axis `O(1 / tau)` count occurs. -/
theorem Proposition63RichTerminalStickyData.tauGridPruningError_le
    {delta sigma outerSourceLoss outerNormalizationLoss targetReentryLoss
      targetLoss tau epsilon₁ : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    {targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current}
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hscalar : (((6 * 103 ^ 3 : ℕ) : ENNReal) *
          Kakeya.realRpowENN delta
            (2 * epsilon₁ - targetReentry.reentryNormalizationLoss)) *
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal) ≤
        (9 / 400 : ENNReal) * wz2PaperPureRefinementFraction delta 61) :
    proposition63TauGridPruningError target.data.selected.family tau epsilon₁ ≤
      (9 / 400 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal)) := by
  let logFactor : ENNReal :=
    ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)
  have hlogPos : 0 < logFactor := by
    dsimp only [logFactor]
    exact_mod_cast Nat.zero_lt_succ (Nat.log 2 target.data.selected.family.card)
  have hlogTop : logFactor ≠ ⊤ := by simp [logFactor]
  have hcardinality :
      Kakeya.realRpowENN delta
          (targetReentry.reentryNormalizationLoss + 2) *
          target.data.selected.family.enncard ≤
        targetReentry.normalization.croppedRefined.mass :=
    selected_cardinality_cancellation
      targetReentry.normalization.final_extremal
      targetReentry.normalization.line_class target.data.selected hdeltaSmall
  have herror : proposition63TauGridPruningError
      target.data.selected.family tau epsilon₁ ≤
      (((6 * 103 ^ 3 : ℕ) : ENNReal) *
        Kakeya.realRpowENN delta
          (2 * epsilon₁ - targetReentry.reentryNormalizationLoss)) *
        targetReentry.normalization.croppedRefined.mass := by
    unfold proposition63TauGridPruningError
    calc
      (target.data.selected.family.card : ENNReal) *
            (((((Nat.ceil (4 / tau) + 1) * 103 ^ 3 : ℕ) : ENNReal) *
              (Kakeya.realRpowENN delta (2 + 2 * epsilon₁) *
                ENNReal.ofReal tau))) =
          ((((Nat.ceil (4 / tau) + 1) * 103 ^ 3 : ℕ) : ENNReal) *
              ENNReal.ofReal tau) *
            (Kakeya.realRpowENN delta (2 + 2 * epsilon₁) *
              target.data.selected.family.enncard) := by
        simp only [Kakeya.Streamlined.TubeFamily.enncard]
        ring
      _ ≤ (((6 * 103 ^ 3 : ℕ) : ENNReal) *
            Kakeya.realRpowENN delta (2 + 2 * epsilon₁)) *
          target.data.selected.family.enncard := by
        calc
          _ ≤ (((6 * 103 ^ 3 : ℕ) : ENNReal)) *
                (Kakeya.realRpowENN delta (2 + 2 * epsilon₁) *
                  target.data.selected.family.enncard) :=
            mul_le_mul_right'
              (proposition63_tau_grid_count_mul_tau_le htau htauOne) _
          _ = _ := by ring
      _ = (((6 * 103 ^ 3 : ℕ) : ENNReal) *
            Kakeya.realRpowENN delta
              (2 * epsilon₁ - targetReentry.reentryNormalizationLoss)) *
          (Kakeya.realRpowENN delta
              (targetReentry.reentryNormalizationLoss + 2) *
            target.data.selected.family.enncard) := by
        have hpower : Kakeya.realRpowENN delta (2 + 2 * epsilon₁) =
            Kakeya.realRpowENN delta
                (2 * epsilon₁ - targetReentry.reentryNormalizationLoss) *
              Kakeya.realRpowENN delta
                (targetReentry.reentryNormalizationLoss + 2) := by
          rw [← realRpowENN_add targetReentry.reentry_extremal.delta_pos]
          congr 1
          ring
        rw [hpower]
        ring
      _ ≤ (((6 * 103 ^ 3 : ℕ) : ENNReal) *
            Kakeya.realRpowENN delta
              (2 * epsilon₁ - targetReentry.reentryNormalizationLoss)) *
          targetReentry.normalization.croppedRefined.mass := by gcongr
  rw [show (9 / 400 : ENNReal) *
        (target.data.refined.mass / logFactor) =
      ((9 / 400 : ENNReal) * target.data.refined.mass) / logFactor by
        simp only [div_eq_mul_inv]; ring]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hlogPos.ne') (Or.inl hlogTop)).2
  calc
    proposition63TauGridPruningError target.data.selected.family tau epsilon₁ *
          logFactor ≤
        ((((6 * 103 ^ 3 : ℕ) : ENNReal) *
            Kakeya.realRpowENN delta
              (2 * epsilon₁ - targetReentry.reentryNormalizationLoss)) *
          targetReentry.normalization.croppedRefined.mass) * logFactor := by
      gcongr
    _ = ((((6 * 103 ^ 3 : ℕ) : ENNReal) *
            Kakeya.realRpowENN delta
              (2 * epsilon₁ - targetReentry.reentryNormalizationLoss)) *
          logFactor) *
        targetReentry.normalization.croppedRefined.mass := by ring
    _ ≤ ((9 / 400 : ENNReal) *
          wz2PaperPureRefinementFraction delta 61) *
        targetReentry.normalization.croppedRefined.mass := by
      exact mul_le_mul_right' (by simpa only [logFactor] using hscalar) _
    _ ≤ (9 / 400 : ENNReal) * target.data.refined.mass := by
      calc
        ((9 / 400 : ENNReal) *
              wz2PaperPureRefinementFraction delta 61) *
            targetReentry.normalization.croppedRefined.mass =
          (9 / 400 : ENNReal) *
            (wz2PaperPureRefinementFraction delta 61 *
              targetReentry.normalization.croppedRefined.mass) := by ring
        _ ≤ (9 / 400 : ENNReal) * target.data.refined.mass :=
          mul_le_mul_left' target.total_mass_retention _

/-- The balanced cell mass of the target rich call is bounded using the
volume upper bound of its exact normalized source.  This is the root-relative
analogue of the cell-mass cancellation in the recursive two-level route. -/
theorem Proposition63RichTerminalStickyData.targetCellMass_power_upper
    {delta sigma outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    {targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current}
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (htargetSmall : targetScale.1 ≤ 1 / 12) :
    target.data.balanced.cellMass ≤
      Kakeya.realRpowENN delta
          (sigma - targetReentry.reentryNormalizationLoss) *
        Kakeya.realRpowENN targetScale.1
          (3 - sigma - 2 * targetLoss) := by
  let active : ENNReal := target.data.balanced.activeCells.card
  let cubeVolume : ENNReal :=
    volume (wz1PaperGridCube targetScale.1 (0, 0, 0))
  let lower : ENNReal :=
    Kakeya.realRpowENN targetScale.1 (sigma + 2 * targetLoss)
  let upper : ENNReal :=
    Kakeya.realRpowENN delta
      (sigma - targetReentry.reentryNormalizationLoss)
  have coarseLower : lower ≤
      volume target.data.croppedCoarseShading.union := by
    exact proposition63_sticky_coarse_union_volume_lower target.data
      htargetSmall
  have coarseVolume : volume target.data.croppedCoarseShading.union =
      active * cubeVolume := by
    simpa only [active, cubeVolume] using
      balanced_cover_coarse_volume target.data.balanced
        target.data.coarse_extremal.delta_pos
  have fineVolume : volume target.data.refined.union =
      active * target.data.balanced.cellMass := by
    simpa only [active] using
      balanced_cover_fine_union_volume target.data.balanced
        target.data.coarse_extremal.delta_pos
  have fineUpper : volume target.data.refined.union ≤ upper := by
    apply (measure_mono ?_).trans
      targetReentry.normalization.final_extremal.volume_upper
    rintro point ⟨index, hpoint⟩
    exact ⟨target.data.selected.embedding index,
      target.data.subshading index hpoint⟩
  have activeCellUpper :
      active * target.data.balanced.cellMass ≤ upper := by
    rw [← fineVolume]
    exact fineUpper
  have cellScaled : target.data.balanced.cellMass * lower ≤
      upper * cubeVolume := by
    calc
      target.data.balanced.cellMass * lower ≤
          target.data.balanced.cellMass * (active * cubeVolume) := by
        gcongr
        simpa only [coarseVolume] using coarseLower
      _ = (active * target.data.balanced.cellMass) * cubeVolume := by ring
      _ ≤ upper * cubeVolume := by gcongr
  have lower_ne_zero : lower ≠ 0 := by
    simp [lower, Kakeya.realRpowENN, Real.rpow_pos_of_pos
      target.data.coarse_extremal.delta_pos]
  have lower_ne_top : lower ≠ ⊤ := by
    simp [lower, Kakeya.realRpowENN]
  have cubePower : ENNReal.ofReal (targetScale.1 ^ 3) =
      Kakeya.realRpowENN targetScale.1 3 := by
    simp only [Kakeya.realRpowENN]
    congr 1
    exact (Real.rpow_natCast targetScale.1 3).symm
  have powerQuotient :
      Kakeya.realRpowENN targetScale.1 3 /
          Kakeya.realRpowENN targetScale.1 (sigma + 2 * targetLoss) =
        Kakeya.realRpowENN targetScale.1
          (3 - sigma - 2 * targetLoss) := by
    have denominatorPos :
        0 < Real.rpow targetScale.1 (sigma + 2 * targetLoss) :=
      Real.rpow_pos_of_pos target.data.coarse_extremal.delta_pos _
    have exponent : 3 - sigma - 2 * targetLoss =
        3 - (sigma + 2 * targetLoss) := by ring
    simp only [Kakeya.realRpowENN]
    calc
      ENNReal.ofReal (Real.rpow targetScale.1 3) /
          ENNReal.ofReal
            (Real.rpow targetScale.1 (sigma + 2 * targetLoss)) =
          ENNReal.ofReal
            (Real.rpow targetScale.1 3 /
              Real.rpow targetScale.1 (sigma + 2 * targetLoss)) :=
        (ENNReal.ofReal_div_of_pos denominatorPos).symm
      _ = ENNReal.ofReal
          (Real.rpow targetScale.1
            (3 - (sigma + 2 * targetLoss))) :=
        congrArg ENNReal.ofReal <|
          (Real.rpow_sub target.data.coarse_extremal.delta_pos 3
            (sigma + 2 * targetLoss)).symm
      _ = ENNReal.ofReal
          (Real.rpow targetScale.1
            (3 - sigma - 2 * targetLoss)) := by rw [exponent]
  have divided : target.data.balanced.cellMass ≤
      upper * cubeVolume / lower :=
    (ENNReal.le_div_iff_mul_le
      (Or.inl lower_ne_zero) (Or.inl lower_ne_top)).2 cellScaled
  calc
    target.data.balanced.cellMass ≤ upper * cubeVolume / lower := divided
    _ = upper * (cubeVolume / lower) := by rw [mul_div_assoc]
    _ = upper * Kakeya.realRpowENN targetScale.1
        (3 - sigma - 2 * targetLoss) := by
      rw [show cubeVolume / lower =
          Kakeya.realRpowENN targetScale.1
            (3 - sigma - 2 * targetLoss) by
        dsimp only [cubeVolume, lower]
        rw [wz1PaperGridCube_volume_exact
          target.data.coarse_extremal.delta_pos, cubePower]
        exact powerQuotient]
    _ = _ := rfl

/-- Local volume on the target terminal is paid by the target call's own
balanced cells.  The factor is cubic only in the bounded ratio between the
local window and the target cover scale; there is no `tau⁻³` grid count. -/
theorem Proposition63RichTerminalStickyData.target_three_tau_volume_upper
    {delta sigma outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    {targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current}
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (htau : 0 < tau) (htargetTau : targetScale.1 ≤ 3 * tau)
    (q : Point3) :
    volume (target.data.refined.union ∩ Metric.closedBall q (3 * tau)) ≤
      (8 * 27 : ENNReal) *
        ENNReal.ofReal (((3 * tau) / targetScale.1) ^ 3) *
        (Kakeya.realRpowENN delta
            (sigma - targetReentry.reentryNormalizationLoss) *
          Kakeya.realRpowENN targetScale.1
            (3 - sigma - 2 * targetLoss)) := by
  have hlocal := Kakeya.Assouad.pureWz2_local_volume_upper
    (delta := delta) (sigma := sigma) (L := targetScale.1)
    (tau := 3 * tau) (fine := target.data.selected.family)
    (coarse := target.data.coarse) (cover := target.data.cover)
    (fineShading := target.data.refined)
    (coarseShading := target.data.croppedCoarseShading)
    target.data.balanced target.data.coarse_extremal.delta_pos
    (by positivity) htargetTau q
  exact hlocal.trans <| by
    gcongr
    exact Proposition63RichTerminalStickyData.targetCellMass_power_upper
      htargetReentryLoss target htargetSmall

/-- Positive aggregate paper-shading mass gives an occupied point. -/
private lemma paperShading_union_nonempty_of_mass_pos
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hmass : 0 < shading.mass) : shading.union.Nonempty := by
  by_contra emptyUnion
  have allEmpty : ∀ index, shading.carrier index = ∅ := by
    intro index
    ext point
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun pointMem => emptyUnion ⟨point, index, pointMem⟩
  have massZero : shading.mass = 0 := by
    dsimp only [Kakeya.Streamlined.Shading.mass]
    simp [allEmpty]
  rw [massZero] at hmass
  exact (lt_irrefl 0) hmass

/-- Cancel the ambient normalized-family cardinality in the fixed-grid CWA
boundary estimate against source density and the target rich refinement
retention.  The remaining premise is a family-free scalar inequality. -/
theorem Proposition63RichTerminalStickyData.boundaryCWA_of_scalar
    {delta sigma outerSourceLoss outerNormalizationLoss targetReentryLoss
      targetLoss tau : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    {targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current}
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hscalar :
      (24000000 : ENNReal) *
          (Kakeya.realRpowENN delta
              (-targetReentry.reentryNormalizationLoss) *
              wz2PaperBoundaryGeometryConstant + 1) *
          Kakeya.realRpowENN delta 2 *
          ENNReal.ofReal (Real.sqrt (delta / gridSide (tau / 2))) ≤
        (1 / 10 : ENNReal) * wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            (targetReentry.reentryNormalizationLoss + 2)) :
    targetReentry.normalization.croppedFamily.enncard *
          ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta
                (-targetReentry.reentryNormalizationLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt
              (delta / gridSide (tau / 2)))) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass := by
  let all := Kakeya.Streamlined.TubeSubfamily.fromFinset
    targetReentry.normalization.croppedFamily
      (Finset.univ : Finset
        (Fin targetReentry.normalization.croppedFamily.card))
  have sourceCard :
      Kakeya.realRpowENN delta
          (targetReentry.reentryNormalizationLoss + 2) *
          targetReentry.normalization.croppedFamily.enncard ≤
        targetReentry.normalization.croppedRefined.mass := by
    have raw := selected_cardinality_cancellation
      targetReentry.normalization.final_extremal
      targetReentry.normalization.line_class all hdeltaSmall
    have allCard : all.family.enncard =
        targetReentry.normalization.croppedFamily.enncard := by
      change
        ((Finset.univ : Finset
            (Fin targetReentry.normalization.croppedFamily.card)).card :
          ENNReal) =
        (targetReentry.normalization.croppedFamily.card : ENNReal)
      rw [Finset.card_univ, Fintype.card_fin]
    rw [allCard] at raw
    exact raw
  calc
    targetReentry.normalization.croppedFamily.enncard *
          ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta
                (-targetReentry.reentryNormalizationLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt
              (delta / gridSide (tau / 2)))) =
        ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta
                (-targetReentry.reentryNormalizationLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt
              (delta / gridSide (tau / 2)))) *
          targetReentry.normalization.croppedFamily.enncard := by ring
    _ ≤ ((1 / 10 : ENNReal) *
          wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            (targetReentry.reentryNormalizationLoss + 2)) *
        targetReentry.normalization.croppedFamily.enncard := by gcongr
    _ = (1 / 10 : ENNReal) * wz2PaperPureRefinementFraction delta 61 *
        (Kakeya.realRpowENN delta
            (targetReentry.reentryNormalizationLoss + 2) *
          targetReentry.normalization.croppedFamily.enncard) := by ring
    _ ≤ (1 / 10 : ENNReal) * wz2PaperPureRefinementFraction delta 61 *
        targetReentry.normalization.croppedRefined.mass := by gcongr
    _ ≤ (1 / 10 : ENNReal) * target.data.refined.mass := by
      calc
        (1 / 10 : ENNReal) * wz2PaperPureRefinementFraction delta 61 *
              targetReentry.normalization.croppedRefined.mass =
            (1 / 10 : ENNReal) *
              (wz2PaperPureRefinementFraction delta 61 *
                targetReentry.normalization.croppedRefined.mass) := by ring
        _ ≤ (1 / 10 : ENNReal) * target.data.refined.mass :=
          mul_le_mul_left' target.total_mass_retention _

/-- Build the fixed-origin boundary pruning from the ambient normalized CWA
estimate.  The required strict mass loss is stated once on the actual
crossing-mass envelope; it is stronger than the `1/10` budget used below and
does not pass through the coarse pointwise multiplicity fallback. -/
theorem Proposition63RichTerminalStickyData.boundaryPruning_of_cwa
    {delta sigma outerSourceLoss outerNormalizationLoss targetReentryLoss
      targetLoss tau : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    {targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current}
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hdeltaGrid : delta ≤ gridSide (tau / 2))
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hperiodic : 50 * delta ≤ gridSide (tau / 2))
    (hboundaryCWA :
      let side := gridSide (tau / 2)
      targetReentry.normalization.croppedFamily.enncard *
          ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta
                (-targetReentry.reentryNormalizationLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt (delta / side))) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass) :
    ∃ pruning : WZ2PaperBoundaryCellPruningData
        (rho := gridSide (tau / 2)) target.data.refined
          target.terminal.delta_pos
          (((target.terminal.regularity *
            target.terminal.fineDegreeFloor : ℕ) : ENNReal) *
              target.terminal.muFine),
      (9 / 10 : ENNReal) * target.data.refined.mass ≤
        pruning.pruned.mass := by
  let side := gridSide (tau / 2)
  let multiplicityCap : ENNReal :=
    ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
      ENNReal) * target.terminal.muFine
  have hsidePos : 0 < side := by
    dsimp only [side, gridSide]
    positivity
  have hsideOne : side ≤ 1 := by
    dsimp only [side, gridSide]
    have sqrtThreeGeOne : 1 ≤ Real.sqrt 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    calc
      2 * (tau / 2) / Real.sqrt 3 = tau / Real.sqrt 3 := by ring
      _ ≤ tau := div_le_self htau.le sqrtThreeGeOne
      _ ≤ 1 := htauOne
  have hdeltaSmall : delta ≤ 1 / 24 := by
    linarith [hperiodic, hsideOne]
  let crossingCells := wz2PaperBoundaryCrossingFineCells
    (rho := side) target.data.refined target.terminal.delta_pos
  have crossingData : ∀ cell ∈ crossingCells,
      cell ∈ wz1PaperActiveCells target.data.refined target.terminal.delta_pos ∧
        ¬ (wz1PaperGridCube delta cell ⊆
          wz1PaperGridCube side
            (wz1PaperGridIndex side (cellCorner delta cell))) := by
    intro cell hcell
    have split := Finset.mem_sdiff.mp hcell
    refine ⟨split.1, ?_⟩
    rw [wz2PaperBoundarySafeFineCells, Finset.mem_filter] at split
    intro contained
    exact split.2 ⟨split.1, contained⟩
  have crossingMass := wz2_paper_subfamily_grid_boundary_mass_normalized
    target.terminal.delta_pos hdeltaSmall
    hsidePos hsideOne hperiodic
    targetReentry.normalization.line_class target.data.selected
    target.data.refined targetReentry.normalization.cropped_top_level_cwa
  have crossingSubset :
      wz2PaperBoundaryCrossingRegion
          (rho := side) target.data.refined target.terminal.delta_pos ⊆
        wz2PaperGridBoundaryRegion delta side := by
    dsimp only [wz2PaperBoundaryCrossingRegion]
    exact wz2_paper_crossing_region_subset_grid_boundary
      target.terminal.fine_cubical target.terminal.delta_pos hsidePos
      crossingCells crossingData
  have actualCrossing :
      (∑ index : Fin target.data.selected.family.card,
        volume (target.data.refined.carrier index ∩
          wz2PaperBoundaryCrossingRegion
            (rho := side) target.data.refined target.terminal.delta_pos)) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass := by
    calc
      _ ≤ ∑ index : Fin target.data.selected.family.card,
          volume (target.data.refined.carrier index ∩
            wz2PaperGridBoundaryRegion delta side) := by
        exact Finset.sum_le_sum fun index _ =>
          measure_mono (Set.inter_subset_inter_right _ crossingSubset)
      _ ≤ targetReentry.normalization.croppedFamily.enncard *
          ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta
                (-targetReentry.reentryNormalizationLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt (delta / side))) := crossingMass
      _ ≤ (1 / 10 : ENNReal) * target.data.refined.mass := by
        simpa only [side] using hboundaryCWA
  have targetMassPos : 0 < target.data.refined.mass := by
    have sourceMassPos := cropped_extremal_shading_mass_pos
      targetReentry.normalization.final_extremal
      targetReentry.normalization.line_class hdeltaSmall
    have fractionBounds := pure_refinement_fraction_pos_ne_top
      targetReentry.reentry_extremal.delta_pos
      (hdeltaSmall.trans_lt (by norm_num)) 61
    exact (ENNReal.mul_pos fractionBounds.1.ne' sourceMassPos.ne').trans_le
      target.total_mass_retention
  have crossingStrict :
      (∑ index : Fin target.data.selected.family.card,
        volume (target.data.refined.carrier index ∩
          wz2PaperBoundaryCrossingRegion
            (rho := side) target.data.refined target.terminal.delta_pos)) <
        target.data.refined.mass :=
    actualCrossing.trans_lt <| by
      have tenthLtOne : (1 / 10 : ENNReal) < 1 := by
        rw [← ENNReal.toReal_lt_toReal
          (ENNReal.div_ne_top (by norm_num) (by norm_num)) (by norm_num)]
        norm_num [ENNReal.toReal_div]
      calc
        (1 / 10 : ENNReal) * target.data.refined.mass =
            target.data.refined.mass * (1 / 10 : ENNReal) := by ring
        _ < target.data.refined.mass * 1 :=
          ENNReal.mul_lt_mul_right targetMassPos.ne'
            paper_shading_mass_ne_top tenthLtOne
        _ = target.data.refined.mass := by simp
  rcases wz2_paper_boundary_cell_pruning_of_crossing_mass
      target.terminal.delta_pos hdeltaGrid hsidePos hsideOne
      target.data.refined target.terminal.fine_cubical multiplicityCap
      target.terminal.fine_pointMultiplicity_upper crossingStrict with
    ⟨pruning⟩
  refine ⟨pruning, ?_⟩
  have pruningError :
      (∑ index : Fin target.data.selected.family.card,
        volume (target.data.refined.carrier index ∩ pruning.crossingRegion)) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass := by
    rw [pruning.crossingRegion_eq_source]
    exact actualCrossing
  apply retained_mass_of_error_le_fraction paper_shading_mass_ne_top
    (by norm_num) nine_tenths_add_one_tenth pruning.source_mass_eq_crossing.le
  exact pruningError

/-- Carrierwise loss for a paper grid pruning, assuming the finite cell count
separately.  This is the part of `gridCellPrune_carrier_loss` independent of
the ordinary finite-segment tube model. -/
private lemma paperGridCellPrune_carrier_loss
    {delta tau threshold : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (htau : 0 < tau) (_hthreshold : 0 ≤ threshold)
    (index : Fin family.card) {bound : ℕ}
    (hfinite : (gridCellsIntersecting tau (source.carrier index)).Finite)
    (hbound : Set.ncard
      (gridCellsIntersecting tau (source.carrier index)) ≤ bound) :
    volume (source.carrier index \
        (paperGridCellPrune source tau threshold htau).carrier index) ≤
      (bound : ENNReal) * ENNReal.ofReal threshold := by
  let cellSet := gridCellsIntersecting tau (source.carrier index)
  let cells : Finset (ℤ × ℤ × ℤ) := hfinite.toFinset
  have cellsCoe : (cells : Set (ℤ × ℤ × ℤ)) = cellSet :=
    Set.Finite.coe_toFinset hfinite
  let good (cell : ℤ × ℤ × ℤ) : Prop :=
    ENNReal.ofReal threshold ≤
      volume (source.carrier index ∩ gridCell tau cell)
  let badCells : Finset (ℤ × ℤ × ℤ) :=
    cells.filter fun cell => ¬ good cell
  have removed : source.carrier index \
      (paperGridCellPrune source tau threshold htau).carrier index ⊆
        ⋃ cell ∈ badCells, source.carrier index ∩ gridCell tau cell := by
    intro point pointMem
    let cell := rhoGridIndex (tau / 2) point
    have pointCell : point ∈ gridCell tau cell := rfl
    have cellMem : cell ∈ cells := by
      have : cell ∈ cellSet := ⟨point, pointCell, pointMem.1⟩
      rw [← cellsCoe] at this
      simpa using this
    have cellBad : ¬ good cell := by
      intro cellGood
      exact pointMem.2 ⟨cell, cellGood, pointMem.1, pointCell⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, Finset.mem_filter.mpr ⟨cellMem, cellBad⟩, pointMem.1,
        pointCell⟩
  have volumeBound : volume (source.carrier index \
      (paperGridCellPrune source tau threshold htau).carrier index) ≤
      ∑ cell ∈ badCells, volume (source.carrier index ∩ gridCell tau cell) :=
    (measure_mono removed).trans
      (measure_biUnion_finset_le badCells fun cell =>
        source.carrier index ∩ gridCell tau cell)
  have badVolume : ∀ cell ∈ badCells,
      volume (source.carrier index ∩ gridCell tau cell) ≤
        ENNReal.ofReal threshold := by
    intro cell cellMem
    exact le_of_not_ge (Finset.mem_filter.mp cellMem).2
  have sumBound :
      ∑ cell ∈ badCells, volume (source.carrier index ∩ gridCell tau cell) ≤
        (badCells.card : ENNReal) * ENNReal.ofReal threshold := by
    calc
      ∑ cell ∈ badCells, volume (source.carrier index ∩ gridCell tau cell) ≤
          ∑ _cell ∈ badCells, ENNReal.ofReal threshold :=
        Finset.sum_le_sum badVolume
      _ = (badCells.card : ENNReal) * ENNReal.ofReal threshold := by
        simp [Finset.sum_const]
  have badCard : badCells.card ≤ cells.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have cellsCard : (cells.card : ENNReal) = Set.ncard cellSet := by
    have equality : Set.ncard (cells : Set (ℤ × ℤ × ℤ)) = cells.card := by
      simp
    rw [cellsCoe] at equality
    exact_mod_cast equality.symm
  exact volumeBound.trans <| sumBound.trans <| by
    apply mul_le_mul_left
    calc
      (badCells.card : ENNReal) ≤ (cells.card : ENNReal) := by
        exact_mod_cast badCard
      _ = Set.ncard cellSet := cellsCard
      _ ≤ (bound : ENNReal) := by exact_mod_cast hbound

/-- One grid pruning loses at most its explicit cell-count error. -/
theorem paperGridCellPrune_mass_le_add_error
    {delta tau epsilon₁ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (hdelta : 0 < delta) (htau : 0 < tau)
    (hcount : ∀ index : Fin family.card,
      (gridCellsIntersecting tau (source.carrier index)).Finite ∧
        Set.ncard (gridCellsIntersecting tau (source.carrier index)) ≤
          (Nat.ceil (4 / tau) + 1) * 103 ^ 3) :
    source.mass ≤
      (paperGridCellPrune source tau
        (Real.rpow delta (2 + 2 * epsilon₁) * tau) htau).mass +
        proposition63TauGridPruningError family tau epsilon₁ := by
  let threshold : ℝ := Real.rpow delta (2 + 2 * epsilon₁) * tau
  let count : ℕ := (Nat.ceil (4 / tau) + 1) * 103 ^ 3
  have countBound : ∀ index : Fin family.card,
      Set.ncard (gridCellsIntersecting tau (source.carrier index)) ≤ count := by
    simpa only [count] using fun index => (hcount index).2
  have carrierLoss : ∀ index : Fin family.card,
      volume (source.carrier index \
        (paperGridCellPrune source tau threshold htau).carrier index) ≤
          (count : ENNReal) * ENNReal.ofReal threshold := by
    intro index
    exact paperGridCellPrune_carrier_loss htau
      (mul_nonneg (Real.rpow_nonneg hdelta.le _) htau.le)
      index (hcount index).1 (countBound index)
  have raw : source.mass ≤
      (paperGridCellPrune source tau threshold htau).mass +
        (family.card : ENNReal) *
          ((count : ENNReal) * ENNReal.ofReal threshold) := by
    let target := paperGridCellPrune source tau threshold htau
    have targetSub : PaperIsSubshading target source :=
      paperGridCellPrune_subshading
    have carrierBound : ∀ index : Fin family.card,
        volume (source.carrier index) ≤
          volume (target.carrier index) +
            volume (source.carrier index \ target.carrier index) := by
      intro index
      have unionEq : target.carrier index ∪
          (source.carrier index \ target.carrier index) =
          source.carrier index := by
        ext point
        constructor
        · rintro (pointTarget | pointRemoved)
          · exact targetSub index pointTarget
          · exact pointRemoved.1
        · intro pointSource
          by_cases pointTarget : point ∈ target.carrier index
          · exact Or.inl pointTarget
          · exact Or.inr ⟨pointSource, pointTarget⟩
      have bound := MeasureTheory.measure_union_le
        (μ := volume) (target.carrier index)
          (source.carrier index \ target.carrier index)
      rw [unionEq] at bound
      exact bound
    calc
      source.mass = ∑ index : Fin family.card,
          volume (source.carrier index) := rfl
      _ ≤ ∑ index : Fin family.card,
          (volume (target.carrier index) +
            volume (source.carrier index \ target.carrier index)) := by
        exact Finset.sum_le_sum fun index _ => carrierBound index
      _ = target.mass + ∑ index : Fin family.card,
          volume (source.carrier index \ target.carrier index) := by
        rw [Finset.sum_add_distrib]
        rfl
      _ ≤ target.mass + ∑ _index : Fin family.card,
          ((count : ENNReal) * ENNReal.ofReal threshold) := by
        gcongr
        exact carrierLoss _
      _ = target.mass + (family.card : ENNReal) *
          ((count : ENNReal) * ENNReal.ofReal threshold) := by
        simp [Finset.sum_const]
  have thresholdEq : ENNReal.ofReal threshold =
      Kakeya.realRpowENN delta (2 + 2 * epsilon₁) *
        ENNReal.ofReal tau := by
    dsimp only [threshold, Kakeya.realRpowENN]
    exact ENNReal.ofReal_mul (Real.rpow_nonneg hdelta.le _)
  rw [thresholdEq] at raw
  simpa only [proposition63TauGridPruningError, count] using raw

/-- Data after the two paper grid prunings on one exact terminal shading. -/
structure Proposition63RobustTauLocalizationData
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale) where
  boundaryPruning : WZ2PaperBoundaryCellPruningData
    (rho := gridSide (tau / 2)) target.data.refined target.terminal.delta_pos
      ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) *
        target.terminal.muFine)
  level : ℕ
  dyadic : WZ1PaperTubeShading target.data.selected.family
  dyadic_sub : PaperIsSubshading dyadic target.data.refined
  dyadic_cubical : WZ1PaperIsCubicalShading dyadic
  dyadic_lower : ∀ point ∈ dyadic.union,
    (2 ^ level : ENNReal) ≤ (dyadic.pointMultiplicity point : ENNReal)
  dyadic_upper : ∀ point ∈ dyadic.union,
    (dyadic.pointMultiplicity point : ENNReal) < 2 * (2 ^ level : ENNReal)
  dyadic_mass : (9 / 10 : ENNReal) *
      (target.data.refined.mass /
        ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)) ≤
    dyadic.mass
  propertyOne : WZ1PaperTubeShading target.data.selected.family
  propertyOne_sub : PaperIsSubshading propertyOne dyadic
  propertyOne_mass : (9 / 10 : ENNReal) * dyadic.mass ≤ propertyOne.mass
  selectedMultiplicity : ℕ
  constantShading : WZ1PaperTubeShading target.data.selected.family
  constant_sub : PaperIsSubshading constantShading propertyOne
  constant_multiplicity : constantShading.HasConstantMultiplicity
    selectedMultiplicity (2 * selectedMultiplicity)
  constant_mass : (1 / 4 : ENNReal) * dyadic.mass ≤ constantShading.mass
  propertyThree : WZ1PaperTubeShading target.data.selected.family
  propertyThree_sub : PaperIsSubshading propertyThree constantShading
  propertyThree_cubical : WZ1PaperIsCubicalShading propertyThree
  propertyThree_mass : (9 / 40 : ENNReal) * dyadic.mass ≤
    propertyThree.mass
  propertyThree_full : ∀ index point,
    point ∈ propertyThree.carrier index →
      Kakeya.realRpowENN delta (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
        volume (propertyThree.carrier index ∩ Metric.closedBall point tau)
  cordoba : PureWZ2CordobaPropertyPData
    (sigma := sigma) (coarseShading := target.data.refined)
    (tau := tau) epsilon₁ epsilon₃
  cordoba_propertyOne : cordoba.propertyOne = propertyOne
  cordoba_propertyThree : cordoba.propertyThree = propertyThree

/-- Construct the target-terminal localization after boundary safety has been
established.  Separating this core from boundary construction lets the fixed
grid use either the legacy pointwise-cap estimate or the sharper ambient-CWA
crossing-mass estimate. -/
theorem proposition63_robust_tau_localization_of_boundary_pruning
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hdeltaTau : delta ≤ tau)
    (htau : 0 < tau)
    (boundaryPruning : WZ2PaperBoundaryCellPruningData
      (rho := gridSide (tau / 2)) target.data.refined
        target.terminal.delta_pos
        (((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
          ENNReal) * target.terminal.muFine))
    (boundaryMass : (9 / 10 : ENNReal) * target.data.refined.mass ≤
      boundaryPruning.pruned.mass)
    (hfirstError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 100 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hsecondError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 400 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hcrossCall :
      4 * (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal))
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1) :
    Nonempty (Proposition63RobustTauLocalizationData
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      outer targetReentry hcurrentSubOuter htargetReentryLoss target) := by
  obtain ⟨level, dyadicCubical, dyadicMassBoundary, dyadicBounds⟩ :=
    paperDyadicBandPigeonhole boundaryPruning.pruned_cubical
  let dyadic := wz1PaperDyadicBandSubshading boundaryPruning.pruned level
  have dyadicBoundarySub : PaperIsSubshading dyadic boundaryPruning.pruned := by
    intro index
    exact Set.inter_subset_left
  have dyadicSub : PaperIsSubshading dyadic target.data.refined :=
    fun index => (dyadicBoundarySub index).trans
      (boundaryPruning.pruned_subshading index)
  have dyadicMass : (9 / 10 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)) ≤
      dyadic.mass := by
    calc
      (9 / 10 : ENNReal) *
          (target.data.refined.mass /
            ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)) =
        ((9 / 10 : ENNReal) * target.data.refined.mass) /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal) := by
            simp only [div_eq_mul_inv]
            ring
      _ ≤ boundaryPruning.pruned.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal) := by
        gcongr
      _ ≤ dyadic.mass := dyadicMassBoundary
  have dyadicLower : ∀ point ∈ dyadic.union,
      (2 ^ level : ENNReal) ≤ (dyadic.pointMultiplicity point : ENNReal) :=
    fun point pointMem => (dyadicBounds point pointMem).1
  have dyadicUpper : ∀ point ∈ dyadic.union,
      (dyadic.pointMultiplicity point : ENNReal) < 2 * (2 ^ level : ENNReal) := by
    intro point pointMem
    simpa [pow_succ, mul_comm] using (dyadicBounds point pointMem).2
  let threshold : ℝ := Real.rpow delta (2 + 2 * epsilon₁) * tau
  have terminalGridCount : ∀ index : Fin target.data.selected.family.card,
      (gridCellsIntersecting tau
        (target.data.refined.carrier index)).Finite ∧
      Set.ncard (gridCellsIntersecting tau
        (target.data.refined.carrier index)) ≤
        (Nat.ceil (4 / tau) + 1) * 103 ^ 3 :=
    paperGridCellsIntersecting_carrier_bound target.data.refined
      target.data.cover.fine_line_class target.terminal.delta_pos htau
      hdeltaTau
  let propertyOne := paperGridCellPrune dyadic tau threshold htau
  have propertyOneSub : PaperIsSubshading propertyOne dyadic :=
    paperGridCellPrune_subshading
  have propertyOneRaw : dyadic.mass ≤ propertyOne.mass +
      proposition63TauGridPruningError target.data.selected.family tau epsilon₁ := by
    simpa only [propertyOne, threshold] using
      paperGridCellPrune_mass_le_add_error (epsilon₁ := epsilon₁) dyadic
        target.terminal.delta_pos htau
        (fun index => by
          have subset : gridCellsIntersecting tau (dyadic.carrier index) ⊆
              gridCellsIntersecting tau
                (target.data.refined.carrier index) := by
            rintro cell ⟨point, pointCell, pointMem⟩
            exact ⟨point, pointCell, dyadicSub index pointMem⟩
          exact ⟨(terminalGridCount index).1.subset subset,
            (Set.ncard_le_ncard subset (terminalGridCount index).1).trans
              (terminalGridCount index).2⟩)
  have firstErrorOnDyadic : proposition63TauGridPruningError
      target.data.selected.family tau epsilon₁ ≤
      (1 / 10 : ENNReal) * dyadic.mass := by
    calc
      proposition63TauGridPruningError
          target.data.selected.family tau epsilon₁ ≤
          (9 / 100 : ENNReal) *
            (target.data.refined.mass /
              ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
                ENNReal)) := hfirstError
      _ = (1 / 10 : ENNReal) *
          ((9 / 10 : ENNReal) *
            (target.data.refined.mass /
              ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
                ENNReal))) := by
            rw [nine_hundredths_eq]
            ring
      _ ≤ (1 / 10 : ENNReal) * dyadic.mass :=
        mul_le_mul_left' dyadicMass _
  have propertyOneMass : (9 / 10 : ENNReal) * dyadic.mass ≤
      propertyOne.mass := by
    apply retained_mass_of_error_le_fraction (paper_shading_mass_ne_top)
      (by norm_num) nine_tenths_add_one_tenth
      propertyOneRaw
    exact firstErrorOnDyadic
  have propertyOneDropped : dyadic.mass - propertyOne.mass ≤
      (1 / 10 : ENNReal) * dyadic.mass :=
    dropped_mass_of_mass_le_add_error <|
      propertyOneRaw.trans <| add_le_add_right
        firstErrorOnDyadic _
  let multiplicity : ℕ := 2 ^ level
  have dyadicConstant : dyadic.HasConstantMultiplicity multiplicity
      (2 * multiplicity) := by
    intro point pointMem
    constructor
    · exact_mod_cast dyadicLower point pointMem
    · exact_mod_cast (dyadicUpper point pointMem).le
  have multiplicityPos : 0 < multiplicity := by
    simp [multiplicity]
  rcases paperExtractConstantMultiplicity propertyOneSub dyadicConstant
      (paperGridCellPrune_cubical_of_boundaryPruned boundaryPruning htau
        dyadicBoundarySub dyadicCubical)
      paper_shading_mass_ne_top multiplicityPos propertyOneDropped with
    ⟨selectedMultiplicity, constantShading, constantSub,
      constantMultiplicity, selectedHalf, quarterMass, constantCubical⟩
  let propertyThree := paperGridCellPrune constantShading tau threshold htau
  have propertyThreeSub : PaperIsSubshading propertyThree constantShading :=
    paperGridCellPrune_subshading
  have propertyThreeRaw : constantShading.mass ≤ propertyThree.mass +
      proposition63TauGridPruningError target.data.selected.family tau epsilon₁ := by
    simpa only [propertyThree, threshold] using
      paperGridCellPrune_mass_le_add_error (epsilon₁ := epsilon₁)
        constantShading
        target.terminal.delta_pos htau
        (fun index => by
          have subset : gridCellsIntersecting tau
              (constantShading.carrier index) ⊆
              gridCellsIntersecting tau
                (target.data.refined.carrier index) := by
            rintro cell ⟨point, pointCell, pointMem⟩
            exact ⟨point, pointCell, dyadicSub index <|
              propertyOneSub index <| constantSub index pointMem⟩
          exact ⟨(terminalGridCount index).1.subset subset,
            (Set.ncard_le_ncard subset (terminalGridCount index).1).trans
              (terminalGridCount index).2⟩)
  have secondErrorOnConstant : proposition63TauGridPruningError
      target.data.selected.family tau epsilon₁ ≤
      (1 / 10 : ENNReal) * constantShading.mass := by
    calc
      proposition63TauGridPruningError target.data.selected.family tau epsilon₁ ≤
          (9 / 400 : ENNReal) *
            (target.data.refined.mass /
              ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
                ENNReal)) := hsecondError
      _ = (1 / 10 : ENNReal) * ((1 / 4 : ENNReal) *
          ((9 / 10 : ENNReal) *
            (target.data.refined.mass /
              ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
                ENNReal)))) := by
            rw [nine_four_hundredths_eq]
            ring
      _ ≤ (1 / 10 : ENNReal) * ((1 / 4 : ENNReal) * dyadic.mass) := by
        gcongr
      _ ≤ (1 / 10 : ENNReal) * constantShading.mass := by
        gcongr
  have propertyThreeMass : (9 / 10 : ENNReal) * constantShading.mass ≤
      propertyThree.mass :=
    retained_mass_of_error_le_fraction paper_shading_mass_ne_top
      (by norm_num) nine_tenths_add_one_tenth
      propertyThreeRaw secondErrorOnConstant
  have propertyThreeReferenceMass : (9 / 40 : ENNReal) * dyadic.mass ≤
      propertyThree.mass := by
    calc
      (9 / 40 : ENNReal) * dyadic.mass =
          (9 / 10 : ENNReal) * ((1 / 4 : ENNReal) * dyadic.mass) := by
        convert congrArg (fun coefficient : ENNReal => coefficient * dyadic.mass)
          nine_fortieths_eq using 1
        ring
      _ ≤ (9 / 10 : ENNReal) * constantShading.mass := by gcongr
      _ ≤ propertyThree.mass := propertyThreeMass
  have propertyThreeCubical : WZ1PaperIsCubicalShading propertyThree :=
    paperGridCellPrune_cubical_of_boundaryPruned boundaryPruning htau
      (fun index point hpoint =>
        dyadicBoundarySub index <| propertyOneSub index <|
          constantSub index hpoint) constantCubical
  have selectedPositive : 0 < selectedMultiplicity := by
    have halfPositive : 0 < (multiplicity + 1) / 2 := by
      apply Nat.div_pos
      · omega
      · norm_num
    exact halfPositive.trans_le selectedHalf
  have sourceFloorLtSelected :
      target.terminal.fineDegreeFloor * target.terminal.muFine <
        4 * selectedMultiplicity := by
    have deltaSmall : delta ≤ 1 / 10000 :=
      robustScale.2.1.trans hrobustSmall
    have deltaLtOne : delta < 1 := deltaSmall.trans_lt (by norm_num)
    have terminalMassPos : 0 < target.data.refined.mass := by
      have fraction := pure_refinement_fraction_pos_ne_top
        targetReentry.normalization.final_extremal.delta_pos deltaLtOne 61
      have sourceMassPos := cropped_extremal_shading_mass_pos
        targetReentry.normalization.final_extremal
        targetReentry.normalization.line_class <|
          robustScale.2.1.trans <| hrobustSmall.trans <| by norm_num
      exact (ENNReal.mul_pos fraction.1.ne' sourceMassPos.ne').trans_le
        target.total_mass_retention
    have dyadicMassPos : 0 < dyadic.mass := by
      have denominatorTop :
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal) ≠ ⊤ := by simp
      exact (ENNReal.mul_pos (by norm_num : (9 / 10 : ENNReal) ≠ 0)
        (ENNReal.div_pos terminalMassPos.ne' denominatorTop).ne').trans_le
          dyadicMass
    have constantMassPos : 0 < constantShading.mass := by
      exact (ENNReal.mul_pos (by norm_num : (1 / 4 : ENNReal) ≠ 0)
        dyadicMassPos.ne').trans_le quarterMass
    have constantPoint : constantShading.union.Nonempty :=
      paperShading_union_nonempty_of_mass_pos constantMassPos
    rcases constantPoint with ⟨point, pointMem⟩
    have pointDyadic : point ∈ dyadic.union := by
      rcases pointMem with ⟨index, indexMem⟩
      exact ⟨index, propertyOneSub index (constantSub index indexMem)⟩
    have pointTerminal : point ∈ target.data.refined.union := by
      rcases pointDyadic with ⟨index, indexMem⟩
      exact ⟨index, dyadicSub index indexMem⟩
    have terminalFloor :
        target.terminal.fineDegreeFloor * target.terminal.muFine ≤
          target.data.refined.pointMultiplicity point :=
      target.terminal.fine_pointMultiplicity_floor_on_union pointTerminal
    have dyadicMultiplicityEq : dyadic.pointMultiplicity point =
        target.data.refined.pointMultiplicity point := by
      have pointBoundary : point ∈ boundaryPruning.pruned.union := by
        rcases pointDyadic with ⟨index, indexMem⟩
        exact ⟨index, dyadicBoundarySub index indexMem⟩
      calc
        dyadic.pointMultiplicity point =
            boundaryPruning.pruned.pointMultiplicity point := by
          dsimp only [dyadic]
          exact dyadicBandSubshading_pointMultiplicity_eq pointDyadic
        _ = target.data.refined.pointMultiplicity point :=
          boundaryPruned_pointMultiplicity_eq boundaryPruning pointBoundary
    have dyadicUpperAtPoint :
        dyadic.pointMultiplicity point < 2 * multiplicity := by
      exact_mod_cast dyadicUpper point pointDyadic
    have result : target.terminal.fineDegreeFloor * target.terminal.muFine <
        4 * selectedMultiplicity := by
      calc
        target.terminal.fineDegreeFloor * target.terminal.muFine ≤
            target.data.refined.pointMultiplicity point := terminalFloor
        _ = dyadic.pointMultiplicity point := dyadicMultiplicityEq.symm
        _ < (2 * multiplicity : ℕ) := dyadicUpperAtPoint
        _ ≤ 4 * selectedMultiplicity := by omega
    exact result
  have closeBound := proposition63_two_rich_close_count_scaled_absorbed outer
    targetReentry hcurrentSubOuter htargetReentryLoss target
    (kappa := robustScale.1) hrobustSmall 4 hcrossCall
  have transverse : ∀ point ∈ propertyThree.union,
      ∀ index, point ∈ propertyThree.carrier index →
        ∃ other, point ∈ propertyOne.carrier other ∧
          Real.rpow delta epsilon₃ ≤
            ‖wz1Cross (target.data.selected.family.tube index).direction
              (target.data.selected.family.tube other).direction‖ := by
    intro point pointMem index indexMem
    have pointConstant : point ∈ constantShading.union := by
      rcases pointMem with ⟨other, otherMem⟩
      exact ⟨other, propertyThreeSub other otherMem⟩
    have pointTerminal : point ∈ target.data.refined.union := by
      rcases pointConstant with ⟨other, otherMem⟩
      exact ⟨other, dyadicSub other <| propertyOneSub other <|
        constantSub other otherMem⟩
    have indexTerminal : point ∈ target.data.refined.carrier index :=
      dyadicSub index <| propertyOneSub index <| constantSub index <|
        propertyThreeSub index indexMem
    have closeFour := closeBound point pointTerminal index indexTerminal
    have closeLt :
        (paperCloseDirectionCount target.data.refined point index
          robustScale.1 : ENNReal) < (selectedMultiplicity : ENNReal) := by
      have closeFourLt :
          (4 : ENNReal) *
              (paperCloseDirectionCount target.data.refined point index
                robustScale.1 : ENNReal) <
            4 * (selectedMultiplicity : ENNReal) := by
        have closeFourCast : (4 : ENNReal) *
              (paperCloseDirectionCount target.data.refined point index
                robustScale.1 : ENNReal) ≤
            ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
              ENNReal) := by
          exact_mod_cast closeFour
        have sourceFloorCast :
            ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
              ENNReal) < (selectedMultiplicity : ENNReal) * 4 := by
          simpa [mul_comm] using
            (show ((target.terminal.fineDegreeFloor *
                target.terminal.muFine : ℕ) : ENNReal) <
              ((4 * selectedMultiplicity : ℕ) : ENNReal) by
                exact_mod_cast sourceFloorLtSelected)
        exact closeFourCast.trans_lt (by
          simpa [mul_comm] using sourceFloorCast)
      have canceled :
          (paperCloseDirectionCount target.data.refined point index
            robustScale.1 : ENNReal) < (selectedMultiplicity : ENNReal) := by
        apply (ENNReal.mul_lt_mul_iff_left
          (a := (paperCloseDirectionCount target.data.refined point index
            robustScale.1 : ENNReal))
          (b := (selectedMultiplicity : ENNReal))
          (by norm_num : (4 : ENNReal) ≠ 0)
          (by norm_num : (4 : ENNReal) ≠ ⊤)).mp
        simpa [mul_comm] using closeFourLt
      exact canceled
    rcases paperTransverseFromCloseCountLtMultiplicity point pointConstant
        (constantMultiplicity point pointConstant).1
        (fun i => (constantSub i).trans <|
          (propertyOneSub i).trans <| dyadicSub i) index robustScale.1 closeLt with
      ⟨other, otherMem, otherTransverse⟩
    exact ⟨other, constantSub other otherMem, hkappa.trans otherTransverse⟩
  have propertyOneFull : ∀ index point,
      point ∈ propertyOne.carrier index →
        Kakeya.realRpowENN delta (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
          volume (propertyOne.carrier index ∩ Metric.closedBall point tau) := by
    intro index point pointMem
    have full := paperGridCellPrune_fullness htau
      (mul_nonneg (Real.rpow_nonneg target.terminal.delta_pos.le _) htau.le)
      pointMem
    have thresholdEq : ENNReal.ofReal threshold =
        Kakeya.realRpowENN delta (2 + 2 * epsilon₁) * ENNReal.ofReal tau := by
      dsimp only [threshold, Kakeya.realRpowENN]
      exact ENNReal.ofReal_mul
        (Real.rpow_nonneg target.terminal.delta_pos.le _)
    calc
      Kakeya.realRpowENN delta (2 + 2 * epsilon₁) * ENNReal.ofReal tau =
          ENNReal.ofReal threshold := thresholdEq.symm
      _ ≤ volume (propertyOne.carrier index ∩
          Metric.closedBall point tau) := by
        exact full
  have propertyThreeFull : ∀ index point,
      point ∈ propertyThree.carrier index →
        Kakeya.realRpowENN delta (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
          volume (propertyThree.carrier index ∩ Metric.closedBall point tau) := by
    intro index point pointMem
    have full := paperGridCellPrune_fullness htau
      (mul_nonneg (Real.rpow_nonneg target.terminal.delta_pos.le _) htau.le)
      pointMem
    have thresholdEq : ENNReal.ofReal threshold =
        Kakeya.realRpowENN delta (2 + 2 * epsilon₁) * ENNReal.ofReal tau := by
      dsimp only [threshold, Kakeya.realRpowENN]
      exact ENNReal.ofReal_mul
        (Real.rpow_nonneg target.terminal.delta_pos.le _)
    calc
      Kakeya.realRpowENN delta (2 + 2 * epsilon₁) * ENNReal.ofReal tau =
          ENNReal.ofReal threshold := thresholdEq.symm
      _ ≤ volume (propertyThree.carrier index ∩
          Metric.closedBall point tau) := by
        exact full
  let cordoba : PureWZ2CordobaPropertyPData
      (sigma := sigma) (coarseShading := target.data.refined)
      (tau := tau) epsilon₁ epsilon₃ :=
    { propertyOne := propertyOne
      propertyOne_sub := fun index =>
        (propertyOneSub index).trans (dyadicSub index)
      propertyThree := propertyThree
      propertyThree_sub := fun index =>
        (propertyThreeSub index).trans (constantSub index)
      propertyOne_full := propertyOneFull
      transverse := transverse }
  exact ⟨{
    boundaryPruning := boundaryPruning
    level := level
    dyadic := dyadic
    dyadic_sub := dyadicSub
    dyadic_cubical := dyadicCubical
    dyadic_lower := dyadicLower
    dyadic_upper := dyadicUpper
    dyadic_mass := dyadicMass
    propertyOne := propertyOne
    propertyOne_sub := propertyOneSub
    propertyOne_mass := propertyOneMass
    selectedMultiplicity := selectedMultiplicity
    constantShading := constantShading
    constant_sub := constantSub
    constant_multiplicity := constantMultiplicity
    constant_mass := quarterMass
    propertyThree := propertyThree
    propertyThree_sub := propertyThreeSub
    propertyThree_cubical := propertyThreeCubical
    propertyThree_mass := propertyThreeReferenceMass
    propertyThree_full := propertyThreeFull
    cordoba := cordoba
    cordoba_propertyOne := rfl
    cordoba_propertyThree := rfl }⟩

/-- Compatibility constructor from the original explicit boundary-error
receipts.  New concrete callers can instead construct the pruning by CWA and
invoke `proposition63_robust_tau_localization_of_boundary_pruning`. -/
theorem proposition63_robust_tau_localization
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hdeltaTau : delta ≤ tau)
    (hdeltaGrid : delta ≤ gridSide (tau / 2))
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hboundary :
      ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
          ENNReal) * (target.terminal.muFine : ENNReal) *
          ENNReal.ofReal (1000 * delta / gridSide (tau / 2)) <
        target.data.refined.mass)
    (hboundaryError :
      ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
          ENNReal) * (target.terminal.muFine : ENNReal) *
          ENNReal.ofReal (1000 * delta / gridSide (tau / 2)) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass)
    (hfirstError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 100 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hsecondError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 400 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hcrossCall :
      4 * (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal))
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1) :
    Nonempty (Proposition63RobustTauLocalizationData
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      outer targetReentry hcurrentSubOuter htargetReentryLoss target) := by
  let multiplicityCap : ENNReal :=
    ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
      ENNReal) * target.terminal.muFine
  have terminalMultiplicityCap : ∀ point,
      (target.data.refined.pointMultiplicity point : ENNReal) ≤
        multiplicityCap := fun point =>
    target.terminal.fine_pointMultiplicity_upper point
  rcases wz2_prop_sticky_boundary_cell_pruning
      target.terminal.delta_pos hdeltaGrid
      (show 0 < gridSide (tau / 2) by unfold gridSide; positivity)
      (show gridSide (tau / 2) ≤ 1 by
        unfold gridSide
        have sqrtThreeGeOne : 1 ≤ Real.sqrt 3 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
            Real.sqrt_nonneg 3]
        calc
          2 * (tau / 2) / Real.sqrt 3 = tau / Real.sqrt 3 := by ring
          _ ≤ tau := div_le_self htau.le sqrtThreeGeOne
          _ ≤ 1 := htauOne)
      target.data.refined target.terminal.fine_cubical multiplicityCap
      terminalMultiplicityCap (by simpa only [multiplicityCap, Nat.cast_mul]
        using hboundary) with ⟨boundaryPruning⟩
  have boundaryMass : (9 / 10 : ENNReal) * target.data.refined.mass ≤
      boundaryPruning.pruned.mass := by
    apply retained_mass_of_error_le_fraction paper_shading_mass_ne_top
      (by norm_num) nine_tenths_add_one_tenth
      boundaryPruning.source_mass_le_explicit
    simpa only [multiplicityCap, Nat.cast_mul] using hboundaryError
  exact proposition63_robust_tau_localization_of_boundary_pruning outer
    targetReentry hcurrentSubOuter htargetReentryLoss target hdeltaTau htau
    boundaryPruning boundaryMass hfirstError hsecondError hrobustSmall
    hcrossCall hkappa

/-- Construct robust localization from the sharp ambient-CWA boundary budget.
This is the production fixed-grid route: the boundary loss is estimated by
CWA, rather than by the terminal pointwise multiplicity cap. -/
theorem proposition63_robust_tau_localization_of_cwa
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hdeltaTau : delta ≤ tau)
    (hdeltaGrid : delta ≤ gridSide (tau / 2))
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hperiodic : 50 * delta ≤ gridSide (tau / 2))
    (hboundaryCWA :
      let side := gridSide (tau / 2)
      targetReentry.normalization.croppedFamily.enncard *
          ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta
                (-targetReentry.reentryNormalizationLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt (delta / side))) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass)
    (hfirstError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 100 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hsecondError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 400 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hcrossCall :
      4 * (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal))
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1) :
    Nonempty (Proposition63RobustTauLocalizationData
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      outer targetReentry hcurrentSubOuter htargetReentryLoss target) := by
  rcases target.boundaryPruning_of_cwa htargetReentryLoss hdeltaGrid htau
      htauOne hperiodic hboundaryCWA with ⟨boundaryPruning, boundaryMass⟩
  exact proposition63_robust_tau_localization_of_boundary_pruning outer
    targetReentry hcurrentSubOuter htargetReentryLoss target hdeltaTau htau
    boundaryPruning boundaryMass hfirstError hsecondError hrobustSmall
    hcrossCall hkappa

/-- The explicit local-volume envelope for the root-relative target call. -/
def proposition63RobustTauTotalVolume
    (delta sigma targetNormalizationLoss targetLoss targetScale tau : ℝ) : ℝ :=
  216 * ((3 * tau) / targetScale) ^ 3 *
    Real.rpow delta (sigma - targetNormalizationLoss) *
    Real.rpow targetScale (3 - sigma - 2 * targetLoss)

/-- The robust/tau localization has the exact point-centered projection
estimate needed by Lemma 17.  Its total-volume bound is generated from the
target rich call's own balanced cells; the only remaining hypothesis is the
scalar absorption into the requested covering constant. -/
theorem Proposition63RobustTauLocalizationData.pointCenteredCovering
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    {outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale}
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    {targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current}
    {hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined)}
    {htargetReentryLoss : 0 < targetReentryLoss}
    {targetScale : WZ2PaperRequestedScale delta}
    {target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale}
    (localization : Proposition63RobustTauLocalizationData
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      outer targetReentry hcurrentSubOuter htargetReentryLoss target)
    (planeMap : Point3 → Point3) (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ target.data.refined.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      point ∈ target.data.refined.carrier index →
        |@Inner.inner ℝ Point3 _
          (target.data.selected.family.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (htauPos : 0 < tau) (hdeltaTau : delta ≤ tau)
    (htargetTau : targetScale.1 ≤ 3 * tau)
    (htauSq : tau ^ 2 ≤ 4 * delta) (htauOne : tau ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              targetReentry.reentryNormalizationLoss targetLoss
              targetScale.1 tau /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                tau ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta tau incidenceBound
              coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN (tau / delta) (1 - sigma)) :
    PureWZ2PointCenteredCoveringAt localization.propertyThree planeMap
      (Real.toNNReal delta) tau
      (C * Kakeya.realRpowENN (tau / delta) (1 - sigma)) := by
  have hratioNonnegative : 0 ≤ (3 * tau) / targetScale.1 :=
    div_nonneg (mul_nonneg (by norm_num) htauPos.le)
      target.data.coarse_extremal.delta_pos.le
  have hdeltaPower :
      0 ≤ Real.rpow delta
        (sigma - targetReentry.reentryNormalizationLoss) :=
    Real.rpow_nonneg target.terminal.delta_pos.le _
  have htargetPower :
      0 ≤ Real.rpow targetScale.1 (3 - sigma - 2 * targetLoss) :=
    Real.rpow_nonneg target.data.coarse_extremal.delta_pos.le _
  intro point
  have hpointCordoba : (point : Point3) ∈
      localization.cordoba.propertyThree.union := by
    rw [localization.cordoba_propertyThree]
    exact point.property
  have hcover := pureWZ2_cordoba_projection_covering_of_local_volume
    localization.cordoba planeMap incidenceBound
    (fun p hp => hplaneUnit p <| by
      rcases hp with ⟨index, hindex⟩
      rw [localization.cordoba_propertyThree] at hindex
      exact ⟨index, localization.dyadic_sub index <|
        localization.propertyOne_sub index <|
          localization.constant_sub index <|
            localization.propertyThree_sub index hindex⟩)
    hplaneLipschitz
    (fun index p hp => hplaneIncidence index p <|
      localization.dyadic_sub index <|
        localization.propertyOne_sub index <| by
          rw [← localization.cordoba_propertyOne]
          exact hp)
    point hpointCordoba target.terminal.delta_pos hdeltaSmall
    htauPos hdeltaTau htauSq htauOne hsigma hsigmaOne
    hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog hlog
    (fun index p hp => by
      rw [localization.cordoba_propertyThree] at hp ⊢
      exact localization.propertyThree_full index p hp) haxis
    (proposition63RobustTauTotalVolume delta sigma
      targetReentry.reentryNormalizationLoss targetLoss targetScale.1 tau)
    (by
      have raw :=
        Proposition63RichTerminalStickyData.target_three_tau_volume_upper
          htargetReentryLoss target htargetSmall htauPos htargetTau
          (point : Point3)
      apply raw.trans_eq
      change
        (8 * 27 : ENNReal) *
            ENNReal.ofReal (((3 * tau) / targetScale.1) ^ 3) *
            (ENNReal.ofReal
                (Real.rpow delta
                  (sigma - targetReentry.reentryNormalizationLoss)) *
              ENNReal.ofReal
                (Real.rpow targetScale.1
                  (3 - sigma - 2 * targetLoss))) =
          ENNReal.ofReal
            (216 * ((3 * tau) / targetScale.1) ^ 3 *
              Real.rpow delta
                (sigma - targetReentry.reentryNormalizationLoss) *
              Real.rpow targetScale.1
                (3 - sigma - 2 * targetLoss))
      rw [show (8 * 27 : ENNReal) = ENNReal.ofReal (216 : ℝ) by norm_num]
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 216)]
      rw [← mul_assoc]
      rw [← ENNReal.ofReal_mul
        (mul_nonneg (by norm_num) (pow_nonneg hratioNonnegative 3))]
      rw [← ENNReal.ofReal_mul
        (mul_nonneg
          (mul_nonneg (by norm_num) (pow_nonneg hratioNonnegative 3))
          hdeltaPower)])
  rw [localization.cordoba_propertyThree] at hcover
  exact hcover.trans harithmetic

/-- Lift the localized Property-(P) shading back to the actual current
`delta`-family and immediately restore extremality and CWA.  The coefficient
`81/400` is exactly the product of the boundary, dyadic-band,
constant-multiplicity, and second grid-pruning retentions. -/
theorem Proposition63RobustTauLocalizationData.liftPointCoverOfCover
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    {outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale}
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    {targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current}
    {hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined)}
    {htargetReentryLoss : 0 < targetReentryLoss}
    {targetScale : WZ2PaperRequestedScale delta}
    {target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale}
    (localization : Proposition63RobustTauLocalizationData
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      outer targetReentry hcurrentSubOuter htargetReentryLoss target)
    (planeMap : Point3 → Point3) (constant : ENNReal)
    (hcover : PureWZ2PointCenteredCoveringAt localization.propertyThree
      planeMap (Real.toNNReal delta) tau constant)
    (hdeltaLtOne : delta < 1)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      outerReentry.toNormalizationData.croppedFamily
      (Kakeya.realRpowENN delta (-targetReentryLoss)))
    (hreentryOutput : targetReentryLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        (((81 / 400 : ENNReal) *
            (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
              ENNReal))⁻¹ *
            wz2PaperPureRefinementFraction delta 61) *
          ((73 / 100 : ENNReal) * targetReentry.normalizationWeight))
        targetReentry.regularized.regularizationLoss *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta targetReentryLoss) :
    ∃ result : Proposition63LiftedPointCoverData
        (outputLoss := outputLoss) (queryScale := delta)
        (spatialRadius := tau) outerReentry.toNormalizationData
        current planeMap constant,
      result.state.shading.union = localization.propertyThree.union := by
  let candidate : WZ1PaperTubeShading
      targetReentry.normalization.croppedFamily :=
    extendShading target.data.selected localization.propertyThree
  have candidateSub : PaperIsSubshading candidate
      targetReentry.normalization.croppedRefined := by
    apply extendShading_subshading
    intro index point hpoint
    exact target.data.subshading index <|
      localization.dyadic_sub index <|
        localization.propertyOne_sub index <|
          localization.constant_sub index <|
            localization.propertyThree_sub index hpoint
  have candidateCubical : WZ1PaperIsCubicalShading candidate :=
    extendShading_cubical target.data.selected
      localization.propertyThree_cubical
  have candidateCover : PureWZ2PointCenteredCoveringAt candidate planeMap
      (Real.toNNReal delta) tau constant := by
    intro point
    have pointLocal : (point : Point3) ∈ localization.propertyThree.union := by
      rw [← extendShading_union target.data.selected
        localization.propertyThree]
      exact point.property
    simpa only [candidate, extendShading_union target.data.selected
      localization.propertyThree] using hcover ⟨point, pointLocal⟩
  let logFactor : ENNReal :=
    ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)
  let refinementFraction : ENNReal :=
    wz2PaperPureRefinementFraction delta 61
  let stateLeft : ENNReal :=
    (81 / 400 : ENNReal) * logFactor⁻¹ * refinementFraction
  have targetMass : refinementFraction *
      targetReentry.normalization.croppedRefined.mass ≤
        target.data.refined.mass := by
    simpa only [refinementFraction] using target.total_mass_retention
  have stateMass : stateLeft *
      targetReentry.normalization.croppedRefined.mass ≤ candidate.mass := by
    calc
      stateLeft * targetReentry.normalization.croppedRefined.mass =
          (9 / 40 : ENNReal) *
            ((9 / 10 : ENNReal) *
              (refinementFraction *
                targetReentry.normalization.croppedRefined.mass /
                  logFactor)) := by
        dsimp only [stateLeft]
        rw [eighty_one_four_hundredths_eq]
        simp only [div_eq_mul_inv]
        ring
      _ ≤ (9 / 40 : ENNReal) *
          ((9 / 10 : ENNReal) *
            (target.data.refined.mass / logFactor)) := by
        gcongr
      _ ≤ (9 / 40 : ENNReal) * localization.dyadic.mass := by
        exact mul_le_mul_left' (by
          simpa only [logFactor] using localization.dyadic_mass) _
      _ ≤ localization.propertyThree.mass := localization.propertyThree_mass
      _ = candidate.mass := by
        exact (extendShading_mass target.data.selected
          localization.propertyThree).symm
  have logFactorPos : 0 < logFactor := by
    dsimp only [logFactor]
    exact_mod_cast Nat.zero_lt_succ (Nat.log 2 target.data.selected.family.card)
  have logFactorTop : logFactor ≠ ⊤ := by
    simp [logFactor]
  have refinementBounds := pure_refinement_fraction_pos_ne_top
    targetReentry.reentry_extremal.delta_pos hdeltaLtOne 61
  have stateLeftPos : 0 < stateLeft := by
    dsimp only [stateLeft]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (by norm_num : (81 / 400 : ENNReal) ≠ 0)
        (ENNReal.inv_ne_zero.mpr logFactorTop)).ne'
      refinementBounds.1.ne'
  have stateLeftTop : stateLeft ≠ ⊤ := by
    dsimp only [stateLeft]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.div_ne_top (by norm_num) (by norm_num))
        (ENNReal.inv_ne_top.mpr logFactorPos.ne'))
      refinementBounds.2
  rcases targetReentry.liftPointCover candidate candidateSub
      candidateCubical planeMap constant stateLeft 1 candidateCover
      (by simpa only [one_mul] using stateMass) stateLeftPos stateLeftTop
      (by norm_num) hcurrentCWA hreentryOutput houtputLoss
      (by simpa only [stateLeft, mul_one] using hrestore) with
    ⟨next, multiplicity, mass, cover, _unionEq⟩
  have regularizationPos :
      0 < targetReentry.regularized.regularizationLoss := by
    rw [targetReentry.regularized.regularizationLoss_eq]
    positivity
  have regularizationTop :
      targetReentry.regularized.regularizationLoss ≠ ⊤ := by
    rw [targetReentry.regularized.regularizationLoss_eq]
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  let retainedFactor : ENNReal :=
    (stateLeft *
      ((73 / 100 : ENNReal) * targetReentry.normalizationWeight)) /
        targetReentry.regularized.regularizationLoss
  have retained : retainedFactor *
      current.mass ≤
        next.shading.mass := by
    have mass' :
        (stateLeft *
            ((73 / 100 : ENNReal) * targetReentry.normalizationWeight)) *
          current.mass ≤
        targetReentry.regularized.regularizationLoss * next.shading.mass := by
      calc
        _ ≤ (targetReentry.regularized.regularizationLoss * 1) *
            next.shading.mass := mass
        _ = _ := by rw [mul_one]
    have divided :
        (stateLeft *
            ((73 / 100 : ENNReal) * targetReentry.normalizationWeight) *
          current.mass) /
            targetReentry.regularized.regularizationLoss ≤
          next.shading.mass := by
      apply (ENNReal.div_le_iff regularizationPos.ne' regularizationTop).2
      simpa [mul_assoc, mul_comm, mul_left_comm] using mass'
    simpa only [retainedFactor, div_eq_mul_inv, mul_assoc, mul_comm,
      mul_left_comm] using divided
  have retainedPos : 0 < retainedFactor := by
    dsimp only [retainedFactor]
    exact ENNReal.div_pos
      (ENNReal.mul_pos stateLeftPos.ne'
        (ENNReal.mul_pos (by norm_num : (73 / 100 : ENNReal) ≠ 0)
          targetReentry.normalization_weight_ne_zero).ne').ne'
      regularizationTop
  have retainedTop : retainedFactor ≠ ⊤ := by
    dsimp only [retainedFactor]
    exact ENNReal.div_ne_top
      (ENNReal.mul_ne_top stateLeftTop <|
        ENNReal.mul_ne_top
          (ENNReal.div_ne_top (by norm_num) (by norm_num))
          targetReentry.normalization_weight_ne_top)
      regularizationPos.ne'
  refine ⟨{
    state := next
    multiplicity := multiplicity
    retainedFactor := retainedFactor
    retained := retained
    retained_factor_pos := retainedPos
    retained_factor_ne_top := retainedTop
    cover := cover
  }, ?_⟩
  exact _unionEq.trans <| extendShading_union target.data.selected
    localization.propertyThree

/-- Keep a robust point cover on the current re-entry normalization and
restore extremality there.  Unlike `liftPointCoverOfCover`, this theorem does
not cross the re-entry subfamily boundary, so it pays neither the `73/100`
ordinary-density factor nor the external-weight regularization loss.  This is
the state needed after the square-root localization, immediately before the
full-grain preparation. -/
theorem Proposition63RobustTauLocalizationData.localPointCoverOfCover
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    {outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale}
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    {targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current}
    {hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined)}
    {htargetReentryLoss : 0 < targetReentryLoss}
    {targetScale : WZ2PaperRequestedScale delta}
    {target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale}
    (localization : Proposition63RobustTauLocalizationData
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      outer targetReentry hcurrentSubOuter htargetReentryLoss target)
    (planeMap : Point3 → Point3) (constant : ENNReal)
    (hcover : PureWZ2PointCenteredCoveringAt localization.propertyThree
      planeMap (Real.toNNReal delta) tau constant)
    (hdeltaLtOne : delta < 1)
    (hnormalizationOutput :
      targetReentry.reentryNormalizationLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        ((81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹ *
          wz2PaperPureRefinementFraction delta 61) 1 *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta
          targetReentry.reentryNormalizationLoss) :
    ∃ result : Proposition63LiftedPointCoverData
        (outputLoss := outputLoss) (queryScale := delta)
        (spatialRadius := tau) targetReentry.normalization
        targetReentry.normalization.croppedRefined planeMap constant,
      result.state.shading.union = localization.propertyThree.union ∧
        result.state.shading.union ⊆
          (extendShading target.data.selected target.data.refined).union ∧
        result.retainedFactor =
          (81 / 400 : ENNReal) *
            (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
              ENNReal))⁻¹ *
            wz2PaperPureRefinementFraction delta 61 := by
  let candidate : WZ1PaperTubeShading
      targetReentry.normalization.croppedFamily :=
    extendShading target.data.selected localization.propertyThree
  have candidateSub : PaperIsSubshading candidate
      targetReentry.normalization.croppedRefined := by
    apply extendShading_subshading
    intro index point hpoint
    exact target.data.subshading index <|
      localization.dyadic_sub index <|
        localization.propertyOne_sub index <|
          localization.constant_sub index <|
            localization.propertyThree_sub index hpoint
  have candidateCubical : WZ1PaperIsCubicalShading candidate :=
    extendShading_cubical target.data.selected
      localization.propertyThree_cubical
  have candidateSubTarget : PaperIsSubshading candidate
      (extendShading target.data.selected target.data.refined) := by
    apply extendShading_subshading
    intro index point hpoint
    rw [extendShading_carrier_mem]
    exact localization.dyadic_sub index <|
      localization.propertyOne_sub index <|
        localization.constant_sub index <|
          localization.propertyThree_sub index hpoint
  have candidateCover : PureWZ2PointCenteredCoveringAt candidate planeMap
      (Real.toNNReal delta) tau constant := by
    intro point
    have pointLocal : (point : Point3) ∈ localization.propertyThree.union := by
      rw [← extendShading_union target.data.selected
        localization.propertyThree]
      exact point.property
    simpa only [candidate, extendShading_union target.data.selected
      localization.propertyThree] using hcover ⟨point, pointLocal⟩
  let logFactor : ENNReal :=
    ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)
  let refinementFraction : ENNReal :=
    wz2PaperPureRefinementFraction delta 61
  let stateLeft : ENNReal :=
    (81 / 400 : ENNReal) * logFactor⁻¹ * refinementFraction
  have targetMass : refinementFraction *
      targetReentry.normalization.croppedRefined.mass ≤
        target.data.refined.mass := by
    simpa only [refinementFraction] using target.total_mass_retention
  have candidateMass : stateLeft *
      targetReentry.normalization.croppedRefined.mass ≤ candidate.mass := by
    calc
      stateLeft * targetReentry.normalization.croppedRefined.mass =
          (9 / 40 : ENNReal) *
            ((9 / 10 : ENNReal) *
              (refinementFraction *
                targetReentry.normalization.croppedRefined.mass /
                  logFactor)) := by
        dsimp only [stateLeft]
        rw [eighty_one_four_hundredths_eq]
        simp only [div_eq_mul_inv]
        ring
      _ ≤ (9 / 40 : ENNReal) *
          ((9 / 10 : ENNReal) * (target.data.refined.mass / logFactor)) := by
        gcongr
      _ ≤ (9 / 40 : ENNReal) * localization.dyadic.mass := by
        exact mul_le_mul_left' (by
          simpa only [logFactor] using localization.dyadic_mass) _
      _ ≤ localization.propertyThree.mass := localization.propertyThree_mass
      _ = candidate.mass := by
        exact (extendShading_mass target.data.selected
          localization.propertyThree).symm
  have logFactorPos : 0 < logFactor := by
    dsimp only [logFactor]
    exact_mod_cast Nat.zero_lt_succ (Nat.log 2 target.data.selected.family.card)
  have logFactorTop : logFactor ≠ ⊤ := by simp [logFactor]
  have refinementBounds := pure_refinement_fraction_pos_ne_top
    targetReentry.reentry_extremal.delta_pos hdeltaLtOne 61
  have stateLeftPos : 0 < stateLeft := by
    dsimp only [stateLeft]
    exact ENNReal.mul_pos
      (ENNReal.mul_pos (by norm_num : (81 / 400 : ENNReal) ≠ 0)
        (ENNReal.inv_ne_zero.mpr logFactorTop)).ne'
      refinementBounds.1.ne'
  have stateLeftTop : stateLeft ≠ ⊤ := by
    dsimp only [stateLeft]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.div_ne_top (by norm_num) (by norm_num))
        (ENNReal.inv_ne_top.mpr logFactorPos.ne'))
      refinementBounds.2
  let nextShading := paperCommonSpatialHull
    targetReentry.normalization.croppedRefined candidate
  have nextSub : PaperIsSubshading nextShading
      targetReentry.normalization.croppedRefined :=
    paperCommonSpatialHull_subshading _ _
  have nextCubical : WZ1PaperIsCubicalShading nextShading :=
    paperCommonSpatialHull_cubical
      targetReentry.normalization.final_extremal.cubical candidateCubical
  have nextUnion : nextShading.union = localization.propertyThree.union := by
    calc
      nextShading.union = candidate.union :=
        paperCommonSpatialHull_union candidateSub
      _ = localization.propertyThree.union :=
        extendShading_union target.data.selected localization.propertyThree
  have nextMass : stateLeft *
      targetReentry.normalization.croppedRefined.mass ≤ nextShading.mass :=
    candidateMass.trans (paperCommonSpatialHull_mass_lower candidateSub)
  let massLoss := proposition63Lemma43MassLoss stateLeft 1
  have nextMassInv : massLoss⁻¹ *
      targetReentry.normalization.croppedRefined.mass ≤ nextShading.mass :=
    proposition63Lemma43MassLoss_inv_mul_le stateLeftPos stateLeftTop
      (by norm_num) (by simpa only [one_mul] using nextMass)
  have nextExtremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      targetReentry.normalization.croppedFamily nextShading := by
    apply transfer_cropped_extremal_to_subshading massLoss
      (proposition63Lemma43MassLoss_pos _ _)
      (proposition63Lemma43MassLoss_ne_top stateLeftPos (by norm_num))
      targetReentry.normalization.final_extremal nextSub nextMassInv
      nextCubical hnormalizationOutput
    · simpa only [massLoss, stateLeft, logFactor, refinementFraction]
        using hrestore
    · exact targetReentry.reentry_extremal.delta_pos
    · exact targetReentry.reentry_extremal.delta_le_one
    · exact houtputLoss
  have nextCWA : WZ2PaperConvexWolffBound
      targetReentry.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-outputLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := targetReentry.normalization.croppedRefined)
      (_shading2 := nextShading)
      targetReentry.normalization.cropped_top_level_cwa
      hnormalizationOutput targetReentry.reentry_extremal.delta_pos
      targetReentry.reentry_extremal.delta_le_one
  let state : Proposition63ExtremalShadingData
      (sigma := sigma) (outputLoss := outputLoss)
      targetReentry.normalization.croppedRefined :=
    { shading := nextShading
      subshading := nextSub
      extremal := nextExtremal
      cwa := nextCWA }
  have nextCover : PureWZ2PointCenteredCoveringAt state.shading planeMap
      (Real.toNNReal delta) tau constant := by
    intro point
    have pointLocal : (point : Point3) ∈ localization.propertyThree.union := by
      rw [← nextUnion]
      exact point.property
    simpa only [state, nextUnion] using hcover ⟨point, pointLocal⟩
  refine ⟨{
    state := state
    multiplicity := paperCommonSpatialHull_pointMultiplicity_eq
      targetReentry.normalization.croppedRefined candidate
    retainedFactor := stateLeft
    retained := nextMass
    retained_factor_pos := stateLeftPos
    retained_factor_ne_top := stateLeftTop
    cover := nextCover
  }, nextUnion, ?_, rfl⟩
  rw [nextUnion, ← extendShading_union target.data.selected
    localization.propertyThree]
  exact paperSubshading_union candidateSubTarget

/-- Restore a robust point cover relative to the target rich terminal's own
zero-extension.  This is the intermediate form used between two applications
of Lemma 17: it remains carrierwise inside the rich terminal, so that the same
terminal can serve as the outer close-count witness for the next call. -/
theorem Proposition63RobustTauLocalizationData.pointCoverOnTargetAmbient
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ parentLoss
      outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    {outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale}
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    {targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current}
    {hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined)}
    {htargetReentryLoss : 0 < targetReentryLoss}
    {targetScale : WZ2PaperRequestedScale delta}
    {target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale}
    (localization : Proposition63RobustTauLocalizationData
      (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
      outer targetReentry hcurrentSubOuter htargetReentryLoss target)
    (planeMap : Point3 → Point3) (constant : ENNReal)
    (hcover : PureWZ2PointCenteredCoveringAt localization.propertyThree
      planeMap (Real.toNNReal delta) tau constant)
    (hnormalizationParent :
      targetReentry.reentryNormalizationLoss ≤ parentLoss)
    (hparentRetention :
      Kakeya.realRpowENN delta parentLoss ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            targetReentry.reentryNormalizationLoss)
    (hparentOutput : parentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        ((81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹) 1 *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta parentLoss) :
    ∃ result : Proposition63LiftedPointCoverData
        (outputLoss := outputLoss) (queryScale := delta)
        (spatialRadius := tau) targetReentry.normalization
        (extendShading target.data.selected target.data.refined) planeMap
        constant,
      result.state.shading.union = localization.propertyThree.union ∧
        result.retainedFactor =
          (81 / 400 : ENNReal) *
            (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
              ENNReal))⁻¹ := by
  let parent : WZ1PaperTubeShading
      targetReentry.normalization.croppedFamily :=
    extendShading target.data.selected target.data.refined
  let candidate : WZ1PaperTubeShading
      targetReentry.normalization.croppedFamily :=
    extendShading target.data.selected localization.propertyThree
  have candidateSub : PaperIsSubshading candidate parent := by
    apply extendShading_subshading
    intro index point hpoint
    change point ∈ (extendShading target.data.selected
      target.data.refined).carrier (target.data.selected.embedding index)
    rw [extendShading_carrier_mem]
    exact localization.dyadic_sub index <|
      localization.propertyOne_sub index <|
        localization.constant_sub index <|
          localization.propertyThree_sub index hpoint
  have candidateCubical : WZ1PaperIsCubicalShading candidate :=
    extendShading_cubical target.data.selected
      localization.propertyThree_cubical
  have candidateCover : PureWZ2PointCenteredCoveringAt candidate planeMap
      (Real.toNNReal delta) tau constant := by
    intro point
    have pointLocal : (point : Point3) ∈ localization.propertyThree.union := by
      rw [← extendShading_union target.data.selected
        localization.propertyThree]
      exact point.property
    simpa only [candidate, extendShading_union target.data.selected
      localization.propertyThree] using hcover ⟨point, pointLocal⟩
  let logFactor : ENNReal :=
    ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)
  let retainedFactor : ENNReal := (81 / 400 : ENNReal) * logFactor⁻¹
  have retained : retainedFactor * parent.mass ≤ candidate.mass := by
    rw [show parent.mass = target.data.refined.mass by
      exact extendShading_mass target.data.selected target.data.refined]
    rw [show candidate.mass = localization.propertyThree.mass by
      exact extendShading_mass target.data.selected
        localization.propertyThree]
    calc
      retainedFactor * target.data.refined.mass =
          (9 / 40 : ENNReal) *
            ((9 / 10 : ENNReal) *
              (target.data.refined.mass / logFactor)) := by
        dsimp only [retainedFactor]
        rw [eighty_one_four_hundredths_eq]
        simp only [div_eq_mul_inv]
        ring
      _ ≤ (9 / 40 : ENNReal) * localization.dyadic.mass := by
        exact mul_le_mul_left' (by
          simpa only [logFactor] using localization.dyadic_mass) _
      _ ≤ localization.propertyThree.mass := localization.propertyThree_mass
  have logFactorPos : 0 < logFactor := by
    dsimp only [logFactor]
    exact_mod_cast Nat.zero_lt_succ (Nat.log 2 target.data.selected.family.card)
  have retainedPos : 0 < retainedFactor := by
    dsimp only [retainedFactor]
    exact ENNReal.mul_pos (by norm_num : (81 / 400 : ENNReal) ≠ 0)
      (ENNReal.inv_ne_zero.mpr <| by simp [logFactor])
  have retainedTop : retainedFactor ≠ ⊤ := by
    dsimp only [retainedFactor]
    exact ENNReal.mul_ne_top
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
      (ENNReal.inv_ne_top.mpr logFactorPos.ne')
  have parentExtremal : WZ2PaperCroppedIsExtremal sigma parentLoss
      targetReentry.normalization.croppedFamily parent :=
    sticky_zero_extension_extremal
      targetReentry.normalization.final_extremal target.data
      hnormalizationParent hparentRetention
  have parentCWA : WZ2PaperConvexWolffBound
      targetReentry.normalization.croppedFamily
      (Kakeya.realRpowENN delta (-parentLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := targetReentry.normalization.croppedRefined)
      (_shading2 := parent)
      targetReentry.normalization.cropped_top_level_cwa
      hnormalizationParent targetReentry.reentry_extremal.delta_pos
      targetReentry.reentry_extremal.delta_le_one
  rcases proposition63_point_cover_on_extremal_parent
      targetReentry.normalization parent parentExtremal parentCWA candidate
      candidateSub candidateCubical planeMap constant candidateCover
      retainedFactor retained retainedPos retainedTop hparentOutput houtputLoss
      (by simpa only [retainedFactor, logFactor] using hrestore) with
    ⟨result, resultUnion, resultFactor⟩
  refine ⟨result, resultUnion.trans ?_, resultFactor⟩
  exact extendShading_union target.data.selected localization.propertyThree

/-- Execute all stages of one root-relative Lemma 17 call and lift the result
once to the incoming current shading.  The returned union equality records
the exact localized Property-(P) set used by the covering proof. -/
theorem proposition63_robust_tau_point_cover
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (planeMap : Point3 → Point3) (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ target.data.refined.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      point ∈ target.data.refined.carrier index →
        |@Inner.inner ℝ Point3 _
          (target.data.selected.family.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hdeltaTau : delta ≤ tau)
    (hdeltaGrid : delta ≤ gridSide (tau / 2))
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hboundary :
      ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
          ENNReal) * (target.terminal.muFine : ENNReal) *
          ENNReal.ofReal (1000 * delta / gridSide (tau / 2)) <
        target.data.refined.mass)
    (hboundaryError :
      ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
          ENNReal) * (target.terminal.muFine : ENNReal) *
          ENNReal.ofReal (1000 * delta / gridSide (tau / 2)) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass)
    (hfirstError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 100 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hsecondError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 400 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hcrossCall :
      4 * (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal))
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (htargetTau : targetScale.1 ≤ 3 * tau)
    (htauSq : tau ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              targetReentry.reentryNormalizationLoss targetLoss
              targetScale.1 tau /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                tau ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta tau incidenceBound
              coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN (tau / delta) (1 - sigma))
    (hdeltaLtOne : delta < 1)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      outerReentry.toNormalizationData.croppedFamily
      (Kakeya.realRpowENN delta (-targetReentryLoss)))
    (hreentryOutput : targetReentryLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        (((81 / 400 : ENNReal) *
            (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
              ENNReal))⁻¹ *
            wz2PaperPureRefinementFraction delta 61) *
          ((73 / 100 : ENNReal) * targetReentry.normalizationWeight))
        targetReentry.regularized.regularizationLoss *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta targetReentryLoss) :
    ∃ localization : Proposition63RobustTauLocalizationData
        (tau := tau) (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃)
        outer targetReentry hcurrentSubOuter htargetReentryLoss target,
      ∃ result : Proposition63LiftedPointCoverData
          (outputLoss := outputLoss) (queryScale := delta)
          (spatialRadius := tau) outerReentry.toNormalizationData
          current planeMap
          (C * Kakeya.realRpowENN (tau / delta) (1 - sigma)),
        result.state.shading.union = localization.propertyThree.union := by
  rcases proposition63_robust_tau_localization outer targetReentry
      hcurrentSubOuter htargetReentryLoss target hdeltaTau hdeltaGrid htau
      htauOne hboundary hboundaryError hfirstError hsecondError hrobustSmall
      hcrossCall hkappa with ⟨localization⟩
  have cover := localization.pointCenteredCovering planeMap incidenceBound
    hplaneUnit hplaneLipschitz hplaneIncidence htargetSmall hdeltaSmall htau
    hdeltaTau htargetTau htauSq htauOne hsigma hsigmaOne hepsilon₁ hepsilon₃
    hepsilonSum logScale hdeltaLog hlog haxis C harithmetic
  rcases localization.liftPointCoverOfCover planeMap
      (C * Kakeya.realRpowENN (tau / delta) (1 - sigma)) cover hdeltaLtOne
      hcurrentCWA hreentryOutput houtputLoss hrestore with
    ⟨result, hunion⟩
  exact ⟨localization, result, hunion⟩

/-- The public one-call output of root-relative Lemma 17.  The intermediate
Property-(P) shading is hidden, while the restored current-family state and
its exact one-sided retention factor remain available for the next dependent
call. -/
theorem proposition63_robust_tau_point_cover_data
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (planeMap : Point3 → Point3) (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ target.data.refined.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      point ∈ target.data.refined.carrier index →
        |@Inner.inner ℝ Point3 _
          (target.data.selected.family.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hdeltaTau : delta ≤ tau)
    (hdeltaGrid : delta ≤ gridSide (tau / 2))
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hboundary :
      ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
          ENNReal) * (target.terminal.muFine : ENNReal) *
          ENNReal.ofReal (1000 * delta / gridSide (tau / 2)) <
        target.data.refined.mass)
    (hboundaryError :
      ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
          ENNReal) * (target.terminal.muFine : ENNReal) *
          ENNReal.ofReal (1000 * delta / gridSide (tau / 2)) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass)
    (hfirstError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 100 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hsecondError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 400 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hcrossCall :
      4 * (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal))
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (htargetTau : targetScale.1 ≤ 3 * tau)
    (htauSq : tau ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              targetReentry.reentryNormalizationLoss targetLoss
              targetScale.1 tau /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                tau ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta tau incidenceBound
              coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN (tau / delta) (1 - sigma))
    (hdeltaLtOne : delta < 1)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      outerReentry.toNormalizationData.croppedFamily
      (Kakeya.realRpowENN delta (-targetReentryLoss)))
    (hreentryOutput : targetReentryLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        (((81 / 400 : ENNReal) *
            (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
              ENNReal))⁻¹ *
            wz2PaperPureRefinementFraction delta 61) *
          ((73 / 100 : ENNReal) * targetReentry.normalizationWeight))
        targetReentry.regularized.regularizationLoss *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta targetReentryLoss) :
    Nonempty (Proposition63LiftedPointCoverData
      (outputLoss := outputLoss) (queryScale := delta)
      (spatialRadius := tau) outerReentry.toNormalizationData
      current planeMap
      (C * Kakeya.realRpowENN (tau / delta) (1 - sigma))) := by
  rcases proposition63_robust_tau_point_cover outer targetReentry
      hcurrentSubOuter htargetReentryLoss target planeMap incidenceBound
      hplaneUnit hplaneLipschitz hplaneIncidence hdeltaTau hdeltaGrid htau
      htauOne hboundary hboundaryError hfirstError hsecondError hrobustSmall
      hcrossCall hkappa htargetSmall hdeltaSmall htargetTau htauSq hsigma
      hsigmaOne hepsilon₁ hepsilon₃ hepsilonSum logScale hdeltaLog hlog haxis C
      harithmetic hdeltaLtOne hcurrentCWA hreentryOutput houtputLoss hrestore with
    ⟨_localization, result, _hunion⟩
  exact ⟨result⟩

/-- CWA-based first robust localization restored on the target terminal's
exact zero-extension.  This is the intermediate output that allows the same
target terminal to become the outer witness of the square-root call. -/
theorem proposition63_robust_tau_target_ambient_point_cover_data_of_cwa
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ parentLoss
      outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (planeMap : Point3 → Point3) (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ target.data.refined.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      point ∈ target.data.refined.carrier index →
        |@Inner.inner ℝ Point3 _
          (target.data.selected.family.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hdeltaTau : delta ≤ tau)
    (hdeltaGrid : delta ≤ gridSide (tau / 2))
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hperiodic : 50 * delta ≤ gridSide (tau / 2))
    (hboundaryCWA :
      let side := gridSide (tau / 2)
      targetReentry.normalization.croppedFamily.enncard *
          ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta
                (-targetReentry.reentryNormalizationLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt (delta / side))) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass)
    (hgridError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 400 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hcrossCall :
      4 * (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal))
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (htargetTau : targetScale.1 ≤ 3 * tau)
    (htauSq : tau ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              targetReentry.reentryNormalizationLoss targetLoss
              targetScale.1 tau /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                tau ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta tau incidenceBound
              coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN (tau / delta) (1 - sigma))
    (hnormalizationParent :
      targetReentry.reentryNormalizationLoss ≤ parentLoss)
    (hparentRetention :
      Kakeya.realRpowENN delta parentLoss ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            targetReentry.reentryNormalizationLoss)
    (hparentOutput : parentLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        ((81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹) 1 *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta parentLoss) :
    ∃ result : Proposition63LiftedPointCoverData
      (outputLoss := outputLoss) (queryScale := delta)
      (spatialRadius := tau) targetReentry.normalization
      (extendShading target.data.selected target.data.refined) planeMap
      (C * Kakeya.realRpowENN (tau / delta) (1 - sigma)),
      result.retainedFactor =
        (81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹ := by
  have hfirstError := grid_pruning_error_first_of_second hgridError
  rcases proposition63_robust_tau_localization_of_cwa outer targetReentry
      hcurrentSubOuter htargetReentryLoss target hdeltaTau hdeltaGrid htau
      htauOne hperiodic hboundaryCWA hfirstError hgridError hrobustSmall
      hcrossCall hkappa with ⟨localization⟩
  have cover := localization.pointCenteredCovering planeMap incidenceBound
    hplaneUnit hplaneLipschitz hplaneIncidence htargetSmall hdeltaSmall htau
    hdeltaTau htargetTau htauSq htauOne hsigma hsigmaOne hepsilon₁ hepsilon₃
    hepsilonSum logScale hdeltaLog hlog haxis C harithmetic
  rcases localization.pointCoverOnTargetAmbient planeMap
      (C * Kakeya.realRpowENN (tau / delta) (1 - sigma)) cover
      hnormalizationParent hparentRetention hparentOutput houtputLoss
      hrestore with
    ⟨result, _hunion, hfactor⟩
  exact ⟨result, hfactor⟩

/-- CWA-based public one-call output on the incoming current family.  A single
`9/400` grid receipt pays for both grid prunings, and the fixed-grid boundary
loss is discharged by the ambient CWA estimate. -/
theorem proposition63_robust_tau_point_cover_data_of_cwa
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (planeMap : Point3 → Point3) (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ target.data.refined.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      point ∈ target.data.refined.carrier index →
        |@Inner.inner ℝ Point3 _
          (target.data.selected.family.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hdeltaTau : delta ≤ tau)
    (hdeltaGrid : delta ≤ gridSide (tau / 2))
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hperiodic : 50 * delta ≤ gridSide (tau / 2))
    (hboundaryCWA :
      let side := gridSide (tau / 2)
      targetReentry.normalization.croppedFamily.enncard *
          ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta
                (-targetReentry.reentryNormalizationLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt (delta / side))) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass)
    (hgridError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 400 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hcrossCall :
      4 * (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal))
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (htargetTau : targetScale.1 ≤ 3 * tau)
    (htauSq : tau ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              targetReentry.reentryNormalizationLoss targetLoss
              targetScale.1 tau /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                tau ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta tau incidenceBound
              coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN (tau / delta) (1 - sigma))
    (hdeltaLtOne : delta < 1)
    (hcurrentCWA : WZ2PaperConvexWolffBound
      outerReentry.toNormalizationData.croppedFamily
      (Kakeya.realRpowENN delta (-targetReentryLoss)))
    (hreentryOutput : targetReentryLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        (((81 / 400 : ENNReal) *
            (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
              ENNReal))⁻¹ *
            wz2PaperPureRefinementFraction delta 61) *
          ((73 / 100 : ENNReal) * targetReentry.normalizationWeight))
        targetReentry.regularized.regularizationLoss *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta targetReentryLoss) :
    Nonempty (Proposition63LiftedPointCoverData
      (outputLoss := outputLoss) (queryScale := delta)
      (spatialRadius := tau) outerReentry.toNormalizationData
      current planeMap
      (C * Kakeya.realRpowENN (tau / delta) (1 - sigma))) := by
  have hfirstError := grid_pruning_error_first_of_second hgridError
  rcases proposition63_robust_tau_localization_of_cwa outer targetReentry
      hcurrentSubOuter htargetReentryLoss target hdeltaTau hdeltaGrid htau
      htauOne hperiodic hboundaryCWA hfirstError hgridError hrobustSmall
      hcrossCall hkappa with ⟨localization⟩
  have cover := localization.pointCenteredCovering planeMap incidenceBound
    hplaneUnit hplaneLipschitz hplaneIncidence htargetSmall hdeltaSmall htau
    hdeltaTau htargetTau htauSq htauOne hsigma hsigmaOne hepsilon₁ hepsilon₃
    hepsilonSum logScale hdeltaLog hlog haxis C harithmetic
  rcases localization.liftPointCoverOfCover planeMap
      (C * Kakeya.realRpowENN (tau / delta) (1 - sigma)) cover hdeltaLtOne
      hcurrentCWA hreentryOutput houtputLoss hrestore with
    ⟨result, _hunion⟩
  exact ⟨result⟩

/-- Public one-call form of robust localization which keeps the restored
point cover on the target re-entry normalization.  This is the terminal
square-root call used by the nested full-grain construction. -/
theorem proposition63_robust_tau_local_point_cover_data
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (planeMap : Point3 → Point3) (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ target.data.refined.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      point ∈ target.data.refined.carrier index →
        |@Inner.inner ℝ Point3 _
          (target.data.selected.family.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hdeltaTau : delta ≤ tau)
    (hdeltaGrid : delta ≤ gridSide (tau / 2))
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hboundary :
      ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
          ENNReal) * (target.terminal.muFine : ENNReal) *
          ENNReal.ofReal (1000 * delta / gridSide (tau / 2)) <
        target.data.refined.mass)
    (hboundaryError :
      ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
          ENNReal) * (target.terminal.muFine : ENNReal) *
          ENNReal.ofReal (1000 * delta / gridSide (tau / 2)) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass)
    (hfirstError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 100 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hsecondError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 400 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hcrossCall :
      4 * (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal))
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (htargetTau : targetScale.1 ≤ 3 * tau)
    (htauSq : tau ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              targetReentry.reentryNormalizationLoss targetLoss
              targetScale.1 tau /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                tau ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta tau incidenceBound
              coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN (tau / delta) (1 - sigma))
    (hdeltaLtOne : delta < 1)
    (hnormalizationOutput :
      targetReentry.reentryNormalizationLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        ((81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹ *
          wz2PaperPureRefinementFraction delta 61) 1 *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta
          targetReentry.reentryNormalizationLoss) :
    ∃ result : Proposition63LiftedPointCoverData
        (outputLoss := outputLoss) (queryScale := delta)
        (spatialRadius := tau) targetReentry.normalization
        targetReentry.normalization.croppedRefined planeMap
        (C * Kakeya.realRpowENN (tau / delta) (1 - sigma)),
      result.retainedFactor =
        (81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹ *
          wz2PaperPureRefinementFraction delta 61 ∧
        result.state.shading.union ⊆
          (extendShading target.data.selected target.data.refined).union := by
  rcases proposition63_robust_tau_localization outer targetReentry
      hcurrentSubOuter htargetReentryLoss target hdeltaTau hdeltaGrid htau
      htauOne hboundary hboundaryError hfirstError hsecondError hrobustSmall
      hcrossCall hkappa with ⟨localization⟩
  have cover := localization.pointCenteredCovering planeMap incidenceBound
    hplaneUnit hplaneLipschitz hplaneIncidence htargetSmall hdeltaSmall htau
    hdeltaTau htargetTau htauSq htauOne hsigma hsigmaOne hepsilon₁ hepsilon₃
    hepsilonSum logScale hdeltaLog hlog haxis C harithmetic
  rcases localization.localPointCoverOfCover planeMap
      (C * Kakeya.realRpowENN (tau / delta) (1 - sigma)) cover hdeltaLtOne
      hnormalizationOutput houtputLoss hrestore with
    ⟨result, _hunion, hsubset, hfactor⟩
  exact ⟨result, hfactor, hsubset⟩

/-- CWA-based terminal one-call output kept on the target normalization.  It
is the production second robust localization used at `sqrt(queryScale)`. -/
theorem proposition63_robust_tau_local_point_cover_data_of_cwa
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss tau epsilon₁ epsilon₃ outputLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (planeMap : Point3 → Point3) (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ target.data.refined.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      point ∈ target.data.refined.carrier index →
        |@Inner.inner ℝ Point3 _
          (target.data.selected.family.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hdeltaTau : delta ≤ tau)
    (hdeltaGrid : delta ≤ gridSide (tau / 2))
    (htau : 0 < tau) (htauOne : tau ≤ 1)
    (hperiodic : 50 * delta ≤ gridSide (tau / 2))
    (hboundaryCWA :
      let side := gridSide (tau / 2)
      targetReentry.normalization.croppedFamily.enncard *
          ((24000000 : ENNReal) *
            (Kakeya.realRpowENN delta
                (-targetReentry.reentryNormalizationLoss) *
                wz2PaperBoundaryGeometryConstant + 1) *
            Kakeya.realRpowENN delta 2 *
            ENNReal.ofReal (Real.sqrt (delta / side))) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass)
    (hgridError : proposition63TauGridPruningError
        target.data.selected.family tau epsilon₁ ≤
      (9 / 400 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hcrossCall :
      4 * (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal))
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (htargetTau : targetScale.1 ≤ 3 * tau)
    (htauSq : tau ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              targetReentry.reentryNormalizationLoss targetLoss
              targetScale.1 tau /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                tau ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta tau incidenceBound
              coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN (tau / delta) (1 - sigma))
    (hdeltaLtOne : delta < 1)
    (hnormalizationOutput :
      targetReentry.reentryNormalizationLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss)
    (hrestore : proposition63Lemma43MassLoss
        ((81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹ *
          wz2PaperPureRefinementFraction delta 61) 1 *
          Kakeya.realRpowENN delta outputLoss ≤
        Kakeya.realRpowENN delta
          targetReentry.reentryNormalizationLoss) :
    ∃ result : Proposition63LiftedPointCoverData
        (outputLoss := outputLoss) (queryScale := delta)
        (spatialRadius := tau) targetReentry.normalization
        targetReentry.normalization.croppedRefined planeMap
        (C * Kakeya.realRpowENN (tau / delta) (1 - sigma)),
      result.retainedFactor =
        (81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹ *
          wz2PaperPureRefinementFraction delta 61 ∧
        result.state.shading.union ⊆
          (extendShading target.data.selected target.data.refined).union := by
  have hfirstError := grid_pruning_error_first_of_second hgridError
  rcases proposition63_robust_tau_localization_of_cwa outer targetReentry
      hcurrentSubOuter htargetReentryLoss target hdeltaTau hdeltaGrid htau
      htauOne hperiodic hboundaryCWA hfirstError hgridError hrobustSmall
      hcrossCall hkappa with ⟨localization⟩
  have cover := localization.pointCenteredCovering planeMap incidenceBound
    hplaneUnit hplaneLipschitz hplaneIncidence htargetSmall hdeltaSmall htau
    hdeltaTau htargetTau htauSq htauOne hsigma hsigmaOne hepsilon₁ hepsilon₃
    hepsilonSum logScale hdeltaLog hlog haxis C harithmetic
  rcases localization.localPointCoverOfCover planeMap
      (C * Kakeya.realRpowENN (tau / delta) (1 - sigma)) cover hdeltaLtOne
      hnormalizationOutput houtputLoss hrestore with
    ⟨result, _hunion, hsubset, hfactor⟩
  exact ⟨result, hfactor, hsubset⟩

/-- Run the square-root robust localization after an arbitrary-radius point
cover has already been restored and re-entered.  The outer input is the exact
rich terminal used before that first cover, the current shading is the actual
first-cover output, and the target is the preselected third rich call.  The
result is the complete analytic two-cover record consumed by fresh
multiplicity/cell preparation. -/
theorem Proposition63NestedPointCoverAnalyticData.ofLiftedFirstAndThirdRobust
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss firstLoss
      reentryLoss targetLoss secondLoss tauScale epsilon₁ epsilon₃ : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    (planeMap : Point3 → Point3) (tauConstant : ENNReal)
    (first : Proposition63LiftedPointCoverData
      (outputLoss := firstLoss) (queryScale := delta)
      (spatialRadius := tauScale) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined) planeMap
      tauConstant)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) outerReentry.toNormalizationData
      first.state.shading)
    (htargetReentryLoss : 0 < reentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (incidenceBound : ℝ)
    (hplaneUnit : ∀ point ∈ target.data.refined.union,
      ‖planeMap point‖ = 1)
    {coefficient : NNReal}
    (hplaneLipschitz : LipschitzWith coefficient planeMap)
    (hplaneIncidence : ∀ index point,
      point ∈ target.data.refined.carrier index →
        |@Inner.inner ℝ Point3 _
          (target.data.selected.family.tube index).direction
          (planeMap point)| ≤ incidenceBound)
    (hdeltaGrid : delta ≤ gridSide (targetScale.1 / 2))
    (htargetOne : targetScale.1 ≤ 1)
    (hboundary :
      ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
          ENNReal) * (target.terminal.muFine : ENNReal) *
          ENNReal.ofReal
            (1000 * delta / gridSide (targetScale.1 / 2)) <
        target.data.refined.mass)
    (hboundaryError :
      ((target.terminal.regularity * target.terminal.fineDegreeFloor : ℕ) :
          ENNReal) * (target.terminal.muFine : ENNReal) *
          ENNReal.ofReal
            (1000 * delta / gridSide (targetScale.1 / 2)) ≤
        (1 / 10 : ENNReal) * target.data.refined.mass)
    (hfirstError : proposition63TauGridPruningError
        target.data.selected.family targetScale.1 epsilon₁ ≤
      (9 / 100 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hsecondError : proposition63TauGridPruningError
        target.data.selected.family targetScale.1 epsilon₁ ≤
      (9 / 400 : ENNReal) *
        (target.data.refined.mass /
          ((Nat.log 2 target.data.selected.family.card + 1 : ℕ) : ENNReal)))
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hcrossCall :
      4 * (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal))
    (hkappa : Real.rpow delta epsilon₃ ≤ robustScale.1)
    (htargetSmall : targetScale.1 ≤ 1 / 12)
    (hdeltaSmall : delta ≤ 1 / 1000)
    (htargetSq : targetScale.1 ^ 2 ≤ 4 * delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (logScale : ℝ) (hdeltaLog : delta ≤ logScale)
    (hlog : 0 < epsilon₁ → ∀ scale : ℝ, 0 < scale →
      scale ≤ logScale → ∀ k : ℕ, 0 < k →
      (k : ℝ) ≤ 100 / scale ^ 3 →
        Real.rpow scale epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (haxis : 4 * (6 * delta) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow delta (1 - epsilon₃)) ^ 2)
    (C : ENNReal)
    (harithmetic :
      ENNReal.ofReal
          ((proposition63RobustTauTotalVolume delta sigma
              targetReentry.reentryNormalizationLoss targetLoss
              targetScale.1 targetScale.1 /
              (Real.rpow delta (1 + 7 * epsilon₁ + epsilon₃) *
                targetScale.1 ^ 2 / 200)) *
            (2 * proposition63DependentSlabWidth delta targetScale.1
              incidenceBound coefficient / delta + 2)) ≤
        C * Kakeya.realRpowENN (targetScale.1 / delta) (1 - sigma))
    (hdeltaLtOne : delta < 1)
    (hnormalizationSecond :
      targetReentry.reentryNormalizationLoss ≤ secondLoss)
    (hsecondLoss : 0 < secondLoss)
    (hrestore : proposition63Lemma43MassLoss
        ((81 / 400 : ENNReal) *
          (((Nat.log 2 target.data.selected.family.card + 1 : ℕ) :
            ENNReal))⁻¹ *
          wz2PaperPureRefinementFraction delta 61) 1 *
          Kakeya.realRpowENN delta secondLoss ≤
        Kakeya.realRpowENN delta
          targetReentry.reentryNormalizationLoss) :
    Nonempty (Proposition63NestedPointCoverAnalyticData
      (firstLoss := firstLoss) (reentryLoss := reentryLoss)
      (sqrtStickyLoss := targetLoss) (secondLoss := secondLoss)
      (queryScale := delta) (tauScale := tauScale)
      (sqrtScale := targetScale.1) outerReentry.toNormalizationData planeMap
      tauConstant
      (C * Kakeya.realRpowENN (targetScale.1 / delta) (1 - sigma))) := by
  have htargetPos : 0 < targetScale.1 :=
    targetReentry.reentry_extremal.delta_pos.trans_le targetScale.2.1
  rcases proposition63_robust_tau_local_point_cover_data outer targetReentry
      first.state.subshading htargetReentryLoss target planeMap incidenceBound
      hplaneUnit hplaneLipschitz hplaneIncidence targetScale.2.1 hdeltaGrid
      htargetPos htargetOne hboundary hboundaryError hfirstError
      hsecondError hrobustSmall hcrossCall hkappa htargetSmall hdeltaSmall
      (by linarith [htargetPos]) htargetSq hsigma hsigmaOne hepsilon₁
      hepsilon₃ hepsilonSum logScale hdeltaLog hlog haxis C harithmetic
      hdeltaLtOne hnormalizationSecond hsecondLoss hrestore with
    ⟨second, _hfactor, hsecondSubset⟩
  exact Proposition63NestedPointCoverAnalyticData.ofLiftedPointCovers
    outerReentry.toNormalizationData
    (extendShading outer.data.selected outer.data.refined) planeMap
    tauConstant
    (C * Kakeya.realRpowENN (targetScale.1 / delta) (1 - sigma))
    first targetReentry targetScale rfl target.data second hsecondSubset

end Kakeya.Assouad.PureWZ2

end
