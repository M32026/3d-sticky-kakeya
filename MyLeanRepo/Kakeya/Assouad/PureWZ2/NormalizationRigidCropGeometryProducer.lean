import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationRigidCropGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DenseCubicalImageContainment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FiniteColoredDegreeSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ExtremalSpatialCellCWAProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureFiberRestriction
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGridCubeVolume
import MyLeanRepo.Kakeya.Assouad.Hairbrush.HomogeneousTwoEndsHelpers
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume

/-!
# Finite rigid-crop geometry after same-scale localization

This module constructs the rigid-crop geometry certificate directly from a
same-scale localized extremizer with a local per-tube density bound.  The
construction is finite:

* select one of `49³` fixed grid cells by the total shaded mass it contains;
* discard tubes whose mass in that common cell is below the relative
  `1 / (2 * 49³)` threshold;
* assign the remaining tubes to six direction cones and two half intervals;
* select one of those twelve classes by its cell-local shaded mass;
* apply one common translation and Householder rotation.

The selected shading is the literal intersection of the localized shading
with the selected common cell.  The conservative small-scale threshold leaves
a strict margin inside the canonical crop box.
-/

noncomputable section

open MeasureTheory Metric Set Finset

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- A conservative threshold for all fixed finite-geometry estimates. -/
def pureWZ2RigidCropGeometryDeltaThreshold : ℝ := 1 / 1000

/-- Side length of the finite spatial cells used before CWA regularization. -/
def pureWZ2RigidCropGridScale : ℝ := 1 / 16

private abbrev rigidCropGridScale : ℝ :=
  pureWZ2RigidCropGridScale

private def rigidCropConeCenter : Fin 6 → Point3
  | 0 => EuclideanSpace.single 0 1
  | 1 => EuclideanSpace.single 0 (-1)
  | 2 => EuclideanSpace.single 1 1
  | 3 => EuclideanSpace.single 1 (-1)
  | 4 => EuclideanSpace.single 2 1
  | 5 => EuclideanSpace.single 2 (-1)

private theorem rigidCropConeCenter_norm (index : Fin 6) :
    ‖rigidCropConeCenter index‖ = 1 := by
  fin_cases index <;>
    simp [rigidCropConeCenter, PiLp.norm_single]

private theorem rigidCrop_exists_coordinate_half
    (direction : Point3)
    (unit : ‖direction‖ = 1) :
    ∃ coordinate : Fin 3, 1 / 2 ≤ |direction coordinate| := by
  have squared :
      ∑ coordinate : Fin 3, direction coordinate ^ 2 = 1 := by
    have normSquared :
        ‖direction‖ ^ 2 =
          ∑ coordinate : Fin 3, direction coordinate ^ 2 :=
      EuclideanSpace.real_norm_sq_eq direction
    rw [unit] at normSquared
    norm_num at normSquared
    exact normSquared.symm
  by_contra noCoordinate
  push Not at noCoordinate
  have coordinateBound :
      ∀ coordinate : Fin 3,
        direction coordinate ^ 2 ≤ 1 / 4 := by
    intro coordinate
    have absolute := noCoordinate coordinate
    have nonnegative := abs_nonneg (direction coordinate)
    rw [← sq_abs]
    nlinarith
  have sumBound :
      ∑ coordinate : Fin 3, direction coordinate ^ 2 ≤ 3 / 4 := by
    calc
      ∑ coordinate : Fin 3, direction coordinate ^ 2 ≤
          ∑ _coordinate : Fin 3, (1 / 4 : ℝ) := by
        exact Finset.sum_le_sum fun coordinate _ =>
          coordinateBound coordinate
      _ = 3 / 4 := by norm_num
  rw [squared] at sumBound
  norm_num at sumBound

private theorem rigidCrop_cone_cover
    (direction : Point3)
    (unit : ‖direction‖ = 1) :
    ∃ cone : Fin 6,
      1 / 2 ≤ inner ℝ direction (rigidCropConeCenter cone) := by
  rcases rigidCrop_exists_coordinate_half direction unit with
    ⟨coordinate, coordinateLarge⟩
  have sign :
      1 / 2 ≤ direction coordinate ∨
        direction coordinate ≤ -(1 / 2) := by
    by_cases nonnegative : 0 ≤ direction coordinate
    · left
      rwa [abs_of_nonneg nonnegative] at coordinateLarge
    · right
      have negative : direction coordinate < 0 :=
        lt_of_not_ge nonnegative
      rw [abs_of_neg negative] at coordinateLarge
      linarith
  fin_cases coordinate
  · rcases sign with positive | negative
    · refine ⟨0, ?_⟩
      simpa [rigidCropConeCenter,
        EuclideanSpace.inner_single_right] using positive
    · refine ⟨1, ?_⟩
      have identity :
          inner ℝ direction
              (EuclideanSpace.single 0 (-1 : ℝ)) =
            -direction 0 := by
        simpa using
          (EuclideanSpace.inner_single_right
            (0 : Fin 3) (-1 : ℝ) direction)
      have negative' :
          direction 0 ≤ -(1 / 2) := by
        simpa using negative
      rw [rigidCropConeCenter, identity]
      linarith [negative']
  · rcases sign with positive | negative
    · refine ⟨2, ?_⟩
      simpa [rigidCropConeCenter,
        EuclideanSpace.inner_single_right] using positive
    · refine ⟨3, ?_⟩
      have identity :
          inner ℝ direction
              (EuclideanSpace.single 1 (-1 : ℝ)) =
            -direction 1 := by
        simpa using
          (EuclideanSpace.inner_single_right
            (1 : Fin 3) (-1 : ℝ) direction)
      have negative' :
          direction 1 ≤ -(1 / 2) := by
        simpa using negative
      rw [rigidCropConeCenter, identity]
      linarith [negative']
  · rcases sign with positive | negative
    · refine ⟨4, ?_⟩
      simpa [rigidCropConeCenter,
        EuclideanSpace.inner_single_right] using positive
    · refine ⟨5, ?_⟩
      have identity :
          inner ℝ direction
              (EuclideanSpace.single 2 (-1 : ℝ)) =
            -direction 2 := by
        simpa using
          (EuclideanSpace.inner_single_right
            (2 : Fin 3) (-1 : ℝ) direction)
      have negative' :
          direction 2 ≤ -(1 / 2) := by
        simpa using negative
      rw [rigidCropConeCenter, identity]
      linarith [negative']

/-- Center of one fixed side-`1/16` spatial cell. -/
def pureWZ2RigidCropCellCenter
    (cell : ℤ × ℤ × ℤ) : Point3 :=
  EuclideanSpace.single 0
      ((cell.1 : ℝ) * pureWZ2RigidCropGridScale +
        pureWZ2RigidCropGridScale / 2) +
    EuclideanSpace.single 1
      ((cell.2.1 : ℝ) * pureWZ2RigidCropGridScale +
        pureWZ2RigidCropGridScale / 2) +
    EuclideanSpace.single 2
      ((cell.2.2 : ℝ) * pureWZ2RigidCropGridScale +
        pureWZ2RigidCropGridScale / 2)

private abbrev rigidCropCellCenter :=
  pureWZ2RigidCropCellCenter

theorem pureWZ2_rigidCropCell_point_dist_center_le
    {point : Point3}
    {cell : ℤ × ℤ × ℤ}
    (pointCell :
      point ∈
        wz1PaperGridCube pureWZ2RigidCropGridScale cell) :
    dist point (pureWZ2RigidCropCellCenter cell) ≤
      Real.sqrt 3 / 32 := by
  have scalePos : 0 < rigidCropGridScale := by
    norm_num [rigidCropGridScale, pureWZ2RigidCropGridScale]
  rw [wz1PaperGridCube_eq_Ico scalePos cell] at pointCell
  have coordinateBound :
      ∀ coordinate : Fin 3,
        |point coordinate -
            rigidCropCellCenter cell coordinate| ≤
          rigidCropGridScale / 2 := by
    intro coordinate
    have bound0 :
        |point 0 -
            rigidCropCellCenter cell 0| ≤
          rigidCropGridScale / 2 := by
      have centerCoordinate :
          rigidCropCellCenter cell 0 =
            (cell.1 : ℝ) * rigidCropGridScale +
              rigidCropGridScale / 2 := by
        simp [rigidCropCellCenter, pureWZ2RigidCropCellCenter]
      rw [centerCoordinate]
      rw [abs_le]
      constructor <;>
        linarith [pointCell.1, pointCell.2.1]
    have bound1 :
        |point 1 -
            rigidCropCellCenter cell 1| ≤
          rigidCropGridScale / 2 := by
      have centerCoordinate :
          rigidCropCellCenter cell 1 =
            (cell.2.1 : ℝ) * rigidCropGridScale +
              rigidCropGridScale / 2 := by
        simp [rigidCropCellCenter, pureWZ2RigidCropCellCenter]
      rw [centerCoordinate]
      rw [abs_le]
      constructor <;>
        linarith [pointCell.2.2.1, pointCell.2.2.2.1]
    have bound2 :
        |point 2 -
            rigidCropCellCenter cell 2| ≤
          rigidCropGridScale / 2 := by
      have centerCoordinate :
          rigidCropCellCenter cell 2 =
            (cell.2.2 : ℝ) * rigidCropGridScale +
              rigidCropGridScale / 2 := by
        simp [rigidCropCellCenter, pureWZ2RigidCropCellCenter]
      rw [centerCoordinate]
      rw [abs_le]
      constructor <;>
        linarith [pointCell.2.2.2.2.1,
          pointCell.2.2.2.2.2]
    fin_cases coordinate
    · exact bound0
    · exact bound1
    · exact bound2
  have squared :
      ‖point - rigidCropCellCenter cell‖ ^ 2 ≤
        3 * (rigidCropGridScale / 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    have bound0 := coordinateBound 0
    have bound1 := coordinateBound 1
    have bound2 := coordinateBound 2
    simp only [PiLp.sub_apply]
    have square0 :
        (point 0 - rigidCropCellCenter cell 0) ^ 2 ≤
          (rigidCropGridScale / 2) ^ 2 := by
      rw [← sq_abs]
      gcongr
    have square1 :
        (point 1 - rigidCropCellCenter cell 1) ^ 2 ≤
          (rigidCropGridScale / 2) ^ 2 := by
      rw [← sq_abs]
      gcongr
    have square2 :
        (point 2 - rigidCropCellCenter cell 2) ^ 2 ≤
          (rigidCropGridScale / 2) ^ 2 := by
      rw [← sq_abs]
      gcongr
    linarith
  have targetSquared :
      (rigidCropGridScale * Real.sqrt 3 / 2) ^ 2 =
        3 * (rigidCropGridScale / 2) ^ 2 := by
    have sqrtSquared :
        (Real.sqrt 3) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  rw [dist_eq_norm]
  have targetNonnegative :
      0 ≤ rigidCropGridScale * Real.sqrt 3 / 2 := by
    positivity
  change
    ‖point - rigidCropCellCenter cell‖ ≤
      Real.sqrt 3 / 32
  have targetEq :
      rigidCropGridScale * Real.sqrt 3 / 2 =
        Real.sqrt 3 / 32 := by
    norm_num [rigidCropGridScale, pureWZ2RigidCropGridScale]
    ring
  rw [← targetEq]
  nlinarith [norm_nonneg (point - rigidCropCellCenter cell)]

/-- The `49³` side-`1/16` cells covering a unit ball around `center`. -/
def pureWZ2RigidCropSpatialCells
    (center : Point3) : Finset (ℤ × ℤ × ℤ) :=
  let centerCell :=
    wz1PaperGridIndex pureWZ2RigidCropGridScale center
  (Finset.Icc (centerCell.1 - 24) (centerCell.1 + 24)).product
    ((Finset.Icc (centerCell.2.1 - 24) (centerCell.2.1 + 24)).product
      (Finset.Icc (centerCell.2.2 - 24) (centerCell.2.2 + 24)))

private abbrev rigidCropSpatialCells :=
  pureWZ2RigidCropSpatialCells

private theorem rigidCropSpatialCells_card
    (center : Point3) :
    (rigidCropSpatialCells center).card = 117649 := by
  have intervalCard :
      ∀ coordinate : ℤ,
        (Finset.Icc (coordinate - 24)
          (coordinate + 24)).card = 49 := by
    intro coordinate
    have castCard :
        ((Finset.Icc (coordinate - 24)
            (coordinate + 24)).card : ℤ) =
          coordinate + 24 + 1 - (coordinate - 24) :=
      Int.card_Icc_of_le _ _ (by omega)
    have exactCast :
        ((Finset.Icc (coordinate - 24)
            (coordinate + 24)).card : ℤ) = 49 := by
      omega
    exact_mod_cast exactCast
  simp [rigidCropSpatialCells, pureWZ2RigidCropSpatialCells,
    intervalCard]

private theorem rigidCrop_gridIndex_mem_spatialCells
    (center point : Point3)
    (pointLocal : point ∈ Metric.closedBall center 1) :
    wz1PaperGridIndex rigidCropGridScale point ∈
      rigidCropSpatialCells center := by
  have coordinateDistance :
      ∀ coordinate : Fin 3,
        |point coordinate - center coordinate| ≤ 1 := by
    intro coordinate
    calc
      |point coordinate - center coordinate| ≤
          dist point center :=
        PiLp.dist_apply_le point center coordinate
      _ ≤ 1 := pointLocal
  have floorBound :
      ∀ coordinate : Fin 3,
        |⌊point coordinate / rigidCropGridScale⌋ -
            ⌊center coordinate / rigidCropGridScale⌋| ≤
          (24 : ℤ) := by
    intro coordinate
    apply wz1_abs_floor_sub_lt_le (N := 24) (by norm_num)
    have scaled :
        |point coordinate / rigidCropGridScale -
            center coordinate / rigidCropGridScale| =
          16 * |point coordinate - center coordinate| := by
      rw [← sub_div, abs_div]
      norm_num [rigidCropGridScale, pureWZ2RigidCropGridScale]
      ring
    calc
      |point coordinate / rigidCropGridScale -
          center coordinate / rigidCropGridScale| =
          16 * |point coordinate - center coordinate| := scaled
      _ ≤ 16 := by
        have bound := coordinateDistance coordinate
        nlinarith [abs_nonneg
          (point coordinate - center coordinate)]
      _ < 24 := by norm_num
  have bound0 := abs_le.mp (floorBound 0)
  have bound1 := abs_le.mp (floorBound 1)
  have bound2 := abs_le.mp (floorBound 2)
  change
    (⌊point 0 / rigidCropGridScale⌋,
        (⌊point 1 / rigidCropGridScale⌋,
          ⌊point 2 / rigidCropGridScale⌋)) ∈
      (Finset.Icc
        (⌊center 0 / rigidCropGridScale⌋ - 24)
        (⌊center 0 / rigidCropGridScale⌋ + 24)).product
      ((Finset.Icc
        (⌊center 1 / rigidCropGridScale⌋ - 24)
        (⌊center 1 / rigidCropGridScale⌋ + 24)).product
      (Finset.Icc
        (⌊center 2 / rigidCropGridScale⌋ - 24)
        (⌊center 2 / rigidCropGridScale⌋ + 24)))
  apply Finset.mem_product.mpr
  constructor
  · have membership :
        ⌊point 0 / rigidCropGridScale⌋ ∈
          Finset.Icc
            (⌊center 0 / rigidCropGridScale⌋ - 24)
            (⌊center 0 / rigidCropGridScale⌋ + 24) := by
      rw [Finset.mem_Icc]
      omega
    exact membership
  · apply Finset.mem_product.mpr
    constructor
    · have membership :
          ⌊point 1 / rigidCropGridScale⌋ ∈
            Finset.Icc
              (⌊center 1 / rigidCropGridScale⌋ - 24)
              (⌊center 1 / rigidCropGridScale⌋ + 24) := by
        rw [Finset.mem_Icc]
        omega
      exact membership
    · have membership :
          ⌊point 2 / rigidCropGridScale⌋ ∈
            Finset.Icc
              (⌊center 2 / rigidCropGridScale⌋ - 24)
              (⌊center 2 / rigidCropGridScale⌋ + 24) := by
        rw [Finset.mem_Icc]
        omega
      exact membership

private theorem rigidCrop_gridCube_disjoint
    {first second : ℤ × ℤ × ℤ}
    (distinct : first ≠ second) :
    Disjoint
      (wz1PaperGridCube rigidCropGridScale first)
      (wz1PaperGridCube rigidCropGridScale second) := by
  rw [Set.disjoint_left]
  intro point pointFirst pointSecond
  have firstEq :
      wz1PaperGridIndex rigidCropGridScale point = first :=
    (mem_wz1PaperGridCube
      rigidCropGridScale first point).mp pointFirst
  have secondEq :
      wz1PaperGridIndex rigidCropGridScale point = second :=
    (mem_wz1PaperGridCube
      rigidCropGridScale second point).mp pointSecond
  exact distinct (firstEq.symm.trans secondEq)

private theorem rigidCrop_volume_eq_sum_spatialCells
    (center : Point3)
    (carrier : Set Point3)
    (carrierMeasurable : MeasurableSet carrier)
    (carrierLocal : carrier ⊆ Metric.closedBall center 1) :
    volume carrier =
      ∑ cell ∈ rigidCropSpatialCells center,
        volume
          (carrier ∩
            wz1PaperGridCube rigidCropGridScale cell) := by
  have carrierEq :
      carrier =
        ⋃ cell ∈ rigidCropSpatialCells center,
          carrier ∩
            wz1PaperGridCube rigidCropGridScale cell := by
    ext point
    constructor
    · intro pointMem
      let cell := wz1PaperGridIndex rigidCropGridScale point
      have cellMem :
          cell ∈ rigidCropSpatialCells center :=
        rigidCrop_gridIndex_mem_spatialCells
          center point (carrierLocal pointMem)
      exact
        Set.mem_iUnion₂.mpr
          ⟨cell, cellMem, pointMem,
            (mem_wz1PaperGridCube _ _ _).mpr rfl⟩
    · intro pointMem
      rcases Set.mem_iUnion₂.mp pointMem with
        ⟨cell, _cellMem, pointCarrier, _pointCell⟩
      exact pointCarrier
  have pairwiseDisjoint :
      Set.PairwiseDisjoint
        (↑(rigidCropSpatialCells center) :
          Set (ℤ × ℤ × ℤ))
        (fun cell =>
          carrier ∩
            wz1PaperGridCube rigidCropGridScale cell) := by
    intro first firstMem second secondMem distinct
    exact
      (rigidCrop_gridCube_disjoint distinct).mono
        Set.inter_subset_right Set.inter_subset_right
  have measurable :
      ∀ cell ∈ rigidCropSpatialCells center,
        MeasurableSet
          (carrier ∩
            wz1PaperGridCube rigidCropGridScale cell) := by
    intro cell _cellMem
    exact
      carrierMeasurable.inter
        (wz1PaperGridCube_measurable cell)
  calc
    volume carrier =
        volume
          (⋃ cell ∈ rigidCropSpatialCells center,
            carrier ∩
              wz1PaperGridCube rigidCropGridScale cell) := by
      exact congrArg volume carrierEq
    _ =
        ∑ cell ∈ rigidCropSpatialCells center,
          volume
            (carrier ∩
              wz1PaperGridCube rigidCropGridScale cell) :=
      MeasureTheory.measure_biUnion_finset
        pairwiseDisjoint measurable

private theorem rigidCrop_weighted_color_pigeonhole
    {Index Color : Type*}
    [Fintype Index] [DecidableEq Index]
    [Fintype Color] [DecidableEq Color]
    (color : Index → Color)
    (colorNonempty : Nonempty Color)
    (weight : Index → ENNReal) :
    ∃ selectedColor : Color,
      (∑ index : Index, weight index) ≤
        (Fintype.card Color : ENNReal) *
          ∑ index ∈
            (Finset.univ.filter fun index =>
              color index = selectedColor),
            weight index := by
  let classWeight : Color → ENNReal := fun selectedColor =>
    ∑ index ∈
      (Finset.univ.filter fun index =>
        color index = selectedColor),
      weight index
  letI : Nonempty Color := colorNonempty
  have total :
      (∑ index : Index, weight index) =
        ∑ selectedColor : Color, classWeight selectedColor := by
    calc
      (∑ index : Index, weight index) =
          ∑ index : Index,
            ∑ selectedColor : Color,
              if color index = selectedColor then
                weight index
              else 0 := by
        apply Finset.sum_congr rfl
        intro index _
        rw [Finset.sum_eq_single_of_mem
          (color index) (Finset.mem_univ _)]
        · rw [if_pos rfl]
        · intro other _ distinct
          rw [if_neg fun equality => distinct equality.symm]
      _ =
          ∑ selectedColor : Color,
            ∑ index : Index,
              if color index = selectedColor then
                weight index else 0 := by
        rw [Finset.sum_comm]
      _ =
          ∑ selectedColor : Color,
            classWeight selectedColor := by
        apply Finset.sum_congr rfl
        intro selectedColor _
        rw [Finset.sum_ite]
        simp [classWeight]
  rcases
      Finset.exists_max_image
        (Finset.univ : Finset Color)
        classWeight Finset.univ_nonempty with
    ⟨selectedColor, _, maximal⟩
  refine ⟨selectedColor, ?_⟩
  calc
    (∑ index : Index, weight index) =
        ∑ colorClass : Color, classWeight colorClass :=
      total
    _ ≤ ∑ _colorClass : Color,
          classWeight selectedColor := by
      apply Finset.sum_le_sum
      intro colorClass _
      exact maximal colorClass (Finset.mem_univ _)
    _ =
        (Fintype.card Color : ENNReal) *
          classWeight selectedColor := by
      simp
    _ =
        (Fintype.card Color : ENNReal) *
          ∑ index ∈
            (Finset.univ.filter fun index =>
              color index = selectedColor),
            weight index := rfl

private theorem rigidCrop_segment_witness
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    {point : Point3}
    (pointTube : point ∈ tube.carrier) :
    ∃ parameter : ℝ,
      parameter ∈ Set.Icc (0 : ℝ) 1 ∧
      dist point
          (tube.base + parameter • tube.direction) ≤ delta := by
  let segment :=
    Kakeya.unitSegment tube.base tube.direction
  have compact : IsCompact segment :=
    isCompact_Icc.image (by fun_prop)
  have pointThickening :
      point ∈ Metric.cthickening delta segment :=
    pointTube
  rcases
      exists_dist_le_of_mem_cthickening_closed
        compact.isClosed deltaPos.le pointThickening with
    ⟨axisPoint, ⟨parameter, parameterMem, axisPointEq⟩,
      pointAxis⟩
  exact
    ⟨parameter, parameterMem, by
      change
        dist point
          ((fun t => tube.base + t • tube.direction)
            parameter) ≤ delta
      rw [axisPointEq]
      exact pointAxis⟩

private structure RigidCropFiniteSelection
    {sigma sourceLoss inputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (localization :
      PureWZ2SameDeltaSpatialCellLocalizationData
        source localized) where
  selected : Kakeya.Streamlined.TubeSubfamily localized.family
  selected_nonempty : selected.family.Nonempty
  ordinaryRefined :
    Kakeya.Streamlined.TubeShading selected.family
  ordinary_subshading :
    ∀ index,
      ordinaryRefined.carrier index ⊆
        localized.shading.carrier (selected.embedding index)
  fixed_mass_retention :
    pureWZ2RigidCropSelectionFactor *
        localized.shading.mass ≤
      ordinaryRefined.mass
  per_tube_density :
    ∀ index,
      (Kakeya.realRpowENN delta inputLoss / 2) *
          volume (selected.family.tube index).carrier ≤
        volume (ordinaryRefined.carrier index)
  centerDirection : Point3
  centerDirection_unit : ‖centerDirection‖ = 1
  commonPoint : Point3
  halfStart : ℝ
  halfStart_cases :
    halfStart = 0 ∨ halfStart = 1 / 2
  direction_cone :
    ∀ index,
      1 / 2 ≤
        inner ℝ centerDirection
          (selected.family.tube index).direction
  segment_near :
    ∀ index,
      ∃ parameter : ℝ,
        parameter ∈ Set.Icc (0 : ℝ) 1 ∧
        parameter ∈ Set.Icc halfStart (halfStart + 1 / 2) ∧
        ‖(selected.family.tube index).base +
              parameter • (selected.family.tube index).direction -
            commonPoint‖ ≤
          Real.sqrt 3 / 32 + delta

private theorem exists_rigidCropFiniteSelection
    {sigma sourceLoss inputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (localization :
      PureWZ2SameDeltaSpatialCellLocalizationData
        source localized)
    (localPerTubeDensity :
      ∀ index,
        (Kakeya.realRpowENN delta inputLoss / 2) *
            volume (localized.family.tube index).carrier ≤
          volume (localized.shading.carrier index)) :
    Nonempty (RigidCropFiniteSelection localization) := by
  let density := Kakeya.realRpowENN delta inputLoss / 2
  have densityPos : 0 < density := by
    exact ENNReal.div_pos
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos
          localized.extremal.delta_pos inputLoss)).ne'
      (by norm_num)
  have tubeVolumePos :
      ∀ index : Fin localized.family.card,
        0 < volume (localized.family.tube index).carrier := by
    intro index
    exact
      wz2_paper_ordinary_tube_volume_pos
        (localized.family.tube index)
        localized.extremal.delta_pos
  have carrierVolumePos :
      ∀ index : Fin localized.family.card,
        0 < volume (localized.shading.carrier index) := by
    intro index
    exact
      (ENNReal.mul_pos densityPos.ne'
        (tubeVolumePos index).ne').trans_le
        (localPerTubeDensity index)
  let shadedPoint :
      ∀ index : Fin localized.family.card, Point3 :=
    fun index =>
      Classical.choose
        (MeasureTheory.nonempty_of_measure_ne_zero
          (carrierVolumePos index).ne')
  have shadedPointMem :
      ∀ index,
        shadedPoint index ∈ localized.shading.carrier index :=
    fun index =>
      Classical.choose_spec
        (MeasureTheory.nonempty_of_measure_ne_zero
          (carrierVolumePos index).ne')
  let parameter : Fin localized.family.card → ℝ := fun index =>
    Classical.choose
      (rigidCrop_segment_witness
        localized.extremal.delta_pos
        (localized.family.tube index)
        (localized.shading.subset_body index
          (shadedPointMem index)))
  have parameterSpec :
      ∀ index,
        parameter index ∈ Set.Icc (0 : ℝ) 1 ∧
        dist (shadedPoint index)
          ((localized.family.tube index).base +
            parameter index •
              (localized.family.tube index).direction) ≤ delta :=
    fun index =>
      Classical.choose_spec
        (rigidCrop_segment_witness
          localized.extremal.delta_pos
          (localized.family.tube index)
          (localized.shading.subset_body index
            (shadedPointMem index)))
  let cone : Fin localized.family.card → Fin 6 := fun index =>
    Classical.choose
      (rigidCrop_cone_cover
        (localized.family.tube index).direction
        (localized.family.tube index).direction_unit)
  have coneSpec :
      ∀ index,
        1 / 2 ≤
          inner ℝ (localized.family.tube index).direction
            (rigidCropConeCenter (cone index)) :=
    fun index =>
      Classical.choose_spec
        (rigidCrop_cone_cover
          (localized.family.tube index).direction
          (localized.family.tube index).direction_unit)
  let cells := rigidCropSpatialCells localization.center
  let spatialColor :
      Fin localized.family.card → {cell // cell ∈ cells} :=
    fun index =>
      ⟨wz1PaperGridIndex rigidCropGridScale (shadedPoint index),
        rigidCrop_gridIndex_mem_spatialCells
          localization.center (shadedPoint index)
          (localization.shading_support_local
            ⟨index, shadedPointMem index⟩)⟩
  let halfColor : Fin localized.family.card → Fin 2 := fun index =>
    if parameter index ≤ 1 / 2 then 0 else 1
  let Color := Fin 6 × {cell // cell ∈ cells} × Fin 2
  let color : Fin localized.family.card → Color := fun index =>
    (cone index, spatialColor index, halfColor index)
  let weight : Fin localized.family.card → ENNReal := fun index =>
    volume (localized.shading.carrier index)
  have colorNonempty : Nonempty Color := by
    let first : Fin localized.family.card :=
      ⟨0, localized.extremal.nonempty⟩
    exact ⟨color first⟩
  rcases
      rigidCrop_weighted_color_pigeonhole
        color colorNonempty weight with
    ⟨best, retainedWeight⟩
  let selectedIndices : Finset (Fin localized.family.card) :=
    Finset.univ.filter fun index => color index = best
  let selected :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      localized.family selectedIndices
  let ordinaryRefined :=
    selected.restrictShading localized.shading
  have cellsCard : cells.card = 117649 := by
    simpa [cells] using
      rigidCropSpatialCells_card localization.center
  have colorCard : Fintype.card Color = 1411788 := by
    simp [Color, cellsCard]
  have selectedMass :
      (∑ index ∈ selectedIndices, weight index) =
        ordinaryRefined.mass := by
    have image :
        Finset.image selected.embedding
            (Finset.univ :
              Finset (Fin selected.family.card)) =
          selectedIndices :=
      Finset.image_orderEmbOfFin_univ selectedIndices rfl
    calc
      (∑ index ∈ selectedIndices, weight index) =
          ∑ index ∈
              Finset.image selected.embedding
                (Finset.univ :
                  Finset (Fin selected.family.card)),
            weight index := by rw [image]
      _ =
          ∑ index : Fin selected.family.card,
            weight (selected.embedding index) := by
        rw [Finset.sum_image]
        intro first _ second _ equality
        exact selected.embedding.injective equality
      _ = ordinaryRefined.mass := rfl
  have totalMass :
      (∑ index : Fin localized.family.card, weight index) =
        localized.shading.mass := rfl
  have retained :
      localized.shading.mass ≤
        (1411788 : ENNReal) * ordinaryRefined.mass := by
    rw [← totalMass, ← selectedMass]
    simpa [selectedIndices, colorCard] using retainedWeight
  have localizedMassPos : 0 < localized.shading.mass := by
    let first : Fin localized.family.card :=
      ⟨0, localized.extremal.nonempty⟩
    calc
      0 < volume (localized.shading.carrier first) :=
        carrierVolumePos first
      _ ≤ localized.shading.mass := by
        exact Finset.single_le_sum
          (fun index _ =>
            (bot_le :
              (0 : ENNReal) ≤
                volume (localized.shading.carrier index)))
          (Finset.mem_univ first)
  have selectedMassPos : 0 < ordinaryRefined.mass := by
    by_contra notPositive
    have zero : ordinaryRefined.mass = 0 := by
      simpa [not_lt] using notPositive
    rw [zero, mul_zero] at retained
    exact (not_le_of_gt localizedMassPos) retained
  have selectedNonempty : selected.family.Nonempty := by
    have selectedIndicesNonempty :
        selectedIndices.Nonempty := by
      by_contra notNonempty
      have selectedEmpty : selectedIndices = ∅ := by
        simpa [Finset.not_nonempty_iff_eq_empty] using
          notNonempty
      have massZero :
          ordinaryRefined.mass = 0 := by
        rw [← selectedMass, selectedEmpty]
        simp
      rw [massZero] at selectedMassPos
      simp at selectedMassPos
    change 0 < selectedIndices.card
    exact selectedIndicesNonempty.card_pos
  have fixedRetention :
      pureWZ2RigidCropSelectionFactor *
          localized.shading.mass ≤
        ordinaryRefined.mass := by
    have inverseRetention :
        (1411788 : ENNReal)⁻¹ *
            localized.shading.mass ≤
          ordinaryRefined.mass := by
      calc
        (1411788 : ENNReal)⁻¹ *
              localized.shading.mass ≤
            (1411788 : ENNReal)⁻¹ *
              ((1411788 : ENNReal) *
                ordinaryRefined.mass) := by
          gcongr
        _ =
            ((1411788 : ENNReal)⁻¹ *
              (1411788 : ENNReal)) *
                ordinaryRefined.mass := by
          rw [mul_assoc]
        _ = ordinaryRefined.mass := by
          rw [ENNReal.inv_mul_cancel]
          · simp
          · norm_num
          · norm_num
    calc
      pureWZ2RigidCropSelectionFactor *
            localized.shading.mass ≤
          (1411788 : ENNReal)⁻¹ *
            localized.shading.mass := by
        gcongr
        unfold pureWZ2RigidCropSelectionFactor
        apply ENNReal.inv_le_inv.mpr
        norm_num
      _ ≤ ordinaryRefined.mass := inverseRetention
  let halfStart : ℝ :=
    if best.2.2 = 0 then 0 else 1 / 2
  have halfStartCases :
      halfStart = 0 ∨ halfStart = 1 / 2 := by
    by_cases first : best.2.2 = 0
    · left
      simp [halfStart, first]
    · right
      simp [halfStart, first]
  have selectedColor :
      ∀ index : Fin selected.family.card,
        color (selected.embedding index) = best := by
    intro index
    exact
      (Finset.mem_filter.mp
        (Finset.orderEmbOfFin_mem selectedIndices rfl index)).2
  have selectedCone :
      ∀ index,
        cone (selected.embedding index) = best.1 := by
    intro index
    exact congrArg Prod.fst (selectedColor index)
  have selectedCell :
      ∀ index,
        wz1PaperGridIndex rigidCropGridScale
            (shadedPoint (selected.embedding index)) =
          best.2.1.1 := by
    intro index
    change
      (spatialColor (selected.embedding index)).1 =
        best.2.1.1
    exact
      congrArg (fun value : Color => value.2.1.1)
        (selectedColor index)
  have selectedHalf :
      ∀ index,
        halfColor (selected.embedding index) = best.2.2 := by
    intro index
    exact congrArg (fun value : Color => value.2.2)
      (selectedColor index)
  let commonPoint :=
    rigidCropCellCenter best.2.1.1
  let centerDirection :=
    rigidCropConeCenter best.1
  refine
    ⟨{
      selected := selected
      selected_nonempty := selectedNonempty
      ordinaryRefined := ordinaryRefined
      ordinary_subshading := fun _ => Set.Subset.rfl
      fixed_mass_retention := fixedRetention
      per_tube_density := ?_
      centerDirection := centerDirection
      centerDirection_unit :=
        rigidCropConeCenter_norm best.1
      commonPoint := commonPoint
      halfStart := halfStart
      halfStart_cases := halfStartCases
      direction_cone := ?_
      segment_near := ?_
    }⟩
  · intro index
    change
      (Kakeya.realRpowENN delta inputLoss / 2) *
          volume (selected.family.tube index).carrier ≤
        volume
          (localized.shading.carrier
            (selected.embedding index))
    rw [selected.tube_eq index]
    exact localPerTubeDensity (selected.embedding index)
  · intro index
    have sourceCone := coneSpec (selected.embedding index)
    rw [selectedCone index] at sourceCone
    have tubeEq := selected.tube_eq index
    rw [tubeEq]
    simpa [centerDirection, real_inner_comm] using sourceCone
  · intro index
    let ambient := selected.embedding index
    have pointCell :
        shadedPoint ambient ∈
          wz1PaperGridCube rigidCropGridScale best.2.1.1 := by
      have ownCell :
          shadedPoint ambient ∈
            wz1PaperGridCube rigidCropGridScale
              (wz1PaperGridIndex rigidCropGridScale
                (shadedPoint ambient)) :=
        (mem_wz1PaperGridCube _ _ _).mpr rfl
      rw [selectedCell index] at ownCell
      exact ownCell
    have pointCenter :
        dist (shadedPoint ambient) commonPoint ≤
          Real.sqrt 3 / 32 := by
      simpa [commonPoint] using
        pureWZ2_rigidCropCell_point_dist_center_le pointCell
    have axisDistance := (parameterSpec ambient).2
    have near :
        ‖(localized.family.tube ambient).base +
              parameter ambient •
                (localized.family.tube ambient).direction -
            commonPoint‖ ≤
          Real.sqrt 3 / 32 + delta := by
      rw [← dist_eq_norm]
      calc
        dist
            ((localized.family.tube ambient).base +
              parameter ambient •
                (localized.family.tube ambient).direction)
            commonPoint ≤
          dist
              ((localized.family.tube ambient).base +
                parameter ambient •
                  (localized.family.tube ambient).direction)
              (shadedPoint ambient) +
            dist (shadedPoint ambient) commonPoint :=
          dist_triangle _ _ _
        _ ≤ delta + Real.sqrt 3 / 32 := by
          apply add_le_add
          · rw [dist_comm]
            exact axisDistance
          · exact pointCenter
        _ = Real.sqrt 3 / 32 + delta := by ring
    have parameterHalf :
        parameter ambient ∈
          Set.Icc halfStart (halfStart + 1 / 2) := by
      have halfEq := selectedHalf index
      by_cases first : parameter ambient ≤ 1 / 2
      · have colorZero : halfColor ambient = 0 := by
          change
            (if parameter ambient ≤ 1 / 2 then
                (0 : Fin 2)
              else 1) = 0
          rw [if_pos first]
        have bestZero : best.2.2 = 0 := by
          rw [← halfEq, colorZero]
        have halfStartZero : halfStart = 0 := by
          change
            (if best.2.2 = 0 then 0 else 1 / 2) = 0
          rw [if_pos bestZero]
        rw [halfStartZero]
        constructor
        · exact (parameterSpec ambient).1.1
        · norm_num
          exact first
      · have colorOne : halfColor ambient = 1 := by
          change
            (if parameter ambient ≤ 1 / 2 then
                (0 : Fin 2)
              else 1) = 1
          rw [if_neg first]
        have bestOne : best.2.2 = 1 := by
          rw [← halfEq, colorOne]
        have lower : 1 / 2 ≤ parameter ambient := by
          linarith
        have upper : parameter ambient ≤ 1 :=
          (parameterSpec ambient).1.2
        have bestNotZero : best.2.2 ≠ 0 := by
          rw [bestOne]
          decide
        have halfStartHalf : halfStart = 1 / 2 := by
          change
            (if best.2.2 = 0 then 0 else 1 / 2) = 1 / 2
          rw [if_neg bestNotZero]
        rw [halfStartHalf]
        constructor
        · exact lower
        · calc
            parameter ambient ≤ 1 := upper
            _ = (1 / 2 : ℝ) + 1 / 2 := by norm_num
    refine
      ⟨parameter ambient, (parameterSpec ambient).1,
        parameterHalf, ?_⟩
    have tubeEq := selected.tube_eq index
    rw [tubeEq]
    exact near

private theorem rigidCrop_abs_inner_le_norm
    (unitDirection vector : Point3)
    (unit : ‖unitDirection‖ = 1) :
    |inner ℝ unitDirection vector| ≤ ‖vector‖ := by
  calc
    |inner ℝ unitDirection vector| ≤
        ‖unitDirection‖ * ‖vector‖ :=
      abs_real_inner_le_norm unitDirection vector
    _ = ‖vector‖ := by rw [unit, one_mul]

private theorem rigidCrop_orthogonal_projection_norm_le
    (vector direction : Point3)
    (directionUnit : ‖direction‖ = 1) :
    ‖vector - inner ℝ vector direction • direction‖ ≤
      ‖vector‖ := by
  let coefficient := inner ℝ vector direction
  have normSquared :
      ‖vector - coefficient • direction‖ ^ 2 =
        ‖vector‖ ^ 2 - coefficient ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right,
      norm_smul, directionUnit]
    simp [coefficient, Real.norm_eq_abs, sq_abs]
    ring
  have squaredBound :
      ‖vector - coefficient • direction‖ ^ 2 ≤
        ‖vector‖ ^ 2 := by
    rw [normSquared]
    exact sub_le_self _ (sq_nonneg coefficient)
  nlinarith [
    norm_nonneg vector,
    norm_nonneg (vector - coefficient • direction)]

private theorem rigidCrop_direction_transverse_bound
    (direction reference : Point3)
    (directionUnit : ‖direction‖ = 1)
    (referenceUnit : ‖reference‖ = 1)
    (cone :
      1 / 2 ≤ inner ℝ reference direction) :
    ‖reference -
        inner ℝ reference direction • direction‖ ≤
      Real.sqrt 3 / 2 := by
  let coefficient := inner ℝ reference direction
  have normSquared :
      ‖reference - coefficient • direction‖ ^ 2 =
        1 - coefficient ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right,
      norm_smul, directionUnit, referenceUnit]
    simp [coefficient, Real.norm_eq_abs, sq_abs]
    ring
  have coefficientLower : 1 / 4 ≤ coefficient ^ 2 := by
    dsimp only [coefficient]
    nlinarith
  have targetSquared :
      (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have targetNonnegative : 0 ≤ Real.sqrt 3 / 2 := by
    positivity
  change
    ‖reference - coefficient • direction‖ ≤
      Real.sqrt 3 / 2
  nlinarith

private theorem rigidCrop_sqrt_three_upper :
    Real.sqrt 3 ≤ 7 / 4 := by
  have nonnegative : 0 ≤ Real.sqrt 3 :=
    Real.sqrt_nonneg 3
  have squared : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  nlinarith

private theorem rigidCrop_coordinate_budget_arithmetic
    {delta : ℝ}
    (deltaLe : delta ≤ 1 / 1000) :
    (7 / 128 + delta) +
        2 * ((7 / 128 + delta) +
          (7 / 128 + 4 * delta)) ≤
      (1 / 3 : ℝ) := by
  linarith

private theorem rigidCrop_frame_coord_two
    (reference : Point3)
    (referenceUnit : ‖reference‖ = 1)
    (vector : Point3) :
    (householderToE3 reference referenceUnit vector) 2 =
      inner ℝ reference vector := by
  let rotation := householderToE3 reference referenceUnit
  calc
    (rotation vector) 2 =
        inner ℝ (rotation vector) e3 := by
      rw [coord2_eq_inner_e3]
    _ = inner ℝ vector (rotation e3) :=
      householderToE3_symmetric
        reference referenceUnit vector e3
    _ = inner ℝ vector reference := by
      rw [householderToE3_sends_e3_to_d]
    _ = inner ℝ reference vector :=
      real_inner_comm _ _

private theorem rigidCrop_frame_transverse_coordinate
    (reference : Point3)
    (referenceUnit : ‖reference‖ = 1)
    (vector : Point3)
    (coordinate : Fin 3)
    (coordinateNe : coordinate ≠ 2) :
    |(householderToE3 reference referenceUnit vector) coordinate| ≤
      ‖vector -
        inner ℝ reference vector • reference‖ := by
  let rotation := householderToE3 reference referenceUnit
  let transverse :=
    vector - inner ℝ reference vector • reference
  have mapped :
      rotation transverse =
        rotation vector -
          inner ℝ reference vector • e3 := by
    dsimp only [transverse]
    rw [map_sub, map_smul,
      householderToE3_sends_d_to_e3]
  have coordinateEq :
      (rotation transverse) coordinate =
        (rotation vector) coordinate := by
    rw [mapped]
    simp [e3, coordinateNe]
  calc
    |(rotation vector) coordinate| =
        ‖(rotation transverse) coordinate‖ := by
      rw [coordinateEq]
      rfl
    _ ≤ ‖rotation transverse‖ :=
      PiLp.norm_apply_le (rotation transverse) coordinate
    _ = ‖transverse‖ :=
      householderToE3_norm reference referenceUnit transverse
    _ =
        ‖vector -
          inner ℝ reference vector • reference‖ := rfl

private theorem rigidCrop_rigidImageTube_lineClass
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (reference commonPoint : Point3)
    (referenceUnit : ‖reference‖ = 1)
    (radius shift : ℝ)
    (nearParameter : ℝ)
    (nearDistance :
      ‖tube.base + nearParameter • tube.direction -
          commonPoint‖ ≤ radius)
    (cone : 1 / 2 ≤ inner ℝ reference tube.direction)
    (coordinateBudget :
      radius + 2 * (radius + |shift|) ≤ 1 / 3) :
    WZ1PaperTubeInLineClass
      (pureWZ2RigidImageTube
        (pureWZ2CanonicalRigidFrame
          (commonPoint + shift • reference)
          reference referenceUnit)
        tube) := by
  let center := commonPoint + shift • reference
  let frame :=
    pureWZ2CanonicalRigidFrame center reference referenceUnit
  let imageTube := pureWZ2RigidImageTube frame tube
  let imageDirection :=
    householderToE3 reference referenceUnit tube.direction
  have imageDirectionEq :
      imageTube.direction = imageDirection := rfl
  have imageDirectionUnit : ‖imageDirection‖ = 1 := by
    calc
      ‖imageDirection‖ = ‖tube.direction‖ :=
        householderToE3_norm
          reference referenceUnit tube.direction
      _ = 1 := tube.direction_unit
  let alpha := inner ℝ reference tube.direction
  have alphaLower : 1 / 2 ≤ alpha := cone
  have imageDirectionTwo : imageDirection 2 = alpha :=
    rigidCrop_frame_coord_two
      reference referenceUnit tube.direction
  have imageDirectionPositive : 0 ≤ imageTube.direction 2 := by
    rw [imageDirectionEq, imageDirectionTwo]
    linarith
  have paperDirectionEq :
      wz1PaperDirection imageTube = imageTube.direction := by
    unfold wz1PaperDirection
    rw [if_pos imageDirectionPositive]
  let nearPoint := tube.base + nearParameter • tube.direction
  let nearError := nearPoint - commonPoint
  have nearErrorNorm : ‖nearError‖ ≤ radius := by
    simpa [nearError, nearPoint] using nearDistance
  have radiusNonnegative : 0 ≤ radius :=
    (norm_nonneg nearError).trans nearErrorNorm
  let sourceOffset := nearPoint - center
  have sourceOffsetEq :
      sourceOffset = nearError - shift • reference := by
    dsimp only [sourceOffset, nearError, center]
    abel
  let imageNear :=
    householderToE3 reference referenceUnit sourceOffset
  have imageNearOnAxis :
      imageNear ∈ tubeAxisLine imageTube := by
    refine ⟨nearParameter, ?_⟩
    have imageNearEq : imageNear = frame nearPoint := by
      change
        householderToE3 reference referenceUnit sourceOffset =
          frame nearPoint
      rfl
    rw [imageNearEq]
    have mapped :=
      frame.map_vadd tube.base
        (nearParameter • tube.direction)
    change
      frame nearPoint =
        imageTube.base +
          nearParameter • imageTube.direction
    change
      frame (tube.base + nearParameter • tube.direction) =
        frame tube.base +
          nearParameter •
            frame.linearIsometryEquiv tube.direction
    simpa only [vadd_eq_add, map_smul, add_comm] using mapped
  have imageNearTransverse :
      ∀ coordinate : Fin 3, coordinate ≠ 2 →
        |imageNear coordinate| ≤ radius := by
    intro coordinate coordinateNe
    dsimp only [imageNear]
    calc
      |(householderToE3 reference referenceUnit
          sourceOffset) coordinate| ≤
          ‖sourceOffset -
            inner ℝ reference sourceOffset • reference‖ :=
        rigidCrop_frame_transverse_coordinate
          reference referenceUnit sourceOffset
          coordinate coordinateNe
      _ = ‖nearError -
            inner ℝ reference nearError • reference‖ := by
        have referenceInner :
            inner ℝ reference reference = 1 := by
          rw [real_inner_self_eq_norm_sq, referenceUnit]
          norm_num
        have innerEq :
            inner ℝ reference sourceOffset =
              inner ℝ reference nearError - shift := by
          rw [sourceOffsetEq, inner_sub_right,
            inner_smul_right, referenceInner]
          ring
        rw [sourceOffsetEq]
        rw [show inner ℝ reference
              (nearError - shift • reference) =
            inner ℝ reference nearError - shift by
          rw [inner_sub_right, inner_smul_right,
            referenceInner]
          ring]
        have vectorEq :
            (nearError - shift • reference) -
                (inner ℝ reference nearError - shift) • reference =
              nearError -
                inner ℝ reference nearError • reference := by
          rw [sub_smul]
          module
        rw [vectorEq]
      _ ≤ ‖nearError‖ := by
        simpa [real_inner_comm] using
          rigidCrop_orthogonal_projection_norm_le
            nearError reference referenceUnit
      _ ≤ radius := nearErrorNorm
  have imageNearTwo :
      imageNear 2 =
        inner ℝ reference nearError - shift := by
    change
      (householderToE3 reference referenceUnit sourceOffset) 2 =
        inner ℝ reference nearError - shift
    rw [rigidCrop_frame_coord_two]
    rw [sourceOffsetEq, inner_sub_right, inner_smul_right]
    have referenceInner :
        inner ℝ reference reference = 1 := by
      rw [real_inner_self_eq_norm_sq, referenceUnit]
      norm_num
    rw [referenceInner]
    ring
  have imageNearTwoAbs :
      |imageNear 2| ≤ radius + |shift| := by
    rw [imageNearTwo]
    calc
      |inner ℝ reference nearError - shift| ≤
          |inner ℝ reference nearError| + |shift| := by
        simpa using abs_sub
          (inner ℝ reference nearError) shift
      _ ≤ ‖nearError‖ + |shift| := by
        gcongr
        exact rigidCrop_abs_inner_le_norm
          reference nearError referenceUnit
      _ ≤ radius + |shift| := by gcongr
  let axisCandidate :=
    imageNear -
      (imageNear 2 / imageDirection 2) • imageDirection
  have imageDirectionTwoLower :
      1 / 2 ≤ imageDirection 2 := by
    rw [imageDirectionTwo]
    exact alphaLower
  have imageDirectionTwoPos :
      0 < imageDirection 2 := by linarith
  have axisCandidateMem :
      axisCandidate ∈ tubeAxisLine imageTube := by
    rcases imageNearOnAxis with ⟨axisParameter, imageNearEq⟩
    refine
      ⟨axisParameter -
        imageNear 2 / imageDirection 2, ?_⟩
    dsimp only [axisCandidate]
    rw [imageNearEq, imageDirectionEq]
    module
  have axisCandidateTwo : axisCandidate 2 = 0 := by
    dsimp only [axisCandidate]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    field_simp [imageDirectionTwoPos.ne']
    ring
  have vertical :
      (1 / 2 : ℝ) ≤ |imageTube.direction 2| := by
    rw [imageDirectionEq, abs_of_pos imageDirectionTwoPos]
    exact imageDirectionTwoLower
  have axisZeroEq :
      wz1TubeAxisZeroPoint imageTube = axisCandidate :=
    wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
      vertical axisCandidateMem axisCandidateTwo
  have candidateCoordinate :
      ∀ coordinate : Fin 3, coordinate ≠ 2 →
        |axisCandidate coordinate| ≤ 1 / 3 := by
    intro coordinate coordinateNe
    have directionCoordinate :
        |imageDirection coordinate| ≤ 1 := by
      calc
        |imageDirection coordinate| ≤ ‖imageDirection‖ := by
          simpa [Real.norm_eq_abs] using
            PiLp.norm_apply_le imageDirection coordinate
        _ = 1 := imageDirectionUnit
    have quotientBound :
        |imageNear 2 / imageDirection 2| ≤
          2 * (radius + |shift|) := by
      rw [abs_div, abs_of_pos imageDirectionTwoPos]
      calc
        |imageNear 2| / imageDirection 2 ≤
            (radius + |shift|) / imageDirection 2 := by
          gcongr
        _ ≤ (radius + |shift|) / (1 / 2 : ℝ) := by
          gcongr
        _ = 2 * (radius + |shift|) := by ring
    have raw :
        |axisCandidate coordinate| ≤
          radius + 2 * (radius + |shift|) := by
      dsimp only [axisCandidate]
      simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      calc
        |imageNear coordinate -
            (imageNear 2 / imageDirection 2) *
              imageDirection coordinate| ≤
            |imageNear coordinate| +
              |imageNear 2 / imageDirection 2| *
                |imageDirection coordinate| := by
          simpa [abs_mul] using
            abs_sub (imageNear coordinate)
              ((imageNear 2 / imageDirection 2) *
                imageDirection coordinate)
        _ ≤ radius +
              (2 * (radius + |shift|)) * 1 := by
          gcongr
          exact imageNearTransverse coordinate coordinateNe
        _ = radius + 2 * (radius + |shift|) := by ring
    exact raw.trans coordinateBudget
  refine ⟨?_, ?_, ?_⟩
  · rw [paperDirectionEq, imageDirectionEq, imageDirectionTwo]
    exact alphaLower
  · rw [axisZeroEq]
    exact candidateCoordinate 0 (by decide)
  · rw [axisZeroEq]
    exact candidateCoordinate 1 (by decide)

/--
The geometric input for the common rigid frame, independent of all mass and
CWA regularization.
-/
structure PureWZ2RigidCropFrameInput
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) where
  centerDirection : Point3
  centerDirection_unit : ‖centerDirection‖ = 1
  commonPoint : Point3
  halfStart : ℝ
  halfStart_cases :
    halfStart = 0 ∨ halfStart = 1 / 2
  direction_cone :
    ∀ index,
      1 / 2 ≤
        inner ℝ centerDirection (family.tube index).direction
  segment_near :
    ∀ index,
      ∃ parameter : ℝ,
        parameter ∈ Set.Icc (0 : ℝ) 1 ∧
        parameter ∈ Set.Icc halfStart (halfStart + 1 / 2) ∧
        ‖(family.tube index).base +
              parameter • (family.tube index).direction -
            commonPoint‖ ≤
          Real.sqrt 3 / 32 + delta

namespace PureWZ2RigidCropFrameInput

/--
Any later final subfamily inherits exactly the same finite frame geometry.
This is the bridge used after weighted CWA regularization.
-/
def subfamily
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (input : PureWZ2RigidCropFrameInput family)
    (selected : WZ2PaperPureTubeSubfamily family) :
    PureWZ2RigidCropFrameInput selected.family where
  centerDirection := input.centerDirection
  centerDirection_unit := input.centerDirection_unit
  commonPoint := input.commonPoint
  halfStart := input.halfStart
  halfStart_cases := input.halfStart_cases
  direction_cone index := by
    rw [selected.tube_eq index]
    exact input.direction_cone (selected.embedding index)
  segment_near index := by
    rcases input.segment_near (selected.embedding index) with
      ⟨parameter, parameterMem, parameterHalf, near⟩
    refine ⟨parameter, parameterMem, parameterHalf, ?_⟩
    rw [selected.tube_eq index]
    exact near

end PureWZ2RigidCropFrameInput

/--
The common rigid image of an arbitrary final selected family satisfying the
finite direction/spatial/half geometry.
-/
structure PureWZ2RigidCropFrameCertificate
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) where
  frame : Point3 ≃ᵃⁱ[ℝ] Point3
  windowCenter : Point3
  local_axial_bound :
    ∀ point,
      dist point windowCenter ≤ Real.sqrt 3 / 32 →
        |(frame point) 2| ≤ Real.sqrt 3 / 16 + 4 * delta
  local_axial_window :
    ∀ point,
      dist point windowCenter ≤ Real.sqrt 3 / 32 →
        |(frame point) 2| ≤ 1 / 8
  croppedFamily : Kakeya.Streamlined.TubeFamily delta
  croppedFamily_eq :
    croppedFamily =
      pureWZ2RigidImageFamily frame family
  indexEquiv :
    Fin family.card ≃
      Fin croppedFamily.card
  cropped_tube_eq :
    ∀ index,
      croppedFamily.tube (indexEquiv index) =
        pureWZ2RigidImageTube frame (family.tube index)
  ordinary_carrier_image_eq :
    ∀ index,
      (croppedFamily.tube (indexEquiv index)).carrier =
        frame '' (family.tube index).carrier
  carrier_margin :
    ∀ index point,
      point ∈ (croppedFamily.tube index).carrier →
        |point 0| ≤ 1 - delta ∧
          |point 1| ≤ 1 - delta ∧
          |point 2| ≤ 1 - delta
  axisBox :
    ∀ index,
      (croppedFamily.tube index).carrier ⊆
        Kakeya.Streamlined.axisBox 2 2 2
  line_class : WZ1PaperIsLineClass croppedFamily

theorem exists_pureWZ2RigidCropFrameCertificate_with_window
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (input : PureWZ2RigidCropFrameInput family)
    (deltaPos : 0 < delta)
    (deltaSmall :
      delta ≤ pureWZ2RigidCropGeometryDeltaThreshold) :
    ∃ certificate : PureWZ2RigidCropFrameCertificate family,
      certificate.windowCenter = input.commonPoint := by
  let reference := input.centerDirection
  let radius := Real.sqrt 3 / 32 + delta
  let shiftMagnitude := radius + 3 * delta
  let shift : ℝ :=
    if input.halfStart = 0 then
      shiftMagnitude
    else
      -shiftMagnitude
  let center :=
    input.commonPoint + shift • reference
  let frame :=
    pureWZ2CanonicalRigidFrame
      center reference input.centerDirection_unit
  let croppedFamily :=
    pureWZ2RigidImageFamily frame family
  let indexEquiv :
      Fin family.card ≃
        Fin croppedFamily.card :=
    Equiv.refl _
  have deltaLe : delta ≤ 1 / 1000 := by
    simpa [pureWZ2RigidCropGeometryDeltaThreshold] using
      deltaSmall
  have sqrtUpper : Real.sqrt 3 ≤ 7 / 4 :=
    rigidCrop_sqrt_three_upper
  have radiusPos : 0 < radius := by
    dsimp only [radius]
    positivity
  have shiftMagnitudePos : 0 < shiftMagnitude := by
    dsimp only [shiftMagnitude]
    positivity
  have shiftAbs : |shift| = shiftMagnitude := by
    by_cases leftHalf : input.halfStart = 0
    · rw [show shift = shiftMagnitude by
        simp [shift, leftHalf]]
      exact abs_of_pos shiftMagnitudePos
    · rw [show shift = -shiftMagnitude by
        simp [shift, leftHalf]]
      rw [abs_neg, abs_of_pos shiftMagnitudePos]
  have radiusUpper : radius ≤ 7 / 128 + delta := by
    dsimp only [radius]
    nlinarith
  have shiftUpper :
      shiftMagnitude ≤ 7 / 128 + 4 * delta := by
    dsimp only [shiftMagnitude]
    linarith
  have transverseBudget :
      radius + Real.sqrt 3 / 2 + delta ≤
        1 - delta := by
    have halfSqrtUpper :
        Real.sqrt 3 / 2 ≤ 7 / 8 := by
      linarith
    nlinarith
  have axialBudget :
      2 * radius + 5 * delta ≤ 1 / 2 := by
    nlinarith
  have frameApply :
      ∀ point : Point3,
        frame point =
          householderToE3 reference
            input.centerDirection_unit (point - center) := by
    intro point
    rfl
  have frameCoordinateTwo :
      ∀ point : Point3,
        (frame point) 2 =
          inner ℝ reference
              (point - input.commonPoint) - shift := by
    intro point
    rw [frameApply, rigidCrop_frame_coord_two]
    dsimp only [center]
    have referenceInner :
        inner ℝ reference reference = 1 := by
      rw [real_inner_self_eq_norm_sq,
        input.centerDirection_unit]
      norm_num
    rw [inner_sub_right, inner_add_right,
      inner_smul_right, referenceInner]
    rw [inner_sub_right]
    ring
  have localAxialBound :
      ∀ point,
        dist point input.commonPoint ≤ Real.sqrt 3 / 32 →
          |(frame point) 2| ≤ Real.sqrt 3 / 16 + 4 * delta := by
    intro point pointDistance
    have pointNorm :
        ‖point - input.commonPoint‖ ≤ Real.sqrt 3 / 32 := by
      simpa [dist_eq_norm] using pointDistance
    have innerBound :
        |inner ℝ reference
            (point - input.commonPoint)| ≤
          Real.sqrt 3 / 32 :=
      (rigidCrop_abs_inner_le_norm
        reference (point - input.commonPoint)
        input.centerDirection_unit).trans pointNorm
    rw [frameCoordinateTwo point]
    calc
      |inner ℝ reference
            (point - input.commonPoint) - shift| ≤
          |inner ℝ reference
              (point - input.commonPoint)| + |shift| :=
        abs_sub _ _
      _ ≤ Real.sqrt 3 / 32 + shiftMagnitude := by
        rw [shiftAbs]
        gcongr
      _ = Real.sqrt 3 / 16 + 4 * delta := by
        dsimp only [shiftMagnitude, radius]
        ring
  have localAxialWindow :
      ∀ point,
        dist point input.commonPoint ≤ Real.sqrt 3 / 32 →
          |(frame point) 2| ≤ 1 / 8 := by
    intro point pointDistance
    exact (localAxialBound point pointDistance).trans <| by
      nlinarith [sqrtUpper, deltaLe]
  have carrierEq :
      ∀ index,
        (croppedFamily.tube (indexEquiv index)).carrier =
          frame '' (family.tube index).carrier := by
    intro index
    exact
      pureWZ2RigidImageFamily_carrier
        frame family index
  have marginAtSource :
      ∀ index : Fin family.card,
        ∀ point,
          point ∈
              (croppedFamily.tube (indexEquiv index)).carrier →
            |point 0| ≤ 1 - delta ∧
              |point 1| ≤ 1 - delta ∧
              |point 2| ≤ 1 - delta := by
    intro index imagePoint imagePointMem
    rw [carrierEq index] at imagePointMem
    rcases imagePointMem with
      ⟨sourcePoint, sourcePointMem, rfl⟩
    let tube := family.tube index
    rcases
        rigidCrop_segment_witness
          deltaPos tube sourcePointMem with
      ⟨parameter, parameterMem, sourceAxisDistance⟩
    rcases input.segment_near index with
      ⟨nearParameter, nearParameterMem,
        nearParameterHalf, nearDistance⟩
    let axisPoint :=
      tube.base + parameter • tube.direction
    let nearPoint :=
      tube.base + nearParameter • tube.direction
    let sourceError := sourcePoint - axisPoint
    let nearError := nearPoint - input.commonPoint
    let alpha := inner ℝ reference tube.direction
    have alphaLower : 1 / 2 ≤ alpha :=
      input.direction_cone index
    have alphaNonnegative : 0 ≤ alpha := by
      linarith
    have alphaUpper : alpha ≤ 1 := by
      dsimp only [alpha, reference]
      calc
        inner ℝ input.centerDirection tube.direction ≤
            ‖input.centerDirection‖ * ‖tube.direction‖ :=
          real_inner_le_norm _ _
        _ = 1 := by
          rw [input.centerDirection_unit,
            tube.direction_unit]
          norm_num
    have sourceErrorNorm : ‖sourceError‖ ≤ delta := by
      simpa [sourceError, axisPoint, dist_eq_norm] using
        sourceAxisDistance
    have nearErrorNorm : ‖nearError‖ ≤ radius := by
      simpa [nearError, nearPoint, radius] using nearDistance
    have parameterDifference :
        -(1 : ℝ) ≤ parameter - nearParameter ∧
          parameter - nearParameter ≤ 1 := by
      constructor <;>
        linarith [parameterMem.1, parameterMem.2,
          nearParameterMem.1, nearParameterMem.2]
    have sourceDecomposition :
        sourcePoint - input.commonPoint =
          nearError +
            (parameter - nearParameter) • tube.direction +
            sourceError := by
      dsimp only [nearError, sourceError, nearPoint, axisPoint]
      module
    have transverseDecomposition :
        (sourcePoint - input.commonPoint) -
              inner ℝ reference
                  (sourcePoint - input.commonPoint) • reference =
          (nearError -
              inner ℝ reference nearError • reference) +
            (parameter - nearParameter) •
              (tube.direction -
                inner ℝ reference tube.direction • reference) +
            (sourceError -
              inner ℝ reference sourceError • reference) := by
      rw [sourceDecomposition, inner_add_right, inner_add_right,
        inner_smul_right, add_smul, add_smul, smul_sub]
      module
    have directionTransverse :
        ‖tube.direction -
            inner ℝ reference tube.direction • reference‖ ≤
          Real.sqrt 3 / 2 := by
      have coneSymmetry :
          1 / 2 ≤ inner ℝ tube.direction reference := by
        simpa [real_inner_comm] using alphaLower
      simpa [real_inner_comm] using
        rigidCrop_direction_transverse_bound
          reference tube.direction
          input.centerDirection_unit
          tube.direction_unit coneSymmetry
    have transverseBound :
        ‖(sourcePoint - input.commonPoint) -
              inner ℝ reference
                  (sourcePoint - input.commonPoint) • reference‖ ≤
          radius + Real.sqrt 3 / 2 + delta := by
      rw [transverseDecomposition]
      calc
        ‖(nearError -
                inner ℝ reference nearError • reference) +
              (parameter - nearParameter) •
                (tube.direction -
                  inner ℝ reference tube.direction • reference) +
              (sourceError -
                inner ℝ reference sourceError • reference)‖ ≤
            ‖nearError -
                inner ℝ reference nearError • reference‖ +
              ‖(parameter - nearParameter) •
                (tube.direction -
                  inner ℝ reference tube.direction • reference)‖ +
              ‖sourceError -
                inner ℝ reference sourceError • reference‖ := by
          calc
            ‖(nearError -
                    inner ℝ reference nearError • reference) +
                  (parameter - nearParameter) •
                    (tube.direction -
                      inner ℝ reference tube.direction • reference) +
                  (sourceError -
                    inner ℝ reference sourceError • reference)‖ ≤
                ‖(nearError -
                    inner ℝ reference nearError • reference) +
                  (parameter - nearParameter) •
                    (tube.direction -
                      inner ℝ reference tube.direction • reference)‖ +
                  ‖sourceError -
                    inner ℝ reference sourceError • reference‖ :=
              norm_add_le _ _
            _ ≤
                (‖nearError -
                    inner ℝ reference nearError • reference‖ +
                  ‖(parameter - nearParameter) •
                    (tube.direction -
                      inner ℝ reference tube.direction • reference)‖) +
                  ‖sourceError -
                    inner ℝ reference sourceError • reference‖ := by
              exact add_le_add (norm_add_le _ _) le_rfl
        _ ≤ ‖nearError‖ +
              |parameter - nearParameter| *
                ‖tube.direction -
                  inner ℝ reference tube.direction • reference‖ +
              ‖sourceError‖ := by
          rw [norm_smul, Real.norm_eq_abs]
          gcongr
          · simpa [real_inner_comm] using
              rigidCrop_orthogonal_projection_norm_le
                nearError reference
                input.centerDirection_unit
          · simpa [real_inner_comm] using
              rigidCrop_orthogonal_projection_norm_le
                sourceError reference
                input.centerDirection_unit
        _ ≤ radius + Real.sqrt 3 / 2 + delta := by
          have differenceAbs :
              |parameter - nearParameter| ≤ 1 := by
            rw [abs_le]
            exact parameterDifference
          have middle :
              |parameter - nearParameter| *
                  ‖tube.direction -
                    inner ℝ reference tube.direction • reference‖ ≤
                Real.sqrt 3 / 2 := by
            calc
              _ ≤ 1 * (Real.sqrt 3 / 2) := by
                exact mul_le_mul differenceAbs directionTransverse
                  (norm_nonneg _) (by norm_num)
              _ = Real.sqrt 3 / 2 := one_mul _
          exact add_le_add
            (add_le_add nearErrorNorm middle) sourceErrorNorm
    have shiftedTransverse :
        (sourcePoint - center) -
              inner ℝ reference (sourcePoint - center) • reference =
          (sourcePoint - input.commonPoint) -
              inner ℝ reference
                  (sourcePoint - input.commonPoint) • reference := by
      dsimp only [center]
      have referenceInner :
          inner ℝ reference reference = 1 := by
        rw [real_inner_self_eq_norm_sq,
          input.centerDirection_unit]
        norm_num
      rw [inner_sub_right, inner_add_right,
        inner_smul_right, referenceInner]
      rw [inner_sub_right]
      module
    have coordinate0 :
        |(frame sourcePoint) 0| ≤ 1 - delta := by
      rw [frameApply]
      calc
        |(householderToE3 reference
            input.centerDirection_unit
            (sourcePoint - center)) 0| ≤
            ‖(sourcePoint - center) -
              inner ℝ reference (sourcePoint - center) • reference‖ :=
          rigidCrop_frame_transverse_coordinate
            reference input.centerDirection_unit
            (sourcePoint - center) 0 (by decide)
        _ = ‖(sourcePoint - input.commonPoint) -
              inner ℝ reference
                (sourcePoint - input.commonPoint) • reference‖ := by
          rw [shiftedTransverse]
        _ ≤ radius + Real.sqrt 3 / 2 + delta :=
          transverseBound
        _ ≤ 1 - delta := transverseBudget
    have coordinate1 :
        |(frame sourcePoint) 1| ≤ 1 - delta := by
      rw [frameApply]
      calc
        |(householderToE3 reference
            input.centerDirection_unit
            (sourcePoint - center)) 1| ≤
            ‖(sourcePoint - center) -
              inner ℝ reference (sourcePoint - center) • reference‖ :=
          rigidCrop_frame_transverse_coordinate
            reference input.centerDirection_unit
            (sourcePoint - center) 1 (by decide)
        _ = ‖(sourcePoint - input.commonPoint) -
              inner ℝ reference
                (sourcePoint - input.commonPoint) • reference‖ := by
          rw [shiftedTransverse]
        _ ≤ radius + Real.sqrt 3 / 2 + delta :=
          transverseBound
        _ ≤ 1 - delta := transverseBudget
    have nearInner :
        |inner ℝ reference nearError| ≤ radius :=
      (rigidCrop_abs_inner_le_norm
        reference nearError
        input.centerDirection_unit).trans nearErrorNorm
    have sourceInner :
        |inner ℝ reference sourceError| ≤ delta :=
      (rigidCrop_abs_inner_le_norm
        reference sourceError
        input.centerDirection_unit).trans sourceErrorNorm
    have longitudinalIdentity :
        inner ℝ reference
            (sourcePoint - input.commonPoint) =
          inner ℝ reference nearError +
            (parameter - nearParameter) * alpha +
            inner ℝ reference sourceError := by
      rw [sourceDecomposition, inner_add_right, inner_add_right,
        inner_smul_right]
    have frameCoordinateTwo :
        (frame sourcePoint) 2 =
          inner ℝ reference
              (sourcePoint - input.commonPoint) - shift := by
      rw [frameApply,
        rigidCrop_frame_coord_two]
      dsimp only [center]
      have referenceInner :
          inner ℝ reference reference = 1 := by
        rw [real_inner_self_eq_norm_sq,
          input.centerDirection_unit]
        norm_num
      rw [inner_sub_right, inner_add_right,
        inner_smul_right, referenceInner]
      rw [inner_sub_right]
      ring
    have coordinate2 :
        |(frame sourcePoint) 2| ≤ 1 - delta := by
      rw [abs_le]
      rcases input.halfStart_cases with
          leftHalf | rightHalf
      · have shiftEq : shift = shiftMagnitude := by
          simp [shift, leftHalf]
        have nearLower : 0 ≤ nearParameter := by
          simpa [leftHalf] using nearParameterHalf.1
        have nearUpper : nearParameter ≤ 1 / 2 := by
          simpa [leftHalf] using nearParameterHalf.2
        have differenceLower :
            -(1 / 2 : ℝ) ≤ parameter - nearParameter := by
          linarith [parameterMem.1]
        have differenceUpper :
            parameter - nearParameter ≤ 1 := by
          linarith [parameterMem.2]
        have productLower :
            -(1 / 2 : ℝ) ≤
              (parameter - nearParameter) * alpha := by
          have step :
              -(1 / 2 : ℝ) * alpha ≤
                (parameter - nearParameter) * alpha := by
            exact mul_le_mul_of_nonneg_right
              differenceLower alphaNonnegative
          nlinarith
        have productUpper :
            (parameter - nearParameter) * alpha ≤ 1 := by
          have step :
              (parameter - nearParameter) * alpha ≤ 1 * alpha :=
            mul_le_mul_of_nonneg_right
              differenceUpper alphaNonnegative
          linarith
        rw [frameCoordinateTwo, shiftEq, longitudinalIdentity]
        constructor
        · have nearLower' :=
            (abs_le.mp nearInner).1
          have sourceLower' :=
            (abs_le.mp sourceInner).1
          dsimp only [shiftMagnitude]
          linarith [axialBudget]
        · have nearUpper' :=
            (abs_le.mp nearInner).2
          have sourceUpper' :=
            (abs_le.mp sourceInner).2
          dsimp only [shiftMagnitude]
          linarith
      · have notLeft : input.halfStart ≠ 0 := by
          rw [rightHalf]
          norm_num
        have shiftEq : shift = -shiftMagnitude := by
          simp [shift, notLeft]
        have nearLower : 1 / 2 ≤ nearParameter := by
          simpa [rightHalf] using nearParameterHalf.1
        have nearUpper : nearParameter ≤ 1 := by
          calc
            nearParameter ≤
                input.halfStart + 1 / 2 :=
              nearParameterHalf.2
            _ = 1 := by rw [rightHalf]; norm_num
        have differenceLower :
            -(1 : ℝ) ≤ parameter - nearParameter := by
          linarith [parameterMem.1]
        have differenceUpper :
            parameter - nearParameter ≤ 1 / 2 := by
          linarith [parameterMem.2]
        have productLower :
            -(1 : ℝ) ≤
              (parameter - nearParameter) * alpha := by
          have step :
              -(1 : ℝ) * alpha ≤
                (parameter - nearParameter) * alpha :=
            mul_le_mul_of_nonneg_right
              differenceLower alphaNonnegative
          linarith
        have productUpper :
            (parameter - nearParameter) * alpha ≤ 1 / 2 := by
          have step :
              (parameter - nearParameter) * alpha ≤
                (1 / 2 : ℝ) * alpha :=
            mul_le_mul_of_nonneg_right
              differenceUpper alphaNonnegative
          nlinarith
        rw [frameCoordinateTwo, shiftEq, longitudinalIdentity]
        constructor
        · have nearLower' :=
            (abs_le.mp nearInner).1
          have sourceLower' :=
            (abs_le.mp sourceInner).1
          dsimp only [shiftMagnitude]
          linarith
        · have nearUpper' :=
            (abs_le.mp nearInner).2
          have sourceUpper' :=
            (abs_le.mp sourceInner).2
          dsimp only [shiftMagnitude]
          linarith [axialBudget]
    exact ⟨coordinate0, coordinate1, coordinate2⟩
  have marginAll :
      ∀ index : Fin croppedFamily.card,
        ∀ point,
          point ∈ (croppedFamily.tube index).carrier →
            |point 0| ≤ 1 - delta ∧
              |point 1| ≤ 1 - delta ∧
              |point 2| ≤ 1 - delta := by
    intro index point pointMem
    have pointMem' :
        point ∈
          (croppedFamily.tube
            (indexEquiv (indexEquiv.symm index))).carrier := by
      rw [indexEquiv.apply_symm_apply]
      exact pointMem
    exact
      marginAtSource
        (indexEquiv.symm index) point pointMem'
  have boxAll :
      ∀ index : Fin croppedFamily.card,
        (croppedFamily.tube index).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2 := by
    intro index point pointMem
    have bounds := marginAll index point pointMem
    have oneMinusLe : 1 - delta ≤ 1 := by
      linarith
    simp only [
      Kakeya.Streamlined.axisBox,
      Set.mem_setOf_eq
    ]
    norm_num
    show
      |point 0| ≤ 1 ∧
        |point 1| ≤ 1 ∧
        |point 2| ≤ 1
    exact
      ⟨bounds.1.trans oneMinusLe,
        bounds.2.1.trans oneMinusLe,
        bounds.2.2.trans oneMinusLe⟩
  have lineAtSource :
      ∀ index : Fin family.card,
        WZ1PaperTubeInLineClass
          (croppedFamily.tube (indexEquiv index)) := by
    intro index
    change
      WZ1PaperTubeInLineClass
        (pureWZ2RigidImageTube frame
          (family.tube index))
    rcases input.segment_near index with
      ⟨nearParameter, _nearParameterMem,
        _nearParameterHalf, nearDistance⟩
    have coordinateBudget :
        radius + 2 * (radius + |shift|) ≤ 1 / 3 := by
      rw [shiftAbs]
      have firstBound :
          radius + 2 * (radius + shiftMagnitude) ≤
            (7 / 128 + delta) +
              2 * ((7 / 128 + delta) +
                (7 / 128 + 4 * delta)) := by
        exact add_le_add radiusUpper <|
          mul_le_mul_of_nonneg_left
            (add_le_add radiusUpper shiftUpper)
            (by norm_num)
      calc
        radius + 2 * (radius + shiftMagnitude) ≤
            (7 / 128 + delta) +
              2 * ((7 / 128 + delta) +
                (7 / 128 + 4 * delta)) := firstBound
        _ ≤ 1 / 3 :=
          rigidCrop_coordinate_budget_arithmetic deltaLe
    have frameEq :
        frame =
          pureWZ2CanonicalRigidFrame
            (input.commonPoint + shift • reference)
            reference input.centerDirection_unit := rfl
    rw [frameEq]
    exact
      rigidCrop_rigidImageTube_lineClass
        (tube := family.tube index)
        reference input.commonPoint
        input.centerDirection_unit
        radius shift nearParameter nearDistance
        (input.direction_cone index)
        coordinateBudget
  have lineAll : WZ1PaperIsLineClass croppedFamily := by
    intro index
    have line := lineAtSource (indexEquiv.symm index)
    rw [indexEquiv.apply_symm_apply] at line
    exact line
  exact
    ⟨{
      frame := frame
      windowCenter := input.commonPoint
      local_axial_bound := localAxialBound
      local_axial_window := localAxialWindow
      croppedFamily := croppedFamily
      croppedFamily_eq := rfl
      indexEquiv := indexEquiv
      cropped_tube_eq := fun _ => rfl
      ordinary_carrier_image_eq := carrierEq
      carrier_margin := marginAll
      axisBox := boxAll
      line_class := lineAll
    }, rfl⟩

/--
Compatibility projection of the rigid-frame construction.  Use
`exists_pureWZ2RigidCropFrameCertificate_with_window` when the exact
common-point identity is needed downstream.
-/
theorem exists_pureWZ2RigidCropFrameCertificate
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (input : PureWZ2RigidCropFrameInput family)
    (deltaPos : 0 < delta)
    (deltaSmall :
      delta ≤ pureWZ2RigidCropGeometryDeltaThreshold) :
    Nonempty (PureWZ2RigidCropFrameCertificate family) := by
  rcases
      exists_pureWZ2RigidCropFrameCertificate_with_window
        input deltaPos deltaSmall with
    ⟨certificate, _windowCenterEq⟩
  exact ⟨certificate⟩

/--
One common cell, the relative-density deletion, six direction cones, and one
half-segment split.
-/
def pureWZ2DirectionalHalfSelectionFactor : ENNReal :=
  (2823576 : ENNReal)⁻¹

/-- Per-tube density retained after the common-cell light-tube deletion. -/
def pureWZ2DirectionalHalfDensityFactor : ENNReal :=
  (235298 : ENNReal)⁻¹

private theorem rigidCrop_cellCount_mul_densityFactor
    (mass : ENNReal) :
    (117649 : ENNReal) *
        (pureWZ2DirectionalHalfDensityFactor * mass) =
      mass / 2 := by
  unfold pureWZ2DirectionalHalfDensityFactor
  rw [show (235298 : ENNReal) = 2 * 117649 by norm_num,
    ENNReal.mul_inv (by norm_num) (by norm_num)]
  calc
    (117649 : ENNReal) *
          (((2 : ENNReal)⁻¹ * (117649 : ENNReal)⁻¹) * mass) =
        (2 : ENNReal)⁻¹ *
          (((117649 : ENNReal)⁻¹ * 117649) * mass) := by
      ring
    _ = (2 : ENNReal)⁻¹ * mass := by
      rw [ENNReal.inv_mul_cancel] <;> norm_num
    _ = mass / 2 := by
      rw [ENNReal.div_eq_inv_mul]

private theorem rigidCrop_twelve_mul_selectionFactor :
    (12 : ENNReal) * pureWZ2DirectionalHalfSelectionFactor =
      pureWZ2DirectionalHalfDensityFactor := by
  unfold pureWZ2DirectionalHalfSelectionFactor
  unfold pureWZ2DirectionalHalfDensityFactor
  rw [show (2823576 : ENNReal) = 12 * 235298 by norm_num,
    ENNReal.mul_inv (by norm_num) (by norm_num)]
  calc
    (12 : ENNReal) *
          ((12 : ENNReal)⁻¹ * (235298 : ENNReal)⁻¹) =
        ((12 : ENNReal) * (12 : ENNReal)⁻¹) *
          (235298 : ENNReal)⁻¹ := by ring
    _ = (235298 : ENNReal)⁻¹ := by
      rw [ENNReal.mul_inv_cancel] <;> norm_num

/--
The fixed-loss finite selection performed before weighted CWA regularization.

The selected family is a genuine subfamily of the supplied spatial
preselection.  No CWA conclusion and no exponent-zero mass claim occurs in
this record.
-/
structure PureWZ2DirectionalHalfPreselectionData
    {sigma sourceLoss pruningLoss outputPruningLoss cellLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    (data :
      PureWZ2SpatialCellPreselectionData
        (cellLoss := cellLoss) source pruning) where
  selectedPre :
    WZ2PaperPureTubeSubfamily data.preSelected.family
  selected_nonempty : selectedPre.family.Nonempty
  spatialCell : ℤ × ℤ × ℤ
  spatialCell_mem :
    spatialCell ∈ pureWZ2RigidCropSpatialCells data.center
  localShading :
    Kakeya.Streamlined.TubeShading selectedPre.family
  local_carrier_eq :
    ∀ index,
      localShading.carrier index =
        data.localShading.carrier (selectedPre.embedding index) ∩
          wz1PaperGridCube pureWZ2RigidCropGridScale spatialCell
  local_subshading :
    ∀ index,
      localShading.carrier index ⊆
        data.localShading.carrier (selectedPre.embedding index)
  fixed_mass_retention :
    pureWZ2DirectionalHalfSelectionFactor *
        data.localShading.mass ≤
      localShading.mass
  per_tube_density :
    ∀ index,
      Kakeya.realRpowENN delta outputPruningLoss *
          (selectedPre.family.tube index).volume ≤
        volume (localShading.carrier index)
  centerDirection : Point3
  centerDirection_unit : ‖centerDirection‖ = 1
  commonPoint : Point3
  commonPoint_eq :
    commonPoint = pureWZ2RigidCropCellCenter spatialCell
  halfStart : ℝ
  halfStart_cases :
    halfStart = 0 ∨ halfStart = 1 / 2
  direction_cone :
    ∀ index,
      1 / 2 ≤
        inner ℝ centerDirection
          (selectedPre.family.tube index).direction
  segment_near :
    ∀ index,
      ∃ parameter : ℝ,
        parameter ∈ Set.Icc (0 : ℝ) 1 ∧
        parameter ∈ Set.Icc halfStart (halfStart + 1 / 2) ∧
        ‖(selectedPre.family.tube index).base +
              parameter • (selectedPre.family.tube index).direction -
            commonPoint‖ ≤
          Real.sqrt 3 / 32 + delta

namespace PureWZ2DirectionalHalfPreselectionData

variable
    {sigma sourceLoss pruningLoss outputPruningLoss cellLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    {data :
      PureWZ2SpatialCellPreselectionData
        (cellLoss := cellLoss) source pruning}
    (selection :
      PureWZ2DirectionalHalfPreselectionData
        (outputPruningLoss := outputPruningLoss) data)

/-- Every retained shaded carrier lies in the selected common cell. -/
theorem local_subset_spatialCell
    (index : Fin selection.selectedPre.family.card) :
    selection.localShading.carrier index ⊆
      wz1PaperGridCube pureWZ2RigidCropGridScale
        selection.spatialCell := by
  rw [selection.local_carrier_eq index]
  exact Set.inter_subset_right

/-- Every retained shaded point is within the cell radius of the common point. -/
theorem local_dist_commonPoint
    (index : Fin selection.selectedPre.family.card)
    {point : Point3}
    (pointMem : point ∈ selection.localShading.carrier index) :
    dist point selection.commonPoint ≤ Real.sqrt 3 / 32 := by
  have pointCell :
      point ∈
        wz1PaperGridCube pureWZ2RigidCropGridScale
          selection.spatialCell :=
    selection.local_subset_spatialCell index pointMem
  rw [selection.commonPoint_eq]
  exact pureWZ2_rigidCropCell_point_dist_center_le pointCell

/--
The same retained index set is a per-tube pruning at the weaker output loss.
The fixed density loss is paid explicitly before this certificate is formed.
-/
noncomputable def toWeakerPruningData
    (densityAbsorption :
      Kakeya.realRpowENN delta outputPruningLoss ≤
        pureWZ2DirectionalHalfDensityFactor *
          Kakeya.realRpowENN delta pruningLoss) :
    PureWZ2PerTubeDensityPruningData source outputPruningLoss where
  indices := pruning.indices
  nonempty := pruning.nonempty
  cardinality_retention := by
    have factorLeOne :
        pureWZ2DirectionalHalfDensityFactor ≤ 1 := by
      norm_num [pureWZ2DirectionalHalfDensityFactor]
    calc
      Kakeya.realRpowENN delta outputPruningLoss *
            source.family.enncard ≤
          (pureWZ2DirectionalHalfDensityFactor *
              Kakeya.realRpowENN delta pruningLoss) *
            source.family.enncard := by
        gcongr
      _ ≤
          Kakeya.realRpowENN delta pruningLoss *
            source.family.enncard := by
        calc
          (pureWZ2DirectionalHalfDensityFactor *
                Kakeya.realRpowENN delta pruningLoss) *
              source.family.enncard ≤
            (1 * Kakeya.realRpowENN delta pruningLoss) *
              source.family.enncard := by
            gcongr
          _ =
              Kakeya.realRpowENN delta pruningLoss *
                source.family.enncard := by ring
      _ ≤
          (selectedTubeFamily
            source.family pruning.indices).enncard :=
        pruning.cardinality_retention
  mass_retention := pruning.mass_retention
  per_tube_density := by
    intro index indexMem
    calc
      Kakeya.realRpowENN delta outputPruningLoss *
            (source.family.tube index).volume ≤
          (pureWZ2DirectionalHalfDensityFactor *
              Kakeya.realRpowENN delta pruningLoss) *
            (source.family.tube index).volume := by
        gcongr
      _ ≤
          Kakeya.realRpowENN delta pruningLoss *
            (source.family.tube index).volume := by
        have factorLeOne :
            pureWZ2DirectionalHalfDensityFactor ≤ 1 := by
          norm_num [pureWZ2DirectionalHalfDensityFactor]
        calc
          (pureWZ2DirectionalHalfDensityFactor *
                Kakeya.realRpowENN delta pruningLoss) *
              (source.family.tube index).volume ≤
            (1 *
                Kakeya.realRpowENN delta pruningLoss) *
              (source.family.tube index).volume := by
            gcongr
          _ =
              Kakeya.realRpowENN delta pruningLoss *
                (source.family.tube index).volume := by ring
      _ ≤ volume (source.shading.carrier index) :=
        pruning.per_tube_density index indexMem

/--
After explicitly absorbing the fixed `1 / 2823576` loss, the finite selection
is a genuine spatial preselection at the weaker cell loss.  This is the object
consumed by weighted CWA regularization.
-/
noncomputable def toSpatialCellPreselectionData
    (outputCellLoss : ℝ)
    (densityAbsorption :
      Kakeya.realRpowENN delta outputPruningLoss ≤
        pureWZ2DirectionalHalfDensityFactor *
          Kakeya.realRpowENN delta pruningLoss)
    (fixedLossAbsorption :
      Kakeya.realRpowENN delta
          (outputCellLoss - cellLoss) ≤
        pureWZ2DirectionalHalfSelectionFactor) :
    PureWZ2SpatialCellPreselectionData
      (cellLoss := outputCellLoss) source
        (toWeakerPruningData
          (pruning := pruning) densityAbsorption) := by
  let selected :=
    WZ2PaperPureTubeSubfamily.comp
      data.preSelected selection.selectedPre
  have powerSplit :
      Kakeya.realRpowENN delta outputCellLoss =
        Kakeya.realRpowENN delta
            (outputCellLoss - cellLoss) *
          Kakeya.realRpowENN delta cellLoss := by
    rw [← Kakeya.Streamlined.realRpowENN_add
      source.extremal.delta_pos]
    congr 1
    ring
  refine
    {
      preSelected := selected
      preSelected_nonempty := selection.selected_nonempty
      selected_from_pruning := ?_
      localShading := selection.localShading
      subshading := ?_
      per_tube_local_density := ?_
      source_mass_retention := ?_
      center := data.center
      family_bases_local := ?_
      shading_support_local := ?_
    }
  · intro index
    change
      data.preSelected.embedding
          (selection.selectedPre.embedding index) ∈
        (toWeakerPruningData
          (pruning := pruning) densityAbsorption).indices
    exact
      data.selected_from_pruning
        (selection.selectedPre.embedding index)
  · intro index point pointMem
    exact
      data.subshading
        (selection.selectedPre.embedding index)
        (selection.local_subshading index pointMem)
  · intro index
    have density :=
      selection.per_tube_density index
    change
      Kakeya.realRpowENN delta outputPruningLoss *
          (selection.selectedPre.family.tube index).volume ≤
        volume (selection.localShading.carrier index)
    exact density
  · rw [powerSplit]
    calc
      (Kakeya.realRpowENN delta
            (outputCellLoss - cellLoss) *
          Kakeya.realRpowENN delta cellLoss) *
            source.shading.mass =
          Kakeya.realRpowENN delta
              (outputCellLoss - cellLoss) *
            (Kakeya.realRpowENN delta cellLoss *
              source.shading.mass) := by ring
      _ ≤
          pureWZ2DirectionalHalfSelectionFactor *
            data.localShading.mass := by
        gcongr
        exact data.source_mass_retention
      _ ≤ selection.localShading.mass :=
        selection.fixed_mass_retention
  · intro index
    change
      dist
        (selection.selectedPre.family.tube index).base
        data.center ≤ 3
    rw [selection.selectedPre.tube_eq index]
    exact
      data.family_bases_local
        (selection.selectedPre.embedding index)
  · rintro point ⟨index, pointMem⟩
    exact
      data.shading_support_local
        ⟨selection.selectedPre.embedding index,
          selection.local_subshading index pointMem⟩

/--
The weaker spatial preselection produced from the directional-half selection
still uses the literal common-cell intersection on every retained tube.
-/
theorem toSpatialCellPreselectionData_local_subset_spatialCell
    (outputCellLoss : ℝ)
    (densityAbsorption :
      Kakeya.realRpowENN delta outputPruningLoss ≤
        pureWZ2DirectionalHalfDensityFactor *
          Kakeya.realRpowENN delta pruningLoss)
    (fixedLossAbsorption :
      Kakeya.realRpowENN delta
          (outputCellLoss - cellLoss) ≤
        pureWZ2DirectionalHalfSelectionFactor)
    (index :
      Fin
        (selection.toSpatialCellPreselectionData
          outputCellLoss densityAbsorption
          fixedLossAbsorption).preSelected.family.card) :
    (selection.toSpatialCellPreselectionData
        outputCellLoss densityAbsorption
        fixedLossAbsorption).localShading.carrier index ⊆
      wz1PaperGridCube pureWZ2RigidCropGridScale
        selection.spatialCell :=
  selection.local_subset_spatialCell index

end PureWZ2DirectionalHalfPreselectionData

/-
/--
Every spatial preselection admits the finite direction-cone and half-segment
selection before weighted CWA regularization.
-/
theorem exists_pureWZ2_directionalHalfPreselectionData
    {sigma sourceLoss pruningLoss cellLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    (data :
      PureWZ2SpatialCellPreselectionData
        (cellLoss := cellLoss) source pruning) :
    Nonempty (PureWZ2DirectionalHalfPreselectionData data) := by
  let density := Kakeya.realRpowENN delta pruningLoss
  have densityPos : 0 < density :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos source.extremal.delta_pos pruningLoss)
  have tubeVolumePos :
      ∀ index : Fin data.preSelected.family.card,
        0 < volume (data.preSelected.family.tube index).carrier := by
    intro index
    exact
      wz2_paper_ordinary_tube_volume_pos
        (data.preSelected.family.tube index)
        source.extremal.delta_pos
  have carrierVolumePos :
      ∀ index : Fin data.preSelected.family.card,
        0 < volume (data.localShading.carrier index) := by
    intro index
    exact
      (ENNReal.mul_pos densityPos.ne'
        (tubeVolumePos index).ne').trans_le
        (data.per_tube_local_density index)
  let shadedPoint :
      Fin data.preSelected.family.card → Point3 := fun index =>
    Classical.choose
      (MeasureTheory.nonempty_of_measure_ne_zero
        (carrierVolumePos index).ne')
  have shadedPointMem :
      ∀ index,
        shadedPoint index ∈ data.localShading.carrier index :=
    fun index =>
      Classical.choose_spec
        (MeasureTheory.nonempty_of_measure_ne_zero
          (carrierVolumePos index).ne')
  let parameter :
      Fin data.preSelected.family.card → ℝ := fun index =>
    Classical.choose
      (rigidCrop_segment_witness
        source.extremal.delta_pos
        (data.preSelected.family.tube index)
        (data.localShading.subset_body index
          (shadedPointMem index)))
  have parameterSpec :
      ∀ index,
        parameter index ∈ Set.Icc (0 : ℝ) 1 ∧
        dist (shadedPoint index)
          ((data.preSelected.family.tube index).base +
            parameter index •
              (data.preSelected.family.tube index).direction) ≤
          delta :=
    fun index =>
      Classical.choose_spec
        (rigidCrop_segment_witness
          source.extremal.delta_pos
          (data.preSelected.family.tube index)
          (data.localShading.subset_body index
            (shadedPointMem index)))
  let cone :
      Fin data.preSelected.family.card → Fin 6 := fun index =>
    Classical.choose
      (rigidCrop_cone_cover
        (data.preSelected.family.tube index).direction
        (data.preSelected.family.tube index).direction_unit)
  have coneSpec :
      ∀ index,
        1 / 2 ≤
          inner ℝ (data.preSelected.family.tube index).direction
            (rigidCropConeCenter (cone index)) :=
    fun index =>
      Classical.choose_spec
        (rigidCrop_cone_cover
          (data.preSelected.family.tube index).direction
          (data.preSelected.family.tube index).direction_unit)
  let cells := pureWZ2RigidCropSpatialCells data.center
  let spatialColor :
      Fin data.preSelected.family.card → {cell // cell ∈ cells} :=
    fun index =>
      ⟨wz1PaperGridIndex pureWZ2RigidCropGridScale
          (shadedPoint index),
        rigidCrop_gridIndex_mem_spatialCells
          data.center (shadedPoint index)
          (data.shading_support_local
            ⟨index, shadedPointMem index⟩)⟩
  let halfColor :
      Fin data.preSelected.family.card → Fin 2 := fun index =>
    if parameter index ≤ 1 / 2 then 0 else 1
  let Color := Fin 6 × {cell // cell ∈ cells} × Fin 2
  let color :
      Fin data.preSelected.family.card → Color := fun index =>
    (cone index, spatialColor index, halfColor index)
  let weight :
      Fin data.preSelected.family.card → ENNReal := fun index =>
    volume (data.localShading.carrier index)
  have colorNonempty : Nonempty Color := by
    let first : Fin data.preSelected.family.card :=
      ⟨0, data.preSelected_nonempty⟩
    exact ⟨color first⟩
  rcases
      rigidCrop_weighted_color_pigeonhole
        color colorNonempty weight with
    ⟨best, retainedWeight⟩
  let selectedIndices :
      Finset (Fin data.preSelected.family.card) :=
    Finset.univ.filter fun index => color index = best
  let selectedPre :=
    WZ2PaperPureTubeSubfamily.fromFinset
      data.preSelected.family selectedIndices
  let localShading :=
    selectedPre.toTubeSubfamily.restrictShading
      data.localShading
  have cellsCard : cells.card = 117649 := by
    simpa [cells] using
      rigidCropSpatialCells_card data.center
  have colorCard : Fintype.card Color = 1411788 := by
    simp [Color, cellsCard]
  have selectedMass :
      (∑ index ∈ selectedIndices, weight index) =
        localShading.mass := by
    have image :
        Finset.image selectedPre.embedding
            (Finset.univ :
              Finset (Fin selectedPre.family.card)) =
          selectedIndices :=
      Finset.image_orderEmbOfFin_univ selectedIndices rfl
    calc
      (∑ index ∈ selectedIndices, weight index) =
          ∑ index ∈
              Finset.image selectedPre.embedding
                (Finset.univ :
                  Finset (Fin selectedPre.family.card)),
            weight index := by rw [image]
      _ =
          ∑ index : Fin selectedPre.family.card,
            weight (selectedPre.embedding index) := by
        rw [Finset.sum_image]
        intro first _ second _ equality
        exact selectedPre.embedding.injective equality
      _ = localShading.mass := rfl
  have totalMass :
      (∑ index : Fin data.preSelected.family.card, weight index) =
        data.localShading.mass := rfl
  have retained :
      data.localShading.mass ≤
        (1411788 : ENNReal) * localShading.mass := by
    rw [← totalMass, ← selectedMass]
    simpa [selectedIndices, colorCard] using retainedWeight
  have dataMassPos : 0 < data.localShading.mass := by
    let first : Fin data.preSelected.family.card :=
      ⟨0, data.preSelected_nonempty⟩
    calc
      0 < volume (data.localShading.carrier first) :=
        carrierVolumePos first
      _ ≤ data.localShading.mass := by
        exact Finset.single_le_sum
          (fun index _ =>
            (bot_le :
              (0 : ENNReal) ≤
                volume (data.localShading.carrier index)))
          (Finset.mem_univ first)
  have localMassPos : 0 < localShading.mass := by
    by_contra notPositive
    have zero : localShading.mass = 0 := by
      simpa [not_lt] using notPositive
    rw [zero, mul_zero] at retained
    exact (not_le_of_gt dataMassPos) retained
  have selectedNonempty : selectedPre.family.Nonempty := by
    have selectedIndicesNonempty : selectedIndices.Nonempty := by
      by_contra notNonempty
      have selectedEmpty : selectedIndices = ∅ := by
        simpa [Finset.not_nonempty_iff_eq_empty] using notNonempty
      have massZero : localShading.mass = 0 := by
        rw [← selectedMass, selectedEmpty]
        simp
      rw [massZero] at localMassPos
      simp at localMassPos
    change 0 < selectedIndices.card
    exact selectedIndicesNonempty.card_pos
  have fixedRetention :
      pureWZ2DirectionalHalfSelectionFactor *
          data.localShading.mass ≤
        localShading.mass := by
    have inverseRetention :
        (1411788 : ENNReal)⁻¹ * data.localShading.mass ≤
          localShading.mass := by
      calc
        (1411788 : ENNReal)⁻¹ * data.localShading.mass ≤
            (1411788 : ENNReal)⁻¹ *
              ((1411788 : ENNReal) * localShading.mass) := by
          gcongr
        _ =
            ((1411788 : ENNReal)⁻¹ *
              (1411788 : ENNReal)) *
              localShading.mass := by rw [mul_assoc]
        _ = localShading.mass := by
          rw [ENNReal.inv_mul_cancel]
          · simp
          · norm_num
          · norm_num
    exact inverseRetention
  let halfStart : ℝ :=
    if best.2.2 = 0 then 0 else 1 / 2
  have halfStartCases :
      halfStart = 0 ∨ halfStart = 1 / 2 := by
    by_cases first : best.2.2 = 0
    · left
      simp [halfStart, first]
    · right
      simp [halfStart, first]
  have selectedColor :
      ∀ index : Fin selectedPre.family.card,
        color (selectedPre.embedding index) = best := by
    intro index
    exact
      (Finset.mem_filter.mp
        (Finset.orderEmbOfFin_mem selectedIndices rfl index)).2
  have selectedCone :
      ∀ index,
        cone (selectedPre.embedding index) = best.1 := by
    intro index
    exact congrArg Prod.fst (selectedColor index)
  have selectedCell :
      ∀ index,
        wz1PaperGridIndex pureWZ2RigidCropGridScale
            (shadedPoint (selectedPre.embedding index)) =
          best.2.1.1 := by
    intro index
    change
      (spatialColor (selectedPre.embedding index)).1 =
        best.2.1.1
    exact
      congrArg (fun value : Color => value.2.1.1)
        (selectedColor index)
  have selectedHalf :
      ∀ index,
        halfColor (selectedPre.embedding index) = best.2.2 := by
    intro index
    exact
      congrArg (fun value : Color => value.2.2)
        (selectedColor index)
  let centerDirection := rigidCropConeCenter best.1
  let commonPoint :=
    pureWZ2RigidCropCellCenter best.2.1.1
  refine
    ⟨{
      selectedPre := selectedPre
      selected_nonempty := selectedNonempty
      localShading := localShading
      local_subshading := fun _ => Set.Subset.rfl
      fixed_mass_retention := fixedRetention
      per_tube_density := ?_
      centerDirection := centerDirection
      centerDirection_unit := rigidCropConeCenter_norm best.1
      spatialCell := best.2.1.1
      spatialCell_mem := best.2.1.2
      commonPoint := commonPoint
      commonPoint_eq := rfl
      halfStart := halfStart
      halfStart_cases := halfStartCases
      direction_cone := ?_
      segment_near := ?_
    }⟩
  · intro index
    change
      Kakeya.realRpowENN delta pruningLoss *
          volume (selectedPre.family.tube index).carrier ≤
        volume
          (data.localShading.carrier
            (selectedPre.embedding index))
    rw [selectedPre.tube_eq index]
    exact
      data.per_tube_local_density
        (selectedPre.embedding index)
  · intro index
    have sourceCone := coneSpec (selectedPre.embedding index)
    rw [selectedCone index] at sourceCone
    rw [selectedPre.tube_eq index]
    simpa [centerDirection, real_inner_comm] using sourceCone
  · intro index
    let ambient := selectedPre.embedding index
    have axisDistance := (parameterSpec ambient).2
    have pointCell :
        shadedPoint ambient ∈
          wz1PaperGridCube pureWZ2RigidCropGridScale
            best.2.1.1 := by
      have ownCell :
          shadedPoint ambient ∈
            wz1PaperGridCube pureWZ2RigidCropGridScale
              (wz1PaperGridIndex
                pureWZ2RigidCropGridScale
                (shadedPoint ambient)) :=
        (mem_wz1PaperGridCube _ _ _).mpr rfl
      rw [selectedCell index] at ownCell
      exact ownCell
    have pointCenter :
        dist (shadedPoint ambient) commonPoint ≤
          pureWZ2RigidCropGridScale * Real.sqrt 3 / 2 := by
      simpa [commonPoint] using
        pureWZ2_rigidCropCell_point_dist_center_le pointCell
    have near :
        ‖(data.preSelected.family.tube ambient).base +
              parameter ambient •
                (data.preSelected.family.tube ambient).direction -
            commonPoint‖ ≤
          Real.sqrt 3 / 32 + delta := by
      rw [← dist_eq_norm]
      calc
        dist
            ((data.preSelected.family.tube ambient).base +
              parameter ambient •
                (data.preSelected.family.tube ambient).direction)
            commonPoint ≤
          dist
              ((data.preSelected.family.tube ambient).base +
                parameter ambient •
                  (data.preSelected.family.tube ambient).direction)
              (shadedPoint ambient) +
            dist (shadedPoint ambient) commonPoint :=
          dist_triangle _ _ _
        _ ≤ delta +
            pureWZ2RigidCropGridScale * Real.sqrt 3 / 2 := by
          apply add_le_add
          · rw [dist_comm]
            exact axisDistance
          · exact pointCenter
        _ = Real.sqrt 3 / 32 + delta := by
          change
            delta + (1 / 16 : ℝ) * Real.sqrt 3 / 2 =
              Real.sqrt 3 / 32 + delta
          ring
    have parameterHalf :
        parameter ambient ∈
          Set.Icc halfStart (halfStart + 1 / 2) := by
      have halfEq := selectedHalf index
      by_cases first : parameter ambient ≤ 1 / 2
      · have colorZero : halfColor ambient = 0 := by
          change
            (if parameter ambient ≤ 1 / 2 then
                (0 : Fin 2)
              else 1) = 0
          rw [if_pos first]
        have bestZero : best.2.2 = 0 := by
          rw [← halfEq, colorZero]
        have halfStartZero : halfStart = 0 := by
          change (if best.2.2 = 0 then 0 else 1 / 2) = 0
          rw [if_pos bestZero]
        rw [halfStartZero]
        exact ⟨(parameterSpec ambient).1.1, by
          norm_num
          exact first⟩
      · have colorOne : halfColor ambient = 1 := by
          change
            (if parameter ambient ≤ 1 / 2 then
                (0 : Fin 2)
              else 1) = 1
          rw [if_neg first]
        have bestOne : best.2.2 = 1 := by
          rw [← halfEq, colorOne]
        have bestNotZero : best.2.2 ≠ 0 := by
          rw [bestOne]
          decide
        have halfStartHalf : halfStart = 1 / 2 := by
          change
            (if best.2.2 = 0 then 0 else 1 / 2) = 1 / 2
          rw [if_neg bestNotZero]
        rw [halfStartHalf]
        constructor
        · linarith
        · calc
            parameter ambient ≤ 1 :=
              (parameterSpec ambient).1.2
            _ = (1 / 2 : ℝ) + 1 / 2 := by norm_num
    refine
      ⟨parameter ambient, (parameterSpec ambient).1,
        parameterHalf, ?_⟩
    rw [selectedPre.tube_eq index]
    exact near
 -/

/--
Every spatial preselection admits a common side-`1/16` cell, a relative
per-tube density pruning inside that cell, and a subsequent weighted
direction-cone/half-segment selection.  The fixed global loss is exactly
`1 / (2 * 49^3 * 12)`.
-/
theorem exists_pureWZ2_directionalHalfPreselectionData
    {sigma sourceLoss pruningLoss outputPruningLoss cellLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {pruning :
      PureWZ2PerTubeDensityPruningData source pruningLoss}
    (data :
      PureWZ2SpatialCellPreselectionData
        (cellLoss := cellLoss) source pruning)
    (densityAbsorption :
      Kakeya.realRpowENN delta outputPruningLoss ≤
        pureWZ2DirectionalHalfDensityFactor *
          Kakeya.realRpowENN delta pruningLoss) :
    Nonempty
      (PureWZ2DirectionalHalfPreselectionData
        (outputPruningLoss := outputPruningLoss) data) := by
  let density := Kakeya.realRpowENN delta pruningLoss
  let outputDensity :=
    Kakeya.realRpowENN delta outputPruningLoss
  let densityFactor := pureWZ2DirectionalHalfDensityFactor
  let cells := pureWZ2RigidCropSpatialCells data.center
  let fullWeight :
      Fin data.preSelected.family.card → ENNReal := fun index =>
    volume (data.localShading.carrier index)
  let cellLocalWeight :
      (ℤ × ℤ × ℤ) →
        Fin data.preSelected.family.card → ENNReal :=
    fun cell index =>
      volume
        (data.localShading.carrier index ∩
          wz1PaperGridCube pureWZ2RigidCropGridScale cell)
  let cellWeight : (ℤ × ℤ × ℤ) → ENNReal := fun cell =>
    ∑ index : Fin data.preSelected.family.card,
      cellLocalWeight cell index
  have densityPos : 0 < density :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos source.extremal.delta_pos pruningLoss)
  have outputDensityPos : 0 < outputDensity :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos
        source.extremal.delta_pos outputPruningLoss)
  have tubeVolumePos :
      ∀ index : Fin data.preSelected.family.card,
        0 < volume (data.preSelected.family.tube index).carrier := by
    intro index
    exact
      wz2_paper_ordinary_tube_volume_pos
        (data.preSelected.family.tube index)
        source.extremal.delta_pos
  have fullWeightPos :
      ∀ index : Fin data.preSelected.family.card,
        0 < fullWeight index := by
    intro index
    exact
      (ENNReal.mul_pos densityPos.ne'
        (tubeVolumePos index).ne').trans_le
        (data.per_tube_local_density index)
  have cellsCard : cells.card = 117649 := by
    simpa [cells] using
      rigidCropSpatialCells_card data.center
  have cellsNonempty : cells.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro cellsEmpty
    have cardZero : cells.card = 0 := by
      rw [cellsEmpty]
      simp
    rw [cellsCard] at cardZero
    omega
  have perTubeCellPartition :
      ∀ index : Fin data.preSelected.family.card,
        ∑ cell ∈ cells, cellLocalWeight cell index =
          fullWeight index := by
    intro index
    simpa [cells, cellLocalWeight, fullWeight] using
      (rigidCrop_volume_eq_sum_spatialCells
        data.center
        (data.localShading.carrier index)
        (data.localShading.measurable_carrier index)
        (fun point pointMem =>
          data.shading_support_local ⟨index, pointMem⟩)).symm
  have totalCellWeight :
      ∑ cell ∈ cells, cellWeight cell =
        data.localShading.mass := by
    calc
      ∑ cell ∈ cells, cellWeight cell =
          ∑ cell ∈ cells,
            ∑ index : Fin data.preSelected.family.card,
              cellLocalWeight cell index := rfl
      _ =
          ∑ index : Fin data.preSelected.family.card,
            ∑ cell ∈ cells, cellLocalWeight cell index := by
        rw [Finset.sum_comm]
      _ =
          ∑ index : Fin data.preSelected.family.card,
            fullWeight index := by
        apply Finset.sum_congr rfl
        intro index _
        exact perTubeCellPartition index
      _ = data.localShading.mass := rfl
  rcases
      Finset.exists_max_image cells cellWeight cellsNonempty with
    ⟨spatialCell, spatialCellMem, spatialCellMax⟩
  have commonCellMass :
      data.localShading.mass ≤
        (117649 : ENNReal) * cellWeight spatialCell := by
    calc
      data.localShading.mass =
          ∑ cell ∈ cells, cellWeight cell :=
        totalCellWeight.symm
      _ ≤
          ∑ _cell ∈ cells, cellWeight spatialCell := by
        apply Finset.sum_le_sum
        intro cell cellMem
        exact spatialCellMax cell cellMem
      _ =
          (cells.card : ENNReal) *
            cellWeight spatialCell := by
        simp
      _ =
          (117649 : ENNReal) *
            cellWeight spatialCell := by
        norm_num [cellsCard]
  let goodIndices :
      Finset (Fin data.preSelected.family.card) :=
    Finset.univ.filter fun index =>
      densityFactor * fullWeight index ≤
        cellLocalWeight spatialCell index
  let badIndices :
      Finset (Fin data.preSelected.family.card) :=
    Finset.univ.filter fun index =>
      ¬ densityFactor * fullWeight index ≤
        cellLocalWeight spatialCell index
  let goodMass : ENNReal :=
    ∑ index ∈ goodIndices,
      cellLocalWeight spatialCell index
  let badMass : ENNReal :=
    ∑ index ∈ badIndices,
      cellLocalWeight spatialCell index
  have cellMassSplit :
      goodMass + badMass = cellWeight spatialCell := by
    simpa [goodMass, badMass, goodIndices, badIndices,
      cellWeight] using
      Finset.sum_filter_add_sum_filter_not
        (Finset.univ :
          Finset (Fin data.preSelected.family.card))
        (fun index =>
          densityFactor * fullWeight index ≤
            cellLocalWeight spatialCell index)
        (fun index => cellLocalWeight spatialCell index)
  have badMassBound :
      badMass ≤ densityFactor * data.localShading.mass := by
    calc
      badMass ≤
          ∑ index ∈ badIndices,
            densityFactor * fullWeight index := by
        apply Finset.sum_le_sum
        intro index indexMem
        exact
          (lt_of_not_ge
            (Finset.mem_filter.mp indexMem).2).le
      _ =
          densityFactor *
            ∑ index ∈ badIndices, fullWeight index := by
        rw [Finset.mul_sum]
      _ ≤
          densityFactor *
            ∑ index : Fin data.preSelected.family.card,
              fullWeight index := by
        gcongr
        exact Finset.filter_subset _ _
      _ = densityFactor * data.localShading.mass := rfl
  have scaledBadMassBound :
      (117649 : ENNReal) * badMass ≤
        data.localShading.mass / 2 := by
    calc
      (117649 : ENNReal) * badMass ≤
          (117649 : ENNReal) *
            (densityFactor * data.localShading.mass) := by
        gcongr
      _ = data.localShading.mass / 2 := by
        exact
          rigidCrop_cellCount_mul_densityFactor
            data.localShading.mass
  have totalMassFinite : data.localShading.mass ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro index _indexMem
    exact
      tubeShading_carrier_volume_ne_top
        data.localShading index
  have halfMassFinite : data.localShading.mass / 2 ≠ ⊤ :=
    ENNReal.div_ne_top totalMassFinite (by norm_num)
  have goodMassLower :
      data.localShading.mass / 2 ≤
        (117649 : ENNReal) * goodMass := by
    have totalUpper :
        data.localShading.mass ≤
          (117649 : ENNReal) * goodMass +
            data.localShading.mass / 2 := by
      calc
        data.localShading.mass ≤
            (117649 : ENNReal) *
              cellWeight spatialCell := commonCellMass
        _ =
            (117649 : ENNReal) *
              (goodMass + badMass) := by
          rw [cellMassSplit]
        _ =
            (117649 : ENNReal) * goodMass +
              (117649 : ENNReal) * badMass := by
          rw [mul_add]
        _ ≤
            (117649 : ENNReal) * goodMass +
              data.localShading.mass / 2 := by
          gcongr
    apply (ENNReal.add_le_add_iff_right halfMassFinite).mp
    simpa only [ENNReal.add_halves] using totalUpper
  have dataMassPos : 0 < data.localShading.mass := by
    let first : Fin data.preSelected.family.card :=
      ⟨0, data.preSelected_nonempty⟩
    calc
      0 < fullWeight first := fullWeightPos first
      _ ≤ data.localShading.mass := by
        exact
          Finset.single_le_sum
            (fun index _ => (bot_le : (0 : ENNReal) ≤ fullWeight index))
            (Finset.mem_univ first)
  have goodMassPos : 0 < goodMass := by
    by_contra notPositive
    have goodMassZero : goodMass = 0 := by
      simpa [not_lt] using notPositive
    rw [goodMassZero, mul_zero] at goodMassLower
    have halfPositive : 0 < data.localShading.mass / 2 :=
      ENNReal.div_pos dataMassPos.ne' (by norm_num)
    exact (not_le_of_gt halfPositive) goodMassLower
  have goodIndicesNonempty : goodIndices.Nonempty := by
    by_contra notNonempty
    have goodEmpty : goodIndices = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using notNonempty
    have goodMassZero : goodMass = 0 := by
      simp [goodMass, goodEmpty]
    rw [goodMassZero] at goodMassPos
    simp at goodMassPos
  let goodPre :=
    WZ2PaperPureTubeSubfamily.fromFinset
      data.preSelected.family goodIndices
  let goodShading :
      Kakeya.Streamlined.TubeShading goodPre.family :=
    {
      carrier := fun index =>
        data.localShading.carrier (goodPre.embedding index) ∩
          wz1PaperGridCube pureWZ2RigidCropGridScale spatialCell
      measurable_carrier := fun index =>
        (data.localShading.measurable_carrier
          (goodPre.embedding index)).inter
            (wz1PaperGridCube_measurable spatialCell)
      subset_body := fun index => by
        change
          data.localShading.carrier (goodPre.embedding index) ∩
              wz1PaperGridCube pureWZ2RigidCropGridScale spatialCell ⊆
            (goodPre.family.tube index).carrier
        rw [goodPre.tube_eq index]
        exact Set.Subset.trans Set.inter_subset_left
          (data.localShading.subset_body _)
    }
  have goodPreNonempty : goodPre.family.Nonempty := by
    change 0 < goodIndices.card
    exact goodIndicesNonempty.card_pos
  have goodEmbeddingMem :
      ∀ index : Fin goodPre.family.card,
        goodPre.embedding index ∈ goodIndices := by
    intro index
    exact Finset.orderEmbOfFin_mem goodIndices rfl index
  have goodPerTube :
      ∀ index : Fin goodPre.family.card,
        outputDensity *
            (goodPre.family.tube index).volume ≤
          volume (goodShading.carrier index) := by
    intro index
    let ambient := goodPre.embedding index
    have goodCriterion :
        densityFactor * fullWeight ambient ≤
          cellLocalWeight spatialCell ambient :=
      (Finset.mem_filter.mp (goodEmbeddingMem index)).2
    have sourceDensity :=
      data.per_tube_local_density ambient
    calc
      outputDensity *
            (goodPre.family.tube index).volume ≤
          (densityFactor * density) *
            (goodPre.family.tube index).volume := by
        gcongr
      _ =
          densityFactor *
            (density *
              (data.preSelected.family.tube ambient).volume) := by
        rw [goodPre.tube_eq index]
        ring
      _ ≤ densityFactor * fullWeight ambient := by
        gcongr
      _ ≤ cellLocalWeight spatialCell ambient :=
        goodCriterion
      _ = volume (goodShading.carrier index) := rfl
  have goodMassEq : goodShading.mass = goodMass := by
    have image :
        Finset.image goodPre.embedding
            (Finset.univ :
              Finset (Fin goodPre.family.card)) =
          goodIndices :=
      Finset.image_orderEmbOfFin_univ goodIndices rfl
    calc
      goodShading.mass =
          ∑ index : Fin goodPre.family.card,
            cellLocalWeight spatialCell
              (goodPre.embedding index) := rfl
      _ =
          ∑ index ∈
              Finset.image goodPre.embedding
                (Finset.univ :
                  Finset (Fin goodPre.family.card)),
            cellLocalWeight spatialCell index := by
        rw [Finset.sum_image]
        intro first _ second _ equality
        exact goodPre.embedding.injective equality
      _ =
          ∑ index ∈ goodIndices,
            cellLocalWeight spatialCell index := by
        rw [image]
      _ = goodMass := rfl
  have goodCarrierVolumePos :
      ∀ index : Fin goodPre.family.card,
        0 < volume (goodShading.carrier index) := by
    intro index
    exact
      (ENNReal.mul_pos outputDensityPos.ne'
        (by
          have positive :=
            wz2_paper_ordinary_tube_volume_pos
              (goodPre.family.tube index)
              source.extremal.delta_pos
          exact positive.ne')).trans_le
        (goodPerTube index)
  let shadedPoint :
      Fin goodPre.family.card → Point3 := fun index =>
    Classical.choose
      (MeasureTheory.nonempty_of_measure_ne_zero
        (goodCarrierVolumePos index).ne')
  have shadedPointMem :
      ∀ index, shadedPoint index ∈ goodShading.carrier index :=
    fun index =>
      Classical.choose_spec
        (MeasureTheory.nonempty_of_measure_ne_zero
          (goodCarrierVolumePos index).ne')
  let parameter : Fin goodPre.family.card → ℝ := fun index =>
    Classical.choose
      (rigidCrop_segment_witness
        source.extremal.delta_pos
        (goodPre.family.tube index)
        (goodShading.subset_body index (shadedPointMem index)))
  have parameterSpec :
      ∀ index,
        parameter index ∈ Set.Icc (0 : ℝ) 1 ∧
        dist (shadedPoint index)
          ((goodPre.family.tube index).base +
            parameter index •
              (goodPre.family.tube index).direction) ≤ delta :=
    fun index =>
      Classical.choose_spec
        (rigidCrop_segment_witness
          source.extremal.delta_pos
          (goodPre.family.tube index)
          (goodShading.subset_body index (shadedPointMem index)))
  let cone : Fin goodPre.family.card → Fin 6 := fun index =>
    Classical.choose
      (rigidCrop_cone_cover
        (goodPre.family.tube index).direction
        (goodPre.family.tube index).direction_unit)
  have coneSpec :
      ∀ index,
        1 / 2 ≤
          inner ℝ (goodPre.family.tube index).direction
            (rigidCropConeCenter (cone index)) :=
    fun index =>
      Classical.choose_spec
        (rigidCrop_cone_cover
          (goodPre.family.tube index).direction
          (goodPre.family.tube index).direction_unit)
  let halfColor : Fin goodPre.family.card → Fin 2 := fun index =>
    if parameter index ≤ 1 / 2 then 0 else 1
  let Color := Fin 6 × Fin 2
  let color : Fin goodPre.family.card → Color := fun index =>
    (cone index, halfColor index)
  let weight : Fin goodPre.family.card → ENNReal := fun index =>
    volume (goodShading.carrier index)
  have colorNonempty : Nonempty Color :=
    ⟨(0, 0)⟩
  rcases
      rigidCrop_weighted_color_pigeonhole
        color colorNonempty weight with
    ⟨best, retainedWeight⟩
  let selectedGoodIndices :
      Finset (Fin goodPre.family.card) :=
    Finset.univ.filter fun index => color index = best
  let selectedWithinGood :=
    WZ2PaperPureTubeSubfamily.fromFinset
      goodPre.family selectedGoodIndices
  let selectedPre :=
    WZ2PaperPureTubeSubfamily.comp
      goodPre selectedWithinGood
  let localShading :=
    selectedWithinGood.toTubeSubfamily.restrictShading goodShading
  have colorCard : Fintype.card Color = 12 := by
    simp [Color]
  have selectedMass :
      (∑ index ∈ selectedGoodIndices, weight index) =
        localShading.mass := by
    have image :
        Finset.image selectedWithinGood.embedding
            (Finset.univ :
              Finset (Fin selectedWithinGood.family.card)) =
          selectedGoodIndices :=
      Finset.image_orderEmbOfFin_univ selectedGoodIndices rfl
    calc
      (∑ index ∈ selectedGoodIndices, weight index) =
          ∑ index ∈
              Finset.image selectedWithinGood.embedding
                (Finset.univ :
                  Finset (Fin selectedWithinGood.family.card)),
            weight index := by rw [image]
      _ =
          ∑ index : Fin selectedWithinGood.family.card,
            weight (selectedWithinGood.embedding index) := by
        rw [Finset.sum_image]
        intro first _ second _ equality
        exact selectedWithinGood.embedding.injective equality
      _ = localShading.mass := rfl
  have retainedGood :
      goodMass ≤ (12 : ENNReal) * localShading.mass := by
    calc
      goodMass = goodShading.mass := goodMassEq.symm
      _ =
          ∑ index : Fin goodPre.family.card,
            weight index := rfl
      _ ≤
          (12 : ENNReal) *
            ∑ index ∈ selectedGoodIndices,
              weight index := by
        simpa [selectedGoodIndices, colorCard] using retainedWeight
      _ = (12 : ENNReal) * localShading.mass := by
        rw [selectedMass]
  have totalRetained :
      data.localShading.mass ≤
        (2823576 : ENNReal) * localShading.mass := by
    calc
      data.localShading.mass =
          data.localShading.mass / 2 +
            data.localShading.mass / 2 :=
        (ENNReal.add_halves _).symm
      _ ≤
          (117649 : ENNReal) * goodMass +
            (117649 : ENNReal) * goodMass := by
        gcongr
      _ =
          (235298 : ENNReal) * goodMass := by
        rw [show (235298 : ENNReal) = 2 * 117649 by norm_num]
        ring
      _ ≤
          (235298 : ENNReal) *
            ((12 : ENNReal) * localShading.mass) := by
        gcongr
      _ =
          (2823576 : ENNReal) * localShading.mass := by
        rw [show (2823576 : ENNReal) = 235298 * 12 by norm_num]
        ring
  have localMassPos : 0 < localShading.mass := by
    by_contra notPositive
    have localMassZero : localShading.mass = 0 := by
      simpa [not_lt] using notPositive
    rw [localMassZero, mul_zero] at totalRetained
    exact (not_le_of_gt dataMassPos) totalRetained
  have selectedNonempty : selectedPre.family.Nonempty := by
    have selectedGoodIndicesNonempty : selectedGoodIndices.Nonempty := by
      by_contra notNonempty
      have selectedEmpty : selectedGoodIndices = ∅ := by
        simpa [Finset.not_nonempty_iff_eq_empty] using notNonempty
      have localMassZero : localShading.mass = 0 := by
        rw [← selectedMass, selectedEmpty]
        simp
      rw [localMassZero] at localMassPos
      simp at localMassPos
    change 0 < selectedGoodIndices.card
    exact selectedGoodIndicesNonempty.card_pos
  have fixedRetention :
      pureWZ2DirectionalHalfSelectionFactor *
          data.localShading.mass ≤
        localShading.mass := by
    calc
      pureWZ2DirectionalHalfSelectionFactor *
            data.localShading.mass ≤
          pureWZ2DirectionalHalfSelectionFactor *
            ((2823576 : ENNReal) * localShading.mass) := by
        gcongr
      _ =
          (pureWZ2DirectionalHalfSelectionFactor *
            (2823576 : ENNReal)) * localShading.mass := by
        rw [mul_assoc]
      _ = localShading.mass := by
        unfold pureWZ2DirectionalHalfSelectionFactor
        rw [ENNReal.inv_mul_cancel] <;> norm_num
  let halfStart : ℝ :=
    if best.2 = 0 then 0 else 1 / 2
  have halfStartCases :
      halfStart = 0 ∨ halfStart = 1 / 2 := by
    by_cases first : best.2 = 0
    · left
      simp [halfStart, first]
    · right
      simp [halfStart, first]
  have selectedColor :
      ∀ index : Fin selectedWithinGood.family.card,
        color (selectedWithinGood.embedding index) = best := by
    intro index
    exact
      (Finset.mem_filter.mp
        (Finset.orderEmbOfFin_mem
          selectedGoodIndices rfl index)).2
  have selectedCone :
      ∀ index,
        cone (selectedWithinGood.embedding index) = best.1 := by
    intro index
    exact congrArg Prod.fst (selectedColor index)
  have selectedHalf :
      ∀ index,
        halfColor (selectedWithinGood.embedding index) = best.2 := by
    intro index
    exact congrArg Prod.snd (selectedColor index)
  let centerDirection := rigidCropConeCenter best.1
  let commonPoint :=
    pureWZ2RigidCropCellCenter spatialCell
  refine
    ⟨{
      selectedPre := selectedPre
      selected_nonempty := selectedNonempty
      spatialCell := spatialCell
      spatialCell_mem := spatialCellMem
      localShading := localShading
      local_carrier_eq := ?_
      local_subshading := ?_
      fixed_mass_retention := fixedRetention
      per_tube_density := ?_
      centerDirection := centerDirection
      centerDirection_unit := rigidCropConeCenter_norm best.1
      commonPoint := commonPoint
      commonPoint_eq := rfl
      halfStart := halfStart
      halfStart_cases := halfStartCases
      direction_cone := ?_
      segment_near := ?_
    }⟩
  · intro index
    rfl
  · intro index
    exact Set.inter_subset_left
  · intro index
    exact goodPerTube (selectedWithinGood.embedding index)
  · intro index
    have sourceCone :=
      coneSpec (selectedWithinGood.embedding index)
    rw [selectedCone index] at sourceCone
    change
      1 / 2 ≤
        inner ℝ centerDirection
          (selectedWithinGood.family.tube index).direction
    rw [selectedWithinGood.tube_eq index]
    simpa [centerDirection, real_inner_comm] using sourceCone
  · intro index
    let goodIndex := selectedWithinGood.embedding index
    have axisDistance := (parameterSpec goodIndex).2
    have pointCell :
        shadedPoint goodIndex ∈
          wz1PaperGridCube pureWZ2RigidCropGridScale
            spatialCell :=
      (shadedPointMem goodIndex).2
    have pointCenter :
        dist (shadedPoint goodIndex) commonPoint ≤
          Real.sqrt 3 / 32 := by
      simpa [commonPoint] using
        pureWZ2_rigidCropCell_point_dist_center_le pointCell
    have near :
        ‖(goodPre.family.tube goodIndex).base +
              parameter goodIndex •
                (goodPre.family.tube goodIndex).direction -
            commonPoint‖ ≤
          Real.sqrt 3 / 32 + delta := by
      rw [← dist_eq_norm]
      calc
        dist
            ((goodPre.family.tube goodIndex).base +
              parameter goodIndex •
                (goodPre.family.tube goodIndex).direction)
            commonPoint ≤
          dist
              ((goodPre.family.tube goodIndex).base +
                parameter goodIndex •
                  (goodPre.family.tube goodIndex).direction)
              (shadedPoint goodIndex) +
            dist (shadedPoint goodIndex) commonPoint :=
          dist_triangle _ _ _
        _ ≤ delta + Real.sqrt 3 / 32 := by
          apply add_le_add
          · rw [dist_comm]
            exact axisDistance
          · exact pointCenter
        _ = Real.sqrt 3 / 32 + delta := by ring
    have parameterHalf :
        parameter goodIndex ∈
          Set.Icc halfStart (halfStart + 1 / 2) := by
      have halfEq := selectedHalf index
      by_cases first : parameter goodIndex ≤ 1 / 2
      · have colorZero : halfColor goodIndex = 0 := by
          change
            (if parameter goodIndex ≤ 1 / 2 then
                (0 : Fin 2)
              else 1) = 0
          rw [if_pos first]
        have bestZero : best.2 = 0 := by
          rw [← halfEq, colorZero]
        have halfStartZero : halfStart = 0 := by
          change (if best.2 = 0 then 0 else 1 / 2) = 0
          rw [if_pos bestZero]
        rw [halfStartZero]
        exact
          ⟨(parameterSpec goodIndex).1.1, by
            norm_num
            exact first⟩
      · have colorOne : halfColor goodIndex = 1 := by
          change
            (if parameter goodIndex ≤ 1 / 2 then
                (0 : Fin 2)
              else 1) = 1
          rw [if_neg first]
        have bestOne : best.2 = 1 := by
          rw [← halfEq, colorOne]
        have bestNotZero : best.2 ≠ 0 := by
          rw [bestOne]
          decide
        have halfStartHalf : halfStart = 1 / 2 := by
          change
            (if best.2 = 0 then 0 else 1 / 2) = 1 / 2
          rw [if_neg bestNotZero]
        rw [halfStartHalf]
        constructor
        · linarith
        · calc
            parameter goodIndex ≤ 1 :=
              (parameterSpec goodIndex).1.2
            _ = (1 / 2 : ℝ) + 1 / 2 := by norm_num
    refine
      ⟨parameter goodIndex, (parameterSpec goodIndex).1,
        parameterHalf, ?_⟩
    change
      ‖(selectedWithinGood.family.tube index).base +
            parameter goodIndex •
              (selectedWithinGood.family.tube index).direction -
          commonPoint‖ ≤
        Real.sqrt 3 / 32 + delta
    rw [selectedWithinGood.tube_eq index]
    exact near

end Kakeya.Assouad

end
