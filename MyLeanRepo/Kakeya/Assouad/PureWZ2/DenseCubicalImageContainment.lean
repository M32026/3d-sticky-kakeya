import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledTube
import MyLeanRepo.Kakeya.Assouad.PropStickyGridCubeBoxHelpers

/-!
# Dense cubical images inside the public ordinary rescaling

A point in the dense cubicalization shares its grid cell with a point of the
ordinary source set.  Both the grid-cell displacement and the source-tube
radius are shrunk by the literal map's factor `1 / 100`; together they fit in
the public ordinary target tube of radius `delta / rho`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

lemma pureWZ2_same_grid_cell_coord_lt
    {delta : ℝ} (hdelta : 0 < delta)
    {cell : ℤ × ℤ × ℤ} {first second : Point3}
    (hfirst : first ∈ wz1PaperGridCube delta cell)
    (hsecond : second ∈ wz1PaperGridCube delta cell)
    (coordinate : Fin 3) :
    |second coordinate - first coordinate| < delta := by
  have firstIndex :
      wz1PaperGridIndex delta first = cell :=
    (mem_wz1PaperGridCube delta cell first).mp hfirst
  have secondIndex :
      wz1PaperGridIndex delta second = cell :=
    (mem_wz1PaperGridCube delta cell second).mp hsecond
  have indexEq :
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second :=
    firstIndex.trans secondIndex.symm
  have floorEq :
      Int.floor (first coordinate / delta) =
        Int.floor (second coordinate / delta) := by
    fin_cases coordinate
    · exact congrArg (fun index : ℤ × ℤ × ℤ => index.1) indexEq
    · exact congrArg (fun index : ℤ × ℤ × ℤ => index.2.1) indexEq
    · exact congrArg (fun index : ℤ × ℤ × ℤ => index.2.2) indexEq
  let level : ℤ := Int.floor (first coordinate / delta)
  have firstLower :
      (level : ℝ) ≤ first coordinate / delta :=
    Int.floor_le _
  have firstUpper :
      first coordinate / delta < (level : ℝ) + 1 :=
    Int.lt_floor_add_one _
  have secondFloor :
      Int.floor (second coordinate / delta) = level :=
    floorEq.symm
  have secondLower :
      (level : ℝ) ≤ second coordinate / delta := by
    have raw :=
      Int.floor_le (second coordinate / delta)
    rwa [secondFloor] at raw
  have secondUpper :
      second coordinate / delta < (level : ℝ) + 1 := by
    have raw :=
      Int.lt_floor_add_one (second coordinate / delta)
    rwa [secondFloor] at raw
  have quotient :
      |(first coordinate - second coordinate) / delta| < 1 := by
    rw [abs_lt]
    constructor
    · have :
          second coordinate / delta -
              first coordinate / delta < 1 := by
        linarith
      have identity :
          (first coordinate - second coordinate) / delta =
            first coordinate / delta -
              second coordinate / delta := by
        field_simp [hdelta.ne']
      rw [identity]
      linarith
    · have :
          first coordinate / delta -
              second coordinate / delta < 1 := by
        linarith
      have identity :
          (first coordinate - second coordinate) / delta =
            first coordinate / delta -
              second coordinate / delta := by
        field_simp [hdelta.ne']
      rwa [identity]
  have distance :
      |first coordinate - second coordinate| < delta := by
    rw [abs_div, abs_of_pos hdelta] at quotient
    exact (div_lt_one hdelta).mp quotient
  simpa [abs_sub_comm] using distance

lemma pureWZ2_same_grid_cell_dist_le
    {delta : ℝ} (hdelta : 0 < delta)
    {cell : ℤ × ℤ × ℤ} {first second : Point3}
    (hfirst : first ∈ wz1PaperGridCube delta cell)
    (hsecond : second ∈ wz1PaperGridCube delta cell) :
    dist second first ≤ delta * Real.sqrt 3 := by
  have coordinateBound :
      ∀ coordinate : Fin 3,
        (second coordinate - first coordinate) ^ 2 ≤ delta ^ 2 := by
    intro coordinate
    have absolute :=
      pureWZ2_same_grid_cell_coord_lt
        hdelta hfirst hsecond coordinate
    have nonnegative :
        0 ≤ |second coordinate - first coordinate| :=
      abs_nonneg _
    have squared :
        |second coordinate - first coordinate| ^ 2 <
          delta ^ 2 := by
      nlinarith
    simpa [sq_abs] using squared.le
  have normSquared :
      ‖second - first‖ ^ 2 =
        (second 0 - first 0) ^ 2 +
          (second 1 - first 1) ^ 2 +
          (second 2 - first 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rw [Fin.sum_univ_three]
    simp
  have squaredBound :
      ‖second - first‖ ^ 2 ≤ 3 * delta ^ 2 := by
    rw [normSquared]
    linarith [coordinateBound 0, coordinateBound 1, coordinateBound 2]
  have sqrtNonnegative : 0 ≤ Real.sqrt 3 :=
    Real.sqrt_nonneg 3
  have sqrtSquared : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have targetSquared :
      (delta * Real.sqrt 3) ^ 2 = 3 * delta ^ 2 := by
    rw [mul_pow, sqrtSquared]
    ring
  rw [dist_eq_norm]
  have targetNonnegative :
      0 ≤ delta * Real.sqrt 3 := by positivity
  nlinarith [
    squaredBound, targetSquared,
    norm_nonneg (second - first)
  ]

theorem wz2PaperLiteral_denseCubicalization_image_subset_ordinary
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (sourceTube : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hcover : WZ1PaperTubeCovers sourceTube anchor)
    (ordinarySource finalCarrier : Set Point3)
    (ordinarySourceSubset :
      ordinarySource ⊆ sourceTube.carrier)
    (ordinarySourceVolumePos :
      0 < volume ordinarySource)
    (finalSubset :
      finalCarrier ⊆
        pureWZ2DenseCubicalization
          sourceTube ordinarySource) :
    wz2PaperLiteralUnitRescalingMap anchor hrho ''
        finalCarrier ⊆
      (wz2PaperLiteralOrdinaryRescaledTube
        sourceTube anchor hrho).carrier := by
  rintro _ ⟨point, pointFinal, rfl⟩
  have pointDense := finalSubset pointFinal
  let cell := wz1PaperGridIndex delta point
  have pointCell :
      point ∈ wz1PaperGridCube delta cell :=
    (mem_wz1PaperGridCube delta cell point).mpr rfl
  have sourceVolumeTop :
      volume sourceTube.carrier ≠ ⊤ :=
    wz2_paper_ordinary_tube_volume_ne_top sourceTube hdelta
  have sourceVolumePos :
      0 < volume sourceTube.carrier :=
    wz2_paper_ordinary_tube_volume_pos sourceTube hdelta
  have cubeVolumePos :
      0 < volume (wz1PaperGridCube delta cell) :=
    wz1PaperGridCube_volume_pos hdelta cell
  have thresholdPos :
      0 <
        (100 : ENNReal)⁻¹ *
          volume ordinarySource *
          (volume sourceTube.carrier)⁻¹ *
          volume (wz1PaperGridCube delta cell) := by
    have hundredInvPos : 0 < (100 : ENNReal)⁻¹ :=
      ENNReal.inv_pos.mpr (by norm_num)
    have sourceInvPos :
        0 < (volume sourceTube.carrier)⁻¹ :=
      ENNReal.inv_pos.mpr sourceVolumeTop
    exact
      ENNReal.mul_pos
        (ENNReal.mul_pos
          (ENNReal.mul_pos
            hundredInvPos.ne'
            ordinarySourceVolumePos.ne' |>.ne')
          sourceInvPos.ne' |>.ne')
        cubeVolumePos.ne'
  have intersectionVolumePos :
      0 <
        volume
          (ordinarySource ∩
            wz1PaperGridCube delta cell) := by
    have lower := pointDense.2
    simpa [cell] using thresholdPos.trans_le lower
  rcases
      MeasureTheory.nonempty_of_measure_ne_zero
        intersectionVolumePos.ne'
    with ⟨ordinaryPoint, ordinaryPointSource, ordinaryPointCell⟩
  have pointOrdinaryDistance :
      dist point ordinaryPoint ≤ delta * Real.sqrt 3 :=
    pureWZ2_same_grid_cell_dist_le
      (cell := cell) hdelta ordinaryPointCell pointCell
  have ordinaryPointCarrier :
      ordinaryPoint ∈ sourceTube.carrier :=
    ordinarySourceSubset ordinaryPointSource
  have segmentCompact :
      IsCompact
        (Kakeya.unitSegment
          sourceTube.base sourceTube.direction) :=
    isCompact_Icc.image
      (continuous_const.add
        (continuous_id.smul continuous_const))
  have ordinaryPointThickening :
      ordinaryPoint ∈
        Metric.cthickening delta
          (Kakeya.unitSegment
            sourceTube.base sourceTube.direction) :=
    ordinaryPointCarrier
  rw [segmentCompact.cthickening_eq_biUnion_closedBall hdelta.le]
    at ordinaryPointThickening
  rcases Set.mem_iUnion₂.mp ordinaryPointThickening with
    ⟨axisPoint, axisPointSegment, ordinaryAxisDistance⟩
  have imageAxisPoint :
      wz2PaperLiteralUnitRescalingMap anchor hrho axisPoint ∈
        Kakeya.unitSegment
          (wz2PaperLiteralOrdinaryRescaledTube
            sourceTube anchor hrho).base
          (wz2PaperLiteralOrdinaryRescaledTube
            sourceTube anchor hrho).direction :=
    wz2PaperLiteral_image_unitSegment_subset
      sourceTube anchor hrho hrhoOne hcover
        ⟨axisPoint, axisPointSegment, rfl⟩
  have ordinaryAxisDistance' :
      dist ordinaryPoint axisPoint ≤ delta := by
    simpa [Metric.mem_closedBall] using ordinaryAxisDistance
  have sourceDistance :
      ‖point - axisPoint‖ ≤
        delta * Real.sqrt 3 + delta := by
    rw [← dist_eq_norm]
    exact
      (dist_triangle point ordinaryPoint axisPoint).trans
        (add_le_add pointOrdinaryDistance ordinaryAxisDistance')
  have imageDistance :
      dist
          (wz2PaperLiteralUnitRescalingMap anchor hrho point)
          (wz2PaperLiteralUnitRescalingMap anchor hrho axisPoint) ≤
        delta / rho := by
    rw [dist_eq_norm,
      wz2PaperLiteralUnitRescalingMap_sub]
    calc
      ‖wz2PaperLiteralUnitRescalingLinear anchor
          (point - axisPoint)‖ ≤
          ‖point - axisPoint‖ / (100 * rho) :=
        wz2PaperLiteralUnitRescalingLinear_norm_le
          anchor hrho hrhoOne _
      _ ≤
          (delta * Real.sqrt 3 + delta) /
            (100 * rho) := by
        gcongr
      _ ≤ delta / rho := by
        have sqrtBound : Real.sqrt 3 ≤ 2 := by
          nlinarith [
            Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
            Real.sqrt_nonneg 3
          ]
        apply
          (div_le_iff₀
            (mul_pos (by norm_num) hrho)).mpr
        calc
          delta * Real.sqrt 3 + delta ≤ 100 * delta := by
            nlinarith
          _ = (delta / rho) * (100 * rho) := by
            field_simp [hrho.ne']
  exact
    Metric.mem_cthickening_of_dist_le
      (wz2PaperLiteralUnitRescalingMap anchor hrho point)
      (wz2PaperLiteralUnitRescalingMap anchor hrho axisPoint)
      (delta / rho)
      (Kakeya.unitSegment
        (wz2PaperLiteralOrdinaryRescaledTube
          sourceTube anchor hrho).base
        (wz2PaperLiteralOrdinaryRescaledTube
          sourceTube anchor hrho).direction)
      imageAxisPoint imageDistance

end Kakeya.Assouad

end
