import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryDistinctToOverlapDistinct
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnisotropicPacking
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralSeparationConstants

/-!
# Bounded-base packing in the paper line metric

The ordinary public notion of essential distinctness permits longitudinally
shifted tubes on the same supporting line.  The paper line metric forgets
that longitudinal parameter, so the five-dimensional WZ line packing lemma
does not apply directly.

For a bounded-base family, add the longitudinal midpoint parameter as one
coarse coordinate.  The other six coordinates are the axis-zero point and
the paper-positive direction.  Equal anisotropic cells force one ordinary
carrier into the centered double of the other, contradicting literal
ordinary essential distinctness.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

noncomputable def pureWZ2OrdinaryAxialParameter
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (line : WZ1PaperTubeInLineClass tube) : ℝ :=
  Classical.choose <| wz1Paper_axis_exists_parameter line <| by
    show wz2PaperTubeMidpoint tube ∈ tubeAxisLine tube
    exact ⟨1 / 2, rfl⟩

theorem pureWZ2OrdinaryAxialParameter_spec
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (line : WZ1PaperTubeInLineClass tube) :
    wz2PaperTubeMidpoint tube =
      wz1TubeAxisZeroPoint tube +
        pureWZ2OrdinaryAxialParameter tube line •
          wz1PaperDirection tube :=
  Classical.choose_spec <|
    wz1Paper_axis_exists_parameter line <| by
      show wz2PaperTubeMidpoint tube ∈ tubeAxisLine tube
      exact ⟨1 / 2, rfl⟩

theorem pureWZ2_axisZero_norm_le_one
    {delta : ℝ}
    {tube : Kakeya.DeltaTube delta}
    (line : WZ1PaperTubeInLineClass tube) :
    ‖wz1TubeAxisZeroPoint tube‖ ≤ 1 := by
  let zero := wz1TubeAxisZeroPoint tube
  have zeroTwo : zero (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two tube line.vertical
  have normSq :
      ‖zero‖ ^ 2 =
        zero 0 ^ 2 + zero 1 ^ 2 + zero 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have zeroSq : zero 0 ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    nlinarith [sq_abs (zero 0), abs_nonneg (zero 0), line.2.1]
  have oneSq : zero 1 ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := by
    nlinarith [sq_abs (zero 1), abs_nonneg (zero 1), line.2.2]
  have normSqBound : ‖zero‖ ^ 2 ≤ 1 := by
    rw [normSq, zeroTwo]
    norm_num at zeroSq oneSq ⊢
    nlinarith
  change ‖zero‖ ≤ 1
  nlinarith [norm_nonneg zero]

theorem pureWZ2OrdinaryAxialParameter_abs_le_six
    {delta : ℝ}
    {tube : Kakeya.DeltaTube delta}
    (line : WZ1PaperTubeInLineClass tube)
    (baseBound : ‖tube.base‖ ≤ 4) :
    |pureWZ2OrdinaryAxialParameter tube line| ≤ 6 := by
  let axial := pureWZ2OrdinaryAxialParameter tube line
  let midpoint := wz2PaperTubeMidpoint tube
  let zero := wz1TubeAxisZeroPoint tube
  have parameterEq :
      midpoint - zero =
        axial • wz1PaperDirection tube := by
    dsimp only [midpoint, zero, axial]
    rw [pureWZ2OrdinaryAxialParameter_spec tube line]
    abel
  have midpointBound : ‖midpoint‖ ≤ 9 / 2 := by
    dsimp only [midpoint, wz2PaperTubeMidpoint]
    calc
      ‖tube.base + (1 / 2 : ℝ) • tube.direction‖ ≤
          ‖tube.base‖ + ‖(1 / 2 : ℝ) • tube.direction‖ :=
        norm_add_le _ _
      _ = ‖tube.base‖ + 1 / 2 := by
        rw [norm_smul, tube.direction_unit]
        norm_num
      _ ≤ 9 / 2 := by linarith
  have zeroBound : ‖zero‖ ≤ 1 :=
    pureWZ2_axisZero_norm_le_one line
  have differenceBound : ‖midpoint - zero‖ ≤ 11 / 2 := by
    exact (norm_sub_le midpoint zero).trans <| by linarith
  have parameterNorm :
      ‖midpoint - zero‖ = |axial| := by
    rw [parameterEq, norm_smul, wz1PaperDirection_norm]
    simp [Real.norm_eq_abs]
  rw [parameterNorm] at differenceBound
  linarith

theorem pureWZ2OrdinaryAxialParameter_abs_le_ten
    {delta : ℝ}
    {tube : Kakeya.DeltaTube delta}
    (line : WZ1PaperTubeInLineClass tube)
    (baseBound : ‖tube.base‖ ≤ 8) :
    |pureWZ2OrdinaryAxialParameter tube line| ≤ 10 := by
  let axial := pureWZ2OrdinaryAxialParameter tube line
  let midpoint := wz2PaperTubeMidpoint tube
  let zero := wz1TubeAxisZeroPoint tube
  have parameterEq :
      midpoint - zero =
        axial • wz1PaperDirection tube := by
    dsimp only [midpoint, zero, axial]
    rw [pureWZ2OrdinaryAxialParameter_spec tube line]
    abel
  have midpointBound : ‖midpoint‖ ≤ 17 / 2 := by
    dsimp only [midpoint, wz2PaperTubeMidpoint]
    calc
      ‖tube.base + (1 / 2 : ℝ) • tube.direction‖ ≤
          ‖tube.base‖ + ‖(1 / 2 : ℝ) • tube.direction‖ :=
        norm_add_le _ _
      _ = ‖tube.base‖ + 1 / 2 := by
        rw [norm_smul, tube.direction_unit]
        norm_num
      _ ≤ 17 / 2 := by linarith
  have zeroBound : ‖zero‖ ≤ 1 :=
    pureWZ2_axisZero_norm_le_one line
  have differenceBound : ‖midpoint - zero‖ ≤ 19 / 2 := by
    exact (norm_sub_le midpoint zero).trans <| by linarith
  have parameterNorm :
      ‖midpoint - zero‖ = |axial| := by
    rw [parameterEq, norm_smul, wz1PaperDirection_norm]
    simp [Real.norm_eq_abs]
  rw [parameterNorm] at differenceBound
  linarith

private theorem pureWZ2_abs_coord_le_norm
    (point : Point3) (coordinate : Fin 3) :
    |point coordinate| ≤ ‖point‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le point coordinate

private theorem pureWZ2_line_conflict_parameter_bounds
    {delta separation : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (line : WZ1PaperIsLineClass family)
    (fixed : Fin family.card)
    (index : Fin family.card)
    (conflict :
      wz1PaperLineDistance
          (family.tube index) (family.tube fixed) ≤
        separation) :
    (∀ coordinate,
      |(wz1TubeAxisZeroPoint (family.tube index) -
          wz1TubeAxisZeroPoint (family.tube fixed)) coordinate| ≤
        separation) ∧
      (∀ coordinate,
        |(wz1PaperDirection (family.tube index) -
            wz1PaperDirection (family.tube fixed)) coordinate| ≤
          separation) := by
  have zeroDistance :
      dist
          (wz1TubeAxisZeroPoint (family.tube index))
          (wz1TubeAxisZeroPoint (family.tube fixed)) ≤
        separation := by
    unfold wz1PaperLineDistance at conflict
    linarith [InnerProductGeometry.angle_nonneg
      (wz1PaperDirection (family.tube index))
      (wz1PaperDirection (family.tube fixed))]
  have angleBound :
      InnerProductGeometry.angle
          (wz1PaperDirection (family.tube index))
          (wz1PaperDirection (family.tube fixed)) ≤
        separation := by
    unfold wz1PaperLineDistance at conflict
    linarith [dist_nonneg
      (x := wz1TubeAxisZeroPoint (family.tube index))
      (y := wz1TubeAxisZeroPoint (family.tube fixed))]
  have directionDistance :
      ‖wz1PaperDirection (family.tube index) -
          wz1PaperDirection (family.tube fixed)‖ ≤
        separation :=
    (unit_norm_sub_le_angle
      (wz1PaperDirection_norm (family.tube index))
      (wz1PaperDirection_norm (family.tube fixed))).trans angleBound
  constructor
  · intro coordinate
    exact
      (pureWZ2_abs_coord_le_norm
        (wz1TubeAxisZeroPoint (family.tube index) -
          wz1TubeAxisZeroPoint (family.tube fixed))
        coordinate).trans <| by
          simpa [dist_eq_norm] using zeroDistance
  · intro coordinate
    exact
      (pureWZ2_abs_coord_le_norm
        (wz1PaperDirection (family.tube index) -
          wz1PaperDirection (family.tube fixed))
        coordinate).trans directionDistance

private theorem pureWZ2_same_ordinary_parameter_cell_containment
    {delta : ℝ}
    (deltaPos : 0 < delta)
    {first second : Kakeya.DeltaTube delta}
    (firstLine : WZ1PaperTubeInLineClass first)
    (secondLine : WZ1PaperTubeInLineClass second)
    (firstBaseBound : ‖first.base‖ ≤ 8)
    (axisClose :
      ∀ coordinate,
        |(wz1TubeAxisZeroPoint first -
            wz1TubeAxisZeroPoint second) coordinate| <
          delta / 10000)
    (directionClose :
      ∀ coordinate,
        |(wz1PaperDirection first -
            wz1PaperDirection second) coordinate| <
          delta / 10000)
    (axialClose :
      |pureWZ2OrdinaryAxialParameter first firstLine -
          pureWZ2OrdinaryAxialParameter second secondLine| <
        1 / 128) :
    first.carrier ⊆ wz2PaperCenteredDilatedCarrier 2 second := by
  let firstCanonical := wz2PaperCanonicalLineTube first
  let secondCanonical := wz2PaperCanonicalLineTube second
  let axialShift :=
    pureWZ2OrdinaryAxialParameter first firstLine -
      pureWZ2OrdinaryAxialParameter second secondLine
  have firstMidpoint :
      wz2PaperTubeMidpoint firstCanonical =
        wz1TubeAxisZeroPoint first +
          pureWZ2OrdinaryAxialParameter first firstLine •
            wz1PaperDirection first := by
    rw [show wz2PaperTubeMidpoint firstCanonical =
      wz2PaperTubeMidpoint first by
        unfold firstCanonical wz2PaperCanonicalLineTube
        split_ifs
        · rfl
        · exact wz2PaperTubeMidpoint_reverse first]
    exact pureWZ2OrdinaryAxialParameter_spec first firstLine
  have secondMidpoint :
      wz2PaperTubeMidpoint secondCanonical =
        wz1TubeAxisZeroPoint second +
          pureWZ2OrdinaryAxialParameter second secondLine •
            wz1PaperDirection second := by
    rw [show wz2PaperTubeMidpoint secondCanonical =
      wz2PaperTubeMidpoint second by
        unfold secondCanonical wz2PaperCanonicalLineTube
        split_ifs
        · rfl
        · exact wz2PaperTubeMidpoint_reverse second]
    exact pureWZ2OrdinaryAxialParameter_spec second secondLine
  have firstDirection :
      firstCanonical.direction = wz1PaperDirection first := by
    unfold firstCanonical wz2PaperCanonicalLineTube wz1PaperDirection
    split_ifs <;> rfl
  have secondDirection :
      secondCanonical.direction = wz1PaperDirection second := by
    unfold secondCanonical wz2PaperCanonicalLineTube wz1PaperDirection
    split_ifs <;> rfl
  have rawDirectionFineBound :
      ‖wz1PaperDirection first - wz1PaperDirection second‖ ≤
        delta / 5000 := by
    have coordinateSq :
        ∀ coordinate,
          ((wz1PaperDirection first -
              wz1PaperDirection second) coordinate) ^ 2 ≤
            (delta / 10000) ^ 2 := by
      intro coordinate
      have close := directionClose coordinate
      have squared :=
        (sq_le_sq₀
          (abs_nonneg
            ((wz1PaperDirection first -
              wz1PaperDirection second) coordinate))
          (by positivity : 0 ≤ delta / 10000)).mpr close.le
      simpa [sq_abs] using squared
    have normSq :
        ‖wz1PaperDirection first -
            wz1PaperDirection second‖ ^ 2 =
          ∑ coordinate : Fin 3,
            ((wz1PaperDirection first -
              wz1PaperDirection second) coordinate) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq _
    have normSqBound :
        ‖wz1PaperDirection first -
            wz1PaperDirection second‖ ^ 2 ≤
          3 * (delta / 10000) ^ 2 := by
      rw [normSq, Fin.sum_univ_three]
      linarith [coordinateSq 0, coordinateSq 1, coordinateSq 2]
    nlinarith [
      norm_nonneg
        (wz1PaperDirection first - wz1PaperDirection second)]
  have directionNorm :
      ‖firstCanonical.direction - secondCanonical.direction‖ ≤
        delta / 16 := by
    rw [firstDirection, secondDirection]
    exact rawDirectionFineBound.trans <| by
      nlinarith
  have axisNorm :
      ‖wz1TubeAxisZeroPoint first -
          wz1TubeAxisZeroPoint second‖ ≤
        delta / 5000 := by
    have coordinateSq :
        ∀ coordinate,
          ((wz1TubeAxisZeroPoint first -
              wz1TubeAxisZeroPoint second) coordinate) ^ 2 ≤
            (delta / 10000) ^ 2 := by
      intro coordinate
      have close := axisClose coordinate
      have squared :=
        (sq_le_sq₀
          (abs_nonneg
            ((wz1TubeAxisZeroPoint first -
              wz1TubeAxisZeroPoint second) coordinate))
          (by positivity : 0 ≤ delta / 10000)).mpr close.le
      simpa [sq_abs] using squared
    have normSq :
        ‖wz1TubeAxisZeroPoint first -
            wz1TubeAxisZeroPoint second‖ ^ 2 =
          ∑ coordinate : Fin 3,
            ((wz1TubeAxisZeroPoint first -
              wz1TubeAxisZeroPoint second) coordinate) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq _
    have normSqBound :
        ‖wz1TubeAxisZeroPoint first -
            wz1TubeAxisZeroPoint second‖ ^ 2 ≤
          3 * (delta / 10000) ^ 2 := by
      rw [normSq, Fin.sum_univ_three]
      linarith [coordinateSq 0, coordinateSq 1, coordinateSq 2]
    nlinarith [
      norm_nonneg
        (wz1TubeAxisZeroPoint first -
          wz1TubeAxisZeroPoint second)]
  have firstAxialBound :
      |pureWZ2OrdinaryAxialParameter first firstLine| ≤ 10 :=
    pureWZ2OrdinaryAxialParameter_abs_le_ten
      firstLine firstBaseBound
  have residualIdentity :
      (wz2PaperTubeMidpoint firstCanonical -
          wz2PaperTubeMidpoint secondCanonical) -
        axialShift • secondCanonical.direction =
      (wz1TubeAxisZeroPoint first -
          wz1TubeAxisZeroPoint second) +
        pureWZ2OrdinaryAxialParameter first firstLine •
          (wz1PaperDirection first -
            wz1PaperDirection second) := by
    rw [firstMidpoint, secondMidpoint, secondDirection]
    dsimp only [axialShift]
    module
  have residualNorm :
      ‖(wz2PaperTubeMidpoint firstCanonical -
            wz2PaperTubeMidpoint secondCanonical) -
          axialShift • secondCanonical.direction‖ ≤
        delta / 16 := by
    rw [residualIdentity]
    calc
      ‖(wz1TubeAxisZeroPoint first -
            wz1TubeAxisZeroPoint second) +
          pureWZ2OrdinaryAxialParameter first firstLine •
            (wz1PaperDirection first -
              wz1PaperDirection second)‖ ≤
          ‖wz1TubeAxisZeroPoint first -
            wz1TubeAxisZeroPoint second‖ +
          ‖pureWZ2OrdinaryAxialParameter first firstLine •
            (wz1PaperDirection first -
              wz1PaperDirection second)‖ :=
        norm_add_le _ _
      _ ≤ delta / 5000 +
          10 * (delta / 5000) := by
        rw [norm_smul, Real.norm_eq_abs]
        gcongr
      _ ≤ delta / 16 := by
        nlinarith
  have axialQuarter : |axialShift| ≤ 1 / 4 := by
    dsimp only [axialShift]
    exact axialClose.le.trans (by norm_num)
  have canonicalContainment :
      firstCanonical.carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 secondCanonical :=
    wz2PaperOrdinary_carrier_subset_centeredDilatedTwo_of_axial_close
      deltaPos axialQuarter residualNorm directionNorm
  have firstCarrier :
      firstCanonical.carrier = first.carrier :=
    wz2PaperCanonicalLineTube_carrier first
  have secondCarrier :
      secondCanonical.carrier = second.carrier :=
    wz2PaperCanonicalLineTube_carrier second
  have secondMidpointEq :
      wz2PaperTubeMidpoint secondCanonical =
        wz2PaperTubeMidpoint second := by
    unfold secondCanonical wz2PaperCanonicalLineTube
    split_ifs
    · rfl
    · exact wz2PaperTubeMidpoint_reverse second
  unfold wz2PaperCenteredDilatedCarrier at canonicalContainment ⊢
  rw [firstCarrier, secondCarrier, secondMidpointEq] at canonicalContainment
  exact canonicalContainment

/-- Absolute conflict degree for the frozen Section 6 source-separation
threshold. -/
def pureWZ2OrdinaryLineConflictDegree : ℕ :=
  ∏ coordinate : Fin 7,
    if coordinate.1 = 6 then 2561
    else
      2 * Nat.ceil
        (10000 * wz2PaperLiteralSourceSeparationFactor) + 1

/-- Seven-coordinate ordinary line packing at an arbitrary nonnegative
line-distance radius. -/
def pureWZ2OrdinaryLineConflictDegreeWithin
    (delta separation : ℝ) : ℕ :=
  ∏ coordinate : Fin 7,
    if coordinate.1 = 6 then 2561
    else 2 * Nat.ceil (separation / (delta / 10000)) + 1

theorem pureWZ2_ordinary_line_conflict_degree_within
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (separation : ℝ)
    (separationNonnegative : 0 ≤ separation)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (line : WZ1PaperIsLineClass family)
    (boundedBase : HasBoundedBase family 8)
    (distinct : WZ2PaperOrdinaryIsEssentiallyDistinct family) :
    ∀ fixed : Fin family.card,
      (Finset.univ.filter fun other =>
        wz1PaperLineDistance
            (family.tube other) (family.tube fixed) ≤
          separation).card ≤
        pureWZ2OrdinaryLineConflictDegreeWithin delta separation := by
  intro fixed
  let conflicts : Finset (Fin family.card) :=
    Finset.univ.filter fun other =>
      wz1PaperLineDistance
          (family.tube other) (family.tube fixed) ≤
        separation
  let parameter : Fin family.card → Fin 7 → ℝ := fun index coordinate =>
    match coordinate.1 with
    | 0 =>
        (wz1TubeAxisZeroPoint (family.tube index) -
          wz1TubeAxisZeroPoint (family.tube fixed)) 0
    | 1 =>
        (wz1TubeAxisZeroPoint (family.tube index) -
          wz1TubeAxisZeroPoint (family.tube fixed)) 1
    | 2 =>
        (wz1TubeAxisZeroPoint (family.tube index) -
          wz1TubeAxisZeroPoint (family.tube fixed)) 2
    | 3 =>
        (wz1PaperDirection (family.tube index) -
          wz1PaperDirection (family.tube fixed)) 0
    | 4 =>
        (wz1PaperDirection (family.tube index) -
          wz1PaperDirection (family.tube fixed)) 1
    | 5 =>
        (wz1PaperDirection (family.tube index) -
          wz1PaperDirection (family.tube fixed)) 2
    | _ =>
        pureWZ2OrdinaryAxialParameter
          (family.tube index) (line index)
  let mesh : Fin 7 → ℝ := fun coordinate =>
    if coordinate.1 = 6 then 1 / 128 else delta / 10000
  let radius : Fin 7 → ℝ := fun coordinate =>
    if coordinate.1 = 6 then 10
    else separation
  let values : Finset (Fin 7 → ℝ) :=
    conflicts.image parameter
  have meshPos : ∀ coordinate, 0 < mesh coordinate := by
    intro coordinate
    dsimp only [mesh]
    split_ifs <;> positivity
  have radiusNonnegative :
      ∀ coordinate, 0 ≤ radius coordinate := by
    intro coordinate
    dsimp only [radius]
    split_ifs
    · norm_num
    · exact separationNonnegative
  have parameterBound :
      ∀ value ∈ values,
        ∀ coordinate, |value coordinate| ≤ radius coordinate := by
    intro value valueMem coordinate
    rcases Finset.mem_image.mp valueMem with
      ⟨index, indexMem, rfl⟩
    have conflict := (Finset.mem_filter.mp indexMem).2
    have bounds :=
      pureWZ2_line_conflict_parameter_bounds line fixed index conflict
    dsimp only [parameter, radius]
    fin_cases coordinate
    · exact bounds.1 0
    · exact bounds.1 1
    · exact bounds.1 2
    · exact bounds.2 0
    · exact bounds.2 1
    · exact bounds.2 2
    · simp
      exact
        pureWZ2OrdinaryAxialParameter_abs_le_ten
          (line index) (boundedBase index)
  have parameterSeparation :
      ∀ first ∈ values,
        ∀ second ∈ values,
          first ≠ second →
            ∃ coordinate,
              |first coordinate - second coordinate| ≥
                mesh coordinate := by
    intro first firstMem second secondMem valuesNe
    rcases Finset.mem_image.mp firstMem with
      ⟨firstIndex, firstConflict, rfl⟩
    rcases Finset.mem_image.mp secondMem with
      ⟨secondIndex, secondConflict, secondEq⟩
    subst second
    by_contra noCoordinate
    push Not at noCoordinate
    have indexNe : firstIndex ≠ secondIndex := by
      intro indexEq
      apply valuesNe
      rw [indexEq]
    have axisClose :
        ∀ coordinate,
          |(wz1TubeAxisZeroPoint (family.tube firstIndex) -
              wz1TubeAxisZeroPoint (family.tube secondIndex))
            coordinate| < delta / 10000 := by
      intro coordinate
      fin_cases coordinate
      · simpa [parameter, mesh] using noCoordinate (0 : Fin 7)
      · simpa [parameter, mesh] using noCoordinate (1 : Fin 7)
      · simpa [parameter, mesh] using noCoordinate (2 : Fin 7)
    have directionClose :
        ∀ coordinate,
          |(wz1PaperDirection (family.tube firstIndex) -
              wz1PaperDirection (family.tube secondIndex))
            coordinate| < delta / 10000 := by
      intro coordinate
      fin_cases coordinate
      · simpa [parameter, mesh] using noCoordinate (3 : Fin 7)
      · simpa [parameter, mesh] using noCoordinate (4 : Fin 7)
      · simpa [parameter, mesh] using noCoordinate (5 : Fin 7)
    have axialClose :
        |pureWZ2OrdinaryAxialParameter
              (family.tube firstIndex) (line firstIndex) -
            pureWZ2OrdinaryAxialParameter
              (family.tube secondIndex) (line secondIndex)| <
          1 / 128 := by
      simpa [parameter, mesh] using noCoordinate (6 : Fin 7)
    have containment :=
      pureWZ2_same_ordinary_parameter_cell_containment
        deltaPos (line firstIndex) (line secondIndex)
        (boundedBase firstIndex)
        axisClose directionClose axialClose
    exact (distinct firstIndex secondIndex indexNe).1 containment
  have packed :=
    anisotropic_cell_pack meshPos radiusNonnegative
      parameterBound parameterSeparation
  have parameterInjective :
      Set.InjOn parameter conflicts := by
    intro first firstMem second secondMem parameterEq
    by_contra indexNe
    have axisClose :
        ∀ coordinate,
          |(wz1TubeAxisZeroPoint (family.tube first) -
              wz1TubeAxisZeroPoint (family.tube second))
            coordinate| < delta / 10000 := by
      intro coordinate
      have coordinateCases :
          coordinate = 0 ∨ coordinate = 1 ∨ coordinate = 2 := by
        omega
      rcases coordinateCases with rfl | rfl | rfl
      · have equality := congrFun parameterEq (0 : Fin 7)
        simp [parameter] at equality
        simp [Pi.sub_apply, equality]
        positivity
      · have equality := congrFun parameterEq (1 : Fin 7)
        simp [parameter] at equality
        simp [Pi.sub_apply, equality]
        positivity
      · have equality := congrFun parameterEq (2 : Fin 7)
        simp [parameter] at equality
        simp [Pi.sub_apply, equality]
        positivity
    have directionClose :
        ∀ coordinate,
          |(wz1PaperDirection (family.tube first) -
              wz1PaperDirection (family.tube second))
            coordinate| < delta / 10000 := by
      intro coordinate
      have coordinateCases :
          coordinate = 0 ∨ coordinate = 1 ∨ coordinate = 2 := by
        omega
      rcases coordinateCases with rfl | rfl | rfl
      · have equality := congrFun parameterEq (3 : Fin 7)
        simp [parameter] at equality
        simp [Pi.sub_apply, equality]
        positivity
      · have equality := congrFun parameterEq (4 : Fin 7)
        simp [parameter] at equality
        simp [Pi.sub_apply, equality]
        positivity
      · have equality := congrFun parameterEq (5 : Fin 7)
        simp [parameter] at equality
        simp [Pi.sub_apply, equality]
        positivity
    have axialClose :
        |pureWZ2OrdinaryAxialParameter
              (family.tube first) (line first) -
            pureWZ2OrdinaryAxialParameter
              (family.tube second) (line second)| <
          1 / 128 := by
      have equality := congrFun parameterEq (6 : Fin 7)
      simp [parameter] at equality
      rw [equality]
      norm_num
    have containment :=
      pureWZ2_same_ordinary_parameter_cell_containment
        deltaPos (line first) (line second) (boundedBase first)
        axisClose directionClose axialClose
    exact (distinct first second indexNe).1 containment
  have valuesCard : values.card = conflicts.card :=
    Finset.card_image_of_injOn parameterInjective
  have axialCeilNormalized :
      Nat.ceil ((10 : ℝ) * 128) = 1280 := by
    norm_num
  have productBound :
      (∏ coordinate : Fin 7,
        (2 * Nat.ceil
          (radius coordinate / mesh coordinate) + 1)) =
        pureWZ2OrdinaryLineConflictDegreeWithin delta separation := by
    unfold pureWZ2OrdinaryLineConflictDegreeWithin
    apply Finset.prod_congr rfl
    intro coordinate _
    fin_cases coordinate
    all_goals
      simp [radius, mesh, axialCeilNormalized]
  rw [← valuesCard]
  exact packed.trans_eq productBound

theorem pureWZ2_ordinary_line_conflict_degree
    {delta : ℝ}
    (deltaPos : 0 < delta)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (line : WZ1PaperIsLineClass family)
    (boundedBase : HasBoundedBase family 8)
    (distinct : WZ2PaperOrdinaryIsEssentiallyDistinct family) :
    ∀ fixed : Fin family.card,
      (Finset.univ.filter fun other =>
        wz1PaperLineDistance
            (family.tube other) (family.tube fixed) ≤
          wz2PaperLiteralSourceSeparationFactor * delta).card ≤
        pureWZ2OrdinaryLineConflictDegree := by
  intro fixed
  have packed := pureWZ2_ordinary_line_conflict_degree_within
    deltaPos (wz2PaperLiteralSourceSeparationFactor * delta)
    (by positivity) line boundedBase distinct fixed
  have quotient :
      (wz2PaperLiteralSourceSeparationFactor : ℝ) * delta /
          (delta / 10000) =
        ((10000 * wz2PaperLiteralSourceSeparationFactor : ℕ) : ℝ) := by
    field_simp [deltaPos.ne']
    norm_num [wz2PaperLiteralSourceSeparationFactor]
  have transverseCeil' :
      Nat.ceil
          ((10000 : ℝ) *
            (wz2PaperLiteralSourceSeparationFactor : ℝ)) =
        10000 * wz2PaperLiteralSourceSeparationFactor := by
    rw [show (10000 : ℝ) *
        (wz2PaperLiteralSourceSeparationFactor : ℝ) =
      ((10000 * wz2PaperLiteralSourceSeparationFactor : ℕ) : ℝ) by
        norm_num]
    exact Nat.ceil_natCast _
  have degreeEq :
      pureWZ2OrdinaryLineConflictDegreeWithin delta
          (wz2PaperLiteralSourceSeparationFactor * delta) =
        pureWZ2OrdinaryLineConflictDegree := by
    unfold pureWZ2OrdinaryLineConflictDegreeWithin
      pureWZ2OrdinaryLineConflictDegree
    apply Finset.prod_congr rfl
    intro coordinate _
    fin_cases coordinate <;>
      simp [quotient, transverseCeil']
  exact packed.trans_eq degreeEq

end Kakeya.Assouad

end
