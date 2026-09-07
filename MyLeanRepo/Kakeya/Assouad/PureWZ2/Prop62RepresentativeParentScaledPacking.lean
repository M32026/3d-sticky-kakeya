import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyCenterCopyPacking
import Mathlib.Tactic

/-!
# Scaled representative-parent conflict packing

This module supplies the coordinatewise degree bound consumed by
`Prop62ProxyQuotientAllScaleColorPreCore`.  It also records the independent
seven-coordinate ordinary line packing argument at an arbitrary natural
multiple `Q * r`.

The representative-line family may be relabelled at any target scale because
relabeling does not change `wz1PaperLineDistance`.  The final bound is obtained
in two layers: pack the `r / 4`-separated quotient centers in the supporting-line
metric, then use the absolute bound for the actual Definition 2.12 parent
copies over each center.  No line-class hypothesis is imposed on the actual
coarse family.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Absolute ordinary line-conflict degree for a radius `Q * r`. -/
def pureWZ2OrdinaryLineConflictDegreeAt (Q : ℕ) : ℕ :=
  ∏ coordinate : Fin 7,
    if coordinate.1 = 6 then 2561
    else 2 * (10000 * Q) + 1

theorem pureWZ2OrdinaryLineConflictDegreeAt_eq
    (Q : ℕ) :
    pureWZ2OrdinaryLineConflictDegreeAt Q =
      2561 * (2 * (10000 * Q) + 1) ^ 6 := by
  unfold pureWZ2OrdinaryLineConflictDegreeAt
  norm_num [Fin.prod_univ_succ]
  ring

private theorem pureWZ2_scaled_abs_coord_le_norm
    (point : Point3) (coordinate : Fin 3) :
    |point coordinate| ≤ ‖point‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le point coordinate

private theorem pureWZ2_scaled_line_conflict_parameter_bounds
    {delta separation : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (line : WZ1PaperIsLineClass family)
    (fixed index : Fin family.card)
    (conflict :
      wz1PaperLineDistance
          (family.tube index) (family.tube fixed) ≤ separation) :
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
          (wz1TubeAxisZeroPoint (family.tube fixed)) ≤ separation := by
    unfold wz1PaperLineDistance at conflict
    linarith [InnerProductGeometry.angle_nonneg
      (wz1PaperDirection (family.tube index))
      (wz1PaperDirection (family.tube fixed))]
  have angleBound :
      InnerProductGeometry.angle
          (wz1PaperDirection (family.tube index))
          (wz1PaperDirection (family.tube fixed)) ≤ separation := by
    unfold wz1PaperLineDistance at conflict
    linarith [dist_nonneg
      (x := wz1TubeAxisZeroPoint (family.tube index))
      (y := wz1TubeAxisZeroPoint (family.tube fixed))]
  have directionDistance :
      ‖wz1PaperDirection (family.tube index) -
          wz1PaperDirection (family.tube fixed)‖ ≤ separation :=
    (unit_norm_sub_le_angle
      (wz1PaperDirection_norm (family.tube index))
      (wz1PaperDirection_norm (family.tube fixed))).trans angleBound
  constructor
  · intro coordinate
    exact
      (pureWZ2_scaled_abs_coord_le_norm
        (wz1TubeAxisZeroPoint (family.tube index) -
          wz1TubeAxisZeroPoint (family.tube fixed))
        coordinate).trans <| by
          simpa [dist_eq_norm] using zeroDistance
  · intro coordinate
    exact
      (pureWZ2_scaled_abs_coord_le_norm
        (wz1PaperDirection (family.tube index) -
          wz1PaperDirection (family.tube fixed))
        coordinate).trans directionDistance

private theorem pureWZ2_scaled_same_ordinary_parameter_cell_containment
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
      _ ≤ delta / 5000 + 10 * (delta / 5000) := by
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

/--
Ordinary line-conflict packing at an arbitrary natural multiple `Q * r`.
The bound is independent of `r`.
-/
theorem pureWZ2_ordinary_line_conflict_degree_at
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (Q : ℕ)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (line : WZ1PaperIsLineClass family)
    (boundedBase : HasBoundedBase family 8)
    (distinct : WZ2PaperOrdinaryIsEssentiallyDistinct family) :
    ∀ fixed : Fin family.card,
      (Finset.univ.filter fun other =>
        wz1PaperLineDistance
            (family.tube other) (family.tube fixed) ≤
          (Q : ℝ) * delta).card ≤
        pureWZ2OrdinaryLineConflictDegreeAt Q := by
  intro fixed
  let conflicts : Finset (Fin family.card) :=
    Finset.univ.filter fun other =>
      wz1PaperLineDistance
          (family.tube other) (family.tube fixed) ≤
        (Q : ℝ) * delta
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
    if coordinate.1 = 6 then 10 else (Q : ℝ) * delta
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
    split_ifs <;> positivity
  have parameterBound :
      ∀ value ∈ values,
        ∀ coordinate, |value coordinate| ≤ radius coordinate := by
    intro value valueMem coordinate
    rcases Finset.mem_image.mp valueMem with
      ⟨index, indexMem, rfl⟩
    have conflict := (Finset.mem_filter.mp indexMem).2
    have bounds :=
      pureWZ2_scaled_line_conflict_parameter_bounds
        line fixed index conflict
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
      pureWZ2_scaled_same_ordinary_parameter_cell_containment
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
      pureWZ2_scaled_same_ordinary_parameter_cell_containment
        deltaPos (line first) (line second) (boundedBase first)
        axisClose directionClose axialClose
    exact (distinct first second indexNe).1 containment
  have valuesCard : values.card = conflicts.card :=
    Finset.card_image_of_injOn parameterInjective
  have quotient :
      (Q : ℝ) * delta / (delta / 10000) =
        ((10000 * Q : ℕ) : ℝ) := by
    field_simp [deltaPos.ne']
    push_cast
    ring
  have axialQuotient :
      (10 : ℝ) / (1 / 128) = ((1280 : ℕ) : ℝ) := by
    norm_num
  have axialCeil :
      Nat.ceil ((10 : ℝ) / (1 / 128)) = 1280 := by
    rw [axialQuotient]
    exact Nat.ceil_natCast _
  have transverseCeil :
      Nat.ceil ((10000 * Q : ℕ) : ℝ) = 10000 * Q :=
    Nat.ceil_natCast _
  have transverseCeil' :
      Nat.ceil ((10000 : ℝ) * (Q : ℝ)) = 10000 * Q := by
    rw [show (10000 : ℝ) * (Q : ℝ) =
      ((10000 * Q : ℕ) : ℝ) by norm_num]
    exact transverseCeil
  have productBound :
      (∏ coordinate : Fin 7,
        (2 * Nat.ceil
          (radius coordinate / mesh coordinate) + 1)) =
        pureWZ2OrdinaryLineConflictDegreeAt Q := by
    unfold pureWZ2OrdinaryLineConflictDegreeAt
    apply Finset.prod_congr rfl
    intro coordinate _
    fin_cases coordinate <;>
      simp [radius, mesh, quotient, transverseCeil,
        transverseCeil', axialCeil] <;> norm_num
  rw [← valuesCard]
  exact packed.trans_eq productBound

/-- The fixed representative-line factor used for all-scale parent colors. -/
def pureWZ2Prop62RepresentativeParentScaledFactor : ℕ :=
  1200000

/-- Conflict multiplier `12000000 * 1200000`. -/
def pureWZ2Prop62RepresentativeParentScaledConflictMultiplier : ℕ :=
  wz2PaperLiteralSourceSeparationFactor *
    pureWZ2Prop62RepresentativeParentScaledFactor

/--
Radius multiplier for quotient centers.  Each representative axis is within
`r / 4` of its center, so a representative conflict at radius `Q * r` puts the
two centers in a ball of radius `(Q + 1) * r`.
-/
def pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier : ℕ :=
  pureWZ2Prop62RepresentativeParentScaledConflictMultiplier + 1

/-- Coordinatewise enlarged middle scale `1200000 * r`. -/
def pureWZ2Prop62RepresentativeParentScaledMiddleScale
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (coordinate : Fin schedule.levelCount) : ℝ :=
  (pureWZ2Prop62RepresentativeParentScaledFactor : ℝ) *
    schedule.actualScale coordinate

/-- Coordinatewise conflict radius `12000000 * 1200000 * r`. -/
def pureWZ2Prop62RepresentativeParentScaledConflictScale
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (coordinate : Fin schedule.levelCount) : ℝ :=
  (wz2PaperLiteralSourceSeparationFactor : ℝ) *
    pureWZ2Prop62RepresentativeParentScaledMiddleScale
      schedule coordinate

/-- Absolute number of quotient centers in one scaled conflict neighborhood. -/
def pureWZ2Prop62RepresentativeParentScaledCenterConflictDegree : ℕ :=
  (2 *
      (32 *
        pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier) + 1) ^ 5

/--
Absolute degree for the scaled representative-parent conflict graph.  The
first factor counts nearby quotient centers and the second counts actual
Definition 2.12 parent copies over one center.
-/
def pureWZ2Prop62RepresentativeParentScaledConflictDegree : ℕ :=
  pureWZ2Prop62RepresentativeParentScaledCenterConflictDegree *
    pureWZ2Prop62ProxyCenterCopyPackingBound

theorem pureWZ2Prop62RepresentativeParentScaledFactor_eq :
    pureWZ2Prop62RepresentativeParentScaledFactor = 1200000 := by
  rfl

theorem pureWZ2Prop62RepresentativeParentScaledConflictMultiplier_eq :
    pureWZ2Prop62RepresentativeParentScaledConflictMultiplier =
      14400000000000 := by
  norm_num [
    pureWZ2Prop62RepresentativeParentScaledConflictMultiplier,
    pureWZ2Prop62RepresentativeParentScaledFactor,
    wz2PaperLiteralSourceSeparationFactor]

theorem pureWZ2Prop62RepresentativeParentScaledMiddleScale_eq
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (coordinate : Fin schedule.levelCount) :
    pureWZ2Prop62RepresentativeParentScaledMiddleScale
        schedule coordinate =
      1200000 * schedule.actualScale coordinate := by
  rfl

theorem pureWZ2Prop62RepresentativeParentScaledConflictScale_eq
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (coordinate : Fin schedule.levelCount) :
    pureWZ2Prop62RepresentativeParentScaledConflictScale
        schedule coordinate =
      14400000000000 * schedule.actualScale coordinate := by
  norm_num [
    pureWZ2Prop62RepresentativeParentScaledConflictScale,
    pureWZ2Prop62RepresentativeParentScaledMiddleScale,
    pureWZ2Prop62RepresentativeParentScaledFactor,
    wz2PaperLiteralSourceSeparationFactor]
  ring

theorem pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier_eq :
    pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier =
      14400000000001 := by
  norm_num [
    pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier,
    pureWZ2Prop62RepresentativeParentScaledConflictMultiplier_eq]

theorem pureWZ2Prop62RepresentativeParentScaledCenterConflictDegree_eq :
    pureWZ2Prop62RepresentativeParentScaledCenterConflictDegree =
      (921600000000065 : ℕ) ^ 5 := by
  rw [pureWZ2Prop62RepresentativeParentScaledCenterConflictDegree,
    pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier_eq]

theorem pureWZ2Prop62RepresentativeParentScaledConflictDegree_eq :
    pureWZ2Prop62RepresentativeParentScaledConflictDegree =
      (921600000000065 : ℕ) ^ 5 *
        pureWZ2Prop62ProxyCenterCopyPackingBound := by
  rw [pureWZ2Prop62RepresentativeParentScaledConflictDegree,
    pureWZ2Prop62RepresentativeParentScaledCenterConflictDegree_eq]

/--
Per-coordinate degree bound for the `F = 1200000` conflict graph used by
`Prop62ProxyQuotientAllScaleColorPreCore`.  Packing is performed in two
layers: first on the `r / 4`-separated quotient center family, then inside
each center fiber by the absolute actual-parent copy bound.
-/
theorem pureWZ2_prop62_representative_parent_scaled_degree
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (coordinate : Fin schedule.levelCount)
    (fixed : Fin (schedule.scaleData coordinate).coarse.card) :
    (Finset.univ.filter fun other =>
      other ≠ fixed ∧
        wz1PaperLineDistance
            ((schedule.representativeLineFamily
              fineNonempty coordinate
                (schedule.actualScale coordinate)).tube other)
            ((schedule.representativeLineFamily
              fineNonempty coordinate
                (schedule.actualScale coordinate)).tube fixed) ≤
          pureWZ2Prop62RepresentativeParentScaledConflictScale
            schedule coordinate).card ≤
      pureWZ2Prop62RepresentativeParentScaledConflictDegree := by
  let representativeConflicts :
      Finset (Fin (schedule.scaleData coordinate).coarse.card) :=
    Finset.univ.filter fun other =>
      other ≠ fixed ∧
        wz1PaperLineDistance
            ((schedule.representativeLineFamily
              fineNonempty coordinate
                (schedule.actualScale coordinate)).tube other)
            ((schedule.representativeLineFamily
              fineNonempty coordinate
                (schedule.actualScale coordinate)).tube fixed) ≤
          pureWZ2Prop62RepresentativeParentScaledConflictScale
            schedule coordinate
  let centerNeighborhood :
      Finset (Fin (quotient.level coordinate).centerFamily.card) :=
    Finset.univ.filter fun other =>
      wz1PaperLineDistance
          ((quotient.level coordinate).centerFamily.tube other)
          ((quotient.level coordinate).centerFamily.tube
            (quotient.actualCenter coordinate fixed)) ≤
        (pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier : ℝ) *
          schedule.actualScale coordinate
  have centerSubset :
      representativeConflicts ⊆
        centerNeighborhood.biUnion
          (quotient.centerActualParents coordinate) := by
    intro other otherMem
    have conflictData := (Finset.mem_filter.mp otherMem).2
    rw [Finset.mem_biUnion]
    refine ⟨quotient.actualCenter coordinate other, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have otherCenter :=
        (quotient.level coordinate).actualProxy_center_lineDistance_le
          fineLine other
      have fixedCenter :=
        (quotient.level coordinate).actualProxy_center_lineDistance_le
          fineLine fixed
      have centerOtherToOther :
        wz1PaperLineDistance
            ((quotient.level coordinate).centerFamily.tube
              (quotient.actualCenter coordinate other))
            (schedule.coordinateProxyTube
              fineNonempty coordinate other) ≤
          schedule.actualScale coordinate / 4 := by
        rw [wz1PaperLineDistance_symm]
        exact otherCenter
      calc
        wz1PaperLineDistance
            ((quotient.level coordinate).centerFamily.tube
              (quotient.actualCenter coordinate other))
            ((quotient.level coordinate).centerFamily.tube
              (quotient.actualCenter coordinate fixed)) ≤
          wz1PaperLineDistance
              ((quotient.level coordinate).centerFamily.tube
                (quotient.actualCenter coordinate other))
              (schedule.coordinateProxyTube
                fineNonempty coordinate other) +
            wz1PaperLineDistance
              (schedule.coordinateProxyTube
                fineNonempty coordinate other)
              ((quotient.level coordinate).centerFamily.tube
                (quotient.actualCenter coordinate fixed)) :=
          wz1PaperLineDistance_triangle _ _ _
        _ ≤ schedule.actualScale coordinate / 4 +
            (wz1PaperLineDistance
                (schedule.coordinateProxyTube
                  fineNonempty coordinate other)
                (schedule.coordinateProxyTube
                  fineNonempty coordinate fixed) +
              wz1PaperLineDistance
                (schedule.coordinateProxyTube
                  fineNonempty coordinate fixed)
                ((quotient.level coordinate).centerFamily.tube
                  (quotient.actualCenter coordinate fixed))) := by
          gcongr
          exact wz1PaperLineDistance_triangle _ _ _
        _ ≤ schedule.actualScale coordinate / 4 +
            (14400000000000 * schedule.actualScale coordinate +
              schedule.actualScale coordinate / 4) := by
          gcongr
          · simpa only [
                PureWZ2Prop62LaminarPureSchedule.coordinateProxyTube,
                pureWZ2Prop62RepresentativeParentScaledConflictScale_eq
              ] using conflictData.2
          · exact fixedCenter
        _ ≤
            (pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier :
                ℝ) *
              schedule.actualScale coordinate := by
          rw [
            pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier_eq]
          nlinarith [(schedule.scaleData coordinate).rho_pos]
    · exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ other, rfl⟩
  have centerPacking :
      centerNeighborhood.card ≤
        pureWZ2Prop62RepresentativeParentScaledCenterConflictDegree := by
    have packed :=
      tube_packing_bound_general
        ((quotient.level coordinate).centerFamily_distinct fineLine)
        ((quotient.level coordinate).centerFamily_lineClass fineLine)
        (by
          have actualPos := (schedule.scaleData coordinate).rho_pos
          positivity :
          0 < schedule.actualScale coordinate / 4)
        ((pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier :
            ℝ) * schedule.actualScale coordinate)
        (mul_pos
          (by
            rw [
              pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier_eq]
            norm_num)
          (schedule.scaleData coordinate).rho_pos)
        (quotient.actualCenter coordinate fixed)
    have quotientIdentity :
        8 *
              ((pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier :
                  ℝ) * schedule.actualScale coordinate) /
            (schedule.actualScale coordinate / 4) =
          (32 *
            pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier :
              ℕ) := by
      field_simp [(schedule.scaleData coordinate).rho_pos.ne']
      norm_num
      ring
    have ceiling :
        Nat.ceil
            (8 *
                ((pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier :
                    ℝ) * schedule.actualScale coordinate) /
              (schedule.actualScale coordinate / 4)) =
          32 *
            pureWZ2Prop62RepresentativeParentScaledCenterRadiusMultiplier := by
      rw [quotientIdentity]
      exact Nat.ceil_natCast _
    change centerNeighborhood.card ≤ _ at packed
    rw [ceiling] at packed
    exact packed
  have unionPacking :
      (centerNeighborhood.biUnion
          (quotient.centerActualParents coordinate)).card ≤
        centerNeighborhood.card *
          pureWZ2Prop62ProxyCenterCopyPackingBound :=
    Finset.card_biUnion_le_card_mul
      centerNeighborhood
      (quotient.centerActualParents coordinate)
      pureWZ2Prop62ProxyCenterCopyPackingBound
      (fun center _ =>
        pureWZ2_prop62_proxy_center_actualParents_card_le
          schedule fineNonempty fineLine fineBase quotient coordinate center)
  change representativeConflicts.card ≤
    pureWZ2Prop62RepresentativeParentScaledConflictDegree
  calc
    representativeConflicts.card ≤
        (centerNeighborhood.biUnion
          (quotient.centerActualParents coordinate)).card :=
      Finset.card_le_card centerSubset
    _ ≤ centerNeighborhood.card *
        pureWZ2Prop62ProxyCenterCopyPackingBound :=
      unionPacking
    _ ≤
        pureWZ2Prop62RepresentativeParentScaledCenterConflictDegree *
          pureWZ2Prop62ProxyCenterCopyPackingBound :=
      Nat.mul_le_mul_right
        pureWZ2Prop62ProxyCenterCopyPackingBound centerPacking
    _ = pureWZ2Prop62RepresentativeParentScaledConflictDegree := rfl

end Kakeya.Assouad

end
