import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterEnvelopeConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnisotropicPacking
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.NonessentialTubeAxisAlignment

/-!
# Ordinary centered-containment distinctness implies overlap distinctness

For sufficiently small positive radius, failure of the volume-overlap notion
forces two unit tubes to be close up to reversal.  Reversing the second tube
does not change its carrier or centered double.  The resulting midpoint and
direction bounds put the first carrier inside the centered double of the
second, contradicting literal ordinary distinctness.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
An ordinary unit tube is contained in the centered double of another when
their midpoint displacement is a bounded axial shift plus a small transverse
error, and their directions are close.

The fixed axial allowance is the reason the relevant packing is
five-dimensional rather than the invalid isotropic six-dimensional fallback.
-/
theorem wz2PaperOrdinary_carrier_subset_centeredDilatedTwo_of_axial_close
    {rho axialShift : ℝ}
    (hrho : 0 < rho)
    {first second : Kakeya.DeltaTube rho}
    (haxial : |axialShift| ≤ 1 / 4)
    (hmidpoint :
      ‖(wz2PaperTubeMidpoint first -
            wz2PaperTubeMidpoint second) -
          axialShift • second.direction‖ ≤
        rho / 16)
    (hdirection :
      ‖first.direction - second.direction‖ ≤
        rho / 16) :
    first.carrier ⊆
      wz2PaperCenteredDilatedCarrier 2 second := by
  intro point pointMem
  have firstSegmentCompact :
      IsCompact
        (Kakeya.unitSegment first.base first.direction) := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  change
    point ∈
      Metric.cthickening rho
        (Kakeya.unitSegment first.base first.direction) at pointMem
  rw [firstSegmentCompact.cthickening_eq_biUnion_closedBall
    hrho.le] at pointMem
  rcases Set.mem_iUnion₂.mp pointMem with
    ⟨axisPoint, axisPointMem, pointAxis⟩
  rcases axisPointMem with ⟨parameter, parameterMem, rfl⟩
  let firstMidpoint := wz2PaperTubeMidpoint first
  let secondMidpoint := wz2PaperTubeMidpoint second
  let secondParameter : ℝ :=
    parameter / 2 + 1 / 4 + axialShift / 2
  let sourcePoint : Point3 :=
    secondMidpoint +
      (1 / 2 : ℝ) • (point - secondMidpoint)
  have secondParameterMem :
      secondParameter ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [secondParameter]
    have axialBounds := abs_le.mp haxial
    constructor <;>
      linarith [parameterMem.1, parameterMem.2,
        axialBounds.1, axialBounds.2]
  have parameterCentered :
      |parameter - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith [parameterMem.1, parameterMem.2]
  have axisIdentity :
      sourcePoint -
          (second.base +
            secondParameter • second.direction) =
        (1 / 2 : ℝ) •
            (point -
              (first.base +
                parameter • first.direction)) +
          (1 / 2 : ℝ) •
            ((firstMidpoint - secondMidpoint) -
              axialShift • second.direction) +
          ((1 / 2 : ℝ) * (parameter - 1 / 2)) •
            (first.direction - second.direction) := by
    dsimp only [sourcePoint, secondParameter,
      firstMidpoint, secondMidpoint, wz2PaperTubeMidpoint]
    module
  have pointAxisNorm :
      ‖point -
          (first.base +
            parameter • first.direction)‖ ≤ rho := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using pointAxis
  have coefficient :
      |(1 / 2 : ℝ) * (parameter - 1 / 2)| ≤
        1 / 4 := by
    rw [abs_mul]
    norm_num
    linarith
  have sourceDistance :
      dist sourcePoint
          (second.base +
            secondParameter • second.direction) ≤ rho := by
    rw [dist_eq_norm, axisIdentity]
    calc
      ‖(1 / 2 : ℝ) •
            (point -
              (first.base +
                parameter • first.direction)) +
          (1 / 2 : ℝ) •
            ((firstMidpoint - secondMidpoint) -
              axialShift • second.direction) +
          ((1 / 2 : ℝ) * (parameter - 1 / 2)) •
            (first.direction - second.direction)‖
          ≤
        ‖(1 / 2 : ℝ) •
            (point -
              (first.base +
                parameter • first.direction))‖ +
          ‖(1 / 2 : ℝ) •
            ((firstMidpoint - secondMidpoint) -
              axialShift • second.direction)‖ +
          ‖((1 / 2 : ℝ) * (parameter - 1 / 2)) •
            (first.direction - second.direction)‖ := by
              exact (norm_add_le _ _).trans <| by
                gcongr
                exact norm_add_le _ _
      _ ≤
          (1 / 2 : ℝ) * rho +
            (1 / 2 : ℝ) * (rho / 16) +
            (1 / 4 : ℝ) * (rho / 16) := by
              repeat' rw [norm_smul, Real.norm_eq_abs]
              have halfAbs :
                  |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
              rw [halfAbs]
              apply add_le_add
              · exact add_le_add
                  (mul_le_mul_of_nonneg_left
                    pointAxisNorm (by norm_num))
                  (mul_le_mul_of_nonneg_left
                    hmidpoint (by norm_num))
              · exact
                  (mul_le_mul_of_nonneg_right
                    coefficient (norm_nonneg _)).trans <|
                    mul_le_mul_of_nonneg_left
                      hdirection (by norm_num)
      _ ≤ rho := by linarith
  have sourceCarrier : sourcePoint ∈ second.carrier :=
    Metric.mem_cthickening_of_dist_le
      sourcePoint
      (second.base + secondParameter • second.direction)
      rho
      (Kakeya.unitSegment second.base second.direction)
      ⟨secondParameter, secondParameterMem, rfl⟩
      sourceDistance
  refine ⟨sourcePoint, sourceCarrier, ?_⟩
  ext coordinate
  simp [sourcePoint, secondMidpoint,
    AffineMap.homothety_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply]

private theorem pureWZ2_point3_norm_le_sum_abs (vector : Point3) :
    ‖vector‖ ≤ |vector 0| + |vector 1| + |vector 2| := by
  have normSquared :
      ‖vector‖ ^ 2 =
        vector 0 ^ 2 + vector 1 ^ 2 + vector 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have squareBound :
      ‖vector‖ ^ 2 ≤
        (|vector 0| + |vector 1| + |vector 2|) ^ 2 := by
    rw [normSquared]
    nlinarith [sq_abs (vector 0), sq_abs (vector 1),
      sq_abs (vector 2), abs_nonneg (vector 0),
      abs_nonneg (vector 1), abs_nonneg (vector 2)]
  nlinarith [norm_nonneg vector, abs_nonneg (vector 0),
    abs_nonneg (vector 1), abs_nonneg (vector 2)]

private theorem pureWZ2_frame_vsub
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3) (first second : Point3) :
    frame.symm.linearIsometryEquiv (first - second) =
      frame.symm first - frame.symm second := by
  simpa [vsub_eq_sub] using frame.symm.map_vsub first second

/--
For unit directions in one vertical chart, two transverse direction
coordinates determine the whole direction up to `O(rho)`.
-/
private theorem pureWZ2_direction_norm_of_five_close
    {rho : ℝ}
    (hrho : 0 < rho)
    (hrhoSmall : rho ≤ 1 / 100)
    (first second : Point3)
    (firstUnit : ‖first‖ = 1)
    (secondUnit : ‖second‖ = 1)
    (firstTransverse :
      |first 0| ≤ 10 * rho ∧ |first 1| ≤ 10 * rho)
    (secondTransverse :
      |second 0| ≤ 10 * rho ∧ |second 1| ≤ 10 * rho)
    (sameSign :
      (first 2 ≥ 1 / 2 ∧ second 2 ≥ 1 / 2) ∨
        (first 2 ≤ -1 / 2 ∧ second 2 ≤ -1 / 2))
    (zeroClose : |(first - second) 0| ≤ rho / 200)
    (oneClose : |(first - second) 1| ≤ rho / 200) :
    ‖first - second‖ ≤ rho / 16 := by
  have firstCoordinates :
      first 0 ^ 2 + first 1 ^ 2 + first 2 ^ 2 = 1 := by
    have identity := EuclideanSpace.real_norm_sq_eq first
    rw [firstUnit] at identity
    norm_num at identity
    simpa [Fin.sum_univ_succ, add_assoc] using identity.symm
  have secondCoordinates :
      second 0 ^ 2 + second 1 ^ 2 + second 2 ^ 2 = 1 := by
    have identity := EuclideanSpace.real_norm_sq_eq second
    rw [secondUnit] at identity
    norm_num at identity
    simpa [Fin.sum_univ_succ, add_assoc] using identity.symm
  have sumZero : |first 0 + second 0| ≤ 20 * rho := by
    calc
      |first 0 + second 0| ≤
          |first 0| + |second 0| := abs_add_le _ _
      _ ≤ 10 * rho + 10 * rho :=
        add_le_add firstTransverse.1 secondTransverse.1
      _ = 20 * rho := by ring
  have sumOne : |first 1 + second 1| ≤ 20 * rho := by
    calc
      |first 1 + second 1| ≤
          |first 1| + |second 1| := abs_add_le _ _
      _ ≤ 10 * rho + 10 * rho :=
        add_le_add firstTransverse.2 secondTransverse.2
      _ = 20 * rho := by ring
  have squareZero :
      |first 0 ^ 2 - second 0 ^ 2| ≤ rho ^ 2 / 10 := by
    rw [show first 0 ^ 2 - second 0 ^ 2 =
      (first 0 - second 0) * (first 0 + second 0) by ring,
      abs_mul]
    calc
      |first 0 - second 0| * |first 0 + second 0| ≤
          (rho / 200) * (20 * rho) := by
        apply mul_le_mul
        · simpa [Pi.sub_apply] using zeroClose
        · exact sumZero
        · positivity
        · positivity
      _ = rho ^ 2 / 10 := by ring
  have squareOne :
      |first 1 ^ 2 - second 1 ^ 2| ≤ rho ^ 2 / 10 := by
    rw [show first 1 ^ 2 - second 1 ^ 2 =
      (first 1 - second 1) * (first 1 + second 1) by ring,
      abs_mul]
    calc
      |first 1 - second 1| * |first 1 + second 1| ≤
          (rho / 200) * (20 * rho) := by
        apply mul_le_mul
        · simpa [Pi.sub_apply] using oneClose
        · exact sumOne
        · positivity
        · positivity
      _ = rho ^ 2 / 10 := by ring
  have squareTwoIdentity :
      first 2 ^ 2 - second 2 ^ 2 =
        -((first 0 ^ 2 - second 0 ^ 2) +
          (first 1 ^ 2 - second 1 ^ 2)) := by
    linarith
  have squareTwo :
      |first 2 ^ 2 - second 2 ^ 2| ≤ rho ^ 2 / 5 := by
    rw [squareTwoIdentity, abs_neg]
    calc
      |(first 0 ^ 2 - second 0 ^ 2) +
          (first 1 ^ 2 - second 1 ^ 2)| ≤
        |first 0 ^ 2 - second 0 ^ 2| +
          |first 1 ^ 2 - second 1 ^ 2| := abs_add_le _ _
      _ ≤ rho ^ 2 / 10 + rho ^ 2 / 10 :=
        add_le_add squareZero squareOne
      _ = rho ^ 2 / 5 := by ring
  have signSum : 1 ≤ |first 2 + second 2| := by
    rcases sameSign with positive | negative
    · rw [abs_of_nonneg (by linarith [positive.1, positive.2])]
      linarith [positive.1, positive.2]
    · rw [abs_of_nonpos (by linarith [negative.1, negative.2])]
      linarith [negative.1, negative.2]
  have twoDifference :
      |first 2 - second 2| ≤ rho ^ 2 / 5 := by
    calc
      |first 2 - second 2| ≤
          |first 2 - second 2| *
            |first 2 + second 2| :=
        le_mul_of_one_le_right (abs_nonneg _) signSum
      _ = |first 2 ^ 2 - second 2 ^ 2| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ rho ^ 2 / 5 := squareTwo
  have twoSmall :
      |(first - second) 2| ≤ rho / 500 := by
    have raw : |first 2 - second 2| ≤ rho / 500 := by
      calc
        |first 2 - second 2| ≤ rho ^ 2 / 5 := twoDifference
        _ ≤ rho / 500 := by nlinarith
    simpa [Pi.sub_apply] using raw
  calc
    ‖first - second‖ ≤
        |(first - second) 0| +
          |(first - second) 1| +
            |(first - second) 2| :=
      pureWZ2_point3_norm_le_sum_abs _
    _ ≤ rho / 200 + rho / 200 + rho / 500 := by
      gcongr
    _ ≤ rho / 16 := by linarith

/--
Two ordinary tubes in the same five-dimensional anisotropic parameter cell
conflict in the centered-containment graph.  The longitudinal midpoint
difference is absorbed by a bounded axial shift.
-/
theorem wz2PaperOrdinary_carrier_subset_centeredDilatedTwo_of_five_close
    {rho : ℝ}
    (hrho : 0 < rho)
    (hrhoSmall : rho ≤ 1 / 100)
    {first second : Kakeya.DeltaTube rho}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (firstMidpoint secondMidpoint firstDirection secondDirection : Point3)
    (firstMidpointEq :
      firstMidpoint =
        frame.symm (wz2PaperTubeMidpoint first))
    (secondMidpointEq :
      secondMidpoint =
        frame.symm (wz2PaperTubeMidpoint second))
    (firstDirectionEq :
      firstDirection =
        frame.symm.linearIsometryEquiv first.direction)
    (secondDirectionEq :
      secondDirection =
        frame.symm.linearIsometryEquiv second.direction)
    (firstTransverse :
      |firstDirection 0| ≤ 10 * rho ∧
        |firstDirection 1| ≤ 10 * rho)
    (secondTransverse :
      |secondDirection 0| ≤ 10 * rho ∧
        |secondDirection 1| ≤ 10 * rho)
    (sameSign :
      (firstDirection 2 ≥ 1 / 2 ∧
          secondDirection 2 ≥ 1 / 2) ∨
        (firstDirection 2 ≤ -1 / 2 ∧
          secondDirection 2 ≤ -1 / 2))
    (midpointZero :
      |(firstMidpoint - secondMidpoint) 0| ≤ rho / 200)
    (midpointOne :
      |(firstMidpoint - secondMidpoint) 1| ≤ rho / 200)
    (midpointTwo :
      |(firstMidpoint - secondMidpoint) 2| ≤ 1 / 6400)
    (directionZero :
      |(firstDirection - secondDirection) 0| ≤ rho / 200)
    (directionOne :
      |(firstDirection - secondDirection) 1| ≤ rho / 200) :
    first.carrier ⊆
      wz2PaperCenteredDilatedCarrier 2 second := by
  have secondLongitudinal :
      1 / 2 ≤ |secondDirection 2| := by
    rcases sameSign with positive | negative
    · rw [abs_of_nonneg (by linarith [positive.2])]
      exact positive.2
    · rw [abs_of_nonpos (by linarith [negative.2])]
      linarith [negative.2]
  let axialShift : ℝ :=
    (firstMidpoint 2 - secondMidpoint 2) / secondDirection 2
  have secondLongitudinalNe : secondDirection 2 ≠ 0 := by
    intro zero
    rw [zero, abs_zero] at secondLongitudinal
    norm_num at secondLongitudinal
  have axialBound : |axialShift| ≤ 1 / 3200 := by
    dsimp only [axialShift]
    rw [abs_div]
    calc
      |firstMidpoint 2 - secondMidpoint 2| /
            |secondDirection 2| ≤
          (1 / 6400 : ℝ) / |secondDirection 2| := by
        apply div_le_div_of_nonneg_right
        · simpa [Pi.sub_apply] using midpointTwo
        · exact abs_nonneg _
      _ ≤ (1 / 6400 : ℝ) / (1 / 2) := by
        apply div_le_div_of_nonneg_left <;> norm_num
        exact secondLongitudinal
      _ = 1 / 3200 := by norm_num
  have axialQuarter : |axialShift| ≤ 1 / 4 :=
    axialBound.trans (by norm_num)
  let residual :=
    (firstMidpoint - secondMidpoint) -
      axialShift • secondDirection
  have residualZero :
      |residual 0| ≤
        rho / 200 + (1 / 3200) * (10 * rho) := by
    dsimp only [residual]
    change
      |(firstMidpoint - secondMidpoint) 0 -
          axialShift * secondDirection 0| ≤
        rho / 200 + (1 / 3200) * (10 * rho)
    calc
      |(firstMidpoint - secondMidpoint) 0 -
          axialShift * secondDirection 0| ≤
        |(firstMidpoint - secondMidpoint) 0| +
          |axialShift * secondDirection 0| := abs_sub _ _
      _ =
          |(firstMidpoint - secondMidpoint) 0| +
            |axialShift| * |secondDirection 0| := by
        rw [abs_mul]
      _ ≤ rho / 200 + (1 / 3200) * (10 * rho) :=
        add_le_add midpointZero
          (mul_le_mul axialBound secondTransverse.1
            (abs_nonneg _) (by norm_num))
  have residualOne :
      |residual 1| ≤
        rho / 200 + (1 / 3200) * (10 * rho) := by
    dsimp only [residual]
    change
      |(firstMidpoint - secondMidpoint) 1 -
          axialShift * secondDirection 1| ≤
        rho / 200 + (1 / 3200) * (10 * rho)
    calc
      |(firstMidpoint - secondMidpoint) 1 -
          axialShift * secondDirection 1| ≤
        |(firstMidpoint - secondMidpoint) 1| +
          |axialShift * secondDirection 1| := abs_sub _ _
      _ =
          |(firstMidpoint - secondMidpoint) 1| +
            |axialShift| * |secondDirection 1| := by
        rw [abs_mul]
      _ ≤ rho / 200 + (1 / 3200) * (10 * rho) :=
        add_le_add midpointOne
          (mul_le_mul axialBound secondTransverse.2
            (abs_nonneg _) (by norm_num))
  have residualTwo : residual 2 = 0 := by
    dsimp only [residual, axialShift]
    change
      (firstMidpoint 2 - secondMidpoint 2) -
          (firstMidpoint 2 - secondMidpoint 2) /
              secondDirection 2 * secondDirection 2 = 0
    field_simp [secondLongitudinalNe]
    ring
  have residualNorm : ‖residual‖ ≤ rho / 16 := by
    calc
      ‖residual‖ ≤
          |residual 0| + |residual 1| + |residual 2| :=
        pureWZ2_point3_norm_le_sum_abs _
      _ = |residual 0| + |residual 1| := by
        rw [residualTwo, abs_zero]
        ring
      _ ≤
          2 * (rho / 200 + (1 / 3200) * (10 * rho)) := by
        linarith
      _ ≤ rho / 16 := by linarith
  have midpointFrame :
      frame.symm.linearIsometryEquiv
          ((wz2PaperTubeMidpoint first -
                wz2PaperTubeMidpoint second) -
            axialShift • second.direction) =
        residual := by
    rw [map_sub, map_smul, ← secondDirectionEq]
    rw [pureWZ2_frame_vsub]
    rw [← firstMidpointEq, ← secondMidpointEq]
  have midpointNorm :
      ‖(wz2PaperTubeMidpoint first -
              wz2PaperTubeMidpoint second) -
          axialShift • second.direction‖ ≤
        rho / 16 := by
    rw [← frame.symm.linearIsometryEquiv.norm_map]
    rw [midpointFrame]
    exact residualNorm
  have firstUnit : ‖firstDirection‖ = 1 := by
    rw [firstDirectionEq,
      frame.symm.linearIsometryEquiv.norm_map,
      first.direction_unit]
  have secondUnit : ‖secondDirection‖ = 1 := by
    rw [secondDirectionEq,
      frame.symm.linearIsometryEquiv.norm_map,
      second.direction_unit]
  have directionFrame :
      frame.symm.linearIsometryEquiv
          (first.direction - second.direction) =
        firstDirection - secondDirection := by
    rw [map_sub, ← firstDirectionEq, ← secondDirectionEq]
  have directionNorm :
      ‖first.direction - second.direction‖ ≤ rho / 16 := by
    rw [← frame.symm.linearIsometryEquiv.norm_map]
    rw [directionFrame]
    exact
      pureWZ2_direction_norm_of_five_close
        hrho hrhoSmall firstDirection secondDirection
        firstUnit secondUnit firstTransverse secondTransverse
        sameSign directionZero directionOne
  exact
    wz2PaperOrdinary_carrier_subset_centeredDilatedTwo_of_axial_close
      hrho axialQuarter midpointNorm directionNorm

/-
private theorem midpoint_sub_of_axis_alignment
    {delta sign s : ℝ}
    {first second : Kakeya.DeltaTube delta}
    {anchor : Point3}
    (signData :
      sign = 1 ∧ anchor = second.base ∨
        sign = -1 ∧ anchor = second.base + second.direction)
    (baseNear :
      ‖first.base -
          (anchor + s • (sign • second.direction))‖ ≤
        1002 * delta)
    (directionNear :
      ‖first.direction - sign • second.direction‖ ≤
        1000 * delta)
    (sMem : s ∈ Set.Icc (-1 : ℝ) 1) :
    ‖wz2PaperTubeMidpoint first -
        wz2PaperTubeMidpoint
          (if sign = 1 then second else reverseTube second)‖ ≤
      2003 * delta := by
  rcases signData with positive | negative
  · rcases positive with ⟨signEq, anchorEq⟩
    subst sign
    subst anchor
    rw [if_pos rfl]
    have vectorIdentity :
        wz2PaperTubeMidpoint first -
            wz2PaperTubeMidpoint second =
          (first.base -
              (second.base + s • second.direction)) +
            (s - 1 / 2) • second.direction +
            (1 / 2 : ℝ) •
              (first.direction - second.direction) := by
      simp only [wz2PaperTubeMidpoint, one_smul]
      module
    have sBound : |s - 1 / 2| ≤ 3 / 2 := by
      rw [abs_le]
      constructor <;> linarith [sMem.1, sMem.2]
    rw [vectorIdentity]
    calc
      ‖(first.base -
            (second.base + s • second.direction)) +
          (s - 1 / 2) • second.direction +
          (1 / 2 : ℝ) •
            (first.direction - second.direction)‖
          ≤
        ‖first.base -
            (second.base + s • second.direction)‖ +
          ‖(s - 1 / 2) • second.direction‖ +
          ‖(1 / 2 : ℝ) •
            (first.direction - second.direction)‖ := by
              exact (norm_add_le _ _).trans <| by
                gcongr
                exact norm_add_le _ _
      _ ≤
          1002 * delta + 3 / 2 + 1000 * delta / 2 := by
        repeat' rw [norm_smul, Real.norm_eq_abs]
        rw [second.direction_unit, mul_one]
        gcongr
        · exact baseNear
        · exact sBound
        · norm_num
          simpa using directionNear
      _ ≤ 2003 * delta := by
        nlinarith
  · rcases negative with ⟨signEq, anchorEq⟩
    subst sign
    subst anchor
    rw [if_neg (by norm_num)]
    have reverseMidpoint :
        wz2PaperTubeMidpoint (reverseTube second) =
          wz2PaperTubeMidpoint second :=
      wz2PaperTubeMidpoint_reverse second
    rw [reverseMidpoint]
    have vectorIdentity :
        wz2PaperTubeMidpoint first -
            wz2PaperTubeMidpoint second =
          (first.base -
              ((second.base + second.direction) +
                s • (-second.direction))) +
            (-s - 1 / 2) • second.direction +
            (1 / 2 : ℝ) •
              (first.direction + second.direction) := by
      simp only [wz2PaperTubeMidpoint, neg_smul]
      module
    have sBound : |-s - 1 / 2| ≤ 3 / 2 := by
      rw [abs_le]
      constructor <;> linarith [sMem.1, sMem.2]
    rw [vectorIdentity]
    calc
      ‖(first.base -
            ((second.base + second.direction) +
              s • (-second.direction))) +
          (-s - 1 / 2) • second.direction +
          (1 / 2 : ℝ) •
            (first.direction + second.direction)‖
          ≤
        ‖first.base -
            ((second.base + second.direction) +
              s • (-second.direction))‖ +
          ‖(-s - 1 / 2) • second.direction‖ +
          ‖(1 / 2 : ℝ) •
            (first.direction + second.direction)‖ := by
              exact (norm_add_le _ _).trans <| by
                gcongr
                exact norm_add_le _ _
      _ ≤
          1002 * delta + 3 / 2 + 1000 * delta / 2 := by
        repeat' rw [norm_smul, Real.norm_eq_abs]
        rw [second.direction_unit, mul_one]
        gcongr
        · simpa using baseNear
        · exact sBound
        · norm_num
          simpa using directionNear
      _ ≤ 2003 * delta := by
        nlinarith

theorem WZ2PaperOrdinaryIsEssentiallyDistinct.overlapDistinct
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ 1 / 100000)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : WZ2PaperOrdinaryIsEssentiallyDistinct family) :
    family.IsEssentiallyDistinct := by
  intro first second distinct
  by_contra notOverlapDistinct
  rcases
      nonessential_tube_axis_alignment
        delta hdelta (hdeltaSmall.trans (by norm_num))
        (family.tube first) (family.tube second)
        notOverlapDistinct
    with
    ⟨sign, anchor, signData, directionNear,
      s, sMem, baseNear⟩
  let orientedSecond :=
    if sign = 1 then family.tube second
    else reverseTube (family.tube second)
  have directionEq :
      orientedSecond.direction =
        sign • (family.tube second).direction := by
    dsimp only [orientedSecond]
    rcases signData with positive | negative
    · rw [if_pos positive.1]
      simp [positive.1]
    · rw [if_neg (by linarith [negative.1])]
      simp [reverseTube, negative.1]
  have directionClose :
      ‖(family.tube first).direction -
          orientedSecond.direction‖ ≤
        delta / 16 := by
    rw [directionEq]
    exact directionNear.trans <| by
      nlinarith
  have midpointClose :
      ‖wz2PaperTubeMidpoint (family.tube first) -
          wz2PaperTubeMidpoint orientedSecond‖ ≤
        delta / 16 := by
    have raw :=
      midpoint_sub_of_axis_alignment
        signData baseNear directionNear sMem
    exact raw.trans <| by
      nlinarith
  have containment :
      (family.tube first).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 orientedSecond :=
    wz2PaperOrdinary_carrier_subset_centeredDilatedTwo_of_close
      hdelta midpointClose directionClose
  have orientedCarrier :
      orientedSecond.carrier =
        (family.tube second).carrier := by
    dsimp only [orientedSecond]
    split_ifs
    · rfl
    · exact reverseTube_carrier _
  have orientedCentered :
      wz2PaperCenteredDilatedCarrier 2 orientedSecond =
        wz2PaperCenteredDilatedCarrier 2
          (family.tube second) := by
    unfold wz2PaperCenteredDilatedCarrier
    rw [orientedCarrier]
    have midpointEq :
        wz2PaperTubeMidpoint orientedSecond =
          wz2PaperTubeMidpoint (family.tube second) := by
      dsimp only [orientedSecond]
      split_ifs
      · rfl
      · exact wz2PaperTubeMidpoint_reverse _
    rw [midpointEq]
  exact (ordinary first second distinct).1 <| by
    rwa [orientedCentered] at containment

end Kakeya.Assouad

end
-/
