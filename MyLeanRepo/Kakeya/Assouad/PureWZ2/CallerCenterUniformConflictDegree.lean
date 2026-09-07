import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterEnvelopeConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryDistinctToOverlapDistinct
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnisotropicPacking
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.CompleteFiberOverlap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ParametricMidpointBounds
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ProjectiveDirectionTriangle

/-!
# Uniform caller-center envelope conflict degree

Two conflicting scheduled parents share a caller whose full carrier lies in
both centered-doubled ordinary envelopes.  At small scheduled scale this
forces the parent directions into one projective cone and their midpoints
into a five-dimensional anisotropic box.  Equal parameter cells force
ordinary centered containment after orienting toward the fixed parent, which
contradicts the literal ordinary distinctness supplied by the scheduled
cover.  No line-class structure on the scheduled coarse family is used.

At larger scales the existing six-parameter estimate is already uniform.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private def pureWZ2CallerCenterSmallConflictDegree : ℕ :=
  (2 * 76000 + 1) ^ 2 *
    (2 * 364800 + 1) *
    (2 * 60800 + 1) ^ 2

private def pureWZ2CallerCenterLargeConflictDegree : ℕ :=
  (2 * 132864 + 1) ^ 3 *
    (2 * 64000 + 1) ^ 3

/-- Fixed degree used for caller-center conflict coloring at every scale. -/
def pureWZ2CallerCenterUniformConflictDegree : ℕ :=
  max pureWZ2CallerCenterSmallConflictDegree
    pureWZ2CallerCenterLargeConflictDegree

private theorem pureWZ2CallerCenter_abs_coord_le_norm
    (point : Point3) (coordinate : Fin 3) :
    |point coordinate| ≤ ‖point‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le point coordinate

private theorem pureWZ2CallerCenter_norm_le_sum_abs
    (point : Point3) :
    ‖point‖ ≤ |point 0| + |point 1| + |point 2| := by
  have normSquared :
      ‖point‖ ^ 2 =
        point 0 ^ 2 + point 1 ^ 2 + point 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  have squareBound :
      ‖point‖ ^ 2 ≤
        (|point 0| + |point 1| + |point 2|) ^ 2 := by
    rw [normSquared]
    nlinarith [sq_abs (point 0), sq_abs (point 1),
      sq_abs (point 2), abs_nonneg (point 0),
      abs_nonneg (point 1), abs_nonneg (point 2)]
  nlinarith [norm_nonneg point, abs_nonneg (point 0),
    abs_nonneg (point 1), abs_nonneg (point 2)]

private def pureWZ2CallerCenterFrame
    (linear : Point3 ≃ₗᵢ[ℝ] Point3)
    (center : Point3) :
    Point3 ≃ᵃⁱ[ℝ] Point3 where
  toFun point := linear point + center
  invFun point := linear.symm (point - center)
  left_inv point := by simp
  right_inv point := by simp
  linear := linear
  map_vadd' vector point := by
    simp [vadd_eq_add]
    abel
  norm_map vector := linear.norm_map vector

private theorem pureWZ2CallerCenter_frame_transverse_coordinates
    (linear : Point3 ≃ₗᵢ[ℝ] Point3)
    (reference vector : Point3)
    (referenceEq :
      linear reference = EuclideanSpace.single 2 1)
    {bound : ℝ}
    (transverse :
      ‖vector - inner ℝ vector reference • reference‖ ≤ bound) :
    |(linear vector) 0| ≤ bound ∧
      |(linear vector) 1| ≤ bound := by
  let residual :=
    vector - inner ℝ vector reference • reference
  have residualMap :
      linear residual =
        linear vector -
          inner ℝ (linear vector) (linear reference) •
            linear reference := by
    dsimp only [residual]
    rw [linear.map_sub, linear.map_smul,
      linear.inner_map_map]
  have residualZero :
      (linear residual) 0 = (linear vector) 0 := by
    rw [residualMap, referenceEq]
    simp [EuclideanSpace.single]
  have residualOne :
      (linear residual) 1 = (linear vector) 1 := by
    rw [residualMap, referenceEq]
    simp [EuclideanSpace.single]
  have residualNorm : ‖linear residual‖ ≤ bound := by
    rw [linear.norm_map]
    exact transverse
  constructor
  · rw [← residualZero]
    exact
      (pureWZ2CallerCenter_abs_coord_le_norm
        (linear residual) 0).trans residualNorm
  · rw [← residualOne]
    exact
      (pureWZ2CallerCenter_abs_coord_le_norm
        (linear residual) 1).trans residualNorm

private theorem pureWZ2CallerCenter_frame_longitudinal_coordinate
    (linear : Point3 ≃ₗᵢ[ℝ] Point3)
    (reference vector : Point3)
    (referenceEq :
      linear reference = EuclideanSpace.single 2 1) :
    (linear vector) 2 = inner ℝ vector reference := by
  have innerMap :=
    linear.inner_map_map vector reference
  rw [referenceEq] at innerMap
  have innerSingle :
      inner ℝ (linear vector)
          (EuclideanSpace.single 2 1 : Point3) =
        (linear vector) 2 := by
    simpa using
      EuclideanSpace.inner_single_right
        (2 : Fin 3) (1 : ℝ) (linear vector)
  linarith

/--
Full-carrier containment in a centered double controls the source direction
projectively, without requiring the source and parent to have the same
radius.
-/
private theorem pureWZ2CallerCenter_projective_direction_of_containment
    {sourceRadius parentRadius : ℝ}
    (sourceRadiusNonnegative : 0 ≤ sourceRadius)
    (parentRadiusPositive : 0 < parentRadius)
    (source : Kakeya.DeltaTube sourceRadius)
    (parent : Kakeya.DeltaTube parentRadius)
    (containment :
      source.carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 parent) :
    ‖source.direction -
        inner ℝ source.direction parent.direction •
          parent.direction‖ ≤
      4 * parentRadius := by
  have sourceBaseMem : source.base ∈ source.carrier := by
    exact
      Metric.mem_cthickening_of_dist_le
        source.base source.base sourceRadius
        (Kakeya.unitSegment source.base source.direction)
        ⟨0, by norm_num, by simp⟩
        (by simp [sourceRadiusNonnegative])
  have sourceEndMem :
      source.base + source.direction ∈ source.carrier := by
    exact
      Metric.mem_cthickening_of_dist_le
        (source.base + source.direction)
        (source.base + source.direction) sourceRadius
        (Kakeya.unitSegment source.base source.direction)
        ⟨1, by norm_num, by simp⟩
        (by simp [sourceRadiusNonnegative])
  rcases
      general_dilation_closest_point parentRadiusPositive.le
        (by norm_num : (0 : ℝ) < 2) parent source.base
        (containment sourceBaseMem) with
    ⟨firstParameter, _, firstDistance⟩
  rcases
      general_dilation_closest_point parentRadiusPositive.le
        (by norm_num : (0 : ℝ) < 2) parent
        (source.base + source.direction)
        (containment sourceEndMem) with
    ⟨secondParameter, _, secondDistance⟩
  let firstAxis :=
    parent.base + firstParameter • parent.direction
  let secondAxis :=
    parent.base + secondParameter • parent.direction
  let error :=
    source.direction -
      (secondParameter - firstParameter) • parent.direction
  have errorIdentity :
      error =
        ((source.base + source.direction) - secondAxis) -
          (source.base - firstAxis) := by
    dsimp only [error, firstAxis, secondAxis]
    module
  have errorNorm : ‖error‖ ≤ 4 * parentRadius := by
    rw [errorIdentity]
    calc
      ‖((source.base + source.direction) - secondAxis) -
          (source.base - firstAxis)‖ ≤
        ‖(source.base + source.direction) - secondAxis‖ +
          ‖source.base - firstAxis‖ :=
        norm_sub_le _ _
      _ ≤ 2 * parentRadius + 2 * parentRadius := by
        apply add_le_add
        · simpa [secondAxis, dist_eq_norm] using secondDistance
        · simpa [firstAxis, dist_eq_norm] using firstDistance
      _ = 4 * parentRadius := by ring
  have projectionIdentity :
      source.direction -
          inner ℝ source.direction parent.direction •
            parent.direction =
        error -
          inner ℝ error parent.direction • parent.direction := by
    dsimp only [error]
    rw [inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, parent.direction_unit]
    norm_num
    module
  rw [projectionIdentity]
  exact
    (pureWZ2_perp_norm_le parent.direction error
      parent.direction_unit).trans errorNorm

/--
A common caller midpoint controls the five parent parameters.  This statement
also permits an arbitrary caller radius; only the parent radius enters the
bounds.
-/
private theorem pureWZ2CallerCenter_midpoint_bounds_of_common_containment
    {sourceRadius parentRadius directionError : ℝ}
    (sourceRadiusNonnegative : 0 ≤ sourceRadius)
    (parentRadiusPositive : 0 < parentRadius)
    (source : Kakeya.DeltaTube sourceRadius)
    (first second : Kakeya.DeltaTube parentRadius)
    (firstContainment :
      source.carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 first)
    (secondContainment :
      source.carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 second)
    (directionClose :
      ‖second.direction -
          inner ℝ second.direction first.direction •
            first.direction‖ ≤ directionError) :
    let displacement :=
      wz2PaperTubeMidpoint second -
        wz2PaperTubeMidpoint first
    ‖displacement -
        inner ℝ displacement first.direction • first.direction‖ ≤
      directionError + 4 * parentRadius ∧
    |inner ℝ displacement first.direction| ≤
      2 + 4 * parentRadius := by
  dsimp only
  let sourceMidpoint := wz2PaperTubeMidpoint source
  have sourceMidpointMem : sourceMidpoint ∈ source.carrier :=
    wz2_paper_tubeMidpoint_mem_carrier source sourceRadiusNonnegative
  rcases
      general_dilation_closest_point parentRadiusPositive.le
        (by norm_num : (0 : ℝ) < 2) first sourceMidpoint
        (firstContainment sourceMidpointMem) with
    ⟨firstParameter, firstParameterMem, firstDistance⟩
  rcases
      general_dilation_closest_point parentRadiusPositive.le
        (by norm_num : (0 : ℝ) < 2) second sourceMidpoint
        (secondContainment sourceMidpointMem) with
    ⟨secondParameter, secondParameterMem, secondDistance⟩
  let firstAxis :=
    first.base + firstParameter • first.direction
  let secondAxis :=
    second.base + secondParameter • second.direction
  let axisDifference := secondAxis - firstAxis
  have axisDifferenceNorm :
      ‖axisDifference‖ ≤ 4 * parentRadius := by
    dsimp only [axisDifference]
    rw [← dist_eq_norm]
    calc
      dist secondAxis firstAxis ≤
          dist secondAxis sourceMidpoint +
            dist sourceMidpoint firstAxis :=
        dist_triangle _ _ _
      _ = dist sourceMidpoint secondAxis +
            dist sourceMidpoint firstAxis := by
        rw [dist_comm secondAxis sourceMidpoint]
      _ ≤ 2 * parentRadius + 2 * parentRadius :=
        add_le_add secondDistance firstDistance
      _ = 4 * parentRadius := by ring
  have firstParameterBound :
      |firstParameter - 1 / 2| ≤ 1 := by
    rw [abs_le]
    constructor <;>
      linarith [firstParameterMem.1, firstParameterMem.2]
  have secondParameterBound :
      |1 / 2 - secondParameter| ≤ 1 := by
    rw [abs_le]
    constructor <;>
      linarith [secondParameterMem.1, secondParameterMem.2]
  let displacement :=
    wz2PaperTubeMidpoint second -
      wz2PaperTubeMidpoint first
  have displacementIdentity :
      displacement =
        (1 / 2 - secondParameter) • second.direction +
          axisDifference +
          (firstParameter - 1 / 2) • first.direction := by
    dsimp only [displacement, axisDifference, firstAxis, secondAxis,
      wz2PaperTubeMidpoint]
    module
  have residualIdentity :
      displacement -
          inner ℝ displacement first.direction • first.direction =
        (1 / 2 - secondParameter) •
            (second.direction -
              inner ℝ second.direction first.direction •
                first.direction) +
          (axisDifference -
            inner ℝ axisDifference first.direction •
              first.direction) := by
    rw [displacementIdentity, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq,
      first.direction_unit]
    norm_num
    module
  have transverseBound :
      ‖displacement -
          inner ℝ displacement first.direction • first.direction‖ ≤
        directionError + 4 * parentRadius := by
    rw [residualIdentity]
    calc
      ‖(1 / 2 - secondParameter) •
              (second.direction -
                inner ℝ second.direction first.direction •
                  first.direction) +
            (axisDifference -
              inner ℝ axisDifference first.direction •
                first.direction)‖ ≤
          ‖(1 / 2 - secondParameter) •
              (second.direction -
                inner ℝ second.direction first.direction •
                  first.direction)‖ +
            ‖axisDifference -
              inner ℝ axisDifference first.direction •
                first.direction‖ :=
        norm_add_le _ _
      _ ≤
          1 * directionError + ‖axisDifference‖ := by
        rw [norm_smul, Real.norm_eq_abs]
        apply add_le_add
        · exact
            mul_le_mul secondParameterBound directionClose
              (norm_nonneg _) (by norm_num)
        · exact
            pureWZ2_perp_norm_le first.direction axisDifference
              first.direction_unit
      _ ≤ directionError + 4 * parentRadius := by
        linarith
  have directionInner :
      |inner ℝ second.direction first.direction| ≤ 1 := by
    exact
      (abs_real_inner_le_norm second.direction first.direction).trans <| by
        rw [second.direction_unit, first.direction_unit]
        norm_num
  have axisInner :
      |inner ℝ axisDifference first.direction| ≤
        ‖axisDifference‖ := by
    exact
      (abs_real_inner_le_norm axisDifference first.direction).trans <| by
        rw [first.direction_unit, mul_one]
  have innerIdentity :
      inner ℝ displacement first.direction =
        (1 / 2 - secondParameter) *
            inner ℝ second.direction first.direction +
          inner ℝ axisDifference first.direction +
          (firstParameter - 1 / 2) := by
    rw [displacementIdentity, inner_add_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq,
      first.direction_unit]
    norm_num
  have firstProduct :
      |(1 / 2 - secondParameter) *
          inner ℝ second.direction first.direction| ≤ 1 := by
    rw [abs_mul]
    exact
      (mul_le_mul secondParameterBound directionInner
        (abs_nonneg _) (by norm_num)).trans_eq (mul_one 1)
  have longitudinalBound :
      |inner ℝ displacement first.direction| ≤
        2 + 4 * parentRadius := by
    rw [innerIdentity]
    calc
      |(1 / 2 - secondParameter) *
              inner ℝ second.direction first.direction +
            inner ℝ axisDifference first.direction +
            (firstParameter - 1 / 2)| ≤
          |(1 / 2 - secondParameter) *
              inner ℝ second.direction first.direction| +
            |inner ℝ axisDifference first.direction| +
            |firstParameter - 1 / 2| :=
        abs_add_three _ _ _
      _ ≤ 1 + ‖axisDifference‖ + 1 := by
        gcongr
      _ ≤ 2 + 4 * parentRadius := by
        linarith
  exact ⟨transverseBound, longitudinalBound⟩

private theorem pureWZ2CallerCenter_direction_norm_of_close_parameters
    {rho : ℝ}
    (rhoPositive : 0 < rho)
    (rhoSmall : rho ≤ 1 / 1000)
    (first second : Point3)
    (firstUnit : ‖first‖ = 1)
    (secondUnit : ‖second‖ = 1)
    (firstTransverse :
      |first 0| ≤ 304 * rho ∧ |first 1| ≤ 304 * rho)
    (secondTransverse :
      |second 0| ≤ 304 * rho ∧ |second 1| ≤ 304 * rho)
    (firstPositive : first 2 ≥ 1 / 2)
    (secondPositive : second 2 ≥ 1 / 2)
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
  have sumZero : |first 0 + second 0| ≤ 608 * rho := by
    calc
      |first 0 + second 0| ≤
          |first 0| + |second 0| := abs_add_le _ _
      _ ≤ 304 * rho + 304 * rho :=
        add_le_add firstTransverse.1 secondTransverse.1
      _ = 608 * rho := by ring
  have sumOne : |first 1 + second 1| ≤ 608 * rho := by
    calc
      |first 1 + second 1| ≤
          |first 1| + |second 1| := abs_add_le _ _
      _ ≤ 304 * rho + 304 * rho :=
        add_le_add firstTransverse.2 secondTransverse.2
      _ = 608 * rho := by ring
  have squareZero :
      |first 0 ^ 2 - second 0 ^ 2| ≤
        (76 / 25 : ℝ) * rho ^ 2 := by
    rw [show first 0 ^ 2 - second 0 ^ 2 =
      (first 0 - second 0) * (first 0 + second 0) by ring,
      abs_mul]
    calc
      |first 0 - second 0| * |first 0 + second 0| ≤
          (rho / 200) * (608 * rho) := by
        apply mul_le_mul
        · simpa [Pi.sub_apply] using zeroClose
        · exact sumZero
        · positivity
        · positivity
      _ = (76 / 25 : ℝ) * rho ^ 2 := by ring
  have squareOne :
      |first 1 ^ 2 - second 1 ^ 2| ≤
        (76 / 25 : ℝ) * rho ^ 2 := by
    rw [show first 1 ^ 2 - second 1 ^ 2 =
      (first 1 - second 1) * (first 1 + second 1) by ring,
      abs_mul]
    calc
      |first 1 - second 1| * |first 1 + second 1| ≤
          (rho / 200) * (608 * rho) := by
        apply mul_le_mul
        · simpa [Pi.sub_apply] using oneClose
        · exact sumOne
        · positivity
        · positivity
      _ = (76 / 25 : ℝ) * rho ^ 2 := by ring
  have squareTwoIdentity :
      first 2 ^ 2 - second 2 ^ 2 =
        -((first 0 ^ 2 - second 0 ^ 2) +
          (first 1 ^ 2 - second 1 ^ 2)) := by
    linarith
  have squareTwo :
      |first 2 ^ 2 - second 2 ^ 2| ≤
        (152 / 25 : ℝ) * rho ^ 2 := by
    rw [squareTwoIdentity, abs_neg]
    calc
      |(first 0 ^ 2 - second 0 ^ 2) +
          (first 1 ^ 2 - second 1 ^ 2)| ≤
        |first 0 ^ 2 - second 0 ^ 2| +
          |first 1 ^ 2 - second 1 ^ 2| := abs_add_le _ _
      _ ≤
          (76 / 25 : ℝ) * rho ^ 2 +
            (76 / 25 : ℝ) * rho ^ 2 :=
        add_le_add squareZero squareOne
      _ = (152 / 25 : ℝ) * rho ^ 2 := by ring
  have signSum : 1 ≤ |first 2 + second 2| := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have twoDifference :
      |first 2 - second 2| ≤
        (152 / 25 : ℝ) * rho ^ 2 := by
    calc
      |first 2 - second 2| ≤
          |first 2 - second 2| *
            |first 2 + second 2| :=
        le_mul_of_one_le_right (abs_nonneg _) signSum
      _ = |first 2 ^ 2 - second 2 ^ 2| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ (152 / 25 : ℝ) * rho ^ 2 := squareTwo
  have twoSmall :
      |(first - second) 2| ≤ rho / 100 := by
    have raw :
        |first 2 - second 2| ≤ rho / 100 := by
      exact twoDifference.trans <| by
        nlinarith
    simpa [Pi.sub_apply] using raw
  calc
    ‖first - second‖ ≤
        |(first - second) 0| +
          |(first - second) 1| +
          |(first - second) 2| :=
      pureWZ2CallerCenter_norm_le_sum_abs _
    _ ≤ rho / 200 + rho / 200 + rho / 100 := by
      gcongr
    _ ≤ rho / 16 := by linarith

/--
The five close oriented parameters force ordinary centered containment.
Constants are specialized to the caller-center cone used below.
-/
private theorem pureWZ2CallerCenter_carrier_subset_of_close_parameters
    {rho : ℝ}
    (rhoPositive : 0 < rho)
    (rhoSmall : rho ≤ 1 / 1000)
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
      |firstDirection 0| ≤ 304 * rho ∧
        |firstDirection 1| ≤ 304 * rho)
    (secondTransverse :
      |secondDirection 0| ≤ 304 * rho ∧
        |secondDirection 1| ≤ 304 * rho)
    (firstPositive : firstDirection 2 ≥ 1 / 2)
    (secondPositive : secondDirection 2 ≥ 1 / 2)
    (midpointZero :
      |(firstMidpoint - secondMidpoint) 0| ≤ rho / 200)
    (midpointOne :
      |(firstMidpoint - secondMidpoint) 1| ≤ rho / 200)
    (midpointTwo :
      |(firstMidpoint - secondMidpoint) 2| ≤ 1 / 121600)
    (directionZero :
      |(firstDirection - secondDirection) 0| ≤ rho / 200)
    (directionOne :
      |(firstDirection - secondDirection) 1| ≤ rho / 200) :
    first.carrier ⊆ wz2PaperCenteredDilatedCarrier 2 second := by
  have secondLongitudinal :
      1 / 2 ≤ |secondDirection 2| := by
    rw [abs_of_nonneg (by linarith)]
    exact secondPositive
  let axialShift : ℝ :=
    (firstMidpoint 2 - secondMidpoint 2) / secondDirection 2
  have secondLongitudinalNe : secondDirection 2 ≠ 0 := by
    intro zero
    rw [zero, abs_zero] at secondLongitudinal
    norm_num at secondLongitudinal
  have axialBound : |axialShift| ≤ 1 / 60800 := by
    dsimp only [axialShift]
    rw [abs_div]
    calc
      |firstMidpoint 2 - secondMidpoint 2| /
            |secondDirection 2| ≤
          (1 / 121600 : ℝ) / |secondDirection 2| := by
        apply div_le_div_of_nonneg_right
        · simpa [Pi.sub_apply] using midpointTwo
        · exact abs_nonneg _
      _ ≤ (1 / 121600 : ℝ) / (1 / 2) := by
        apply div_le_div_of_nonneg_left <;> norm_num
        exact secondLongitudinal
      _ = 1 / 60800 := by norm_num
  have axialQuarter : |axialShift| ≤ 1 / 4 :=
    axialBound.trans (by norm_num)
  let residual :=
    (firstMidpoint - secondMidpoint) -
      axialShift • secondDirection
  have residualZero :
      |residual 0| ≤ rho / 100 := by
    dsimp only [residual]
    change
      |(firstMidpoint - secondMidpoint) 0 -
          axialShift * secondDirection 0| ≤ rho / 100
    calc
      |(firstMidpoint - secondMidpoint) 0 -
          axialShift * secondDirection 0| ≤
        |(firstMidpoint - secondMidpoint) 0| +
          |axialShift * secondDirection 0| := abs_sub _ _
      _ =
          |(firstMidpoint - secondMidpoint) 0| +
            |axialShift| * |secondDirection 0| := by
        rw [abs_mul]
      _ ≤ rho / 200 + (1 / 60800) * (304 * rho) :=
        add_le_add midpointZero <|
          mul_le_mul axialBound secondTransverse.1
            (abs_nonneg _) (by norm_num)
      _ = rho / 100 := by ring
  have residualOne :
      |residual 1| ≤ rho / 100 := by
    dsimp only [residual]
    change
      |(firstMidpoint - secondMidpoint) 1 -
          axialShift * secondDirection 1| ≤ rho / 100
    calc
      |(firstMidpoint - secondMidpoint) 1 -
          axialShift * secondDirection 1| ≤
        |(firstMidpoint - secondMidpoint) 1| +
          |axialShift * secondDirection 1| := abs_sub _ _
      _ =
          |(firstMidpoint - secondMidpoint) 1| +
            |axialShift| * |secondDirection 1| := by
        rw [abs_mul]
      _ ≤ rho / 200 + (1 / 60800) * (304 * rho) :=
        add_le_add midpointOne <|
          mul_le_mul axialBound secondTransverse.2
            (abs_nonneg _) (by norm_num)
      _ = rho / 100 := by ring
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
        pureWZ2CallerCenter_norm_le_sum_abs _
      _ = |residual 0| + |residual 1| := by
        rw [residualTwo, abs_zero]
        ring
      _ ≤ rho / 100 + rho / 100 :=
        add_le_add residualZero residualOne
      _ ≤ rho / 16 := by linarith
  have midpointFrame :
      frame.symm.linearIsometryEquiv
          ((wz2PaperTubeMidpoint first -
                wz2PaperTubeMidpoint second) -
            axialShift • second.direction) =
        residual := by
    rw [map_sub, map_smul, ← secondDirectionEq]
    simpa [vsub_eq_sub, residual, firstMidpointEq,
      secondMidpointEq] using
      congrArg
        (fun difference =>
          difference - axialShift • secondDirection)
        (frame.symm.map_vsub
          (wz2PaperTubeMidpoint first)
          (wz2PaperTubeMidpoint second))
  have midpointNorm :
      ‖(wz2PaperTubeMidpoint first -
              wz2PaperTubeMidpoint second) -
          axialShift • second.direction‖ ≤ rho / 16 := by
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
      pureWZ2CallerCenter_direction_norm_of_close_parameters
        rhoPositive rhoSmall firstDirection secondDirection
        firstUnit secondUnit firstTransverse secondTransverse
        firstPositive secondPositive directionZero directionOne
  exact
    wz2PaperOrdinary_carrier_subset_centeredDilatedTwo_of_axial_close
      rhoPositive axialQuarter midpointNorm directionNorm

/--
The actual caller-center envelope conflict graph has one fixed degree bound,
independent of the runtime family and all selected radii.
-/
theorem pureWZ2_caller_center_envelope_uniform_conflict_degree
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby :
      WZ2PaperPureNearbyScaleCoverData
        fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient : PureWZ2ParentQuotientNetSelectionData
      actualNearby callerRequested shading)
    {scheduledRequested : WZ2PaperRequestedScale delta}
    (scheduled : WZ2PaperPureNearbyScaleCoverData
      fine scheduledRequested ambientConstant)
    (callerBase : WZ2PaperPureTubeSubfamily quotient.callerCoarse)
    (fineNonempty : fine.Nonempty)
    (_fineBoundedBase : HasBoundedBase fine 4) :
    ∀ fixed : Fin scheduled.scaleData.coarse.card,
      (Finset.univ.filter fun other =>
        other ≠ fixed ∧
          (wz2PaperOrdinaryDilatedFiberIndices
              2 callerBase.family
              (wz2PaperOrdinaryEnvelopeFamily
                scheduled.scaleData.coarse) fixed ∩
            wz2PaperOrdinaryDilatedFiberIndices
              2 callerBase.family
              (wz2PaperOrdinaryEnvelopeFamily
                scheduled.scaleData.coarse) other).Nonempty).card ≤
        pureWZ2CallerCenterUniformConflictDegree := by
  intro fixed
  by_cases rhoSmall : scheduled.rho ≤ 1 / 1000
  · let conflicts :=
      Finset.univ.filter fun other =>
        other ≠ fixed ∧
          (wz2PaperOrdinaryDilatedFiberIndices
              2 callerBase.family
              (wz2PaperOrdinaryEnvelopeFamily
                scheduled.scaleData.coarse) fixed ∩
            wz2PaperOrdinaryDilatedFiberIndices
              2 callerBase.family
              (wz2PaperOrdinaryEnvelopeFamily
                scheduled.scaleData.coarse) other).Nonempty
    let parent (index : Fin scheduled.scaleData.coarse.card) :=
      scheduled.scaleData.coarse.tube index
    let oriented (index : Fin scheduled.scaleData.coarse.card) :=
      pureWZ2OrientedParent (parent fixed).direction (parent index)
    have conflictWitness :
        ∀ other ∈ conflicts,
          ∃ caller : Fin callerBase.family.card,
            (callerBase.family.tube caller).carrier ⊆
              wz2PaperCenteredDilatedCarrier 2
                (wz2PaperOrdinaryEnvelope (parent fixed)) ∧
            (callerBase.family.tube caller).carrier ⊆
              wz2PaperCenteredDilatedCarrier 2
                (wz2PaperOrdinaryEnvelope (parent other)) := by
      intro other otherMem
      have overlap :=
        (Finset.mem_filter.mp otherMem).2.2
      rcases overlap with ⟨caller, callerMem⟩
      rcases Finset.mem_inter.mp callerMem with
        ⟨fixedMem, otherMem'⟩
      rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        at fixedMem otherMem'
      exact ⟨caller, by simpa [parent] using fixedMem,
        by simpa [parent] using otherMem'⟩
    choose caller callerFixed callerOther using conflictWitness
    have projectiveToFixed :
        ∀ other ∈ conflicts,
          ‖(parent other).direction -
              inner ℝ (parent other).direction
                  (parent fixed).direction •
                (parent fixed).direction‖ ≤
            304 * scheduled.rho := by
      intro other otherMem
      let callerTube := callerBase.family.tube (caller other otherMem)
      have callerFixedProjective :=
        pureWZ2CallerCenter_projective_direction_of_containment
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1).le
          (mul_pos (by norm_num) scheduled.scaleData.rho_pos)
          callerTube
          (wz2PaperOrdinaryEnvelope (parent fixed))
          (callerFixed other otherMem)
      have callerOtherProjective :=
        pureWZ2CallerCenter_projective_direction_of_containment
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1).le
          (mul_pos (by norm_num) scheduled.scaleData.rho_pos)
          callerTube
          (wz2PaperOrdinaryEnvelope (parent other))
          (callerOther other otherMem)
      have callerFixedProjective' :
          ‖callerTube.direction -
              inner ℝ callerTube.direction (parent fixed).direction •
                (parent fixed).direction‖ ≤
            76 * scheduled.rho := by
        have converted :=
          callerFixedProjective.trans_eq
            (show 4 * (19 * scheduled.rho) =
                76 * scheduled.rho by ring)
        simpa only [wz2PaperOrdinaryEnvelope_direction] using converted
      have callerOtherProjective' :
          ‖callerTube.direction -
              inner ℝ callerTube.direction (parent other).direction •
                (parent other).direction‖ ≤
            76 * scheduled.rho := by
        have converted :=
          callerOtherProjective.trans_eq
            (show 4 * (19 * scheduled.rho) =
                76 * scheduled.rho by ring)
        simpa only [wz2PaperOrdinaryEnvelope_direction] using converted
      have triangle :=
        pureWZ2_projective_direction_triangle
          (error := 76 * scheduled.rho)
          (parent fixed).direction_unit
          (parent other).direction_unit
          callerTube.direction_unit
          (mul_nonneg (by norm_num) scheduled.scaleData.rho_pos.le)
          (by nlinarith [scheduled.scaleData.rho_pos])
          callerFixedProjective'
          callerOtherProjective'
      nlinarith
    have orientedTransverse :
        ∀ other ∈ conflicts,
          ‖(oriented other).direction -
              inner ℝ (oriented other).direction
                  (parent fixed).direction •
                (parent fixed).direction‖ ≤
            304 * scheduled.rho := by
      intro other otherMem
      rw [pureWZ2OrientedParent_transverse]
      exact projectiveToFixed other otherMem
    have orientedPositive :
        ∀ other ∈ conflicts,
          inner ℝ (oriented other).direction
              (parent fixed).direction ≥ 1 / 2 := by
      intro other otherMem
      rw [pureWZ2OrientedParent_inner_eq_abs]
      let coefficient :=
        inner ℝ (parent other).direction (parent fixed).direction
      have transverse := projectiveToFixed other otherMem
      have normIdentity :
          ‖(parent other).direction -
              coefficient • (parent fixed).direction‖ ^ 2 =
            1 - coefficient ^ 2 := by
        rw [norm_sub_sq_real, inner_smul_right,
          norm_smul, (parent other).direction_unit,
          (parent fixed).direction_unit]
        simp [coefficient, Real.norm_eq_abs, sq_abs]
        ring
      have squared :
          ‖(parent other).direction -
              coefficient • (parent fixed).direction‖ ^ 2 ≤
            (304 * scheduled.rho) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (by norm_num)
            scheduled.scaleData.rho_pos.le)).mpr transverse
      have coefficientSquared :
          (1 / 2 : ℝ) ^ 2 ≤ coefficient ^ 2 := by
        rw [normIdentity] at squared
        nlinarith [scheduled.scaleData.rho_pos]
      change 1 / 2 ≤ |coefficient|
      nlinarith [sq_abs coefficient, abs_nonneg coefficient]
    have midpointGeometry :
        ∀ other ∈ conflicts,
          let displacement :=
            wz2PaperTubeMidpoint (parent other) -
              wz2PaperTubeMidpoint (parent fixed)
          ‖displacement -
              inner ℝ displacement (parent fixed).direction •
                (parent fixed).direction‖ ≤
              380 * scheduled.rho ∧
            |inner ℝ displacement (parent fixed).direction| ≤ 3 := by
      intro other otherMem
      let callerTube := callerBase.family.tube (caller other otherMem)
      have bounds :=
        pureWZ2CallerCenter_midpoint_bounds_of_common_containment
          (actualNearby.scaleData.delta_pos.trans_le
            callerRequested.2.1).le
          (mul_pos (by norm_num) scheduled.scaleData.rho_pos)
          callerTube
          (wz2PaperOrdinaryEnvelope (parent fixed))
          (wz2PaperOrdinaryEnvelope (parent other))
          (callerFixed other otherMem)
          (callerOther other otherMem)
          (projectiveToFixed other otherMem)
      dsimp only
      constructor
      · have envelopeBound :
            ‖wz2PaperTubeMidpoint (parent other) -
                  wz2PaperTubeMidpoint (parent fixed) -
                inner ℝ
                    (wz2PaperTubeMidpoint (parent other) -
                      wz2PaperTubeMidpoint (parent fixed))
                    (parent fixed).direction •
                  (parent fixed).direction‖ ≤
              304 * scheduled.rho + 4 * (19 * scheduled.rho) := by
          simpa only [wz2PaperTubeMidpoint,
            wz2PaperOrdinaryEnvelope_base,
            wz2PaperOrdinaryEnvelope_direction] using bounds.1
        exact envelopeBound.trans_eq (by ring)
      · have longitudinal :
            |inner ℝ
                (wz2PaperTubeMidpoint (parent other) -
                  wz2PaperTubeMidpoint (parent fixed))
                (parent fixed).direction| ≤
              2 + 76 * scheduled.rho := by
          have envelopeBound :
              |inner ℝ
                  (wz2PaperTubeMidpoint (parent other) -
                    wz2PaperTubeMidpoint (parent fixed))
                  (parent fixed).direction| ≤
                2 + 4 * (19 * scheduled.rho) := by
            simpa only [wz2PaperTubeMidpoint,
              wz2PaperOrdinaryEnvelope_base,
              wz2PaperOrdinaryEnvelope_direction] using bounds.2
          exact envelopeBound.trans_eq (by ring)
        exact longitudinal.trans (by nlinarith)
    rcases
        frame_of_axis (parent fixed).direction
          (parent fixed).direction_unit with
      ⟨_, _, rawFrame, fixedTwo, fixedZero, fixedOne⟩
    let linear := rawFrame.linearIsometryEquiv
    let frame :=
      pureWZ2CallerCenterFrame linear
        (wz2PaperTubeMidpoint (parent fixed))
    let midpoint (index : Fin scheduled.scaleData.coarse.card) :=
      frame.symm (wz2PaperTubeMidpoint (oriented index))
    let direction (index : Fin scheduled.scaleData.coarse.card) :=
      frame.symm.linearIsometryEquiv (oriented index).direction
    have fixedDirection :
        frame.symm.linearIsometryEquiv (parent fixed).direction =
          EuclideanSpace.single 2 1 := by
      change
        rawFrame.symm.linearIsometryEquiv (parent fixed).direction =
          EuclideanSpace.single 2 1
      ext coordinate
      fin_cases coordinate
      · simpa [EuclideanSpace.single] using fixedZero
      · simpa [EuclideanSpace.single] using fixedOne
      · simpa [EuclideanSpace.single] using fixedTwo
    have midpointMap :
        ∀ index,
          midpoint index =
            frame.symm.linearIsometryEquiv
              (wz2PaperTubeMidpoint (parent index) -
                wz2PaperTubeMidpoint (parent fixed)) := by
      intro index
      change
        linear.symm
            (wz2PaperTubeMidpoint (oriented index) -
              wz2PaperTubeMidpoint (parent fixed)) =
          linear.symm
            (wz2PaperTubeMidpoint (parent index) -
              wz2PaperTubeMidpoint (parent fixed))
      rw [pureWZ2OrientedParent_midpoint]
    have midpointBounds :
        ∀ other ∈ conflicts,
          |midpoint other 0| ≤ 380 * scheduled.rho ∧
            |midpoint other 1| ≤ 380 * scheduled.rho ∧
            |midpoint other 2| ≤ 3 := by
      intro other otherMem
      let displacement :=
        wz2PaperTubeMidpoint (parent other) -
          wz2PaperTubeMidpoint (parent fixed)
      have geometry := midpointGeometry other otherMem
      have transverseCoordinates :=
        pureWZ2CallerCenter_frame_transverse_coordinates
          frame.symm.linearIsometryEquiv
          (parent fixed).direction displacement fixedDirection
          geometry.1
      have longitudinalCoordinate :=
        pureWZ2CallerCenter_frame_longitudinal_coordinate
          frame.symm.linearIsometryEquiv
          (parent fixed).direction displacement fixedDirection
      rw [midpointMap other]
      exact
        ⟨transverseCoordinates.1, transverseCoordinates.2,
          by rw [longitudinalCoordinate]; exact geometry.2⟩
    have directionBounds :
        ∀ other ∈ conflicts,
          |direction other 0| ≤ 304 * scheduled.rho ∧
            |direction other 1| ≤ 304 * scheduled.rho ∧
            direction other 2 ≥ 1 / 2 := by
      intro other otherMem
      have transverseCoordinates :=
        pureWZ2CallerCenter_frame_transverse_coordinates
          frame.symm.linearIsometryEquiv
          (parent fixed).direction (oriented other).direction
          fixedDirection (orientedTransverse other otherMem)
      have longitudinalCoordinate :=
        pureWZ2CallerCenter_frame_longitudinal_coordinate
          frame.symm.linearIsometryEquiv
          (parent fixed).direction (oriented other).direction
          fixedDirection
      exact
        ⟨transverseCoordinates.1, transverseCoordinates.2,
          by
            rw [longitudinalCoordinate]
            exact orientedPositive other otherMem⟩
    let parameter :
        Fin scheduled.scaleData.coarse.card → Fin 5 → ℝ :=
      fun index coordinate =>
        match coordinate.1 with
        | 0 => midpoint index 0
        | 1 => midpoint index 1
        | 2 => midpoint index 2
        | 3 => direction index 0
        | _ => direction index 1
    let mesh : Fin 5 → ℝ := fun coordinate =>
      if coordinate.1 = 2 then 1 / 121600
      else scheduled.rho / 200
    let radius : Fin 5 → ℝ := fun coordinate =>
      match coordinate.1 with
      | 0 => 380 * scheduled.rho
      | 1 => 380 * scheduled.rho
      | 2 => 3
      | _ => 304 * scheduled.rho
    let values := conflicts.image parameter
    have meshPositive : ∀ coordinate, 0 < mesh coordinate := by
      intro coordinate
      dsimp only [mesh]
      split_ifs
      · norm_num
      · exact div_pos scheduled.scaleData.rho_pos (by norm_num)
    have radiusNonnegative : ∀ coordinate, 0 ≤ radius coordinate := by
      intro coordinate
      fin_cases coordinate
      · exact mul_nonneg (by norm_num) scheduled.scaleData.rho_pos.le
      · exact mul_nonneg (by norm_num) scheduled.scaleData.rho_pos.le
      · change (0 : ℝ) ≤ 3
        norm_num
      · exact mul_nonneg (by norm_num) scheduled.scaleData.rho_pos.le
      · exact mul_nonneg (by norm_num) scheduled.scaleData.rho_pos.le
    have parameterBound :
        ∀ value ∈ values,
          ∀ coordinate, |value coordinate| ≤ radius coordinate := by
      intro value valueMem coordinate
      rcases Finset.mem_image.mp valueMem with
        ⟨index, indexMem, rfl⟩
      have midpointBound := midpointBounds index indexMem
      have directionBound := directionBounds index indexMem
      dsimp only [parameter, radius]
      fin_cases coordinate
      · exact midpointBound.1
      · exact midpointBound.2.1
      · exact midpointBound.2.2
      · exact directionBound.1
      · exact directionBound.2.1
    have rawDistinct :
        WZ2PaperOrdinaryIsEssentiallyDistinct
          scheduled.scaleData.coarse :=
      scheduled.scaleData.cover.coarse_essentiallyDistinct_of_uniform
        scheduled.scaleData.rho_pos.le fineNonempty
        scheduled.scaleData.full_fiber_uniform
    have indexEqOfClose :
        ∀ first ∈ conflicts,
          ∀ second ∈ conflicts,
            (∀ coordinate,
              |parameter first coordinate -
                  parameter second coordinate| ≤ mesh coordinate) →
            first = second := by
      intro first firstMem second secondMem close
      by_contra indexNe
      have firstMidpointBounds := midpointBounds first firstMem
      have secondMidpointBounds := midpointBounds second secondMem
      have firstDirectionBounds := directionBounds first firstMem
      have secondDirectionBounds := directionBounds second secondMem
      have midpointZero :
          |(midpoint first - midpoint second) 0| ≤
            scheduled.rho / 200 := by
        simpa [parameter, mesh, Pi.sub_apply] using
          close (0 : Fin 5)
      have midpointOne :
          |(midpoint first - midpoint second) 1| ≤
            scheduled.rho / 200 := by
        simpa [parameter, mesh, Pi.sub_apply] using
          close (1 : Fin 5)
      have midpointTwo :
          |(midpoint first - midpoint second) 2| ≤
            1 / 121600 := by
        simpa [parameter, mesh, Pi.sub_apply] using
          close (2 : Fin 5)
      have directionZero :
          |(direction first - direction second) 0| ≤
            scheduled.rho / 200 := by
        simpa [parameter, mesh, Pi.sub_apply] using
          close (3 : Fin 5)
      have directionOne :
          |(direction first - direction second) 1| ≤
            scheduled.rho / 200 := by
        simpa [parameter, mesh, Pi.sub_apply] using
          close (4 : Fin 5)
      have orientedContainment :
          (oriented first).carrier ⊆
            wz2PaperCenteredDilatedCarrier 2 (oriented second) :=
        pureWZ2CallerCenter_carrier_subset_of_close_parameters
          scheduled.scaleData.rho_pos rhoSmall frame
          (midpoint first) (midpoint second)
          (direction first) (direction second)
          rfl rfl rfl rfl
          ⟨firstDirectionBounds.1, firstDirectionBounds.2.1⟩
          ⟨secondDirectionBounds.1, secondDirectionBounds.2.1⟩
          firstDirectionBounds.2.2 secondDirectionBounds.2.2
          midpointZero midpointOne midpointTwo
          directionZero directionOne
      have originalContainment :
          (parent first).carrier ⊆
            wz2PaperCenteredDilatedCarrier 2 (parent second) := by
        have firstCarrier :
            (oriented first).carrier = (parent first).carrier :=
          pureWZ2OrientedParent_carrier _ _
        have secondCarrier :
            (oriented second).carrier = (parent second).carrier :=
          pureWZ2OrientedParent_carrier _ _
        have secondMidpoint :
            wz2PaperTubeMidpoint (oriented second) =
              wz2PaperTubeMidpoint (parent second) :=
          pureWZ2OrientedParent_midpoint _ _
        unfold wz2PaperCenteredDilatedCarrier at orientedContainment ⊢
        rwa [firstCarrier, secondCarrier, secondMidpoint]
          at orientedContainment
      exact (rawDistinct first second indexNe).1 originalContainment
    have parameterSeparation :
        ∀ first ∈ values,
          ∀ second ∈ values,
            first ≠ second →
              ∃ coordinate,
                |first coordinate - second coordinate| ≥
                  mesh coordinate := by
      intro first firstMem second secondMem valuesNe
      rcases Finset.mem_image.mp firstMem with
        ⟨firstIndex, firstIndexMem, rfl⟩
      rcases Finset.mem_image.mp secondMem with
        ⟨secondIndex, secondIndexMem, secondEq⟩
      subst second
      by_contra noCoordinate
      push Not at noCoordinate
      have indexEq :=
        indexEqOfClose firstIndex firstIndexMem
          secondIndex secondIndexMem fun coordinate =>
            (noCoordinate coordinate).le
      exact valuesNe <| by rw [indexEq]
    have packed :=
      anisotropic_cell_pack meshPositive radiusNonnegative
        parameterBound parameterSeparation
    have parameterInjective : Set.InjOn parameter conflicts := by
      intro first firstMem second secondMem parameterEq
      apply indexEqOfClose first firstMem second secondMem
      intro coordinate
      rw [congrFun parameterEq coordinate, sub_self, abs_zero]
      exact (meshPositive coordinate).le
    have valuesCard : values.card = conflicts.card :=
      Finset.card_image_of_injOn parameterInjective
    have transverseQuotient :
        380 * scheduled.rho / (scheduled.rho / 200) =
          (76000 : ℝ) := by
      field_simp [scheduled.scaleData.rho_pos.ne']
      ring
    have directionQuotient :
        304 * scheduled.rho / (scheduled.rho / 200) =
          (60800 : ℝ) := by
      field_simp [scheduled.scaleData.rho_pos.ne']
      ring
    have longitudinalQuotient :
        (3 : ℝ) / (1 / 121600) = 364800 := by
      norm_num
    have transverseCeil :
        Nat.ceil
            (380 * scheduled.rho / (scheduled.rho / 200)) =
          76000 := by
      rw [transverseQuotient]
      exact Nat.ceil_natCast _
    have directionCeil :
        Nat.ceil
            (304 * scheduled.rho / (scheduled.rho / 200)) =
          60800 := by
      rw [directionQuotient]
      exact Nat.ceil_natCast _
    have longitudinalCeil :
        Nat.ceil ((3 : ℝ) / (1 / 121600)) = 364800 := by
      rw [longitudinalQuotient]
      exact Nat.ceil_natCast _
    let expectedFactor : Fin 5 → ℕ := fun coordinate =>
      match coordinate.1 with
      | 0 => 152001
      | 1 => 152001
      | 2 => 729601
      | _ => 121601
    have factorEq :
        ∀ coordinate : Fin 5,
          (2 * Nat.ceil
              (radius coordinate / mesh coordinate) + 1) =
            expectedFactor coordinate := by
      intro coordinate
      fin_cases coordinate
      · change
          2 * Nat.ceil
              (380 * scheduled.rho / (scheduled.rho / 200)) + 1 =
            152001
        rw [transverseCeil]
      · change
          2 * Nat.ceil
              (380 * scheduled.rho / (scheduled.rho / 200)) + 1 =
            152001
        rw [transverseCeil]
      · change
          2 * Nat.ceil ((3 : ℝ) / (1 / 121600)) + 1 = 729601
        rw [longitudinalCeil]
      · change
          2 * Nat.ceil
              (304 * scheduled.rho / (scheduled.rho / 200)) + 1 =
            121601
        rw [directionCeil]
      · change
          2 * Nat.ceil
              (304 * scheduled.rho / (scheduled.rho / 200)) + 1 =
            121601
        rw [directionCeil]
    have productBound :
        (∏ coordinate : Fin 5,
            (2 * Nat.ceil
              (radius coordinate / mesh coordinate) + 1)) =
          pureWZ2CallerCenterSmallConflictDegree := by
      calc
        (∏ coordinate : Fin 5,
            (2 * Nat.ceil
              (radius coordinate / mesh coordinate) + 1)) =
            ∏ coordinate : Fin 5, expectedFactor coordinate := by
          apply Finset.prod_congr rfl
          intro coordinate _
          exact factorEq coordinate
        _ = pureWZ2CallerCenterSmallConflictDegree := by
          norm_num [expectedFactor,
            pureWZ2CallerCenterSmallConflictDegree,
            Fin.prod_univ_succ]
    change conflicts.card ≤ pureWZ2CallerCenterUniformConflictDegree
    rw [← valuesCard]
    exact packed.trans <| productBound.le.trans <|
      le_max_left _ _
  · have rhoLower : 1 / 1000 ≤ scheduled.rho :=
      le_of_not_ge rhoSmall
    have oldBound :=
      pureWZ2_caller_center_envelope_conflict_degree
        quotient scheduled callerBase fineNonempty fixed
    have firstRatio :
        (2 + 76 * scheduled.rho) / (scheduled.rho / 64) ≤
          132864 := by
      rw [div_le_iff₀
        (div_pos scheduled.scaleData.rho_pos (by norm_num))]
      nlinarith [scheduled.scaleData.rho_pos]
    have secondRatio :
        1 / (scheduled.rho / 64) ≤ 64000 := by
      rw [div_le_iff₀
        (div_pos scheduled.scaleData.rho_pos (by norm_num))]
      nlinarith [scheduled.scaleData.rho_pos]
    have firstCeil :
        Nat.ceil
            ((2 + 76 * scheduled.rho) /
              (scheduled.rho / 64)) ≤ 132864 :=
      Nat.ceil_le.mpr firstRatio
    have secondCeil :
        Nat.ceil (1 / (scheduled.rho / 64)) ≤ 64000 :=
      Nat.ceil_le.mpr secondRatio
    refine oldBound.trans ?_
    unfold pureWZ2CallerCenterEnvelopeConflictDegree
      pureWZ2CallerCenterUniformConflictDegree
      pureWZ2CallerCenterLargeConflictDegree
    apply le_trans ?_ (le_max_right _ _)
    gcongr

/-- Proper caller-center coloring with a fixed color type. -/
theorem pureWZ2_caller_center_envelope_uniform_coloring
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {actualRequested : WZ2PaperRequestedScale delta}
    {ambientConstant : ENNReal}
    {actualNearby : WZ2PaperPureNearbyScaleCoverData
      fine actualRequested ambientConstant}
    {callerRequested : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (quotient : PureWZ2ParentQuotientNetSelectionData
      actualNearby callerRequested shading)
    {scheduledRequested : WZ2PaperRequestedScale delta}
    (scheduled : WZ2PaperPureNearbyScaleCoverData
      fine scheduledRequested ambientConstant)
    (callerBase : WZ2PaperPureTubeSubfamily quotient.callerCoarse)
    (fineNonempty : fine.Nonempty)
    (fineBoundedBase : HasBoundedBase fine 4) :
    Nonempty (PureWZ2CallerCenterEnvelopeColoringData
      quotient scheduled callerBase
        (Fin (pureWZ2CallerCenterUniformConflictDegree + 1))) :=
  pureWZ2_caller_center_envelope_coloring quotient scheduled callerBase
    pureWZ2CallerCenterUniformConflictDegree
    (pureWZ2_caller_center_envelope_uniform_conflict_degree
      quotient scheduled callerBase fineNonempty fineBoundedBase)

end Kakeya.Assouad

end
