import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCanonicalDilatedDirection
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperJohnHomotheticEnvelopeStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitRescalingBasics
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperUnitScaleCarrierHomotheticContainmentHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickySelectedDilatedScaleCover
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWAFromVolumeFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.GeneralInclusionMain
import Mathlib.Analysis.Convex.Measure
import Mathlib.Tactic

/-!
# Paper nearby-scale CWA implies top-level CWA with a power loss

This file uses the cropped `WZ2PaperCWAAtNearbyScales` interface directly.
The requested scale is `delta ^ loss`.  Its strict nearby window forces the
raw actual scale below one.  At that arbitrary subunit scale, the historical
rescaling of each complete literal full fiber controls the original cropped
fiber through a common convex envelope whose volume loss is a fixed multiple
of `rho⁻²`.  Summing the complete fibers and using
`rho ≥ delta ^ loss` gives the stated `delta ^ (-3 * loss)` bound.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory
open scoped Pointwise

attribute [local instance] Classical.propDecidable

private def historicalInverseLinear
    {rho : ℝ} (parent : Kakeya.DeltaTube rho) :
    Point3 →ₗ[ℝ] Point3 :=
  (householderToE3
      (wz1PaperDirection parent)
      (wz1PaperDirection_norm parent)).toLinearMap.comp
    (transverseScaleLin (1 / (100 * rho) : ℝ))

private theorem historicalInverseLinear_left
    {rho : ℝ} (parent : Kakeya.DeltaTube rho)
    (rhoPos : 0 < rho) (vector : Point3) :
    historicalInverseLinear parent
        (wz1PaperUnitRescalingLinear parent vector) =
      vector := by
  dsimp only [historicalInverseLinear, LinearMap.comp_apply,
    wz1PaperUnitRescalingLinear, unitRescalingLinear]
  let rotation :=
    householderToE3
      (wz1PaperDirection parent)
      (wz1PaperDirection_norm parent)
  change
    rotation
        (transverseScaleLin (1 / (100 * rho) : ℝ)
          (transverseScaleLin (100 * rho) (rotation vector))) =
      vector
  have scalingCancel :
      transverseScaleLin (1 / (100 * rho) : ℝ)
          (transverseScaleLin (100 * rho) (rotation vector)) =
        rotation vector := by
    ext coordinate
    fin_cases coordinate <;>
      simp [transverseScaleLin_coord0, transverseScaleLin_coord1,
        transverseScaleLin_coord2] <;>
      field_simp [rhoPos.ne']
  rw [scalingCancel]
  exact householderToE3_involution _ _ _

private theorem historicalInverseLinear_right
    {rho : ℝ} (parent : Kakeya.DeltaTube rho)
    (rhoPos : 0 < rho) (vector : Point3) :
    wz1PaperUnitRescalingLinear parent
        (historicalInverseLinear parent vector) =
      vector := by
  dsimp only [historicalInverseLinear, LinearMap.comp_apply,
    wz1PaperUnitRescalingLinear, unitRescalingLinear]
  let rotation :=
    householderToE3
      (wz1PaperDirection parent)
      (wz1PaperDirection_norm parent)
  change
    transverseScaleLin (100 * rho)
        (rotation
          (rotation
            (transverseScaleLin (1 / (100 * rho) : ℝ) vector))) =
      vector
  have rotationCancel :
      rotation (rotation
          (transverseScaleLin (1 / (100 * rho) : ℝ) vector)) =
        transverseScaleLin (1 / (100 * rho) : ℝ) vector :=
    householderToE3_involution _ _ _
  rw [rotationCancel]
  ext coordinate
  fin_cases coordinate <;>
    simp [transverseScaleLin_coord0, transverseScaleLin_coord1,
      transverseScaleLin_coord2] <;>
    field_simp [rhoPos.ne']

private theorem historicalInverseLinear_norm_of_coord_two_zero
    {rho : ℝ} (parent : Kakeya.DeltaTube rho)
    (rhoPos : 0 < rho) (vector : Point3)
    (vectorTwo : vector (2 : Fin 3) = 0) :
    ‖historicalInverseLinear parent vector‖ =
      (100 * rho) * ‖vector‖ := by
  dsimp only [historicalInverseLinear, LinearMap.comp_apply]
  change
    ‖(householderToE3
        (wz1PaperDirection parent)
        (wz1PaperDirection_norm parent))
      (transverseScaleLin (1 / (100 * rho) : ℝ) vector)‖ =
        (100 * rho) * ‖vector‖
  rw [householderToE3_norm,
    transverseScaleLin_norm_of_coord2_zero
      (1 / (100 * rho) : ℝ) (by positivity) vector vectorTwo]
  field_simp [rhoPos.ne']

private theorem historicalLinear_lower_bound
    {rho : ℝ} (parent : Kakeya.DeltaTube rho)
    (rhoPos : 0 < rho) (rhoLeOne : rho ≤ 1)
    (vector : Point3) :
    ‖wz1PaperUnitRescalingLinear parent vector‖ ≥
      ‖vector‖ / 100 := by
  let rotation :=
    householderToE3
      (wz1PaperDirection parent)
      (wz1PaperDirection_norm parent)
  set rotated := rotation vector with rotatedEq
  have rotationNorm : ‖rotated‖ = ‖vector‖ :=
    householderToE3_norm _ _ _
  have linearEq :
      wz1PaperUnitRescalingLinear parent vector =
        transverseScaleLin (100 * rho) rotated := by
    dsimp only [wz1PaperUnitRescalingLinear, unitRescalingLinear]
    rfl
  have normSq :
      ‖wz1PaperUnitRescalingLinear parent vector‖ ^ 2 =
        (1 / (100 * rho) ^ 2) *
            ((rotated 0) ^ 2 + (rotated 1) ^ 2) +
          (rotated 2) ^ 2 := by
    rw [linearEq]
    exact transverseScaleLin_norm_sq (100 * rho) (by positivity) rotated
  have rotatedNormSq :
      ‖rotated‖ ^ 2 =
        (rotated 0) ^ 2 + (rotated 1) ^ 2 + (rotated 2) ^ 2 :=
    point3_coord_norm_sq rotated
  have coefficientLower :
      (1 / (100 * rho) ^ 2 : ℝ) ≥ 1 / 100 ^ 2 := by
    have denominator : (100 * rho) ^ 2 ≤ (100 : ℝ) ^ 2 := by
      nlinarith
    exact (div_le_div_iff_of_pos_left (by norm_num)
      (sq_pos_of_pos (by positivity : 0 < (100 : ℝ)))
      (sq_pos_of_pos (by positivity : 0 < 100 * rho))).mpr denominator
  have lowerSq :
      ‖wz1PaperUnitRescalingLinear parent vector‖ ^ 2 ≥
        ‖vector‖ ^ 2 / 100 ^ 2 := by
    rw [normSq, ← rotationNorm, rotatedNormSq]
    nlinarith [sq_nonneg (rotated 0), sq_nonneg (rotated 1),
      sq_nonneg (rotated 2)]
  nlinarith [norm_nonneg
    (wz1PaperUnitRescalingLinear parent vector), norm_nonneg vector]

private structure HistoricalCommonBodyData
    {delta rho : ℝ}
    (parent : Kakeya.DeltaTube rho)
    (rhoPos : 0 < rho)
    (convexSet : Set Point3) where
  body : Set Point3
  convex_body : JohnEllipsoid.IsConvexBody body
  volume_le :
    volume body ≤
      ENNReal.ofReal ((1 / (100 * rho)) ^ 2) * volume convexSet
  source_image_subset :
    ∀ source : Kakeya.DeltaTube delta,
      WZ1PaperTubeInLineClass source →
      wz1PaperTubeCarrier source ⊆ convexSet →
        wz1PaperUnitRescalingMap parent rhoPos ''
            wz1PaperTubeCarrier source ⊆
          body
  source_center_mem :
    ∀ source : Kakeya.DeltaTube delta,
      WZ1PaperTubeInLineClass source →
      wz1PaperTubeCarrier source ⊆ convexSet →
        wz1PaperUnitRescalingMap parent rhoPos
            (wz1TubeAxisZeroPoint source) ∈
          body

private theorem historical_image_interior_ball
    {delta rho : ℝ}
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ 1 / 100)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (parent : Kakeya.DeltaTube rho)
    (source : Kakeya.DeltaTube delta)
    (sourceLine : WZ1PaperTubeInLineClass source) :
    Metric.closedBall
        (wz1PaperUnitRescalingMap parent rhoPos
          (wz1TubeAxisZeroPoint source))
        (6 * delta / 100) ⊆
      wz1PaperUnitRescalingMap parent rhoPos ''
        wz1PaperTubeCarrier source := by
  let center := wz1TubeAxisZeroPoint source
  let rescaling := wz1PaperUnitRescalingMap parent rhoPos
  let linearMap := wz1PaperUnitRescalingLinear parent
  have centerAxis : center ∈ tubeAxisLine source :=
    wz1TubeAxisZeroPoint_mem_axis source
  have ballCarrier :
      Metric.closedBall center (6 * delta) ⊆
        wz1PaperTubeCarrier source := by
    intro point pointMem
    have distance : dist point center ≤ 6 * delta := by
      simpa [Metric.mem_closedBall] using pointMem
    have pointNorm : ‖point - center‖ ≤ 6 * delta := by
      simpa [dist_eq_norm] using distance
    have centerTwo : center (2 : Fin 3) = 0 :=
      wz1TubeAxisZeroPoint_coord_two source sourceLine.vertical
    have pointBox :
        point ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
      simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq]
      norm_num
      have coordinate :
          ∀ index : Fin 3,
            |point index - center index| ≤ ‖point - center‖ := by
        intro index
        simpa [dist_eq_norm] using
          abs_coord_sub_le_dist (x := point) (y := center) index
      constructor
      · calc
          |point 0| ≤ |point 0 - center 0| + |center 0| := by
            simpa [sub_add_cancel] using
              abs_add_le (point 0 - center 0) (center 0)
          _ ≤ 6 * delta + 1 / 3 :=
            add_le_add ((coordinate 0).trans pointNorm) sourceLine.2.1
          _ ≤ 1 := by linarith
      constructor
      · calc
          |point 1| ≤ |point 1 - center 1| + |center 1| := by
            simpa [sub_add_cancel] using
              abs_add_le (point 1 - center 1) (center 1)
          _ ≤ 6 * delta + 1 / 3 :=
            add_le_add ((coordinate 1).trans pointNorm) sourceLine.2.2
          _ ≤ 1 := by linarith
      · rw [show point 2 = point 2 - center 2 by rw [centerTwo, sub_zero]]
        exact (coordinate 2).trans (pointNorm.trans (by linarith))
    exact
      ⟨Metric.mem_cthickening_of_dist_le
          point center (6 * delta) (tubeAxisLine source)
          centerAxis distance,
        pointBox⟩
  have linearSurjective : Function.Surjective linearMap :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
      (wz1PaperUnitRescalingLinear_injective parent rhoPos)
  intro point pointMem
  have pointNorm :
      ‖point - rescaling center‖ ≤ 6 * delta / 100 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using pointMem
  rcases linearSurjective (point - rescaling center) with
    ⟨vector, vectorEq⟩
  have vectorNorm : ‖vector‖ ≤ 6 * delta := by
    have lower := historicalLinear_lower_bound
      parent rhoPos rhoLeOne vector
    change ‖linearMap vector‖ ≥ ‖vector‖ / 100 at lower
    rw [vectorEq] at lower
    linarith
  have sourcePoint : center + vector ∈ wz1PaperTubeCarrier source := by
    apply ballCarrier
    simpa [Metric.mem_closedBall, dist_eq_norm] using vectorNorm
  refine ⟨center + vector, sourcePoint, ?_⟩
  rw [wz1PaperUnitRescalingMap_add parent rhoPos center vector,
    vectorEq]
  abel

private theorem historical_common_body
    {delta rho : ℝ}
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ 1 / 100)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (parent : Kakeya.DeltaTube rho)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet)
    (eligible :
      ∃ source : Kakeya.DeltaTube delta,
        WZ1PaperTubeInLineClass source ∧
          wz1PaperTubeCarrier source ⊆ convexSet) :
    Nonempty
      (HistoricalCommonBodyData (delta := delta)
        parent rhoPos convexSet) := by
  rcases eligible with ⟨eligibleSource, eligibleLine, eligibleCarrier⟩
  let cropped := convexSet ∩ Kakeya.Streamlined.axisBox 2 2 2
  let rescaling := wz1PaperUnitRescalingMap parent rhoPos
  let linearMap := wz1PaperUnitRescalingLinear parent
  let body := rescaling '' closure cropped
  have croppedConvex : Convex ℝ cropped :=
    convex.inter (Kakeya.Streamlined.convex_axisBox 2 2 2)
  have bodyConvex : Convex ℝ body := by
    intro first firstMem second secondMem
      firstWeight secondWeight firstWeightNonnegative
      secondWeightNonnegative weights
    rcases firstMem with ⟨sourceFirst, sourceFirstMem, rfl⟩
    rcases secondMem with ⟨sourceSecond, sourceSecondMem, rfl⟩
    let sourceCombination :=
      firstWeight • sourceFirst + secondWeight • sourceSecond
    refine
      ⟨sourceCombination,
        croppedConvex.closure sourceFirstMem sourceSecondMem
          firstWeightNonnegative secondWeightNonnegative weights, ?_⟩
    have affineExpansion :
        ∀ source,
          rescaling source = rescaling 0 + linearMap source := by
      intro source
      simpa using
        wz1PaperUnitRescalingMap_add parent rhoPos 0 source
    rw [affineExpansion sourceCombination,
      affineExpansion sourceFirst, affineExpansion sourceSecond]
    dsimp only [sourceCombination]
    rw [map_add, map_smul, map_smul, smul_add, smul_add]
    have translation :
        firstWeight • rescaling 0 + secondWeight • rescaling 0 =
          rescaling 0 := by
      rw [← add_smul, weights, one_smul]
    rw [show
      firstWeight • rescaling 0 +
            firstWeight • linearMap sourceFirst +
          (secondWeight • rescaling 0 +
            secondWeight • linearMap sourceSecond) =
        (firstWeight • rescaling 0 +
          secondWeight • rescaling 0) +
          (firstWeight • linearMap sourceFirst +
            secondWeight • linearMap sourceSecond) by abel,
      translation]
  have axisBoxBounded :
      Bornology.IsBounded (Kakeya.Streamlined.axisBox 2 2 2) := by
    apply
      (isCompact_closedBall
        (0 : Point3) (Real.sqrt 3)).isBounded.subset
    intro point pointMem
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at pointMem
    norm_num at pointMem
    rw [Metric.mem_closedBall, dist_zero_right]
    have normSq := point3_coord_norm_sq point
    have zeroSq : point 0 ^ 2 ≤ 1 := by
      nlinarith [abs_le.mp pointMem.1]
    have oneSq : point 1 ^ 2 ≤ 1 := by
      nlinarith [abs_le.mp pointMem.2.1]
    have twoSq : point 2 ^ 2 ≤ 1 := by
      nlinarith [abs_le.mp pointMem.2.2]
    have normSqBound : ‖point‖ ^ 2 ≤ 3 := by
      rw [normSq]
      linarith
    nlinarith [norm_nonneg point, Real.sqrt_nonneg 3,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have croppedBounded : Bornology.IsBounded cropped :=
    axisBoxBounded.subset fun _ pointMem => pointMem.2
  have closureCompact : IsCompact (closure cropped) :=
    Metric.isCompact_of_isClosed_isBounded
      isClosed_closure croppedBounded.closure
  have rescalingContinuous : Continuous rescaling := by
    have functionEq :
        rescaling = fun point => rescaling 0 + linearMap point := by
      funext point
      simpa using wz1PaperUnitRescalingMap_add parent rhoPos 0 point
    rw [functionEq]
    exact continuous_const.add
      (LinearMap.continuous_of_finiteDimensional linearMap)
  have bodyCompact : IsCompact body :=
    closureCompact.image rescalingContinuous
  have carrierCropped :
      ∀ source : Kakeya.DeltaTube delta,
        WZ1PaperTubeInLineClass source →
        wz1PaperTubeCarrier source ⊆ convexSet →
          wz1PaperTubeCarrier source ⊆ cropped := by
    intro source _ sourceCarrier point pointMem
    exact ⟨sourceCarrier pointMem, pointMem.2⟩
  have ballBody :
      Metric.closedBall
          (rescaling (wz1TubeAxisZeroPoint eligibleSource))
          (6 * delta / 100) ⊆ body := by
    refine
      (historical_image_interior_ball deltaPos deltaSmall rhoPos rhoLeOne
        parent eligibleSource eligibleLine).trans ?_
    rintro point ⟨sourcePoint, sourcePointMem, rfl⟩
    exact
      ⟨sourcePoint,
        subset_closure
          (carrierCropped eligibleSource eligibleLine eligibleCarrier
            sourcePointMem),
        rfl⟩
  have bodyInterior : (interior body).Nonempty := by
    let center := rescaling (wz1TubeAxisZeroPoint eligibleSource)
    let radius := 6 * delta / 100
    have ballInterior :
        Metric.ball center radius ⊆
          interior (Metric.closedBall center radius) :=
      interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
    exact
      ⟨center,
        interior_mono ballBody
          (ballInterior (Metric.mem_ball_self (by positivity)))⟩
  have closureMeasurable : MeasurableSet (closure cropped) :=
    isClosed_closure.measurableSet
  have closureSubset : closure cropped ⊆ closure convexSet :=
    closure_mono fun _ pointMem => pointMem.1
  have closureVolume : volume (closure cropped) ≤ volume convexSet := by
    calc
      volume (closure cropped) ≤ volume (closure convexSet) :=
        measure_mono closureSubset
      _ = volume convexSet :=
        measure_closure_of_null_frontier
          (Convex.addHaar_frontier volume convex)
  have bodyVolume :
      volume body ≤
        ENNReal.ofReal ((1 / (100 * rho)) ^ 2) *
          volume convexSet := by
    rw [wz1PaperUnitRescalingMap_volume
      parent rhoPos (closure cropped) closureMeasurable]
    gcongr
  refine
    ⟨{
      body := body
      convex_body := ⟨bodyConvex, bodyCompact, bodyInterior⟩
      volume_le := bodyVolume
      source_image_subset := ?_
      source_center_mem := ?_ }⟩
  · intro source sourceLine sourceCarrier point pointMem
    rcases pointMem with ⟨sourcePoint, sourcePointMem, rfl⟩
    exact
      ⟨sourcePoint,
        subset_closure
          (carrierCropped source sourceLine sourceCarrier sourcePointMem),
        rfl⟩
  · intro source sourceLine sourceCarrier
    have zeroAxis :
        wz1TubeAxisZeroPoint source ∈ tubeAxisLine source :=
      wz1TubeAxisZeroPoint_mem_axis source
    have zeroTwo :
        wz1TubeAxisZeroPoint source 2 = 0 :=
      wz1TubeAxisZeroPoint_coord_two source sourceLine.vertical
    have zeroCarrier :
        wz1TubeAxisZeroPoint source ∈ wz1PaperTubeCarrier source := by
      refine
        ⟨Metric.mem_cthickening_of_dist_le
            _ _ (6 * delta) _ zeroAxis (by simp; positivity), ?_⟩
      simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq]
      norm_num
      exact
        ⟨sourceLine.2.1.trans (by norm_num),
          sourceLine.2.2.trans (by norm_num),
          by rw [zeroTwo]; norm_num⟩
    exact
      ⟨wz1TubeAxisZeroPoint source,
        subset_closure
          (carrierCropped source sourceLine sourceCarrier zeroCarrier),
        rfl⟩

private theorem historical_subunit_carrier_homothetic_containment
    {delta rho : ℝ}
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ 1 / 100)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (parent : Kakeya.DeltaTube rho)
    (source : Kakeya.DeltaTube delta)
    (target : Kakeya.DeltaTube (delta / rho))
    (sourceLine : WZ1PaperTubeInLineClass source)
    (targetLine : WZ1PaperTubeInLineClass target)
    (covered : WZ2PaperDilatedTubeCovers 2 source parent)
    (axis :
      tubeAxisLine target =
        wz1PaperUnitRescalingMap parent rhoPos ''
          tubeAxisLine source) :
    wz1PaperTubeCarrier target ⊆
      AffineMap.homothety
          (wz1PaperUnitRescalingMap parent rhoPos
            (wz1TubeAxisZeroPoint source))
          (200 : ℝ) ''
        (wz1PaperUnitRescalingMap parent rhoPos ''
          wz1PaperTubeCarrier source) := by
  let image := wz1PaperUnitRescalingMap parent rhoPos
  let linearMap := wz1PaperUnitRescalingLinear parent
  let inverseMap := historicalInverseLinear parent
  let sourceZero := wz1TubeAxisZeroPoint source
  let parentZero := wz1TubeAxisZeroPoint parent
  let imageZero := image sourceZero
  intro targetPoint targetPointMem
  rcases
      exists_dist_le_of_mem_cthickening_closed
        (isClosed_tubeAxisLine target)
        (by positivity : 0 ≤ 6 * (delta / rho))
        targetPointMem.1
    with ⟨nearAxis, nearAxisMem, targetNearAxis⟩
  let targetAxisPoint :=
    wz1PaperAxisPointAtHeight target (targetPoint 2)
  have targetAxisMem : targetAxisPoint ∈ tubeAxisLine target :=
    wz1PaperAxisPointAtHeight_mem_axis target (targetPoint 2)
  have targetAxisTwo :
      targetAxisPoint (2 : Fin 3) = targetPoint 2 :=
    wz1PaperAxisPointAtHeight_coord_two targetLine (targetPoint 2)
  have targetAxisDistance :
      dist targetAxisPoint targetPoint ≤ 12 * (delta / rho) := by
    exact
      (wz1Paper_axisPointAtHeight_dist_point_le_two_mul
        targetLine targetPoint nearAxis nearAxisMem).trans <| by
          nlinarith
  have targetAxisImage :
      targetAxisPoint ∈ image '' tubeAxisLine source := by
    rw [← axis]
    exact targetAxisMem
  rcases targetAxisImage with
    ⟨sourceAxisPoint, sourceAxisMem, sourceAxisImage⟩
  let shrunkPoint :=
    imageZero + (1 / 200 : ℝ) • (targetPoint - imageZero)
  let sourcePoint :=
    sourceZero + inverseMap (shrunkPoint - imageZero)
  have imageSourcePoint : image sourcePoint = shrunkPoint := by
    have difference :
        image sourcePoint - imageZero =
          linearMap (sourcePoint - sourceZero) :=
      wz1PaperUnitRescalingMap_sub parent rhoPos sourcePoint sourceZero
    have linear :
        linearMap (sourcePoint - sourceZero) =
          shrunkPoint - imageZero := by
      simpa [sourcePoint] using
        historicalInverseLinear_right parent rhoPos
          (shrunkPoint - imageZero)
    calc
      image sourcePoint =
          (image sourcePoint - imageZero) + imageZero := by abel
      _ = (shrunkPoint - imageZero) + imageZero := by
        rw [difference, linear]
      _ = shrunkPoint := by abel
  let sourceAxisShrunk :=
    sourceZero + (1 / 200 : ℝ) • (sourceAxisPoint - sourceZero)
  have sourceAxisShrunkMem : sourceAxisShrunk ∈ tubeAxisLine source :=
    wz1TubeAxisLine_smul_about_zero_point
      source sourceLine.vertical sourceAxisMem (1 / 200 : ℝ)
  have imageSourceAxisShrunk :
      image sourceAxisShrunk - imageZero =
        (1 / 200 : ℝ) • (targetAxisPoint - imageZero) := by
    have mapIdentity :=
      wz1PaperUnitRescalingMap_smul_about_zero_point
        parent rhoPos sourceAxisPoint (1 / 200 : ℝ)
        (source := source)
    change
      image sourceAxisShrunk =
        imageZero +
          (1 / 200 : ℝ) •
            (image sourceAxisPoint - imageZero) at mapIdentity
    rw [sourceAxisImage] at mapIdentity
    rw [mapIdentity]
    abel
  have targetDifferenceTwo :
      (targetPoint - targetAxisPoint) (2 : Fin 3) = 0 := by
    simp [PiLp.sub_apply, targetAxisTwo]
  have sourceAxisDistance :
      ‖sourcePoint - sourceAxisShrunk‖ ≤ 6 * delta := by
    have inverseSub :
        ∀ first second,
          inverseMap first - inverseMap second =
            inverseMap (first - second) := by
      intro first second
      exact (map_sub inverseMap first second).symm
    have difference :
        sourcePoint - sourceAxisShrunk =
          inverseMap
            ((1 / 200 : ℝ) •
              (targetPoint - targetAxisPoint)) := by
      have sourcePointDifference :
          sourcePoint - sourceZero =
            inverseMap (shrunkPoint - imageZero) := by
        simp [sourcePoint]
      have sourceAxisDifference :
          sourceAxisShrunk - sourceZero =
            inverseMap (image sourceAxisShrunk - imageZero) := by
        have mapDifference :
            image sourceAxisShrunk - imageZero =
              linearMap (sourceAxisShrunk - sourceZero) :=
          wz1PaperUnitRescalingMap_sub
            parent rhoPos sourceAxisShrunk sourceZero
        rw [mapDifference]
        exact
          (historicalInverseLinear_left parent rhoPos
            (sourceAxisShrunk - sourceZero)).symm
      rw [show
        sourcePoint - sourceAxisShrunk =
          (sourcePoint - sourceZero) -
            (sourceAxisShrunk - sourceZero) by abel,
        sourcePointDifference, sourceAxisDifference, inverseSub]
      have shrunkDifference :
          shrunkPoint - image sourceAxisShrunk =
            (1 / 200 : ℝ) •
              (targetPoint - targetAxisPoint) := by
        rw [show
          shrunkPoint - image sourceAxisShrunk =
            (shrunkPoint - imageZero) -
              (image sourceAxisShrunk - imageZero) by abel,
          imageSourceAxisShrunk]
        dsimp only [shrunkPoint]
        module
      rw [show
        (shrunkPoint - imageZero) -
            (image sourceAxisShrunk - imageZero) =
          shrunkPoint - image sourceAxisShrunk by abel,
        shrunkDifference]
    rw [difference,
      historicalInverseLinear_norm_of_coord_two_zero
        parent rhoPos _ (by
          simp [PiLp.smul_apply, targetDifferenceTwo])]
    rw [norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 200)]
    have distanceNorm :
        ‖targetPoint - targetAxisPoint‖ ≤ 12 * (delta / rho) := by
      simpa [dist_eq_norm, norm_sub_rev] using targetAxisDistance
    calc
      (100 * rho) * ((1 / 200) * ‖targetPoint - targetAxisPoint‖)
          ≤ (100 * rho) * ((1 / 200) * (12 * (delta / rho))) := by
        gcongr
      _ = 6 * delta := by
        field_simp [rhoPos.ne']
        ring
  have sourceAxisParameter :
      ∃ parameter : ℝ,
        sourceAxisPoint - sourceZero =
          parameter • wz1PaperDirection source := by
    rw [tubeAxisLine_eq_affineSpan source sourceLine.vertical]
      at sourceAxisMem
    rcases sourceAxisMem with ⟨parameter, parameterEq⟩
    refine ⟨parameter, ?_⟩
    rw [parameterEq]
    abel
  rcases sourceAxisParameter with ⟨parameter, parameterEq⟩
  have imageZeroBound : |imageZero 2| ≤ rho := by
    rw [wz1PaperUnitRescalingMap_coord2]
    have innerBound :=
      abs_real_inner_le_norm
        (sourceZero - parentZero) (wz1PaperDirection parent)
    rw [wz1PaperDirection_norm parent, mul_one, ← dist_eq_norm]
      at innerBound
    exact innerBound.trans covered.components.1
  have parameterCoefficient :
      (image sourceAxisPoint - imageZero) 2 =
        parameter *
          inner ℝ
            (wz1PaperDirection source)
            (wz1PaperDirection parent) := by
    rw [wz1PaperUnitRescalingMap_sub, parameterEq, map_smul,
      PiLp.smul_apply, smul_eq_mul,
      wz1PaperUnitRescalingLinear_coord2]
  have targetPointTwo : |targetPoint 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using targetPointMem.2.2.2
  have parameterAbs : |parameter| ≤ 4 := by
    have coefficientPositive :
        0 <
          inner ℝ
            (wz1PaperDirection source)
            (wz1PaperDirection parent) := by
      linarith [covered.inner_direction_ge_half rhoLeOne]
    have productBound :
        |parameter| *
            inner ℝ
              (wz1PaperDirection source)
              (wz1PaperDirection parent) ≤
          2 := by
      rw [← abs_of_pos coefficientPositive, ← abs_mul,
        ← parameterCoefficient, sourceAxisImage]
      exact
        (abs_sub _ _).trans <| by
          calc
            |targetAxisPoint 2| + |imageZero 2|
                = |targetPoint 2| + |imageZero 2| := by
                  rw [targetAxisTwo]
            _ ≤ 1 + rho := add_le_add targetPointTwo imageZeroBound
            _ ≤ 2 := by linarith
    nlinarith [covered.inner_direction_ge_half rhoLeOne]
  have sourceAxisShrunkNorm :
      ‖sourceAxisShrunk - sourceZero‖ ≤ 1 / 50 := by
    rw [show
      sourceAxisShrunk - sourceZero =
        (1 / 200 : ℝ) •
          (sourceAxisPoint - sourceZero) by simp [sourceAxisShrunk],
      parameterEq, smul_smul, norm_smul,
      wz1PaperDirection_norm source, mul_one]
    simp only [Real.norm_eq_abs]
    norm_num
    linarith
  have sourcePointNorm :
      ‖sourcePoint - sourceZero‖ ≤ 2 / 25 := by
    rw [show
      sourcePoint - sourceZero =
        (sourcePoint - sourceAxisShrunk) +
          (sourceAxisShrunk - sourceZero) by abel]
    calc
      ‖(sourcePoint - sourceAxisShrunk) +
          (sourceAxisShrunk - sourceZero)‖ ≤
          ‖sourcePoint - sourceAxisShrunk‖ +
            ‖sourceAxisShrunk - sourceZero‖ :=
        norm_add_le _ _
      _ ≤ 6 * delta + 1 / 50 := by gcongr
      _ ≤ 2 / 25 := by linarith
  have sourcePointBox :
      sourcePoint ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq]
    norm_num
    have coordinate :
        ∀ index : Fin 3,
          |sourcePoint index - sourceZero index| ≤
            ‖sourcePoint - sourceZero‖ := by
      intro index
      simpa [dist_eq_norm] using
        abs_coord_sub_le_dist (x := sourcePoint) (y := sourceZero) index
    have sourceZeroTwo :
        sourceZero (2 : Fin 3) = 0 :=
      wz1TubeAxisZeroPoint_coord_two source sourceLine.vertical
    constructor
    · calc
        |sourcePoint 0| ≤
            |sourcePoint 0 - sourceZero 0| + |sourceZero 0| := by
          simpa [sub_add_cancel] using
            abs_add_le (sourcePoint 0 - sourceZero 0) (sourceZero 0)
        _ ≤ 2 / 25 + 1 / 3 :=
          add_le_add ((coordinate 0).trans sourcePointNorm) sourceLine.2.1
        _ ≤ 1 := by norm_num
    constructor
    · calc
        |sourcePoint 1| ≤
            |sourcePoint 1 - sourceZero 1| + |sourceZero 1| := by
          simpa [sub_add_cancel] using
            abs_add_le (sourcePoint 1 - sourceZero 1) (sourceZero 1)
        _ ≤ 2 / 25 + 1 / 3 :=
          add_le_add ((coordinate 1).trans sourcePointNorm) sourceLine.2.2
        _ ≤ 1 := by norm_num
    · rw [show sourcePoint 2 =
          sourcePoint 2 - sourceZero 2 by rw [sourceZeroTwo, sub_zero]]
      exact (coordinate 2).trans (sourcePointNorm.trans (by norm_num))
  have sourcePointCarrier :
      sourcePoint ∈ wz1PaperTubeCarrier source :=
    ⟨Metric.mem_cthickening_of_dist_le
        sourcePoint sourceAxisShrunk (6 * delta) (tubeAxisLine source)
        sourceAxisShrunkMem
        (by simpa [dist_eq_norm] using sourceAxisDistance),
      sourcePointBox⟩
  refine
    ⟨image sourcePoint,
      ⟨sourcePoint, sourcePointCarrier, rfl⟩, ?_⟩
  rw [imageSourcePoint, AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  dsimp only [shrunkPoint]
  module

private theorem historical_john_homothetic_envelope_point
    {center : Point3}
    {linear : Point3 ≃ₗ[ℝ] Point3}
    {sourcePoint homothetyCenter : Point3}
    (sourceMem :
      sourcePoint ∈ JohnEllipsoid.ellipsoid center linear)
    (centerMem :
      homothetyCenter ∈ JohnEllipsoid.ellipsoid center linear) :
    AffineMap.homothety homothetyCenter (200 : ℝ) sourcePoint ∈
      AffineMap.homothety center (399 : ℝ) ''
        JohnEllipsoid.ellipsoid center linear := by
  have sourceNorm :
      ‖linear.symm (sourcePoint - center)‖ ≤ 1 :=
    (JohnEllipsoid.ellipsoid_mem_iff center linear sourcePoint).mp
      sourceMem
  have centerNorm :
      ‖linear.symm (homothetyCenter - center)‖ ≤ 1 :=
    (JohnEllipsoid.ellipsoid_mem_iff center linear homothetyCenter).mp
      centerMem
  let sourceVector := linear.symm (sourcePoint - center)
  let centerVector := linear.symm (homothetyCenter - center)
  let envelopePoint : Point3 :=
    center +
      (1 / 399 : ℝ) •
        ((200 : ℝ) • (sourcePoint - center) -
          (199 : ℝ) • (homothetyCenter - center))
  have envelopeCoordinates :
      linear.symm (envelopePoint - center) =
        (1 / 399 : ℝ) •
          ((200 : ℝ) • sourceVector -
            (199 : ℝ) • centerVector) := by
    simp [envelopePoint, sourceVector, centerVector, map_sub, map_smul]
  have combination :
      ‖(200 : ℝ) • sourceVector -
          (199 : ℝ) • centerVector‖ ≤ 399 := by
    calc
      ‖(200 : ℝ) • sourceVector -
          (199 : ℝ) • centerVector‖ ≤
          ‖(200 : ℝ) • sourceVector‖ +
            ‖(199 : ℝ) • centerVector‖ :=
        norm_sub_le _ _
      _ = (200 : ℝ) * ‖sourceVector‖ +
          (199 : ℝ) * ‖centerVector‖ := by
        simp [norm_smul]
      _ ≤ (200 : ℝ) * 1 + (199 : ℝ) * 1 := by gcongr
      _ = 399 := by norm_num
  have envelopePointMem :
      envelopePoint ∈ JohnEllipsoid.ellipsoid center linear := by
    rw [JohnEllipsoid.ellipsoid_mem_iff, envelopeCoordinates]
    calc
      ‖(1 / 399 : ℝ) •
          ((200 : ℝ) • sourceVector -
            (199 : ℝ) • centerVector)‖ =
          (1 / 399 : ℝ) *
            ‖(200 : ℝ) • sourceVector -
              (199 : ℝ) • centerVector‖ := by
        simp [norm_smul]
      _ ≤ (1 / 399 : ℝ) * 399 := by gcongr
      _ = 1 := by norm_num
  have scaledDifference :
      (399 : ℝ) • (envelopePoint - center) =
        (200 : ℝ) • (sourcePoint - center) -
          (199 : ℝ) • (homothetyCenter - center) := by
    simp [envelopePoint, smul_sub, smul_smul]
  refine ⟨envelopePoint, envelopePointMem, ?_⟩
  rw [AffineMap.homothety_apply, AffineMap.homothety_apply]
  simp only [vsub_eq_sub, vadd_eq_add]
  rw [scaledDifference]
  module

private theorem historical_john_homothetic_envelope
    (convexBody : Set Point3)
    (body : JohnEllipsoid.IsConvexBody convexBody) :
    ∃ envelope : Set Point3,
      Convex ℝ envelope ∧
      volume envelope ≤
        (1715072373 : ENNReal) * volume convexBody ∧
      ∀ point ∈ convexBody,
        AffineMap.homothety point (200 : ℝ) '' convexBody ⊆
          envelope := by
  let center : Point3 :=
    JohnEllipsoid.IsConvexBody.outerJohnEllipsoidCenter body
  let linear : Point3 ≃ₗ[ℝ] Point3 :=
    JohnEllipsoid.IsConvexBody.outerJohnEllipsoidMap body
  let ellipsoid : Set Point3 :=
    JohnEllipsoid.IsConvexBody.outerJohnEllipsoid body
  let envelope : Set Point3 :=
    AffineMap.homothety center (399 : ℝ) '' ellipsoid
  refine ⟨envelope, ?_, ?_, ?_⟩
  · exact
      (JohnEllipsoid.ellipsoid_convex center linear).affine_image
        (AffineMap.homothety center (399 : ℝ))
  · have inner :
        AffineMap.homothety center ((3 : ℝ)⁻¹) '' ellipsoid ⊆
          convexBody :=
      JohnEllipsoid.IsConvexBody.homothety_subset_outerJohnEllipsoid_main
        body
    have innerVolume :
        ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid ≤
          volume convexBody := by
      calc
        ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid =
            volume
              (AffineMap.homothety center ((3 : ℝ)⁻¹) '' ellipsoid) := by
          rw [JohnEllipsoid.volume_homothety]
          norm_num
        _ ≤ volume convexBody := measure_mono inner
    have ellipsoidVolume :
        volume ellipsoid ≤ (27 : ENNReal) * volume convexBody := by
      have twentySeven :
          (27 : ENNReal) = ENNReal.ofReal (27 : ℝ) := by
        norm_cast
      have cancel :
          (27 : ENNReal) * ENNReal.ofReal (1 / 27 : ℝ) = 1 := by
        rw [twentySeven, ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      calc
        volume ellipsoid =
            (27 : ENNReal) *
              (ENNReal.ofReal (1 / 27 : ℝ) * volume ellipsoid) := by
          rw [← mul_assoc, cancel, one_mul]
        _ ≤ (27 : ENNReal) * volume convexBody := by gcongr
    rw [JohnEllipsoid.volume_homothety]
    norm_num
    calc
      (63521199 : ENNReal) * volume ellipsoid ≤
          (63521199 : ENNReal) *
            ((27 : ENNReal) * volume convexBody) := by gcongr
      _ = (1715072373 : ENNReal) * volume convexBody := by
        ring
  · intro homothetyCenter centerMem point pointMem
    rcases pointMem with ⟨sourcePoint, sourceMem, rfl⟩
    have outer :=
      JohnEllipsoid.IsConvexBody.outerJohnEllipsoid_spec body
    exact
      historical_john_homothetic_envelope_point
        (outer.1 sourceMem) (outer.1 centerMem)

private theorem historical_jacobian_le_negative_two
    {rho : ℝ} (rhoPos : 0 < rho) :
    ENNReal.ofReal ((1 / (100 * rho)) ^ 2) ≤
      Kakeya.realRpowENN rho (-2) := by
  unfold Kakeya.realRpowENN
  apply ENNReal.ofReal_mono
  have power :
      Real.rpow rho (-2) = (rho ^ 2)⁻¹ := by
    simpa [Real.rpow_two] using Real.rpow_neg rhoPos.le (2 : ℝ)
  rw [power]
  field_simp [rhoPos.ne']
  nlinarith [sq_nonneg rho]

private theorem historical_subunit_carrier_envelope
    {delta rho : ℝ}
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ 1 / 100)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    (parent : Kakeya.DeltaTube rho)
    (convexSet : Set Point3)
    (convex : Convex ℝ convexSet) :
    ∃ targetConvexSet : Set Point3,
      Convex ℝ targetConvexSet ∧
      volume targetConvexSet ≤
        ((1715072373 : ENNReal) *
          Kakeya.realRpowENN rho (-2)) *
          volume convexSet ∧
      ∀ (source : Kakeya.DeltaTube delta)
        (target : Kakeya.DeltaTube (delta / rho)),
        WZ1PaperTubeInLineClass source →
        WZ1PaperTubeInLineClass target →
        WZ2PaperDilatedTubeCovers 2 source parent →
        tubeAxisLine target =
            wz1PaperUnitRescalingMap parent rhoPos ''
              tubeAxisLine source →
        wz1PaperTubeCarrier source ⊆ convexSet →
          wz1PaperTubeCarrier target ⊆ targetConvexSet := by
  by_cases eligible :
      ∃ source : Kakeya.DeltaTube delta,
        WZ1PaperTubeInLineClass source ∧
          wz1PaperTubeCarrier source ⊆ convexSet
  · rcases
        historical_common_body deltaPos deltaSmall rhoPos rhoLeOne
          parent convexSet convex eligible
      with ⟨bodyData⟩
    rcases
        historical_john_homothetic_envelope
          bodyData.body bodyData.convex_body
      with ⟨envelope, envelopeConvex, envelopeVolume,
        envelopeContains⟩
    refine ⟨envelope, envelopeConvex, ?_, ?_⟩
    · calc
        volume envelope ≤
            (1715072373 : ENNReal) * volume bodyData.body :=
          envelopeVolume
        _ ≤
            (1715072373 : ENNReal) *
              (ENNReal.ofReal ((1 / (100 * rho)) ^ 2) *
                volume convexSet) := by
          gcongr
          exact bodyData.volume_le
        _ ≤
            ((1715072373 : ENNReal) *
              Kakeya.realRpowENN rho (-2)) *
                volume convexSet := by
          rw [mul_assoc]
          gcongr
          exact historical_jacobian_le_negative_two rhoPos
    · intro source target sourceLine targetLine covered axis sourceSubset
      have carrierHomothetic :=
        historical_subunit_carrier_homothetic_containment
          deltaPos deltaSmall rhoPos rhoLeOne parent source target
          sourceLine targetLine covered axis
      let imageCenter :=
        wz1PaperUnitRescalingMap parent rhoPos
          (wz1TubeAxisZeroPoint source)
      let imageCarrier :=
        wz1PaperUnitRescalingMap parent rhoPos ''
          wz1PaperTubeCarrier source
      exact
        carrierHomothetic.trans <|
          (Set.image_mono
            (bodyData.source_image_subset source sourceLine sourceSubset)).trans <|
              envelopeContains imageCenter
                (bodyData.source_center_mem source sourceLine sourceSubset)
  · refine ⟨∅, convex_empty, by simp, ?_⟩
    intro source _ sourceLine _ _ _ sourceSubset
    exact (eligible ⟨source, sourceLine, sourceSubset⟩).elim

private theorem historical_full_fiber_cwa
    {delta rho : ℝ}
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ 1 / 100)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (fineLine : WZ1PaperIsLineClass fine)
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperLiteralDilatedPartitioningCover fine coarse)
    (parent : Fin coarse.card)
    {C : ENNReal}
    (fiber :
      WZ2PaperLiteralFullFiberRescaledFamilyData
        cover parent rhoPos C) :
    WZ2PaperConvexWolffBound
      (cover.toWZ2PaperDilatedTubeCover.fiberSubfamily parent).family
      (((1715072373 : ENNReal) *
        Kakeya.realRpowENN rho (-2)) * C) := by
  let assigned := fiber.toAssigned
  let sourceFamily :=
    (cover.toWZ2PaperDilatedTubeCover.fiberSubfamily parent).family
  have sourceLine : WZ1PaperIsLineClass sourceFamily :=
    fineLine.subfamily
      (cover.toWZ2PaperDilatedTubeCover.fiberSubfamily parent)
  intro convexSet convex
  rcases
      historical_subunit_carrier_envelope
        deltaPos deltaSmall rhoPos rhoLeOne
        (coarse.tube parent) convexSet convex
    with ⟨targetSet, targetConvex, targetVolume, targetEnvelope⟩
  let equivalence := assigned.targetEquivFiber
  let sourceBody := wz1PaperBodyFamily sourceFamily
  let targetBody := wz1PaperBodyFamily assigned.targetFamily
  let sourceContained := sourceBody.containedIndices convexSet
  let targetContained := targetBody.containedIndices targetSet
  have indexMap :
      ∀ sourceIndex : Fin sourceFamily.card,
        sourceIndex ∈ sourceContained →
          equivalence.symm sourceIndex ∈ targetContained := by
    intro sourceIndex sourceMem
    let targetIndex := equivalence.symm sourceIndex
    have ambient :
        (cover.toWZ2PaperDilatedTubeCover.fiberSubfamily parent).embedding
            sourceIndex =
          assigned.sourceIndex targetIndex := by
      have equality := assigned.targetEquivFiber_ambient targetIndex
      rw [equivalence.apply_symm_apply sourceIndex] at equality
      exact equality
    have parentEq :
        cover.parent
            ((cover.toWZ2PaperDilatedTubeCover.fiberSubfamily parent).embedding
              sourceIndex) =
          parent := by
      have member :=
        Finset.orderEmbOfFin_mem
          (cover.toWZ2PaperDilatedTubeCover.fiberIndices parent)
          rfl sourceIndex
      change
        cover.parent
            ((cover.toWZ2PaperDilatedTubeCover.fiberIndices parent)
              |>.orderEmbOfFin rfl sourceIndex) =
          parent
      exact (Finset.mem_filter.mp member).2
    apply Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
    apply
      targetEnvelope
        (sourceFamily.tube sourceIndex)
        (assigned.targetFamily.tube targetIndex)
        (sourceLine sourceIndex)
        (assigned.target_line_class targetIndex)
    · rw [
        (cover.toWZ2PaperDilatedTubeCover.fiberSubfamily parent).tube_eq]
      simpa [parentEq] using
        cover.parent_covers
          ((cover.toWZ2PaperDilatedTubeCover.fiberSubfamily parent).embedding
            sourceIndex)
    · calc
        tubeAxisLine (assigned.targetFamily.tube targetIndex) =
            wz1PaperUnitRescalingMap (coarse.tube parent) rhoPos ''
              tubeAxisLine
                (fine.tube (assigned.sourceIndex targetIndex)) :=
          assigned.target_axis targetIndex
        _ =
            wz1PaperUnitRescalingMap (coarse.tube parent) rhoPos ''
              tubeAxisLine (sourceFamily.tube sourceIndex) := by
          rw [
            (cover.toWZ2PaperDilatedTubeCover.fiberSubfamily parent).tube_eq,
            ambient]
    · exact
        Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mp sourceMem
  have imageSubset :
      Finset.image equivalence.symm sourceContained ⊆
        targetContained := by
    intro targetIndex targetMem
    rcases Finset.mem_image.mp targetMem with
      ⟨sourceIndex, sourceMem, rfl⟩
    exact indexMap sourceIndex sourceMem
  have cardinality :
      (sourceContained.card : ENNReal) ≤
        (targetContained.card : ENNReal) := by
    exact_mod_cast
      (show sourceContained.card ≤ targetContained.card by
        rw [← Finset.card_image_of_injective
          sourceContained equivalence.symm.injective]
        exact Finset.card_le_card imageSubset)
  calc
    sourceBody.containedCount convexSet =
        (sourceContained.card : ENNReal) := rfl
    _ ≤ (targetContained.card : ENNReal) := cardinality
    _ = targetBody.containedCount targetSet := rfl
    _ ≤ C * volume targetSet * assigned.targetFamily.enncard :=
      assigned.convex_wolff targetSet targetConvex
    _ ≤
        C *
          (((1715072373 : ENNReal) *
            Kakeya.realRpowENN rho (-2)) * volume convexSet) *
          assigned.targetFamily.enncard := by
      gcongr
    _ =
        (((1715072373 : ENNReal) *
          Kakeya.realRpowENN rho (-2)) * C) *
          volume convexSet * sourceFamily.enncard := by
      rw [assigned.targetFamily_enncard_eq_fiber]
      ring

private theorem historical_dilated_full_fiber_assembly
    {factor delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover factor fine coarse)
    {C : ENNReal}
    (fibers :
      ∀ parent : Fin coarse.card,
        WZ2PaperConvexWolffBound
          (cover.fiberSubfamily parent).family C) :
    WZ2PaperConvexWolffBound fine C := by
  intro convexSet convex
  let predicate : Fin fine.card → Prop :=
    fun index =>
      wz1PaperTubeCarrier (fine.tube index) ⊆ convexSet
  let contained : Finset (Fin fine.card) :=
    Finset.univ.filter predicate
  have fiberCount :
      ∀ parent : Fin coarse.card,
        (wz1PaperBodyFamily
          (cover.fiberSubfamily parent).family).containedCount convexSet =
          ((contained ∩ cover.fiberIndices parent).card : ENNReal) := by
    intro parent
    let indices := cover.fiberIndices parent
    let fiber := cover.fiberSubfamily parent
    let equivalence : Fin indices.card ≃ indices :=
      (indices.orderIsoOfFin rfl).toEquiv
    let embedding : Fin indices.card → Fin fine.card :=
      fun index => (equivalence index : Fin fine.card)
    let fiberContained : Finset (Fin indices.card) :=
      Finset.univ.filter fun index => predicate (embedding index)
    let ambientContained : Finset (Fin fine.card) :=
      indices.filter predicate
    have embeddingInjective : Function.Injective embedding := by
      intro first second equality
      exact equivalence.injective (Subtype.ext equality)
    have imageEquality :
        fiberContained.image embedding = ambientContained := by
      ext ambient
      simp only [fiberContained, ambientContained,
        Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨index, indexMem, rfl⟩
        exact ⟨(equivalence index).property, indexMem⟩
      · rintro ⟨indexMem, predicateMem⟩
        let member : indices := ⟨ambient, indexMem⟩
        let index := equivalence.symm member
        have indexEquality : embedding index = ambient :=
          congrArg Subtype.val (equivalence.apply_symm_apply member)
        exact ⟨index, by simpa [indexEquality] using predicateMem,
          indexEquality⟩
    have cardEquality :
        fiberContained.card = ambientContained.card := by
      rw [← Finset.card_image_of_injective
        fiberContained embeddingInjective, imageEquality]
    have ambientEquality :
        ambientContained = contained ∩ indices := by
      ext index
      simp [ambientContained, contained, predicate, and_comm]
    have countEquality :
        (wz1PaperBodyFamily fiber.family).containedCount convexSet =
          (fiberContained.card : ENNReal) := by
      simp [Kakeya.Streamlined.BodyFamily.containedCount,
        Kakeya.Streamlined.BodyFamily.containedIndices,
        fiberContained, embedding, fiber]
      all_goals rfl
    rw [countEquality, cardEquality, ambientEquality]
  have sumContained :
      ∑ parent : Fin coarse.card,
          (wz1PaperBodyFamily
            (cover.fiberSubfamily parent).family).containedCount
              convexSet =
        (contained.card : ENNReal) := by
    have filterEquality :
        ∀ parent : Fin coarse.card,
          contained ∩ cover.fiberIndices parent =
            contained.filter fun source =>
              cover.parent source = parent := by
      intro parent
      ext index
      simp [contained, WZ2PaperDilatedTubeCover.fiberIndices,
        predicate, and_comm]
    have naturalSum :
        ∑ parent ∈ (Finset.univ : Finset (Fin coarse.card)),
            (contained.filter fun source =>
              cover.parent source = parent).card =
          contained.card := by
      simpa [Finset.mem_univ] using
        Finset.sum_card_fiberwise_eq_card_filter
          contained (Finset.univ : Finset (Fin coarse.card))
          cover.parent
    calc
      ∑ parent : Fin coarse.card,
          (wz1PaperBodyFamily
            (cover.fiberSubfamily parent).family).containedCount
              convexSet =
          ∑ parent : Fin coarse.card,
            ((contained ∩ cover.fiberIndices parent).card :
              ENNReal) := by
        apply Finset.sum_congr rfl
        intro parent _
        exact fiberCount parent
      _ =
          ∑ parent ∈ (Finset.univ : Finset (Fin coarse.card)),
            ((contained.filter fun source =>
              cover.parent source = parent).card : ENNReal) := by
        apply Finset.sum_congr rfl
        intro parent _
        rw [filterEquality parent]
      _ = (contained.card : ENNReal) := by
        exact_mod_cast naturalSum
  have sumCardinality :
      ∑ parent : Fin coarse.card,
          (cover.fiberSubfamily parent).family.enncard =
        fine.enncard := by
    change
      (∑ parent : Fin coarse.card,
        ((cover.fiberIndices parent).card : ENNReal)) =
          (fine.card : ENNReal)
    rw [← Nat.cast_sum]
    exact_mod_cast
      ((Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin fine.card))
        (Finset.univ : Finset (Fin coarse.card))
        cover.parent).trans (by simp))
  calc
    (wz1PaperBodyFamily fine).containedCount convexSet =
        (contained.card : ENNReal) := rfl
    _ =
        ∑ parent : Fin coarse.card,
          (wz1PaperBodyFamily
            (cover.fiberSubfamily parent).family).containedCount
              convexSet := sumContained.symm
    _ ≤
        ∑ parent : Fin coarse.card,
          C * volume convexSet *
            (cover.fiberSubfamily parent).family.enncard := by
      exact Finset.sum_le_sum fun parent _ =>
        fibers parent convexSet convex
    _ =
        C * volume convexSet *
          (∑ parent : Fin coarse.card,
            (cover.fiberSubfamily parent).family.enncard) := by
      rw [← Finset.mul_sum]
    _ = C * volume convexSet * fine.enncard := by
      rw [sumCardinality]

/--
The fixed dimension-only coefficient in the direct cropped nearby-scale
top-level CWA bound.
-/
def pureWZ2Prop62PaperNearbyTopLevelConstant : ENNReal :=
  1715072373

theorem pureWZ2Prop62PaperNearbyTopLevelConstant_ne_top :
    pureWZ2Prop62PaperNearbyTopLevelConstant ≠ ⊤ := by
  simp [pureWZ2Prop62PaperNearbyTopLevelConstant]

/--
Directly from cropped nearby-scale CWA with constant `delta⁻loss`, recover
the paper-carrier top-level CWA with constant
`D * delta⁻(3 loss)`.
-/
private theorem wz2_paper_nearby_top_level_power_cwa_of_loss_le_one
    {delta loss : ℝ}
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ 1 / 100)
    (lossPos : 0 < loss)
    (lossLeOne : loss ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (nearbyCWA :
      WZ2PaperCWAAtNearbyScales family
        (Kakeya.realRpowENN delta (-loss))) :
    WZ2PaperConvexWolffBound family
      (pureWZ2Prop62PaperNearbyTopLevelConstant *
        Kakeya.realRpowENN delta (-3 * loss)) := by
  have deltaLeOne : delta ≤ 1 :=
    deltaSmall.trans (by norm_num)
  have requestedLower :
      delta ≤ Real.rpow delta loss := by
    have power :=
      Real.rpow_le_rpow_of_exponent_ge
        deltaPos deltaLeOne lossLeOne
    simpa using power
  have requestedUpper :
      Real.rpow delta loss ≤ 1 :=
    Real.rpow_le_one deltaPos.le deltaLeOne lossPos.le
  let requested : Kakeya.Streamlined.AdmissibleScale delta :=
    ⟨Real.rpow delta loss, requestedLower, requestedUpper⟩
  rcases nearbyCWA.2.2.2 requested with ⟨actual⟩
  have windowProduct :
      Kakeya.realRpowENN delta (-loss) *
          ENNReal.ofReal (Real.rpow delta loss) =
        1 := by
    unfold Kakeya.realRpowENN
    calc
      ENNReal.ofReal (Real.rpow delta (-loss)) *
            ENNReal.ofReal (Real.rpow delta loss) =
          ENNReal.ofReal
            (Real.rpow delta (-loss) * Real.rpow delta loss) :=
        (ENNReal.ofReal_mul
          (Real.rpow_nonneg deltaPos.le (-loss))).symm
      _ = ENNReal.ofReal (Real.rpow delta (-loss + loss)) := by
        congr 1
        exact (Real.rpow_add deltaPos (-loss) loss).symm
      _ = 1 := by norm_num
  have rhoLtOne : actual.rho < 1 := by
    apply ENNReal.ofReal_lt_one.mp
    calc
      ENNReal.ofReal actual.rho <
          Kakeya.realRpowENN delta (-loss) *
            ENNReal.ofReal requested.1 :=
        actual.within_factor
      _ = 1 := by
        simpa [requested] using windowProduct
  have rhoLeOne : actual.rho ≤ 1 := rhoLtOne.le
  have requestedRho :
      Real.rpow delta loss ≤ actual.rho :=
    actual.requested_le
  let assignedCover :=
    actual.scaleData.cover.toWZ2PaperDilatedTubeCover
  have fibers :
      ∀ parent : Fin actual.scaleData.coarse.card,
        WZ2PaperConvexWolffBound
          (assignedCover.fiberSubfamily parent).family
          (((1715072373 : ENNReal) *
              Kakeya.realRpowENN actual.rho (-2)) *
            Kakeya.realRpowENN delta (-loss)) := by
    intro parent
    rcases actual.scaleData.rescaledFiber parent with ⟨fiber⟩
    exact
      historical_full_fiber_cwa
        deltaPos deltaSmall actual.rho_pos rhoLeOne
        nearbyCWA.2.1
        actual.scaleData.cover parent fiber
  have rawTop :
      WZ2PaperConvexWolffBound family
        (((1715072373 : ENNReal) *
            Kakeya.realRpowENN actual.rho (-2)) *
          Kakeya.realRpowENN delta (-loss)) :=
    historical_dilated_full_fiber_assembly assignedCover fibers
  have rhoPower :
      Kakeya.realRpowENN actual.rho (-2) ≤
        Kakeya.realRpowENN delta (-2 * loss) := by
    calc
      Kakeya.realRpowENN actual.rho (-2) ≤
          Kakeya.realRpowENN (Real.rpow delta loss) (-2) :=
        ENNReal.ofReal_mono <|
          Real.rpow_le_rpow_of_nonpos
            (Real.rpow_pos_of_pos deltaPos loss)
            requestedRho (by norm_num)
      _ = Kakeya.realRpowENN delta (-2 * loss) := by
        unfold Kakeya.realRpowENN
        congr 1
        calc
          Real.rpow (Real.rpow delta loss) (-2) =
              Real.rpow delta (loss * (-2)) :=
            (Real.rpow_mul deltaPos.le loss (-2)).symm
          _ = Real.rpow delta (-2 * loss) := by ring_nf
  intro convexSet convex
  calc
    (wz1PaperBodyFamily family).containedCount convexSet ≤
        (((1715072373 : ENNReal) *
            Kakeya.realRpowENN actual.rho (-2)) *
          Kakeya.realRpowENN delta (-loss)) *
          volume convexSet * family.enncard :=
      rawTop convexSet convex
    _ ≤
        (((1715072373 : ENNReal) *
            Kakeya.realRpowENN delta (-2 * loss)) *
          Kakeya.realRpowENN delta (-loss)) *
          volume convexSet * family.enncard := by
      gcongr
    _ =
        (pureWZ2Prop62PaperNearbyTopLevelConstant *
          Kakeya.realRpowENN delta (-3 * loss)) *
          volume convexSet * family.enncard := by
      unfold pureWZ2Prop62PaperNearbyTopLevelConstant
      have powerProduct :
          Kakeya.realRpowENN delta (-2 * loss) *
              Kakeya.realRpowENN delta (-loss) =
            Kakeya.realRpowENN delta (-3 * loss) := by
        unfold Kakeya.realRpowENN
        calc
          ENNReal.ofReal (Real.rpow delta (-2 * loss)) *
                ENNReal.ofReal (Real.rpow delta (-loss)) =
              ENNReal.ofReal
                (Real.rpow delta (-2 * loss) *
                  Real.rpow delta (-loss)) :=
            (ENNReal.ofReal_mul
              (Real.rpow_nonneg deltaPos.le (-2 * loss))).symm
          _ = ENNReal.ofReal
              (Real.rpow delta ((-2 * loss) + (-loss))) := by
            congr 1
            exact
              (Real.rpow_add deltaPos (-2 * loss) (-loss)).symm
          _ = ENNReal.ofReal (Real.rpow delta (-3 * loss)) := by
            congr 2
            ring
      rw [← powerProduct]
      ring

/--
Directly from cropped nearby-scale CWA with constant `delta⁻loss`, recover
the paper-carrier top-level CWA with constant
`D * delta⁻(3 loss)` for every positive loss.

For `loss ≤ 1` this is the nearby-scale geometric argument above.  For
`loss > 1`, the target constant already dominates the elementary
`delta⁻2` bound coming from the uniform volume floor of cropped paper tubes.
-/
theorem wz2_paper_nearby_top_level_power_cwa
    {delta loss : ℝ}
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ 1 / 100)
    (lossPos : 0 < loss)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (nearbyCWA :
      WZ2PaperCWAAtNearbyScales family
        (Kakeya.realRpowENN delta (-loss))) :
    WZ2PaperConvexWolffBound family
      (pureWZ2Prop62PaperNearbyTopLevelConstant *
        Kakeya.realRpowENN delta (-3 * loss)) := by
  by_cases lossLeOne : loss ≤ 1
  · exact
      wz2_paper_nearby_top_level_power_cwa_of_loss_le_one
        deltaPos deltaSmall lossPos lossLeOne nearbyCWA
  · have oneLtLoss : 1 < loss := lt_of_not_ge lossLeOne
    have deltaLeOne : delta ≤ 1 :=
      deltaSmall.trans (by norm_num)
    have deltaSmallTwelve : delta ≤ 1 / 12 :=
      deltaSmall.trans (by norm_num)
    have volumeFloor :
        ∀ index,
          Kakeya.realRpowENN delta 2 ≤
            ((wz1PaperBodyFamily family).body index).volume := by
      intro index
      change
        Kakeya.realRpowENN delta 2 ≤
          volume (wz1PaperTubeCarrier (family.tube index))
      have canonicalLower :
          Kakeya.realRpowENN delta 2 ≤
            Kakeya.deltaTubeVolume delta := by
        simpa [Kakeya.realRpowENN, Real.rpow_two] using
          canonical_volume_lower deltaPos
      exact canonicalLower.trans
        (wz2PaperTubeCarrier_volume_lower
          deltaPos deltaSmallTwelve
          (family.tube index) (nearbyCWA.2.1 index))
    have floorNeZero :
        Kakeya.realRpowENN delta 2 ≠ 0 := by
      simp [Kakeya.realRpowENN, deltaPos.ne']
    have floorNeTop :
        Kakeya.realRpowENN delta 2 ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    have floorCWA :
        WZ2PaperConvexWolffBound family
          (Kakeya.realRpowENN delta 2)⁻¹ :=
      wz2PaperBodyConvexWolffBound_of_volume_floor
        (wz1PaperBodyFamily family)
        (Kakeya.realRpowENN delta 2)
        floorNeZero floorNeTop volumeFloor
    have inverseEq :
        (Kakeya.realRpowENN delta 2)⁻¹ =
          Kakeya.realRpowENN delta (-2) :=
      pure_wz2_realRpowENN_inv deltaPos
    have exponentLe : -3 * loss ≤ (-2 : ℝ) := by
      nlinarith
    have powerLe :
        Kakeya.realRpowENN delta (-2) ≤
          Kakeya.realRpowENN delta (-3 * loss) :=
      pure_wz2_rpowENN_antitone deltaPos deltaLeOne exponentLe
    intro convexSet convex
    calc
      (wz1PaperBodyFamily family).containedCount convexSet ≤
          (Kakeya.realRpowENN delta 2)⁻¹ *
            volume convexSet * family.enncard :=
        floorCWA convexSet convex
      _ =
          Kakeya.realRpowENN delta (-2) *
            volume convexSet * family.enncard := by
        rw [inverseEq]
      _ ≤
          (pureWZ2Prop62PaperNearbyTopLevelConstant *
            Kakeya.realRpowENN delta (-3 * loss)) *
              volume convexSet * family.enncard := by
        gcongr
        calc
          Kakeya.realRpowENN delta (-2) ≤
              Kakeya.realRpowENN delta (-3 * loss) :=
            powerLe
          _ =
              1 * Kakeya.realRpowENN delta (-3 * loss) := by
            rw [one_mul]
          _ ≤
              pureWZ2Prop62PaperNearbyTopLevelConstant *
                Kakeya.realRpowENN delta (-3 * loss) := by
            gcongr
            unfold pureWZ2Prop62PaperNearbyTopLevelConstant
            norm_num

end Kakeya.Assouad

end
