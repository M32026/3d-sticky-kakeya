import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryDistinctToOverlapDistinct
import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryLineConflictPacking
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterEnvelopeConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnisotropicPacking
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.TightDistinctness
import MyLeanRepo.Kakeya.Assouad.WZ1.Factor2Packing

/-!
# Absolute packing of actual parents over one proxy center

At one scheduled scale, orient every actual Definition 2.12 parent toward
the canonical fine representative of its complete fiber.  Parents with the
same quotient center then lie in one fixed five-dimensional anisotropic box:

* the two transverse direction coordinates are `O(r)`;
* the two transverse midpoint coordinates are `O(r)`;
* the longitudinal midpoint coordinate is `O(1)`.

Two oriented parents in the same anisotropic cell force ordinary carrier
containment in a centered double.  Reversal preserves both the carrier and
the midpoint, so the contradiction is with the ordinary essential
distinctness of the original actual parent family, not with volumetric
essential distinctness.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

open Kakeya.Streamlined Metric Set

/-- The dimension-only five-dimensional small-scale packing bound. -/
def pureWZ2Prop62ProxyCenterCopySmallScaleBound : ℕ :=
  ∏ coordinate : Fin 5,
    if coordinate.1 = 4 then 140801 else 4001

/-- The dimension-only six-dimensional large-scale packing bound. -/
def pureWZ2Prop62ProxyCenterCopyLargeScaleBound : ℕ :=
  (2 * 44992 + 1) ^ 3 * (2 * 6400 + 1) ^ 3

/-- One dimension-only bound valid at every scheduled scale. -/
def pureWZ2Prop62ProxyCenterCopyPackingBound : ℕ :=
  pureWZ2Prop62ProxyCenterCopySmallScaleBound +
    pureWZ2Prop62ProxyCenterCopyLargeScaleBound

private def pureWZ2Prop62OrientedActualParent
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount)
    (parent : Fin (schedule.scaleData coordinate).coarse.card) :
    Kakeya.DeltaTube (schedule.actualScale coordinate) :=
  let representative :=
    wz2PaperCanonicalLineTube <|
      fine.tube <|
        schedule.parentRepresentative fineNonempty coordinate parent
  let actual := (schedule.scaleData coordinate).coarse.tube parent
  if ‖representative.direction - actual.direction‖ ≤
      4 * schedule.actualScale coordinate then
    actual
  else
    reverseTube actual

@[simp] private theorem pureWZ2Prop62OrientedActualParent_carrier
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount)
    (parent : Fin (schedule.scaleData coordinate).coarse.card) :
    (pureWZ2Prop62OrientedActualParent
        schedule fineNonempty coordinate parent).carrier =
      ((schedule.scaleData coordinate).coarse.tube parent).carrier := by
  by_cases aligned :
      ‖(wz2PaperCanonicalLineTube
            (fine.tube
              (schedule.parentRepresentative
                fineNonempty coordinate parent))).direction -
          ((schedule.scaleData coordinate).coarse.tube parent).direction‖ ≤
        4 * schedule.actualScale coordinate
  · simp [pureWZ2Prop62OrientedActualParent, aligned]
  · simp only [pureWZ2Prop62OrientedActualParent, if_neg aligned]
    exact reverseTube_carrier _

@[simp] private theorem pureWZ2Prop62OrientedActualParent_midpoint
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount)
    (parent : Fin (schedule.scaleData coordinate).coarse.card) :
    wz2PaperTubeMidpoint
        (pureWZ2Prop62OrientedActualParent
          schedule fineNonempty coordinate parent) =
      wz2PaperTubeMidpoint
        ((schedule.scaleData coordinate).coarse.tube parent) := by
  by_cases aligned :
      ‖(wz2PaperCanonicalLineTube
            (fine.tube
              (schedule.parentRepresentative
                fineNonempty coordinate parent))).direction -
          ((schedule.scaleData coordinate).coarse.tube parent).direction‖ ≤
        4 * schedule.actualScale coordinate
  · simp [pureWZ2Prop62OrientedActualParent, aligned]
  · simp only [pureWZ2Prop62OrientedActualParent, if_neg aligned]
    exact wz2PaperTubeMidpoint_reverse _

private theorem pureWZ2Prop62_oriented_actual_parent_close
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (coordinate : Fin schedule.levelCount)
    (parent : Fin (schedule.scaleData coordinate).coarse.card)
    (actualSmall : schedule.actualScale coordinate ≤ 1 / 100) :
    let representative :=
      wz2PaperCanonicalLineTube <|
        fine.tube <|
          schedule.parentRepresentative fineNonempty coordinate parent
    let oriented :=
      pureWZ2Prop62OrientedActualParent
        schedule fineNonempty coordinate parent
    ‖representative.direction - oriented.direction‖ ≤
        4 * schedule.actualScale coordinate ∧
      ‖wz2PaperTubeMidpoint oriented -
          wz2PaperTubeMidpoint representative‖ ≤
        5 * schedule.actualScale coordinate := by
  dsimp only
  let source :=
    fine.tube <|
      schedule.parentRepresentative fineNonempty coordinate parent
  let representative := wz2PaperCanonicalLineTube source
  let actual := (schedule.scaleData coordinate).coarse.tube parent
  have actualPos : 0 < schedule.actualScale coordinate :=
    (schedule.scaleData coordinate).rho_pos
  have sourceMem :=
    schedule.parentRepresentative_mem fineNonempty coordinate parent
  have sourceContainment :
      source.carrier ⊆ actual.carrier :=
    (mem_wz2PaperOrdinaryFullFiberIndices_iff
      parent
      (schedule.parentRepresentative
        fineNonempty coordinate parent)).mp sourceMem
  have representativeContainment :
      representative.carrier ⊆ actual.carrier := by
    rw [wz2PaperCanonicalLineTube_carrier]
    exact sourceContainment
  have alignment :=
    containment_alignment_bound
      (schedule.scaleData coordinate).delta_pos.le
      (schedule.scaleData coordinate).rho_pos
      representative actual representativeContainment
  by_cases aligned :
      ‖representative.direction - actual.direction‖ ≤
        4 * schedule.actualScale coordinate
  · have baseClose :
        ‖actual.base - representative.base‖ ≤
          3 * schedule.actualScale coordinate := by
      rcases alignment with forward | backward
      · exact forward.2
      · have unitSum :
            2 ≤
              ‖representative.direction - actual.direction‖ +
                ‖representative.direction + actual.direction‖ := by
          have triangle :=
            norm_add_le
              (representative.direction - actual.direction)
              (representative.direction + actual.direction)
          rw [show
            representative.direction - actual.direction +
                (representative.direction + actual.direction) =
              (2 : ℝ) • representative.direction by module,
            norm_smul, representative.direction_unit] at triangle
          norm_num at triangle ⊢
          exact triangle
        exfalso
        nlinarith [aligned, backward.1]
    have midpointClose :
        ‖wz2PaperTubeMidpoint actual -
            wz2PaperTubeMidpoint representative‖ ≤
          5 * schedule.actualScale coordinate := by
      unfold wz2PaperTubeMidpoint
      rw [show
        actual.base + (1 / 2 : ℝ) • actual.direction -
            (representative.base +
              (1 / 2 : ℝ) • representative.direction) =
          (actual.base - representative.base) +
            (1 / 2 : ℝ) •
              (actual.direction - representative.direction) by module]
      calc
        ‖(actual.base - representative.base) +
            (1 / 2 : ℝ) •
              (actual.direction - representative.direction)‖ ≤
            ‖actual.base - representative.base‖ +
              ‖(1 / 2 : ℝ) •
                (actual.direction - representative.direction)‖ :=
          norm_add_le _ _
        _ ≤
            3 * schedule.actualScale coordinate +
              (1 / 2) *
                (4 * schedule.actualScale coordinate) := by
          rw [norm_smul, Real.norm_eq_abs]
          norm_num
          gcongr
          simpa [norm_sub_rev] using aligned
        _ = 5 * schedule.actualScale coordinate := by ring
    change
      ‖representative.direction -
          (pureWZ2Prop62OrientedActualParent
            schedule fineNonempty coordinate parent).direction‖ ≤
          4 * schedule.actualScale coordinate ∧
        ‖wz2PaperTubeMidpoint
              (pureWZ2Prop62OrientedActualParent
                schedule fineNonempty coordinate parent) -
            wz2PaperTubeMidpoint representative‖ ≤
          5 * schedule.actualScale coordinate
    rw [show
      pureWZ2Prop62OrientedActualParent
          schedule fineNonempty coordinate parent = actual by
        simp [pureWZ2Prop62OrientedActualParent, representative,
          source, actual, aligned]]
    exact ⟨aligned, midpointClose⟩
  · rcases alignment with forward | backward
    · exact False.elim (aligned forward.1)
    · have directionClose :
          ‖representative.direction -
              (reverseTube actual).direction‖ ≤
            4 * schedule.actualScale coordinate := by
        simpa [reverseTube] using backward.1
      have midpointClose :
          ‖wz2PaperTubeMidpoint (reverseTube actual) -
              wz2PaperTubeMidpoint representative‖ ≤
            5 * schedule.actualScale coordinate := by
        rw [wz2PaperTubeMidpoint_reverse]
        unfold wz2PaperTubeMidpoint
        rw [show
          actual.base + (1 / 2 : ℝ) • actual.direction -
              (representative.base +
                (1 / 2 : ℝ) • representative.direction) =
            (actual.base -
                (representative.base + representative.direction)) +
              (1 / 2 : ℝ) •
                (actual.direction + representative.direction) by module]
        calc
          ‖(actual.base -
                  (representative.base + representative.direction)) +
              (1 / 2 : ℝ) •
                (actual.direction + representative.direction)‖ ≤
              ‖actual.base -
                  (representative.base + representative.direction)‖ +
                ‖(1 / 2 : ℝ) •
                  (actual.direction + representative.direction)‖ :=
            norm_add_le _ _
          _ ≤
              3 * schedule.actualScale coordinate +
                (1 / 2) *
                  (4 * schedule.actualScale coordinate) := by
            rw [norm_smul, Real.norm_eq_abs]
            norm_num
            apply add_le_add backward.2
            exact
              mul_le_mul_of_nonneg_left
                (by simpa [add_comm] using backward.1)
                (by norm_num)
          _ = 5 * schedule.actualScale coordinate := by ring
      change
        ‖representative.direction -
            (pureWZ2Prop62OrientedActualParent
              schedule fineNonempty coordinate parent).direction‖ ≤
            4 * schedule.actualScale coordinate ∧
          ‖wz2PaperTubeMidpoint
                (pureWZ2Prop62OrientedActualParent
                  schedule fineNonempty coordinate parent) -
              wz2PaperTubeMidpoint representative‖ ≤
            5 * schedule.actualScale coordinate
      rw [show
        pureWZ2Prop62OrientedActualParent
            schedule fineNonempty coordinate parent =
          reverseTube actual by
        simp [pureWZ2Prop62OrientedActualParent, representative,
          source, actual, aligned]]
      exact ⟨directionClose, midpointClose⟩

private def pureWZ2Prop62CenteredFrame
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

@[simp] private theorem pureWZ2Prop62CenteredFrame_symm_apply
    (linear : Point3 ≃ₗᵢ[ℝ] Point3)
    (center point : Point3) :
    (pureWZ2Prop62CenteredFrame linear center).symm point =
      linear.symm (point - center) :=
  rfl

private theorem pureWZ2Prop62_abs_coord_le_norm
    (point : Point3)
    (coordinate : Fin 3) :
    |point coordinate| ≤ ‖point‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le point coordinate

/--
Fixed-center geometry of the actual parents represented by one quotient
center.  Each actual parent is oriented using its own canonical fine
representative.  In the frame centered on the common quotient center, the
four transverse coordinates are `O(r)` and the remaining midpoint coordinate
is absolutely bounded.
-/
private theorem pureWZ2Prop62_center_parent_parameter_bounds
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
    (center : Fin (quotient.level coordinate).centerFamily.card)
    (actualSmall : schedule.actualScale coordinate ≤ 1 / 100)
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (centerDirection :
      frame.symm.linearIsometryEquiv
          ((quotient.level coordinate).centerFamily.tube center).direction =
        EuclideanSpace.single 2 1)
    (centerOrigin :
      frame.symm
          (wz2PaperTubeMidpoint
            ((quotient.level coordinate).centerFamily.tube center)) = 0) :
    let midpoint := fun parent =>
      frame.symm <|
        wz2PaperTubeMidpoint <|
          pureWZ2Prop62OrientedActualParent
            schedule fineNonempty coordinate parent
    let direction := fun parent =>
      frame.symm.linearIsometryEquiv <|
        (pureWZ2Prop62OrientedActualParent
          schedule fineNonempty coordinate parent).direction
    ∀ parent ∈ quotient.centerActualParents coordinate center,
      |direction parent 0| ≤
          10 * schedule.actualScale coordinate ∧
        |direction parent 1| ≤
          10 * schedule.actualScale coordinate ∧
        direction parent 2 ≥ 1 / 2 ∧
        |midpoint parent 0| ≤
          10 * schedule.actualScale coordinate ∧
        |midpoint parent 1| ≤
          10 * schedule.actualScale coordinate ∧
        |midpoint parent 2| ≤ 11 := by
  dsimp only
  intro parent parentMem
  let actual :=
    pureWZ2Prop62OrientedActualParent
      schedule fineNonempty coordinate parent
  let representativeSource :=
    schedule.parentRepresentative fineNonempty coordinate parent
  let representative :=
    wz2PaperCanonicalLineTube (fine.tube representativeSource)
  let centerTube :=
    (quotient.level coordinate).centerFamily.tube center
  let representativeProxy :=
    schedule.coordinateProxyTube fineNonempty coordinate parent
  have parentCenter :
      quotient.actualCenter coordinate parent = center :=
    (Finset.mem_filter.mp parentMem).2
  have proxyCenterDistance :
      wz1PaperLineDistance representativeProxy centerTube ≤
        schedule.actualScale coordinate / 4 := by
    have close :=
      (quotient.level coordinate).actualProxy_center_lineDistance_le
        fineLine parent
    change
      (quotient.level coordinate).net.center parent = center at parentCenter
    change
      wz1PaperLineDistance representativeProxy centerTube ≤
        schedule.actualScale coordinate / 4
    rwa [parentCenter] at close
  have representativeLine :
      WZ1PaperTubeInLineClass (fine.tube representativeSource) :=
    fineLine representativeSource
  have centerLine :
      WZ1PaperTubeInLineClass centerTube :=
    (quotient.level coordinate).centerFamily_lineClass fineLine center
  have axisDistance :
      dist
          (wz1TubeAxisZeroPoint (fine.tube representativeSource))
          (wz1TubeAxisZeroPoint centerTube) ≤
        schedule.actualScale coordinate / 4 := by
    have nonnegative :=
      InnerProductGeometry.angle_nonneg
        (wz1PaperDirection representativeProxy)
        (wz1PaperDirection centerTube)
    have bound :
        dist
            (wz1TubeAxisZeroPoint representativeProxy)
            (wz1TubeAxisZeroPoint centerTube) ≤
          schedule.actualScale coordinate / 4 := by
      unfold wz1PaperLineDistance at proxyCenterDistance
      linarith
    have proxyAxis :
        wz1TubeAxisZeroPoint representativeProxy =
          wz1TubeAxisZeroPoint (fine.tube representativeSource) := by
      change
        wz1TubeAxisZeroPoint
            (wz2PaperCanonicalLineTube
              (fine.tube representativeSource)) =
          wz1TubeAxisZeroPoint (fine.tube representativeSource)
      exact wz2PaperCanonicalLineTube_axisZero representativeLine
    rwa [proxyAxis] at bound
  have angleDistance :
      InnerProductGeometry.angle
          (wz1PaperDirection (fine.tube representativeSource))
          (wz1PaperDirection centerTube) ≤
        schedule.actualScale coordinate / 4 := by
    have nonnegative :=
      dist_nonneg
        (x := wz1TubeAxisZeroPoint representativeProxy)
        (y := wz1TubeAxisZeroPoint centerTube)
    have bound :
        InnerProductGeometry.angle
            (wz1PaperDirection representativeProxy)
            (wz1PaperDirection centerTube) ≤
          schedule.actualScale coordinate / 4 := by
      unfold wz1PaperLineDistance at proxyCenterDistance
      linarith
    have proxyDirection :
        wz1PaperDirection representativeProxy =
          wz1PaperDirection (fine.tube representativeSource) := by
      change
        wz1PaperDirection
            (wz2PaperCanonicalLineTube
              (fine.tube representativeSource)) =
          wz1PaperDirection (fine.tube representativeSource)
      exact wz2PaperCanonicalLineTube_paperDirection representativeLine
    rwa [proxyDirection] at bound
  have representativeDirectionClose :
      ‖representative.direction - centerTube.direction‖ ≤
        schedule.actualScale coordinate / 4 := by
    have chord :=
      unit_norm_sub_le_angle
        (wz1PaperDirection_norm (fine.tube representativeSource))
        (wz1PaperDirection_norm centerTube)
    have canonicalDirection :
        representative.direction =
          wz1PaperDirection (fine.tube representativeSource) := by
      change
        (wz2PaperCanonicalLineTube
          (fine.tube representativeSource)).direction =
            wz1PaperDirection (fine.tube representativeSource)
      unfold wz2PaperCanonicalLineTube wz1PaperDirection
      split_ifs <;> rfl
    have centerDirectionEq :
        centerTube.direction = wz1PaperDirection centerTube := by
      dsimp only [centerTube,
        PureWZ2Prop62ProxyQuotientLevelData.centerFamily]
      exact
        (wz2PaperCenteredLineTube_paperDirection <|
          schedule.coordinateProxyTube_lineClass
            fineNonempty fineLine coordinate
            ((quotient.level coordinate).net.centerEmbedding center)).symm
    rw [canonicalDirection, centerDirectionEq]
    exact chord.trans angleDistance
  have actualClose :=
    pureWZ2Prop62_oriented_actual_parent_close
      schedule fineNonempty coordinate parent actualSmall
  have actualDirectionClose :
      ‖actual.direction - centerTube.direction‖ ≤
        5 * schedule.actualScale coordinate := by
    calc
      ‖actual.direction - centerTube.direction‖ ≤
          ‖actual.direction - representative.direction‖ +
            ‖representative.direction - centerTube.direction‖ := by
        rw [show
          actual.direction - centerTube.direction =
            (actual.direction - representative.direction) +
              (representative.direction - centerTube.direction) by abel]
        exact norm_add_le _ _
      _ ≤
          4 * schedule.actualScale coordinate +
            schedule.actualScale coordinate / 4 := by
        gcongr
        simpa [norm_sub_rev] using actualClose.1
      _ ≤ 5 * schedule.actualScale coordinate := by
        nlinarith [(schedule.scaleData coordinate).rho_pos]
  have transformedDirectionClose :
      ‖frame.symm.linearIsometryEquiv actual.direction -
          EuclideanSpace.single 2 1‖ ≤
        5 * schedule.actualScale coordinate := by
    rw [← centerDirection, ← map_sub,
      frame.symm.linearIsometryEquiv.norm_map]
    exact actualDirectionClose
  have directionZero :
      |(frame.symm.linearIsometryEquiv actual.direction) 0| ≤
        10 * schedule.actualScale coordinate := by
    have coordinateBound :=
      pureWZ2Prop62_abs_coord_le_norm
        (frame.symm.linearIsometryEquiv actual.direction -
          EuclideanSpace.single 2 1) 0
    simp [EuclideanSpace.single] at coordinateBound
    exact coordinateBound.trans <| by
      nlinarith [(schedule.scaleData coordinate).rho_pos]
  have directionOne :
      |(frame.symm.linearIsometryEquiv actual.direction) 1| ≤
        10 * schedule.actualScale coordinate := by
    have coordinateBound :=
      pureWZ2Prop62_abs_coord_le_norm
        (frame.symm.linearIsometryEquiv actual.direction -
          EuclideanSpace.single 2 1) 1
    simp [EuclideanSpace.single] at coordinateBound
    exact coordinateBound.trans <| by
      nlinarith [(schedule.scaleData coordinate).rho_pos]
  have directionTwo :
      (frame.symm.linearIsometryEquiv actual.direction) 2 ≥ 1 / 2 := by
    have coordinateBound :=
      pureWZ2Prop62_abs_coord_le_norm
        (frame.symm.linearIsometryEquiv actual.direction -
          EuclideanSpace.single 2 1) 2
    have close :
        |(frame.symm.linearIsometryEquiv actual.direction) 2 - 1| ≤
          5 * schedule.actualScale coordinate := by
      simpa [EuclideanSpace.single, Pi.sub_apply] using
        coordinateBound.trans transformedDirectionClose
    have lower := (abs_le.mp close).1
    nlinarith
  let axial :=
    pureWZ2OrdinaryAxialParameter
      (fine.tube representativeSource) representativeLine
  have axialBound : |axial| ≤ 10 :=
    pureWZ2OrdinaryAxialParameter_abs_le_ten
      representativeLine <| by
        exact (fineBase representativeSource).trans (by norm_num)
  have representativeMidpointEq :
      wz2PaperTubeMidpoint representative =
        wz1TubeAxisZeroPoint (fine.tube representativeSource) +
          axial •
            wz1PaperDirection (fine.tube representativeSource) := by
    rw [show
      wz2PaperTubeMidpoint representative =
        wz2PaperTubeMidpoint (fine.tube representativeSource) by
          unfold representative wz2PaperCanonicalLineTube
          split_ifs
          · rfl
          · exact wz2PaperTubeMidpoint_reverse _]
    exact
      pureWZ2OrdinaryAxialParameter_spec
        (fine.tube representativeSource) representativeLine
  have centerMidpoint :
      wz2PaperTubeMidpoint centerTube =
        wz1TubeAxisZeroPoint centerTube := by
    change
      wz2PaperTubeMidpoint
          (wz2PaperCenteredLineTube
            (schedule.coordinateProxyTube
              fineNonempty coordinate
              ((quotient.level coordinate).net.centerEmbedding center))) =
        wz1TubeAxisZeroPoint
          (wz2PaperCenteredLineTube
            (schedule.coordinateProxyTube
              fineNonempty coordinate
              ((quotient.level coordinate).net.centerEmbedding center)))
    rw [wz2PaperCenteredLineTube_midpoint,
      wz2PaperCenteredLineTube_axisZero <|
        schedule.coordinateProxyTube_lineClass
          fineNonempty fineLine coordinate
          ((quotient.level coordinate).net.centerEmbedding center)]
  have representativeMidpointDifference :
      wz2PaperTubeMidpoint representative -
          wz2PaperTubeMidpoint centerTube =
        (wz1TubeAxisZeroPoint (fine.tube representativeSource) -
            wz1TubeAxisZeroPoint centerTube) +
          axial • representative.direction := by
    rw [representativeMidpointEq, centerMidpoint]
    have directionEq :
        representative.direction =
          wz1PaperDirection (fine.tube representativeSource) := by
      change
        (wz2PaperCanonicalLineTube
          (fine.tube representativeSource)).direction =
            wz1PaperDirection (fine.tube representativeSource)
      unfold wz2PaperCanonicalLineTube wz1PaperDirection
      split_ifs <;> rfl
    rw [directionEq]
    abel
  have actualMidpointDifference :
      wz2PaperTubeMidpoint actual -
          wz2PaperTubeMidpoint centerTube =
        (wz2PaperTubeMidpoint actual -
            wz2PaperTubeMidpoint representative) +
          (wz2PaperTubeMidpoint representative -
            wz2PaperTubeMidpoint centerTube) := by
    abel
  have midpointTransform :
      frame.symm (wz2PaperTubeMidpoint actual) =
        frame.symm.linearIsometryEquiv
          (wz2PaperTubeMidpoint actual -
            wz2PaperTubeMidpoint centerTube) := by
    have mapVsub :=
      frame.symm.map_vsub
        (wz2PaperTubeMidpoint actual)
        (wz2PaperTubeMidpoint centerTube)
    calc
      frame.symm (wz2PaperTubeMidpoint actual) =
          frame.symm (wz2PaperTubeMidpoint actual) -
            frame.symm (wz2PaperTubeMidpoint centerTube) := by
        rw [centerOrigin, sub_zero]
      _ =
          frame.symm.linearIsometryEquiv
            (wz2PaperTubeMidpoint actual -
              wz2PaperTubeMidpoint centerTube) := by
        simpa [vsub_eq_sub] using mapVsub.symm
  have representativeZeroDifference :
      |(frame.symm.linearIsometryEquiv
          (wz2PaperTubeMidpoint representative -
            wz2PaperTubeMidpoint centerTube)) 0| ≤
        3 * schedule.actualScale coordinate := by
    rw [representativeMidpointDifference, map_add, map_smul]
    have axisCoordinate :
        |(frame.symm.linearIsometryEquiv
            (wz1TubeAxisZeroPoint (fine.tube representativeSource) -
              wz1TubeAxisZeroPoint centerTube)) 0| ≤
          schedule.actualScale coordinate / 4 := by
      exact
        (pureWZ2Prop62_abs_coord_le_norm _ 0).trans <| by
          rw [frame.symm.linearIsometryEquiv.norm_map]
          simpa [dist_eq_norm] using axisDistance
    have directionCoordinate :
        |(frame.symm.linearIsometryEquiv representative.direction) 0| ≤
          schedule.actualScale coordinate / 4 := by
      have coordinateBound :=
        pureWZ2Prop62_abs_coord_le_norm
          (frame.symm.linearIsometryEquiv representative.direction -
            EuclideanSpace.single 2 1) 0
      have transformedClose :
          ‖frame.symm.linearIsometryEquiv representative.direction -
              EuclideanSpace.single 2 1‖ ≤
            schedule.actualScale coordinate / 4 := by
        rw [← centerDirection, ← map_sub,
          frame.symm.linearIsometryEquiv.norm_map]
        exact representativeDirectionClose
      simp [EuclideanSpace.single] at coordinateBound
      exact coordinateBound.trans transformedClose
    calc
      |(frame.symm.linearIsometryEquiv
              (wz1TubeAxisZeroPoint (fine.tube representativeSource) -
                wz1TubeAxisZeroPoint centerTube) +
            axial •
              frame.symm.linearIsometryEquiv representative.direction) 0| ≤
          |(frame.symm.linearIsometryEquiv
              (wz1TubeAxisZeroPoint (fine.tube representativeSource) -
                wz1TubeAxisZeroPoint centerTube)) 0| +
            |axial| *
              |(frame.symm.linearIsometryEquiv
                representative.direction) 0| := by
        simpa [Pi.add_apply, Pi.smul_apply, abs_mul] using
          abs_add_le
            ((frame.symm.linearIsometryEquiv
              (wz1TubeAxisZeroPoint (fine.tube representativeSource) -
                wz1TubeAxisZeroPoint centerTube)) 0)
            ((axial •
              frame.symm.linearIsometryEquiv representative.direction) 0)
      _ ≤
          schedule.actualScale coordinate / 4 +
            10 * (schedule.actualScale coordinate / 4) := by
        gcongr
      _ ≤ 3 * schedule.actualScale coordinate := by
        nlinarith [(schedule.scaleData coordinate).rho_pos]
  have representativeOneDifference :
      |(frame.symm.linearIsometryEquiv
          (wz2PaperTubeMidpoint representative -
            wz2PaperTubeMidpoint centerTube)) 1| ≤
        3 * schedule.actualScale coordinate := by
    rw [representativeMidpointDifference, map_add, map_smul]
    have axisCoordinate :
        |(frame.symm.linearIsometryEquiv
            (wz1TubeAxisZeroPoint (fine.tube representativeSource) -
              wz1TubeAxisZeroPoint centerTube)) 1| ≤
          schedule.actualScale coordinate / 4 := by
      exact
        (pureWZ2Prop62_abs_coord_le_norm _ 1).trans <| by
          rw [frame.symm.linearIsometryEquiv.norm_map]
          simpa [dist_eq_norm] using axisDistance
    have directionCoordinate :
        |(frame.symm.linearIsometryEquiv representative.direction) 1| ≤
          schedule.actualScale coordinate / 4 := by
      have coordinateBound :=
        pureWZ2Prop62_abs_coord_le_norm
          (frame.symm.linearIsometryEquiv representative.direction -
            EuclideanSpace.single 2 1) 1
      have transformedClose :
          ‖frame.symm.linearIsometryEquiv representative.direction -
              EuclideanSpace.single 2 1‖ ≤
            schedule.actualScale coordinate / 4 := by
        rw [← centerDirection, ← map_sub,
          frame.symm.linearIsometryEquiv.norm_map]
        exact representativeDirectionClose
      simp [EuclideanSpace.single] at coordinateBound
      exact coordinateBound.trans transformedClose
    calc
      |(frame.symm.linearIsometryEquiv
              (wz1TubeAxisZeroPoint (fine.tube representativeSource) -
                wz1TubeAxisZeroPoint centerTube) +
            axial •
              frame.symm.linearIsometryEquiv representative.direction) 1| ≤
          |(frame.symm.linearIsometryEquiv
              (wz1TubeAxisZeroPoint (fine.tube representativeSource) -
                wz1TubeAxisZeroPoint centerTube)) 1| +
            |axial| *
              |(frame.symm.linearIsometryEquiv
                representative.direction) 1| := by
        simpa [Pi.add_apply, Pi.smul_apply, abs_mul] using
          abs_add_le
            ((frame.symm.linearIsometryEquiv
              (wz1TubeAxisZeroPoint (fine.tube representativeSource) -
                wz1TubeAxisZeroPoint centerTube)) 1)
            ((axial •
              frame.symm.linearIsometryEquiv representative.direction) 1)
      _ ≤
          schedule.actualScale coordinate / 4 +
            10 * (schedule.actualScale coordinate / 4) := by
        gcongr
      _ ≤ 3 * schedule.actualScale coordinate := by
        nlinarith [(schedule.scaleData coordinate).rho_pos]
  have actualMidpointNorm :
      ‖wz2PaperTubeMidpoint actual -
          wz2PaperTubeMidpoint representative‖ ≤
        5 * schedule.actualScale coordinate :=
    actualClose.2
  have midpointZero :
      |(frame.symm (wz2PaperTubeMidpoint actual)) 0| ≤
        10 * schedule.actualScale coordinate := by
    rw [midpointTransform, actualMidpointDifference, map_add]
    calc
      |(frame.symm.linearIsometryEquiv
              (wz2PaperTubeMidpoint actual -
                wz2PaperTubeMidpoint representative) +
            frame.symm.linearIsometryEquiv
              (wz2PaperTubeMidpoint representative -
                wz2PaperTubeMidpoint centerTube)) 0| ≤
          |(frame.symm.linearIsometryEquiv
              (wz2PaperTubeMidpoint actual -
                wz2PaperTubeMidpoint representative)) 0| +
            |(frame.symm.linearIsometryEquiv
              (wz2PaperTubeMidpoint representative -
                wz2PaperTubeMidpoint centerTube)) 0| := by
        simpa [Pi.add_apply] using abs_add_le
          ((frame.symm.linearIsometryEquiv
            (wz2PaperTubeMidpoint actual -
              wz2PaperTubeMidpoint representative)) 0)
          ((frame.symm.linearIsometryEquiv
            (wz2PaperTubeMidpoint representative -
              wz2PaperTubeMidpoint centerTube)) 0)
      _ ≤
          5 * schedule.actualScale coordinate +
            3 * schedule.actualScale coordinate := by
        gcongr
        exact
          (pureWZ2Prop62_abs_coord_le_norm _ 0).trans <| by
            rwa [frame.symm.linearIsometryEquiv.norm_map]
      _ ≤ 10 * schedule.actualScale coordinate := by
        nlinarith [(schedule.scaleData coordinate).rho_pos]
  have midpointOne :
      |(frame.symm (wz2PaperTubeMidpoint actual)) 1| ≤
        10 * schedule.actualScale coordinate := by
    rw [midpointTransform, actualMidpointDifference, map_add]
    calc
      |(frame.symm.linearIsometryEquiv
              (wz2PaperTubeMidpoint actual -
                wz2PaperTubeMidpoint representative) +
            frame.symm.linearIsometryEquiv
              (wz2PaperTubeMidpoint representative -
                wz2PaperTubeMidpoint centerTube)) 1| ≤
          |(frame.symm.linearIsometryEquiv
              (wz2PaperTubeMidpoint actual -
                wz2PaperTubeMidpoint representative)) 1| +
            |(frame.symm.linearIsometryEquiv
              (wz2PaperTubeMidpoint representative -
                wz2PaperTubeMidpoint centerTube)) 1| := by
        simpa [Pi.add_apply] using abs_add_le
          ((frame.symm.linearIsometryEquiv
            (wz2PaperTubeMidpoint actual -
              wz2PaperTubeMidpoint representative)) 1)
          ((frame.symm.linearIsometryEquiv
            (wz2PaperTubeMidpoint representative -
              wz2PaperTubeMidpoint centerTube)) 1)
      _ ≤
          5 * schedule.actualScale coordinate +
            3 * schedule.actualScale coordinate := by
        gcongr
        exact
          (pureWZ2Prop62_abs_coord_le_norm _ 1).trans <| by
            rwa [frame.symm.linearIsometryEquiv.norm_map]
      _ ≤ 10 * schedule.actualScale coordinate := by
        nlinarith [(schedule.scaleData coordinate).rho_pos]
  have midpointTwo :
      |(frame.symm (wz2PaperTubeMidpoint actual)) 2| ≤ 11 := by
    have actualCenterNorm :
        ‖wz2PaperTubeMidpoint actual -
            wz2PaperTubeMidpoint centerTube‖ ≤
          11 := by
      rw [actualMidpointDifference]
      calc
        ‖(wz2PaperTubeMidpoint actual -
              wz2PaperTubeMidpoint representative) +
            (wz2PaperTubeMidpoint representative -
              wz2PaperTubeMidpoint centerTube)‖ ≤
            ‖wz2PaperTubeMidpoint actual -
              wz2PaperTubeMidpoint representative‖ +
              ‖wz2PaperTubeMidpoint representative -
                wz2PaperTubeMidpoint centerTube‖ :=
          norm_add_le _ _
        _ ≤
            5 * schedule.actualScale coordinate +
              (schedule.actualScale coordinate / 4 + 10) := by
          gcongr
          rw [representativeMidpointDifference]
          calc
            ‖(wz1TubeAxisZeroPoint (fine.tube representativeSource) -
                  wz1TubeAxisZeroPoint centerTube) +
                axial • representative.direction‖ ≤
                ‖wz1TubeAxisZeroPoint (fine.tube representativeSource) -
                    wz1TubeAxisZeroPoint centerTube‖ +
                  ‖axial • representative.direction‖ :=
              norm_add_le _ _
            _ ≤
                schedule.actualScale coordinate / 4 + 10 := by
              rw [norm_smul, representative.direction_unit,
                mul_one, Real.norm_eq_abs]
              gcongr
              simpa [dist_eq_norm] using axisDistance
        _ ≤ 11 := by nlinarith
    rw [midpointTransform]
    exact
      (pureWZ2Prop62_abs_coord_le_norm _ 2).trans <| by
        rwa [frame.symm.linearIsometryEquiv.norm_map]
  exact
    ⟨directionZero, directionOne, directionTwo,
      midpointZero, midpointOne, midpointTwo⟩

/--
Every quotient center contains only an absolute number of actual ordinary
parents.  The bound is independent of the source scale, scheduled scale,
schedule depth, and all family cardinalities.
-/
theorem pureWZ2_prop62_proxy_center_actualParents_card_le_of_small
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
    (actualSmall : schedule.actualScale coordinate ≤ 1 / 100)
    (center : Fin (quotient.level coordinate).centerFamily.card) :
    (quotient.centerActualParents coordinate center).card ≤
      pureWZ2Prop62ProxyCenterCopySmallScaleBound := by
  let rho := schedule.actualScale coordinate
  let indices := quotient.centerActualParents coordinate center
  let centerTube :=
    (quotient.level coordinate).centerFamily.tube center
  rcases frame_of_axis centerTube.direction centerTube.direction_unit with
    ⟨_, _, rawFrame, centerTwo, centerZero, centerOne⟩
  let linear := rawFrame.linearIsometryEquiv
  let frame :=
    pureWZ2Prop62CenteredFrame
      linear (wz2PaperTubeMidpoint centerTube)
  let tubes :
      Fin (schedule.scaleData coordinate).coarse.card →
        Kakeya.DeltaTube rho :=
    pureWZ2Prop62OrientedActualParent
      schedule fineNonempty coordinate
  let midpoint :
      Fin (schedule.scaleData coordinate).coarse.card → Point3 :=
    fun parent => frame.symm (wz2PaperTubeMidpoint (tubes parent))
  let direction :
      Fin (schedule.scaleData coordinate).coarse.card → Point3 :=
    fun parent =>
      frame.symm.linearIsometryEquiv (tubes parent).direction
  have centerDirection :
      frame.symm.linearIsometryEquiv centerTube.direction =
        EuclideanSpace.single 2 1 := by
    change rawFrame.symm.linearIsometryEquiv centerTube.direction =
      EuclideanSpace.single 2 1
    ext current
    fin_cases current
    · simpa [EuclideanSpace.single] using centerZero
    · simpa [EuclideanSpace.single] using centerOne
    · simpa [EuclideanSpace.single] using centerTwo
  have centerOrigin :
      frame.symm (wz2PaperTubeMidpoint centerTube) = 0 := by
    change
      linear.symm
          (wz2PaperTubeMidpoint centerTube -
            wz2PaperTubeMidpoint centerTube) = 0
    rw [sub_self, map_zero]
  have bounds :=
    pureWZ2Prop62_center_parent_parameter_bounds
      schedule fineNonempty fineLine fineBase quotient coordinate center
      actualSmall frame centerDirection centerOrigin
  let parameter :
      Fin (schedule.scaleData coordinate).coarse.card → Fin 5 → ℝ :=
    fun parent current =>
      match current.1 with
      | 0 => direction parent 0
      | 1 => direction parent 1
      | 2 => midpoint parent 0
      | 3 => midpoint parent 1
      | _ => midpoint parent 2
  let mesh : Fin 5 → ℝ := fun current =>
    if current.1 = 4 then 1 / 6400 else rho / 200
  let radius : Fin 5 → ℝ := fun current =>
    if current.1 = 4 then 11 else 10 * rho
  let values := indices.image parameter
  have rhoPos : 0 < rho :=
    (schedule.scaleData coordinate).rho_pos
  have rhoSmall : rho ≤ 1 / 100 := actualSmall
  have meshPos : ∀ current, 0 < mesh current := by
    intro current
    dsimp only [mesh]
    split_ifs <;> positivity
  have radiusNonnegative : ∀ current, 0 ≤ radius current := by
    intro current
    dsimp only [radius]
    split_ifs <;> positivity
  have parameterBound :
      ∀ value ∈ values,
        ∀ current, |value current| ≤ radius current := by
    intro value valueMem current
    rcases Finset.mem_image.mp valueMem with
      ⟨parent, parentMem, rfl⟩
    have parentBounds := bounds parent parentMem
    dsimp only [parameter, radius]
    fin_cases current
    · exact parentBounds.1
    · exact parentBounds.2.1
    · exact parentBounds.2.2.2.1
    · exact parentBounds.2.2.2.2.1
    · exact parentBounds.2.2.2.2.2
  have coarseDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct
        (schedule.scaleData coordinate).coarse :=
    (schedule.scaleData coordinate).cover
      |>.coarse_essentiallyDistinct_of_uniform
        (schedule.scaleData coordinate).rho_pos.le
        fineNonempty
        (schedule.scaleData coordinate).full_fiber_uniform
  have parentEqOfClose :
      ∀ first ∈ indices,
        ∀ second ∈ indices,
          (∀ current,
            |parameter first current -
                parameter second current| ≤ mesh current) →
          first = second := by
    intro firstParent firstParentMem secondParent secondParentMem close
    by_contra parentNe
    have firstBounds := bounds firstParent firstParentMem
    have secondBounds := bounds secondParent secondParentMem
    have midpointZero :
        |(midpoint firstParent - midpoint secondParent) 0| ≤
          rho / 200 := by
      simpa [parameter, mesh, Pi.sub_apply] using close (2 : Fin 5)
    have midpointOne :
        |(midpoint firstParent - midpoint secondParent) 1| ≤
          rho / 200 := by
      simpa [parameter, mesh, Pi.sub_apply] using close (3 : Fin 5)
    have midpointTwo :
        |(midpoint firstParent - midpoint secondParent) 2| ≤
          1 / 6400 := by
      simpa [parameter, mesh, Pi.sub_apply] using close (4 : Fin 5)
    have directionZero :
        |(direction firstParent - direction secondParent) 0| ≤
          rho / 200 := by
      simpa [parameter, mesh, Pi.sub_apply] using close (0 : Fin 5)
    have directionOne :
        |(direction firstParent - direction secondParent) 1| ≤
          rho / 200 := by
      simpa [parameter, mesh, Pi.sub_apply] using close (1 : Fin 5)
    have containment :
        (tubes firstParent).carrier ⊆
          wz2PaperCenteredDilatedCarrier 2
            (tubes secondParent) :=
      wz2PaperOrdinary_carrier_subset_centeredDilatedTwo_of_five_close
        rhoPos rhoSmall frame
        (midpoint firstParent) (midpoint secondParent)
        (direction firstParent) (direction secondParent)
        rfl rfl rfl rfl
        ⟨firstBounds.1, firstBounds.2.1⟩
        ⟨secondBounds.1, secondBounds.2.1⟩
        (Or.inl ⟨firstBounds.2.2.1, secondBounds.2.2.1⟩)
        midpointZero midpointOne midpointTwo directionZero directionOne
    have originalContainment :
        ((schedule.scaleData coordinate).coarse.tube
            firstParent).carrier ⊆
          wz2PaperCenteredDilatedCarrier 2
            ((schedule.scaleData coordinate).coarse.tube
              secondParent) := by
      have firstCarrier :
          (tubes firstParent).carrier =
            ((schedule.scaleData coordinate).coarse.tube
              firstParent).carrier :=
        pureWZ2Prop62OrientedActualParent_carrier
          schedule fineNonempty coordinate firstParent
      have secondCarrier :
          (tubes secondParent).carrier =
            ((schedule.scaleData coordinate).coarse.tube
              secondParent).carrier :=
        pureWZ2Prop62OrientedActualParent_carrier
          schedule fineNonempty coordinate secondParent
      have secondMidpoint :
          wz2PaperTubeMidpoint (tubes secondParent) =
            wz2PaperTubeMidpoint
              ((schedule.scaleData coordinate).coarse.tube
                secondParent) :=
        pureWZ2Prop62OrientedActualParent_midpoint
          schedule fineNonempty coordinate secondParent
      unfold wz2PaperCenteredDilatedCarrier at containment ⊢
      rwa [firstCarrier, secondCarrier, secondMidpoint] at containment
    exact
      (coarseDistinct firstParent secondParent parentNe).1
        originalContainment
  have parameterSeparation :
      ∀ first ∈ values,
        ∀ second ∈ values,
          first ≠ second →
            ∃ current,
              |first current - second current| ≥ mesh current := by
    intro first firstMem second secondMem valuesNe
    rcases Finset.mem_image.mp firstMem with
      ⟨firstParent, firstParentMem, rfl⟩
    rcases Finset.mem_image.mp secondMem with
      ⟨secondParent, secondParentMem, secondEq⟩
    subst second
    by_contra noCoordinate
    push Not at noCoordinate
    have parentEq :=
      parentEqOfClose firstParent firstParentMem
        secondParent secondParentMem fun current =>
          (noCoordinate current).le
    exact valuesNe <| by rw [parentEq]
  have packed :=
    anisotropic_cell_pack meshPos radiusNonnegative
      parameterBound parameterSeparation
  have parameterInjective : Set.InjOn parameter indices := by
    intro first firstMem second secondMem parameterEq
    apply parentEqOfClose first firstMem second secondMem
    intro current
    rw [congrFun parameterEq current, sub_self, abs_zero]
    exact (meshPos current).le
  have valuesCard : values.card = indices.card :=
    Finset.card_image_of_injOn parameterInjective
  have transverseQuotient :
      10 * rho / (rho / 200) = (2000 : ℝ) := by
    field_simp [rhoPos.ne']
    ring
  have transverseCeil :
      Nat.ceil (10 * rho / (rho / 200)) = 2000 := by
    rw [transverseQuotient]
    exact Nat.ceil_natCast _
  have longitudinalCeil :
      Nat.ceil ((11 : ℝ) / (1 / 6400)) = 70400 := by
    norm_num
  have longitudinalCeilMul :
      Nat.ceil ((11 : ℝ) * 6400) = 70400 := by
    norm_num
  have productBound :
      (∏ current : Fin 5,
        (2 * Nat.ceil
          (radius current / mesh current) + 1)) =
        pureWZ2Prop62ProxyCenterCopySmallScaleBound := by
    unfold pureWZ2Prop62ProxyCenterCopySmallScaleBound
    apply Finset.prod_congr rfl
    intro current _
    fin_cases current <;>
      simp [radius, mesh, transverseCeil, longitudinalCeil,
        longitudinalCeilMul]
  rw [← valuesCard]
  exact packed.trans_eq productBound

private theorem pureWZ2Prop62_actual_parent_midpoint_norm_le
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {scale : ℝ}
    (data : WZ2PaperPureScaleCoverData fine scale C)
    (fineNonempty : fine.Nonempty)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (parent : Fin data.coarse.card) :
    ‖wz2PaperTubeMidpoint (data.coarse.tube parent)‖ ≤
      7 + 3 * scale := by
  let source :=
    Classical.choose <|
      data.cover.fullFiber_nonempty_of_uniform
        fineNonempty data.full_fiber_uniform parent
  have sourceMem :
      source ∈
        wz2PaperOrdinaryFullFiberIndices fine data.coarse parent :=
    Classical.choose_spec <|
      data.cover.fullFiber_nonempty_of_uniform
        fineNonempty data.full_fiber_uniform parent
  have containment :
      (fine.tube source).carrier ⊆
        (data.coarse.tube parent).carrier :=
    (mem_wz2PaperOrdinaryFullFiberIndices_iff parent source).mp
      sourceMem
  rcases
      containment_alignment_bound
        data.delta_pos.le data.rho_pos
        (fine.tube source) (data.coarse.tube parent) containment
    with aligned | reversed
  · have parentBase :
        ‖(data.coarse.tube parent).base‖ ≤
          5 + 3 * scale := by
      calc
        ‖(data.coarse.tube parent).base‖ =
            ‖(fine.tube source).base +
              ((data.coarse.tube parent).base -
                (fine.tube source).base)‖ := by
          congr 1
          abel
        _ ≤
            ‖(fine.tube source).base‖ +
              ‖(data.coarse.tube parent).base -
                (fine.tube source).base‖ :=
          norm_add_le _ _
        _ ≤ 5 + 3 * scale :=
          add_le_add (fineBase source) aligned.2
    unfold wz2PaperTubeMidpoint
    calc
      ‖(data.coarse.tube parent).base +
          (1 / 2 : ℝ) • (data.coarse.tube parent).direction‖ ≤
          ‖(data.coarse.tube parent).base‖ +
            ‖(1 / 2 : ℝ) •
              (data.coarse.tube parent).direction‖ :=
        norm_add_le _ _
      _ ≤ (5 + 3 * scale) + 1 / 2 := by
        rw [norm_smul, (data.coarse.tube parent).direction_unit,
          Real.norm_eq_abs]
        norm_num
        simpa only [show (5 : ℝ) + 1 = 6 by norm_num] using parentBase
      _ ≤ 7 + 3 * scale := by linarith
  · have sourceEndpoint :
        ‖(fine.tube source).base +
            (fine.tube source).direction‖ ≤
          5 + 1 := by
      exact
        (norm_add_le _ _).trans <| by
          rw [(fine.tube source).direction_unit]
          linarith [fineBase source]
    have parentBase :
        ‖(data.coarse.tube parent).base‖ ≤
          (5 + 1) + 3 * scale := by
      calc
        ‖(data.coarse.tube parent).base‖ =
            ‖((fine.tube source).base +
                (fine.tube source).direction) +
              ((data.coarse.tube parent).base -
                ((fine.tube source).base +
                  (fine.tube source).direction))‖ := by
          congr 1
          abel
        _ ≤
            ‖(fine.tube source).base +
                (fine.tube source).direction‖ +
              ‖(data.coarse.tube parent).base -
                ((fine.tube source).base +
                  (fine.tube source).direction)‖ :=
          norm_add_le _ _
        _ ≤ (5 + 1) + 3 * scale :=
          add_le_add sourceEndpoint reversed.2
    unfold wz2PaperTubeMidpoint
    calc
      ‖(data.coarse.tube parent).base +
          (1 / 2 : ℝ) • (data.coarse.tube parent).direction‖ ≤
          ‖(data.coarse.tube parent).base‖ +
            ‖(1 / 2 : ℝ) •
              (data.coarse.tube parent).direction‖ :=
        norm_add_le _ _
      _ ≤ ((5 + 1) + 3 * scale) + 1 / 2 := by
        rw [norm_smul, (data.coarse.tube parent).direction_unit,
          Real.norm_eq_abs]
        norm_num
        simpa only [show (5 : ℝ) + 1 = 6 by norm_num] using parentBase
      _ ≤ 7 + 3 * scale := by linarith

theorem pureWZ2_prop62_proxy_center_actualParents_card_le_of_large
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    (schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow)
    (fineNonempty : fine.Nonempty)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty)
    (coordinate : Fin schedule.levelCount)
    (actualLarge : 1 / 100 < schedule.actualScale coordinate)
    (center : Fin (quotient.level coordinate).centerFamily.card) :
    (quotient.centerActualParents coordinate center).card ≤
      pureWZ2Prop62ProxyCenterCopyLargeScaleBound := by
  let rho := schedule.actualScale coordinate
  let indices := quotient.centerActualParents coordinate center
  have rhoPos : 0 < rho :=
    (schedule.scaleData coordinate).rho_pos
  have coarseDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct
        (schedule.scaleData coordinate).coarse :=
    (schedule.scaleData coordinate).cover
      |>.coarse_essentiallyDistinct_of_uniform
        (schedule.scaleData coordinate).rho_pos.le
        fineNonempty
        (schedule.scaleData coordinate).full_fiber_uniform
  have packed :=
    wz2PaperOrdinary_local_six_grid_card_bound
      rhoPos
      (show 0 ≤ 7 + 3 * rho by positivity)
      coarseDistinct indices 0
      (fun parent _ => by
        simpa [rho] using
          pureWZ2Prop62_actual_parent_midpoint_norm_le
            (schedule.scaleData coordinate)
            fineNonempty fineBase parent)
  have midpointRatio :
      (7 + 3 * rho) / (rho / 64) ≤ 44992 := by
    apply (div_le_iff₀ (by positivity : 0 < rho / 64)).2
    nlinarith
  have directionRatio :
      1 / (rho / 64) ≤ 6400 := by
    apply (div_le_iff₀ (by positivity : 0 < rho / 64)).2
    nlinarith
  have midpointCeil :
      Nat.ceil ((7 + 3 * rho) / (rho / 64)) ≤ 44992 := by
    exact Nat.ceil_le.mpr midpointRatio
  have directionCeil :
      Nat.ceil (1 / (rho / 64)) ≤ 6400 := by
    exact Nat.ceil_le.mpr directionRatio
  exact packed.trans <| by
    unfold pureWZ2Prop62ProxyCenterCopyLargeScaleBound
    gcongr

/--
Every quotient center has a dimension-only number of actual parent copies,
with no dependence on `delta`, the actual scale, schedule depth, or family
cardinality.
-/
theorem pureWZ2_prop62_proxy_center_actualParents_card_le
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
    (center : Fin (quotient.level coordinate).centerFamily.card) :
    (quotient.centerActualParents coordinate center).card ≤
      pureWZ2Prop62ProxyCenterCopyPackingBound := by
  by_cases actualSmall :
      schedule.actualScale coordinate ≤ 1 / 100
  · exact
      (pureWZ2_prop62_proxy_center_actualParents_card_le_of_small
        schedule fineNonempty fineLine fineBase quotient coordinate
        actualSmall center).trans <|
          Nat.le_add_right _ _
  · have actualLarge :
        1 / 100 < schedule.actualScale coordinate :=
      lt_of_not_ge actualSmall
    exact
      (pureWZ2_prop62_proxy_center_actualParents_card_le_of_large
        schedule fineNonempty fineBase quotient coordinate
        actualLarge center).trans <|
          Nat.le_add_left _ _

/-- Uniform form over every coordinate and quotient center. -/
theorem pureWZ2_prop62_proxy_center_actualParents_card_le_all
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
        schedule fineNonempty) :
    ∀ coordinate center,
      (quotient.centerActualParents coordinate center).card ≤
        pureWZ2Prop62ProxyCenterCopyPackingBound := by
  intro coordinate center
  exact
    pureWZ2_prop62_proxy_center_actualParents_card_le
      schedule fineNonempty fineLine fineBase quotient coordinate center

/-- Existential form matching the paper-audit copy-packing interface. -/
theorem exists_pureWZ2_prop62_proxy_center_copy_bound :
    ∃ copyBound : ℕ,
      ∀ (delta : ℝ),
        ∀ (fine : Kakeya.Streamlined.TubeFamily delta),
          ∀ (ambientConstant scaleWindow : ENNReal),
            ∀ (schedule :
                PureWZ2Prop62LaminarPureSchedule
                  fine ambientConstant scaleWindow),
              ∀ (fineNonempty : fine.Nonempty),
                ∀ (fineLine : WZ1PaperIsLineClass fine),
                  ∀ (fineBase :
                      ∀ source, ‖(fine.tube source).base‖ ≤ 5),
                    ∀ (quotient :
                        PureWZ2Prop62ProxyQuotientScheduleData
                          schedule fineNonempty),
                      ∀ coordinate center,
                        (quotient.centerActualParents
                          coordinate center).card ≤ copyBound := by
  refine ⟨pureWZ2Prop62ProxyCenterCopyPackingBound, ?_⟩
  intro delta fine ambientConstant scaleWindow schedule fineNonempty
    fineLine fineBase quotient coordinate center
  exact
    pureWZ2_prop62_proxy_center_actualParents_card_le
      schedule fineNonempty fineLine fineBase quotient coordinate center

end Kakeya.Assouad

end
