import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.CompleteFiberOverlap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.Reanchoring

/-!
# Common-anchor parent containment

If a source tube lies in a complete fixed-dilation GWZ fiber and meets the
localization ball, then canonical coaxial reanchoring at the common cell
center turns it into strict ordinary containment in one canonically
reanchored parent of radius `8 * A * rho`.

The proof uses only complete geometric containment.  The common anchor removes
the uncontrolled unit-segment endpoint displacement that made the historical
unchanged-carrier Node 9 statement false.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

/-- The canonically reanchored parent, enlarged to the safe radius `8*A*rho`. -/
def pureWZ2ReanchoredParentTube
    {rho A : ℝ}
    (center : Point3)
    (parent : Kakeya.DeltaTube rho) :
    Kakeya.DeltaTube (8 * A * rho) where
  base :=
    pureWZ2ReanchoredMidpoint center parent -
      (1 / 2 : ℝ) • parent.direction
  direction := parent.direction
  direction_unit := parent.direction_unit

@[simp] theorem pureWZ2ReanchoredParentTube_direction
    {rho A : ℝ}
    (center : Point3)
    (parent : Kakeya.DeltaTube rho) :
    (pureWZ2ReanchoredParentTube
      (A := A) center parent).direction =
      parent.direction :=
  rfl

theorem pureWZ2ReanchoredParentTube_midpoint
    {rho A : ℝ}
    (center : Point3)
    (parent : Kakeya.DeltaTube rho) :
    wz2PaperTubeMidpoint
        (pureWZ2ReanchoredParentTube
          (A := A) center parent) =
      pureWZ2ReanchoredMidpoint center parent := by
  simp [pureWZ2ReanchoredParentTube,
    wz2PaperTubeMidpoint]

private theorem pureWZ2_reanchoredMidpoint_sub_axisPoint
    {delta : ℝ}
    (center : Point3)
    (tube : Kakeya.DeltaTube delta)
    (parameter : ℝ) :
    pureWZ2ReanchoredMidpoint center tube -
        (tube.base + parameter • tube.direction) =
      inner ℝ
          (center -
            (tube.base + parameter • tube.direction))
          tube.direction • tube.direction := by
  let midpoint := wz2PaperTubeMidpoint tube
  have haxis :
      tube.base + parameter • tube.direction =
        midpoint +
          (parameter - 1 / 2 : ℝ) • tube.direction := by
    dsimp only [midpoint, wz2PaperTubeMidpoint]
    module
  rw [pureWZ2ReanchoredMidpoint, haxis]
  have hinner :
      inner ℝ
          (center -
            (midpoint +
              (parameter - 1 / 2 : ℝ) • tube.direction))
          tube.direction =
        inner ℝ (center - midpoint) tube.direction -
          (parameter - 1 / 2) := by
    rw [show
      center -
          (midpoint +
            (parameter - 1 / 2 : ℝ) • tube.direction) =
        (center - midpoint) -
          (parameter - 1 / 2 : ℝ) • tube.direction by
      abel,
      inner_sub_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, tube.direction_unit]
    ring
  rw [hinner]
  module

private theorem pureWZ2_reanchoredMidpoint_sub_center_orthogonal
    {delta : ℝ}
    (center : Point3)
    (tube : Kakeya.DeltaTube delta) :
    inner ℝ
        (pureWZ2ReanchoredMidpoint center tube - center)
        tube.direction = 0 := by
  rw [pureWZ2ReanchoredMidpoint]
  have hvector :
      wz2PaperTubeMidpoint tube +
          inner ℝ
              (center - wz2PaperTubeMidpoint tube)
              tube.direction • tube.direction -
          center =
        -(center - wz2PaperTubeMidpoint tube) +
          inner ℝ
              (center - wz2PaperTubeMidpoint tube)
              tube.direction • tube.direction := by
    abel
  rw [hvector, inner_add_left, inner_neg_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq,
    tube.direction_unit]
  ring

private theorem pureWZ2_reanchoredMidpoint_dist_center_le
    {delta radius : ℝ}
    (hdelta : 0 ≤ delta)
    {center point : Point3}
    {tube : Kakeya.DeltaTube delta}
    (hpointTube : point ∈ tube.carrier)
    (hpointBall : point ∈ Metric.closedBall center radius) :
    dist
        (pureWZ2ReanchoredMidpoint center tube)
        center ≤
      radius + delta := by
  rcases
      exists_closest_on_axis
        hdelta tube point hpointTube with
    ⟨parameter, _, hpointAxis⟩
  let axisPoint :=
    tube.base + parameter • tube.direction
  have hcenterAxis :
      dist center axisPoint ≤ radius + delta := by
    calc
      dist center axisPoint ≤
          dist center point + dist point axisPoint :=
        dist_triangle _ _ _
      _ ≤ radius + delta := by
        gcongr
        simpa [Metric.mem_closedBall, dist_comm] using
          hpointBall
  have hprojection :
      ‖pureWZ2ReanchoredMidpoint center tube -
          axisPoint‖ ≤ ‖center - axisPoint‖ := by
    rw [pureWZ2_reanchoredMidpoint_sub_axisPoint]
    calc
      ‖inner ℝ (center - axisPoint) tube.direction •
          tube.direction‖ =
          |inner ℝ (center - axisPoint) tube.direction| := by
        rw [norm_smul, tube.direction_unit,
          Real.norm_eq_abs, mul_one]
      _ ≤ ‖center - axisPoint‖ :=
        (abs_real_inner_le_norm
          (center - axisPoint) tube.direction).trans_eq
          (by rw [tube.direction_unit, mul_one])
  have hclosest :
      dist
          (pureWZ2ReanchoredMidpoint center tube)
          center ≤
        dist axisPoint center := by
    have horthogonal :
        inner ℝ
            (pureWZ2ReanchoredMidpoint center tube -
              axisPoint)
            (center -
              pureWZ2ReanchoredMidpoint center tube) = 0 := by
      have hfirstParallel :=
        pureWZ2_reanchoredMidpoint_sub_axisPoint
          center tube parameter
      have hsecondOrthogonal :
          inner ℝ
              (center -
                pureWZ2ReanchoredMidpoint center tube)
              tube.direction = 0 := by
        rw [show center -
            pureWZ2ReanchoredMidpoint center tube =
          -(pureWZ2ReanchoredMidpoint center tube -
            center) by abel,
          inner_neg_left,
          pureWZ2_reanchoredMidpoint_sub_center_orthogonal]
        simp
      rw [hfirstParallel, real_inner_smul_left]
      have hsecondOrthogonal' :
          inner ℝ tube.direction
              (center -
                pureWZ2ReanchoredMidpoint center tube) = 0 := by
        rw [real_inner_comm]
        exact hsecondOrthogonal
      rw [hsecondOrthogonal', mul_zero]
    have hpythagoras :
        ‖axisPoint - center‖ ^ 2 =
          ‖axisPoint -
              pureWZ2ReanchoredMidpoint center tube‖ ^ 2 +
            ‖pureWZ2ReanchoredMidpoint center tube -
              center‖ ^ 2 := by
      have hdecomp :
          axisPoint - center =
            (axisPoint -
              pureWZ2ReanchoredMidpoint center tube) +
            (pureWZ2ReanchoredMidpoint center tube -
              center) := by
        abel
      rw [hdecomp]
      have horthogonal' :
          inner ℝ
              (axisPoint -
                pureWZ2ReanchoredMidpoint center tube)
              (pureWZ2ReanchoredMidpoint center tube -
                center) = 0 := by
        have hreverse :
            inner ℝ
                (pureWZ2ReanchoredMidpoint center tube -
                  axisPoint)
                (pureWZ2ReanchoredMidpoint center tube -
                  center) = 0 := by
          rw [show
            pureWZ2ReanchoredMidpoint center tube - center =
              -(center -
                pureWZ2ReanchoredMidpoint center tube) by
            abel,
            inner_neg_right, horthogonal]
          simp
        rw [show axisPoint -
            pureWZ2ReanchoredMidpoint center tube =
          -(pureWZ2ReanchoredMidpoint center tube -
            axisPoint) by abel,
          inner_neg_left, hreverse]
        simp
      simpa [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_real horthogonal'
    rw [dist_eq_norm, dist_eq_norm]
    nlinarith [
      norm_nonneg
        (pureWZ2ReanchoredMidpoint center tube - center),
      norm_nonneg (axisPoint - center),
      sq_nonneg
        ‖axisPoint -
          pureWZ2ReanchoredMidpoint center tube‖]
  exact
    hclosest.trans (by
      simpa [dist_comm] using hcenterAxis)

private theorem pureWZ2_clamp_half_mem
    (value : ℝ) :
    max (-(1 / 2 : ℝ)) (min (1 / 2 : ℝ) value) ∈
      Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

private theorem pureWZ2_clamp_half_gap
    (value error : ℝ)
    (hvalue : |value| ≤ 1 / 2 + error)
    (herror : 0 ≤ error) :
    |value -
        max (-(1 / 2 : ℝ))
          (min (1 / 2 : ℝ) value)| ≤
      error := by
  by_cases hlower : value < -(1 / 2 : ℝ)
  · have hmin : min (1 / 2 : ℝ) value = value :=
      min_eq_right (by linarith)
    have hmax :
        max (-(1 / 2 : ℝ)) value =
          -(1 / 2 : ℝ) :=
      max_eq_left (by linarith)
    rw [hmin, hmax, abs_of_nonpos (by linarith)]
    have habs := (abs_le.mp hvalue).1
    linarith
  · by_cases hupper : 1 / 2 < value
    · have hmin :
          min (1 / 2 : ℝ) value = 1 / 2 :=
        min_eq_left (by linarith)
      have hmax :
          max (-(1 / 2 : ℝ)) (1 / 2) = 1 / 2 := by
        norm_num
      rw [hmin, hmax, abs_of_nonneg (by linarith)]
      have habs := (abs_le.mp hvalue).2
      linarith
    · have hmin :
          min (1 / 2 : ℝ) value = value :=
        min_eq_right (by linarith)
      have hmax :
          max (-(1 / 2 : ℝ)) value = value :=
        max_eq_right (by linarith)
      rw [hmin, hmax]
      simpa using herror

private theorem pureWZ2_reanchored_axis_distance
    {delta rho A radius : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hA : 1 ≤ A)
    (hdeltaRho : delta ≤ rho)
    (hrhoSmall : rho ≤ 1 / (200 * A))
    (hradius : 0 ≤ radius)
    (hradiusSmall : radius ≤ 1 / 4)
    {center point : Point3}
    {source : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (hpointSource : point ∈ source.carrier)
    (hpointBall : point ∈ Metric.closedBall center radius)
    (hcontainment :
      source.carrier ⊆
        wz2PaperCenteredDilatedCarrier A parent) :
    ∀ parameter : ℝ,
      parameter ∈ Set.Icc (0 : ℝ) 1 →
      Metric.infDist
          ((pureWZ2ReanchoredTube center source).base +
            parameter •
              (pureWZ2ReanchoredTube center source).direction)
          (Kakeya.unitSegment
            (pureWZ2ReanchoredParentTube
              (A := A) center parent).base
            (pureWZ2ReanchoredParentTube
              (A := A) center parent).direction) ≤
        6 * A * rho := by
  intro parameter hparameter
  let sourceMidpoint :=
    pureWZ2ReanchoredMidpoint center source
  let parentMidpoint :=
    pureWZ2ReanchoredMidpoint center parent
  let sourceDirection := source.direction
  let parentDirection := parent.direction
  let sourceScalar := parameter - 1 / 2
  let sourceAxisPoint :=
    sourceMidpoint + sourceScalar • sourceDirection
  have hsourceScalar :
      |sourceScalar| ≤ 1 / 2 := by
    dsimp only [sourceScalar]
    rw [abs_le]
    constructor <;> linarith [hparameter.1, hparameter.2]
  have hsourcePoint :
      (pureWZ2ReanchoredTube center source).base +
          parameter •
            (pureWZ2ReanchoredTube center source).direction =
        sourceAxisPoint := by
    dsimp only [sourceAxisPoint, sourceMidpoint,
      sourceScalar, pureWZ2ReanchoredTube]
    module
  rcases
      exists_closest_on_axis
        hdelta.le source point hpointSource with
    ⟨sourceParameter, _, hpointAxis⟩
  let originalAxisPoint :=
    source.base + sourceParameter • source.direction
  have horiginalAxisCarrier :
      originalAxisPoint ∈ source.carrier := by
    exact
      Metric.mem_cthickening_of_dist_le
        originalAxisPoint originalAxisPoint delta
        (Kakeya.unitSegment source.base source.direction)
        ⟨sourceParameter, by assumption, rfl⟩
        (by simp [hdelta.le])
  rcases
      pureWZ2_general_dilation_closest_point
        hrho.le (by linarith) parent
        originalAxisPoint
        (hcontainment horiginalAxisCarrier) with
    ⟨parentParameter, _, haxisDistance⟩
  let originalParentAxisPoint :=
    parent.base + parentParameter • parent.direction
  have hcenterOriginalAxis :
      dist center originalAxisPoint ≤ radius + delta := by
    calc
      dist center originalAxisPoint ≤
          dist center point + dist point originalAxisPoint :=
        dist_triangle _ _ _
      _ ≤ radius + delta := by
        gcongr
        simpa [Metric.mem_closedBall, dist_comm] using hpointBall
  have hsourceMidpointAxis :
      sourceMidpoint - originalAxisPoint =
        inner ℝ (center - originalAxisPoint)
          sourceDirection • sourceDirection := by
    exact
      pureWZ2_reanchoredMidpoint_sub_axisPoint
        center source sourceParameter
  have hsourceShift :
      ‖sourceMidpoint - originalAxisPoint‖ ≤
        radius + delta := by
    rw [hsourceMidpointAxis, norm_smul,
      source.direction_unit, Real.norm_eq_abs, mul_one]
    exact
      (abs_real_inner_le_norm
        (center - originalAxisPoint)
        sourceDirection).trans
        (by
          rw [source.direction_unit, mul_one,
            ← dist_eq_norm]
          simpa [dist_comm] using hcenterOriginalAxis)
  have hsourcePerp :
      ‖sourceDirection -
          inner ℝ sourceDirection parentDirection •
            parentDirection‖ ≤
        2 * A * rho := by
    exact
      (gwz_direction_constraint
        hdelta hrho hA
        (by
          have hArho : rho ≤ A * rho := by nlinarith
          exact hdeltaRho.trans hArho)
        source parent hcontainment).trans
        (by linarith)
  have hparentPerp :
      ‖parentDirection -
          inner ℝ parentDirection sourceDirection •
            sourceDirection‖ ≤
        2 * A * rho := by
    exact
      (pureWZ2_projective_parent_direction
        hdelta hrho hA hrhoSmall
        (by
          have hArho : rho ≤ A * rho := by nlinarith
          exact hdeltaRho.trans hArho)
        source parent hcontainment).1
  let midpointDifference :=
    sourceMidpoint - parentMidpoint
  let longitudinal :=
    inner ℝ midpointDifference parentDirection
  have hparentOrthogonal :
      inner ℝ
          (parentMidpoint - center)
          parentDirection = 0 :=
    pureWZ2_reanchoredMidpoint_sub_center_orthogonal
      center parent
  have hsourceOrthogonal :
      inner ℝ
          (sourceMidpoint - center)
          sourceDirection = 0 :=
    pureWZ2_reanchoredMidpoint_sub_center_orthogonal
      center source
  have hsourceCenter :
      ‖sourceMidpoint - center‖ ≤ radius + delta := by
    simpa [dist_eq_norm] using
      pureWZ2_reanchoredMidpoint_dist_center_le
        hdelta.le hpointSource hpointBall
  have hlongitudinal :
      |longitudinal| ≤ 2 * A * rho := by
    have heq :
        longitudinal =
          inner ℝ
            (sourceMidpoint - center)
            (parentDirection -
              inner ℝ parentDirection sourceDirection •
                sourceDirection) := by
      dsimp only [longitudinal, midpointDifference]
      rw [show sourceMidpoint - parentMidpoint =
        (sourceMidpoint - center) -
          (parentMidpoint - center) by abel,
        inner_sub_left, hparentOrthogonal, sub_zero,
        inner_sub_right, real_inner_smul_right,
        hsourceOrthogonal]
      ring
    rw [heq]
    calc
      |inner ℝ
          (sourceMidpoint - center)
          (parentDirection -
            inner ℝ parentDirection sourceDirection •
              sourceDirection)|
          ≤
        ‖sourceMidpoint - center‖ *
          ‖parentDirection -
            inner ℝ parentDirection sourceDirection •
              sourceDirection‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (radius + delta) * (2 * A * rho) := by
        gcongr
      _ ≤ 2 * A * rho := by
        have hrhoOne : rho ≤ 1 / 200 := by
          have hApos : 0 < A := by linarith
          calc
            rho ≤ 1 / (200 * A) := hrhoSmall
            _ ≤ 1 / 200 := by
              apply one_div_le_one_div_of_le
              · norm_num
              · nlinarith
        have hradiusDelta : radius + delta ≤ 1 := by
          linarith [hdeltaRho, hradiusSmall, hrhoOne]
        calc
          (radius + delta) * (2 * A * rho)
              ≤ 1 * (2 * A * rho) :=
            mul_le_mul_of_nonneg_right
              hradiusDelta (by positivity)
          _ = 2 * A * rho := by ring
  have hmidpointTransverse :
      ‖midpointDifference -
          longitudinal • parentDirection‖ ≤
        3 * A * rho := by
    have hparentAxis :
        parentMidpoint - originalParentAxisPoint =
          inner ℝ
              (center - originalParentAxisPoint)
              parentDirection • parentDirection :=
      pureWZ2_reanchoredMidpoint_sub_axisPoint
        center parent parentParameter
    have hperpInvariant :
        midpointDifference -
            longitudinal • parentDirection =
          (sourceMidpoint - originalParentAxisPoint) -
            inner ℝ
                (sourceMidpoint - originalParentAxisPoint)
                parentDirection • parentDirection := by
      have hparentMidpoint :
          parentMidpoint =
            originalParentAxisPoint +
              inner ℝ
                  (center - originalParentAxisPoint)
                  parentDirection • parentDirection := by
        rw [show parentMidpoint =
          (parentMidpoint - originalParentAxisPoint) +
            originalParentAxisPoint by abel,
          hparentAxis]
        abel
      dsimp only [midpointDifference, longitudinal]
      let coefficient :=
        inner ℝ
          (center - originalParentAxisPoint)
          parentDirection
      have hvector :
          sourceMidpoint - parentMidpoint =
            (sourceMidpoint - originalParentAxisPoint) -
              coefficient • parentDirection := by
        rw [hparentMidpoint]
        dsimp only [coefficient]
        abel
      have hinner :
          inner ℝ
              ((sourceMidpoint - originalParentAxisPoint) -
                coefficient • parentDirection)
              parentDirection =
            inner ℝ
                (sourceMidpoint - originalParentAxisPoint)
                parentDirection -
              coefficient := by
        rw [inner_sub_left,
          real_inner_smul_left,
          real_inner_self_eq_norm_sq,
          parent.direction_unit]
        ring
      rw [hvector, hinner]
      module
    have hdecomp :
        sourceMidpoint - originalParentAxisPoint =
          (sourceMidpoint - originalAxisPoint) +
            (originalAxisPoint - originalParentAxisPoint) := by
      abel
    have hperpSum :
        (sourceMidpoint - originalParentAxisPoint) -
            inner ℝ
                (sourceMidpoint - originalParentAxisPoint)
                parentDirection • parentDirection =
          ((sourceMidpoint - originalAxisPoint) -
            inner ℝ
                (sourceMidpoint - originalAxisPoint)
                parentDirection • parentDirection) +
          ((originalAxisPoint - originalParentAxisPoint) -
            inner ℝ
                (originalAxisPoint - originalParentAxisPoint)
                parentDirection • parentDirection) := by
      rw [hdecomp, inner_add_left, add_smul]
      abel
    have hfirst :
        ‖(sourceMidpoint - originalAxisPoint) -
            inner ℝ
                (sourceMidpoint - originalAxisPoint)
                parentDirection • parentDirection‖ ≤
          2 * A * rho := by
      rw [hsourceMidpointAxis, real_inner_smul_left]
      have hfactor :
          inner ℝ
              (center - originalAxisPoint)
              sourceDirection • sourceDirection -
            (inner ℝ
                (center - originalAxisPoint)
                sourceDirection *
              inner ℝ sourceDirection parentDirection) •
              parentDirection =
            inner ℝ
                (center - originalAxisPoint)
                sourceDirection •
              (sourceDirection -
                inner ℝ sourceDirection parentDirection •
                  parentDirection) := by
        module
      rw [hfactor, norm_smul, Real.norm_eq_abs]
      calc
        |inner ℝ
            (center - originalAxisPoint)
            sourceDirection| *
            ‖sourceDirection -
              inner ℝ sourceDirection parentDirection •
                parentDirection‖
            ≤
          (radius + delta) * (2 * A * rho) := by
          gcongr
          exact
            (abs_real_inner_le_norm
              (center - originalAxisPoint)
              sourceDirection).trans
              (by
                rw [source.direction_unit, mul_one,
                  ← dist_eq_norm]
                simpa [dist_comm] using hcenterOriginalAxis)
        _ ≤ 2 * A * rho := by
          have hrhoOne : rho ≤ 1 / 200 := by
            have hApos : 0 < A := by linarith
            calc
              rho ≤ 1 / (200 * A) := hrhoSmall
              _ ≤ 1 / 200 := by
                apply one_div_le_one_div_of_le
                · norm_num
                · nlinarith
          have hradiusDelta : radius + delta ≤ 1 := by
            linarith [hdeltaRho, hradiusSmall, hrhoOne]
          calc
            (radius + delta) * (2 * A * rho)
                ≤ 1 * (2 * A * rho) :=
              mul_le_mul_of_nonneg_right
                hradiusDelta (by positivity)
            _ = 2 * A * rho := by ring
    have hsecond :
        ‖(originalAxisPoint - originalParentAxisPoint) -
            inner ℝ
                (originalAxisPoint - originalParentAxisPoint)
                parentDirection • parentDirection‖ ≤
          A * rho := by
      exact
        (pureWZ2_perp_norm_le
          parentDirection
          (originalAxisPoint - originalParentAxisPoint)
          parent.direction_unit).trans
          (by
            simpa [dist_eq_norm] using haxisDistance)
    rw [hperpInvariant, hperpSum]
    calc
      ‖((sourceMidpoint - originalAxisPoint) -
            inner ℝ
                (sourceMidpoint - originalAxisPoint)
                parentDirection • parentDirection) +
          ((originalAxisPoint - originalParentAxisPoint) -
            inner ℝ
                (originalAxisPoint - originalParentAxisPoint)
                parentDirection • parentDirection)‖
          ≤ _ :=
        norm_add_le _ _
      _ ≤ 3 * A * rho := by linarith
  let coefficient :=
    inner ℝ sourceDirection parentDirection
  let rawParentCoordinate :=
    longitudinal + sourceScalar * coefficient
  let clampedParentCoordinate :=
    max (-(1 / 2 : ℝ))
      (min (1 / 2 : ℝ) rawParentCoordinate)
  have hcoefficient :
      |coefficient| ≤ 1 := by
    exact
      (abs_real_inner_le_norm
        sourceDirection parentDirection).trans
        (by
          rw [source.direction_unit,
            parent.direction_unit]
          norm_num)
  have hrawCoordinate :
      |rawParentCoordinate| ≤
        1 / 2 + 2 * A * rho := by
    dsimp only [rawParentCoordinate]
    calc
      |longitudinal + sourceScalar * coefficient|
          ≤ |longitudinal| +
            |sourceScalar| * |coefficient| := by
        simpa [abs_mul] using
          abs_add_le longitudinal
            (sourceScalar * coefficient)
      _ ≤ 2 * A * rho + (1 / 2) * 1 := by
        gcongr
      _ = 1 / 2 + 2 * A * rho := by ring
  have hclamped :
      clampedParentCoordinate ∈
        Set.Icc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) :=
    pureWZ2_clamp_half_mem rawParentCoordinate
  have hgap :
      |rawParentCoordinate - clampedParentCoordinate| ≤
        2 * A * rho :=
    pureWZ2_clamp_half_gap
      rawParentCoordinate (2 * A * rho)
      hrawCoordinate (by positivity)
  let parentAxisPoint :=
    parentMidpoint +
      clampedParentCoordinate • parentDirection
  have hparentAxisPoint :
      parentAxisPoint ∈
        Kakeya.unitSegment
          (pureWZ2ReanchoredParentTube
            (A := A) center parent).base
          (pureWZ2ReanchoredParentTube
            (A := A) center parent).direction := by
    refine
      ⟨clampedParentCoordinate + 1 / 2,
        ⟨by linarith [hclamped.1],
          by linarith [hclamped.2]⟩, ?_⟩
    dsimp only [parentAxisPoint,
      pureWZ2ReanchoredParentTube, parentMidpoint]
    module
  have hdifference :
      sourceAxisPoint - parentAxisPoint =
        (midpointDifference -
          longitudinal • parentDirection) +
        sourceScalar •
          (sourceDirection -
            coefficient • parentDirection) +
        (rawParentCoordinate -
          clampedParentCoordinate) • parentDirection := by
    dsimp only [sourceAxisPoint, parentAxisPoint,
      midpointDifference, longitudinal,
      rawParentCoordinate, coefficient]
    module
  have hdistance :
      dist sourceAxisPoint parentAxisPoint ≤
        6 * A * rho := by
    rw [dist_eq_norm, hdifference]
    calc
      ‖(midpointDifference -
            longitudinal • parentDirection) +
          sourceScalar •
            (sourceDirection -
              coefficient • parentDirection) +
          (rawParentCoordinate -
            clampedParentCoordinate) • parentDirection‖
          ≤
        ‖midpointDifference -
            longitudinal • parentDirection‖ +
          ‖sourceScalar •
            (sourceDirection -
              coefficient • parentDirection)‖ +
          ‖(rawParentCoordinate -
            clampedParentCoordinate) • parentDirection‖ := by
        calc
          ‖(midpointDifference -
                longitudinal • parentDirection) +
              sourceScalar •
                (sourceDirection -
                  coefficient • parentDirection) +
              (rawParentCoordinate -
                clampedParentCoordinate) • parentDirection‖
              ≤
            ‖(midpointDifference -
                longitudinal • parentDirection) +
              sourceScalar •
                (sourceDirection -
                  coefficient • parentDirection)‖ +
            ‖(rawParentCoordinate -
                clampedParentCoordinate) • parentDirection‖ :=
              norm_add_le _ _
          _ ≤
            (‖midpointDifference -
                longitudinal • parentDirection‖ +
              ‖sourceScalar •
                (sourceDirection -
                  coefficient • parentDirection)‖) +
            ‖(rawParentCoordinate -
                clampedParentCoordinate) • parentDirection‖ :=
              by
                linarith [norm_add_le
                  (midpointDifference -
                    longitudinal • parentDirection)
                  (sourceScalar •
                    (sourceDirection -
                      coefficient • parentDirection))]
      _ ≤
          3 * A * rho +
            (1 / 2) * (2 * A * rho) +
            (2 * A * rho) * 1 := by
        rw [norm_smul, norm_smul,
          Real.norm_eq_abs, Real.norm_eq_abs,
          parent.direction_unit]
        gcongr
      _ = 6 * A * rho := by ring
  rw [hsourcePoint]
  exact
    (Metric.infDist_le_dist_of_mem hparentAxisPoint).trans
      hdistance

/--
Complete fixed-dilation containment plus a common localization anchor yields
strict ordinary containment after canonical reanchoring.
-/
theorem pureWZ2_reanchored_complete_parent_containment
    {delta rho A radius : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hA : 1 ≤ A)
    (hdeltaRho : delta ≤ rho)
    (hrhoSmall : rho ≤ 1 / (200 * A))
    (hradius : 0 ≤ radius)
    (hradiusSmall : radius ≤ 1 / 4)
    {center point : Point3}
    {source : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (hpointSource : point ∈ source.carrier)
    (hpointBall : point ∈ Metric.closedBall center radius)
    (hcontainment :
      source.carrier ⊆
        wz2PaperCenteredDilatedCarrier A parent) :
    (pureWZ2ReanchoredTube center source).carrier ⊆
      (pureWZ2ReanchoredParentTube
        (A := A) center parent).carrier := by
  have hscale :
      delta ≤ 8 * A * rho := by
    have hrhoScale : rho ≤ 8 * A * rho := by
      nlinarith
    exact hdeltaRho.trans hrhoScale
  have hsegment :
      ∀ parameter : ℝ,
        parameter ∈ Set.Icc (0 : ℝ) 1 →
        Metric.infDist
            ((pureWZ2ReanchoredTube center source).base +
              parameter •
                (pureWZ2ReanchoredTube center source).direction)
            (Kakeya.unitSegment
              (pureWZ2ReanchoredParentTube
                (A := A) center parent).base
              (pureWZ2ReanchoredParentTube
                (A := A) center parent).direction) ≤
          8 * A * rho - delta := by
    intro parameter hparameter
    have hbound :=
      pureWZ2_reanchored_axis_distance
        hdelta hrho hA hdeltaRho hrhoSmall
        hradius hradiusSmall
        hpointSource hpointBall hcontainment
        parameter hparameter
    calc
      _ ≤ 6 * A * rho := hbound
      _ ≤ 8 * A * rho - delta := by
        have : delta ≤ rho := hdeltaRho
        nlinarith
  let sourceReanchored :=
    pureWZ2ReanchoredTube center source
  let parentReanchored :=
    pureWZ2ReanchoredParentTube
      (A := A) center parent
  let sourceSegment :=
    Kakeya.unitSegment
      sourceReanchored.base sourceReanchored.direction
  let parentSegment :=
    Kakeya.unitSegment
      parentReanchored.base parentReanchored.direction
  have hsourceCompact : IsCompact sourceSegment := by
    exact isCompact_Icc.image
      (continuous_const.add
        (continuous_id.smul continuous_const))
  have hparentCompact : IsCompact parentSegment := by
    exact isCompact_Icc.image
      (continuous_const.add
        (continuous_id.smul continuous_const))
  have hparentNonempty : parentSegment.Nonempty :=
    ⟨parentReanchored.base,
      ⟨0, by norm_num, by simp⟩⟩
  have hsourceUnion :
      sourceReanchored.carrier =
        ⋃ axisPoint ∈ sourceSegment,
          Metric.closedBall axisPoint delta :=
    hsourceCompact.cthickening_eq_biUnion_closedBall
      hdelta.le
  intro arbitrary harbitrary
  change arbitrary ∈ sourceReanchored.carrier at harbitrary
  rw [hsourceUnion] at harbitrary
  rcases Set.mem_iUnion₂.mp harbitrary with
    ⟨axisPoint, haxisPoint, harbitraryAxis⟩
  rcases haxisPoint with
    ⟨parameter, hparameter, rfl⟩
  have haxisDistance :
      Metric.infDist
          (sourceReanchored.base +
            parameter • sourceReanchored.direction)
          parentSegment ≤
        8 * A * rho - delta :=
    hsegment parameter hparameter
  rcases
      hparentCompact.exists_infDist_eq_dist
        hparentNonempty
        (sourceReanchored.base +
          parameter • sourceReanchored.direction) with
    ⟨parentPoint, hparentPoint, hdistance⟩
  have haxisParent :
      dist
          (sourceReanchored.base +
            parameter • sourceReanchored.direction)
          parentPoint ≤
        8 * A * rho - delta := by
    rw [← hdistance]
    exact haxisDistance
  have harbitraryAxisDistance :
      dist arbitrary
          (sourceReanchored.base +
            parameter • sourceReanchored.direction) ≤
        delta := by
    simpa [Metric.mem_closedBall] using harbitraryAxis
  have harbitraryParent :
      dist arbitrary parentPoint ≤ 8 * A * rho := by
    calc
      dist arbitrary parentPoint ≤
          dist arbitrary
              (sourceReanchored.base +
                parameter • sourceReanchored.direction) +
            dist
              (sourceReanchored.base +
                parameter • sourceReanchored.direction)
              parentPoint :=
        dist_triangle _ _ _
      _ ≤ delta + (8 * A * rho - delta) := by
        gcongr
      _ = 8 * A * rho := by ring
  exact
    Metric.mem_cthickening_of_dist_le
      arbitrary parentPoint (8 * A * rho)
      parentSegment hparentPoint harbitraryParent

end Kakeya.Assouad

end
