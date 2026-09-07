import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnchoredParentContainment

/-!
# Active-parent geometry at the localization anchor

An original GWZ parent is active when one complete-fiber child meets the
common localization ball.  This controls:

* the distance from the common anchor to the parent coaxial line;
* the axial translation from the canonically reanchored parent midpoint back
  to the original parent midpoint.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

/-- A tube lies in the radius-`rho + 1/2` ball around its midpoint. -/
theorem pureWZ2_tube_carrier_subset_midpoint_ball
    {rho : ℝ}
    (hrho : 0 ≤ rho)
    (tube : Kakeya.DeltaTube rho) :
    tube.carrier ⊆
      Metric.closedBall
        (wz2PaperTubeMidpoint tube) (rho + 1 / 2) := by
  have hsegmentCompact :
      IsCompact
        (Kakeya.unitSegment tube.base tube.direction) := by
    apply IsCompact.image isCompact_Icc
    exact
      continuous_const.add
        (continuous_id.smul continuous_const)
  have hsegmentClosed :
      IsClosed
        (Kakeya.unitSegment tube.base tube.direction) :=
    hsegmentCompact.isClosed
  intro point hpoint
  have haxis :
      ∃ axisPoint :
          Point3,
        axisPoint ∈
            Kakeya.unitSegment tube.base tube.direction ∧
          dist point axisPoint ≤ rho := by
    have hmember :
        point ∈
          Metric.cthickening rho
            (Kakeya.unitSegment
              tube.base tube.direction) :=
      hpoint
    rw [Metric.cthickening_eq_biUnion_closedBall
      (Kakeya.unitSegment tube.base tube.direction)
      hrho] at hmember
    have :
        point ∈
          ⋃ axisPoint ∈
            Kakeya.unitSegment tube.base tube.direction,
              Metric.closedBall axisPoint rho := by
      simpa [hsegmentClosed.closure_eq] using hmember
    simpa [Set.mem_iUnion, Metric.mem_closedBall] using this
  rcases haxis with
    ⟨axisPoint, haxisPoint, hpointAxis⟩
  have haxisMidpoint :
      dist axisPoint (wz2PaperTubeMidpoint tube) ≤
        1 / 2 := by
    rcases haxisPoint with
      ⟨parameter, hparameter, rfl⟩
    have hdistance :
        dist
            (tube.base + parameter • tube.direction)
            (tube.base + (1 / 2 : ℝ) •
              tube.direction) =
          |parameter - 1 / 2| := by
      have hdifference :
          (tube.base + parameter • tube.direction) -
              (tube.base + (1 / 2 : ℝ) •
                tube.direction) =
            (parameter - 1 / 2 : ℝ) •
              tube.direction := by
        simp [sub_smul]
      rw [dist_eq_norm, hdifference, norm_smul,
        tube.direction_unit]
      simp
    rw [show
      wz2PaperTubeMidpoint tube =
        tube.base +
          (1 / 2 : ℝ) • tube.direction by
      rfl, hdistance, abs_le]
    constructor <;>
      linarith [hparameter.1, hparameter.2]
  calc
    dist point (wz2PaperTubeMidpoint tube) ≤
        dist point axisPoint +
          dist axisPoint
            (wz2PaperTubeMidpoint tube) :=
      dist_triangle point axisPoint _
    _ ≤ rho + 1 / 2 := by
      linarith

/--
An active complete-fiber parent passes within `radius + A*rho` of the common
localization center.
-/
theorem pureWZ2_active_parent_center_distance
    {delta rho A radius : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hA : 1 ≤ A)
    (hdeltaScale : delta ≤ A * rho)
    {center point : Point3}
    {source : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (hpointSource : point ∈ source.carrier)
    (hpointBall : point ∈ Metric.closedBall center radius)
    (hcontainment :
      source.carrier ⊆
        wz2PaperCenteredDilatedCarrier A parent) :
    dist
        (pureWZ2ReanchoredMidpoint center parent)
        center ≤
      radius + A * rho := by
  rcases
      exists_closest_on_axis
        hdelta.le source point hpointSource with
    ⟨parameter, hparameter, hpointAxis⟩
  let sourceAxisPoint :=
    source.base + parameter • source.direction
  have hsourceAxisSegment :
      sourceAxisPoint ∈
        Kakeya.unitSegment source.base source.direction :=
    ⟨parameter, hparameter, rfl⟩
  have hsourceAxisCenter :
      dist sourceAxisPoint center ≤ radius + delta := by
    calc
      dist sourceAxisPoint center ≤
          dist sourceAxisPoint point + dist point center :=
        dist_triangle _ _ _
      _ ≤ delta + radius := by
        gcongr
        · simpa [dist_comm] using hpointAxis
        · simpa [Metric.mem_closedBall] using hpointBall
      _ = radius + delta := by ring
  have hsourceAxisPerp :
      ‖(sourceAxisPoint - wz2PaperTubeMidpoint parent) -
          inner ℝ
              (sourceAxisPoint - wz2PaperTubeMidpoint parent)
              parent.direction • parent.direction‖ ≤
        A * rho - delta :=
    gwz_point_transverse_bound
      hdelta hrho hA hdeltaScale
      source parent hcontainment
      sourceAxisPoint hsourceAxisSegment
  have hprojection :
      pureWZ2ReanchoredMidpoint center parent - center =
        -((center - wz2PaperTubeMidpoint parent) -
          inner ℝ
              (center - wz2PaperTubeMidpoint parent)
              parent.direction • parent.direction) := by
    simp only [pureWZ2ReanchoredMidpoint]
    module
  have hdecomposition :
      (center - wz2PaperTubeMidpoint parent) -
          inner ℝ
              (center - wz2PaperTubeMidpoint parent)
              parent.direction • parent.direction =
        ((center - sourceAxisPoint) -
          inner ℝ (center - sourceAxisPoint)
              parent.direction • parent.direction) +
        ((sourceAxisPoint - wz2PaperTubeMidpoint parent) -
          inner ℝ
              (sourceAxisPoint - wz2PaperTubeMidpoint parent)
              parent.direction • parent.direction) := by
    rw [show center - wz2PaperTubeMidpoint parent =
      (center - sourceAxisPoint) +
        (sourceAxisPoint - wz2PaperTubeMidpoint parent) by
      abel,
      inner_add_left, add_smul]
    abel
  rw [dist_eq_norm, hprojection, norm_neg, hdecomposition]
  calc
    ‖((center - sourceAxisPoint) -
          inner ℝ (center - sourceAxisPoint)
              parent.direction • parent.direction) +
        ((sourceAxisPoint - wz2PaperTubeMidpoint parent) -
          inner ℝ
              (sourceAxisPoint - wz2PaperTubeMidpoint parent)
              parent.direction • parent.direction)‖
        ≤
      ‖(center - sourceAxisPoint) -
          inner ℝ (center - sourceAxisPoint)
              parent.direction • parent.direction‖ +
      ‖(sourceAxisPoint - wz2PaperTubeMidpoint parent) -
          inner ℝ
              (sourceAxisPoint - wz2PaperTubeMidpoint parent)
              parent.direction • parent.direction‖ :=
      norm_add_le _ _
    _ ≤ (radius + delta) + (A * rho - delta) := by
      gcongr
      exact
        (pureWZ2_perp_norm_le
          parent.direction
          (center - sourceAxisPoint)
          parent.direction_unit).trans
          (by
            rw [← dist_eq_norm]
            simpa [dist_comm] using hsourceAxisCenter)
    _ = radius + A * rho := by ring

/--
The original parent midpoint differs axially from its canonical reanchoring
by a bounded amount determined only by the fixed dilation and localization
radius.
-/
theorem pureWZ2_active_parent_axial_shift
    {delta rho A radius : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hA : 1 ≤ A)
    {center point : Point3}
    {source : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (hpointSource : point ∈ source.carrier)
    (hpointBall : point ∈ Metric.closedBall center radius)
    (hcontainment :
      source.carrier ⊆
        wz2PaperCenteredDilatedCarrier A parent) :
    |pureWZ2AxialShift center parent| ≤
      A / 2 + A * rho + radius + 1 / 2 + delta := by
  let sourceMidpoint := wz2PaperTubeMidpoint source
  let parentMidpoint := wz2PaperTubeMidpoint parent
  have hsourceMidpointCarrier :
      sourceMidpoint ∈ source.carrier :=
    wz2_paper_tubeMidpoint_mem_carrier source hdelta.le
  rcases
      pureWZ2_general_dilation_closest_point
        hrho.le (by linarith) parent
        sourceMidpoint
        (hcontainment hsourceMidpointCarrier) with
    ⟨parameter, hparameter, hdistance⟩
  let parentAxisPoint :=
    parent.base + parameter • parent.direction
  have hparentLongitudinal :
      |inner ℝ (parentMidpoint - sourceMidpoint)
          parent.direction| ≤
        A / 2 + A * rho := by
    have hdecomposition :
        parentMidpoint - sourceMidpoint =
          (parentMidpoint - parentAxisPoint) +
            (parentAxisPoint - sourceMidpoint) := by
      abel
    have haxis :
        parentMidpoint - parentAxisPoint =
          (1 / 2 - parameter : ℝ) • parent.direction := by
      dsimp only [parentMidpoint, parentAxisPoint,
        wz2PaperTubeMidpoint]
      module
    have hinnerAxis :
        inner ℝ
            (parentMidpoint - parentAxisPoint)
            parent.direction =
          1 / 2 - parameter := by
      rw [haxis, real_inner_smul_left,
        real_inner_self_eq_norm_sq,
        parent.direction_unit]
      norm_num
    rw [hdecomposition, inner_add_left,
      hinnerAxis]
    calc
      |1 / 2 - parameter +
          inner ℝ (parentAxisPoint - sourceMidpoint)
            parent.direction|
          ≤
        |1 / 2 - parameter| +
          |inner ℝ (parentAxisPoint - sourceMidpoint)
            parent.direction| :=
        abs_add_le _ _
      _ ≤ A / 2 + A * rho := by
        gcongr
        · rw [abs_le]
          constructor <;>
            linarith [hparameter.1, hparameter.2]
        · exact
            (abs_real_inner_le_norm
              (parentAxisPoint - sourceMidpoint)
              parent.direction).trans
              (by
                rw [parent.direction_unit, mul_one,
                  ← dist_eq_norm]
                simpa [dist_comm] using hdistance)
  have hsourceMidpointCenter :
      dist sourceMidpoint center ≤
        radius + 1 / 2 + delta := by
    rcases
        exists_closest_on_axis
          hdelta.le source point hpointSource with
      ⟨sourceParameter, hsourceParameter, hpointAxis⟩
    let sourceAxisPoint :=
      source.base + sourceParameter • source.direction
    have hmidpointAxis :
        dist sourceMidpoint sourceAxisPoint ≤ 1 / 2 := by
      rw [dist_eq_norm]
      have hvector :
          sourceMidpoint - sourceAxisPoint =
            (1 / 2 - sourceParameter : ℝ) •
              source.direction := by
        dsimp only [sourceMidpoint, sourceAxisPoint,
          wz2PaperTubeMidpoint]
        module
      rw [hvector, norm_smul, Real.norm_eq_abs,
        source.direction_unit, mul_one, abs_le]
      constructor <;>
        linarith [hsourceParameter.1, hsourceParameter.2]
    calc
      dist sourceMidpoint center ≤
          dist sourceMidpoint sourceAxisPoint +
            dist sourceAxisPoint point +
              dist point center := by
        calc
          dist sourceMidpoint center ≤
              dist sourceMidpoint sourceAxisPoint +
                dist sourceAxisPoint center :=
            dist_triangle _ _ _
          _ ≤
              dist sourceMidpoint sourceAxisPoint +
                (dist sourceAxisPoint point +
                  dist point center) := by
            gcongr
            exact dist_triangle _ _ _
          _ =
              dist sourceMidpoint sourceAxisPoint +
                dist sourceAxisPoint point +
                  dist point center := by ring
      _ ≤ 1 / 2 + delta + radius := by
        gcongr
        · simpa [dist_comm] using hpointAxis
        · simpa [Metric.mem_closedBall] using hpointBall
      _ = radius + 1 / 2 + delta := by ring
  change
    |inner ℝ (parentMidpoint - center)
        parent.direction| ≤ _
  rw [show parentMidpoint - center =
    (parentMidpoint - sourceMidpoint) +
      (sourceMidpoint - center) by abel,
    inner_add_left]
  calc
    |inner ℝ (parentMidpoint - sourceMidpoint)
          parent.direction +
        inner ℝ (sourceMidpoint - center)
          parent.direction|
        ≤
      |inner ℝ (parentMidpoint - sourceMidpoint)
          parent.direction| +
        |inner ℝ (sourceMidpoint - center)
          parent.direction| :=
      abs_add_le _ _
    _ ≤
        (A / 2 + A * rho) +
          (radius + 1 / 2 + delta) := by
      gcongr
      exact
        (abs_real_inner_le_norm
          (sourceMidpoint - center)
          parent.direction).trans
          (by
            rw [parent.direction_unit, mul_one,
              ← dist_eq_norm]
            exact hsourceMidpointCenter)
    _ =
      A / 2 + A * rho + radius + 1 / 2 + delta := by
      ring

end Kakeya.Assouad

end
