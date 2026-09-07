import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredLineTube
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance
import MyLeanRepo.Kakeya.Assouad.TubeAlignmentGeometry

/-!
# Ordinary trace containment in a centered parent

A fine ordinary trace in the central height window lies in a same-radius
midpoint-centered parent when the fine and parent paper lines are sufficiently
close.
-/

noncomputable section

namespace Kakeya.Assouad

private lemma ordinaryTraceCenteredParent_axisPoint_mem_segment
    {rho : ℝ}
    {parent : Kakeya.DeltaTube rho}
    (parentLine : WZ1PaperTubeInLineClass parent)
    (parentCentered :
      wz2PaperCenteredLineTube (targetScale := rho) parent = parent)
    {height : ℝ}
    (heightWindow : |height| ≤ 1 / 4) :
    wz1PaperAxisPointAtHeight parent height ∈
      Kakeya.unitSegment parent.base parent.direction := by
  have verticalPos : 0 < wz1PaperDirection parent (2 : Fin 3) := by
    linarith [parentLine.1]
  have parameterLower :
      0 ≤ 1 / 2 + height / wz1PaperDirection parent (2 : Fin 3) := by
    have heightLower : -(1 / 4 : ℝ) ≤ height :=
      (abs_le.mp heightWindow).1
    have quotientLower :
        -(1 / 2 : ℝ) ≤
          height / wz1PaperDirection parent (2 : Fin 3) := by
      rw [le_div_iff₀ verticalPos]
      nlinarith [parentLine.1]
    linarith
  have parameterUpper :
      1 / 2 + height / wz1PaperDirection parent (2 : Fin 3) ≤ 1 := by
    have heightUpper : height ≤ (1 / 4 : ℝ) :=
      (abs_le.mp heightWindow).2
    have quotientUpper :
        height / wz1PaperDirection parent (2 : Fin 3) ≤ 1 / 2 := by
      rw [div_le_iff₀ verticalPos]
      nlinarith [parentLine.1]
    linarith
  refine
    ⟨1 / 2 + height / wz1PaperDirection parent (2 : Fin 3),
      ⟨parameterLower, parameterUpper⟩, ?_⟩
  have centeredBase :=
    congrArg Kakeya.DeltaTube.base parentCentered
  have centeredDirection :=
    congrArg Kakeya.DeltaTube.direction parentCentered
  change
    parent.base +
        (1 / 2 + height / wz1PaperDirection parent (2 : Fin 3)) •
          parent.direction =
      wz1TubeAxisZeroPoint parent +
        (height / wz1PaperDirection parent (2 : Fin 3)) •
          wz1PaperDirection parent
  change
    wz1TubeAxisZeroPoint parent -
        (1 / 2 : ℝ) • wz1PaperDirection parent =
      parent.base at centeredBase
  change wz1PaperDirection parent = parent.direction at centeredDirection
  rw [← centeredBase, ← centeredDirection]
  module

private lemma ordinaryTraceCenteredParent_axisPoint_dist_le
    {delta rho : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (fineLine : WZ1PaperTubeInLineClass fine)
    (parentLine : WZ1PaperTubeInLineClass parent)
    {height : ℝ}
    (heightWindow : |height| ≤ 1 / 4) :
    dist (wz1PaperAxisPointAtHeight fine height)
        (wz1PaperAxisPointAtHeight parent height) ≤
      (3 / 2 : ℝ) * wz1PaperLineDistance fine parent := by
  let fineZero := wz1TubeAxisZeroPoint fine
  let parentZero := wz1TubeAxisZeroPoint parent
  let fineDirection := wz1PaperDirection fine
  let parentDirection := wz1PaperDirection parent
  let fineVertical := fineDirection (2 : Fin 3)
  let parentVertical := parentDirection (2 : Fin 3)
  have fineVerticalPos : 0 < fineVertical := by
    dsimp only [fineVertical, fineDirection]
    linarith [fineLine.1]
  have parentVerticalPos : 0 < parentVertical := by
    dsimp only [parentVertical, parentDirection]
    linarith [parentLine.1]
  have verticalDifference :
      |fineVertical - parentVertical| ≤
        ‖fineDirection - parentDirection‖ :=
    abs_coord_sub_le_dist
        (x := fineDirection) (y := parentDirection) (2 : Fin 3)
      |>.trans_eq (dist_eq_norm _ _)
  have parameterDifference :
      |height / fineVertical - height / parentVertical| ≤
        ‖fineDirection - parentDirection‖ := by
    have inverseDifference :
        |fineVertical⁻¹ - parentVertical⁻¹| ≤
          4 * |fineVertical - parentVertical| := by
      have algebra :
          fineVertical⁻¹ - parentVertical⁻¹ =
            (parentVertical - fineVertical) /
              (fineVertical * parentVertical) := by
        field_simp [fineVerticalPos.ne', parentVerticalPos.ne']
      rw [algebra, abs_div, abs_mul,
        abs_of_pos fineVerticalPos, abs_of_pos parentVerticalPos,
        abs_sub_comm]
      have denominatorLower :
          1 / 4 ≤ fineVertical * parentVertical := by
        dsimp only [
          fineVertical, parentVertical, fineDirection, parentDirection]
        nlinarith [fineLine.1, parentLine.1]
      have denominatorPos : 0 < fineVertical * parentVertical := by
        positivity
      exact
        (div_le_iff₀ denominatorPos).mpr
          (by
            nlinarith [
              abs_nonneg (fineVertical - parentVertical)])
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_sub, abs_mul]
    calc
      |height| * |fineVertical⁻¹ - parentVertical⁻¹| ≤
          (1 / 4 : ℝ) *
            (4 * |fineVertical - parentVertical|) := by
        gcongr
      _ = |fineVertical - parentVertical| := by ring
      _ ≤ ‖fineDirection - parentDirection‖ := verticalDifference
  have pointDifference :
      wz1PaperAxisPointAtHeight fine height -
          wz1PaperAxisPointAtHeight parent height =
        (fineZero - parentZero) +
          (height / fineVertical) •
            (fineDirection - parentDirection) +
          (height / fineVertical - height / parentVertical) •
            parentDirection := by
    dsimp only [
      wz1PaperAxisPointAtHeight, fineZero, parentZero,
      fineDirection, parentDirection, fineVertical, parentVertical]
    module
  rw [dist_eq_norm, pointDifference]
  calc
    ‖(fineZero - parentZero) +
        (height / fineVertical) •
          (fineDirection - parentDirection) +
        (height / fineVertical - height / parentVertical) •
          parentDirection‖ ≤
        ‖fineZero - parentZero‖ +
          ‖(height / fineVertical) •
            (fineDirection - parentDirection)‖ +
          ‖(height / fineVertical - height / parentVertical) •
            parentDirection‖ := by
      exact
        (norm_add_le _ _).trans
          (add_le_add_left (norm_add_le _ _) _)
    _ = dist fineZero parentZero +
          |height / fineVertical| *
            ‖fineDirection - parentDirection‖ +
          |height / fineVertical - height / parentVertical| := by
      rw [norm_smul, norm_smul, wz1PaperDirection_norm parent,
        mul_one, dist_eq_norm]
      simp only [Real.norm_eq_abs]
    _ ≤ dist fineZero parentZero +
          (1 / 2 : ℝ) * ‖fineDirection - parentDirection‖ +
          ‖fineDirection - parentDirection‖ := by
      gcongr
      rw [abs_div, abs_of_pos fineVerticalPos]
      rw [div_le_iff₀ fineVerticalPos]
      dsimp only [fineVertical, fineDirection]
      nlinarith [fineLine.1, abs_nonneg height]
    _ ≤ dist fineZero parentZero +
          (3 / 2 : ℝ) *
            InnerProductGeometry.angle
              fineDirection parentDirection := by
      have chord :=
        unit_norm_sub_le_angle
          (wz1PaperDirection_norm fine)
          (wz1PaperDirection_norm parent)
      nlinarith
    _ ≤ (3 / 2 : ℝ) * wz1PaperLineDistance fine parent := by
      have distanceNonnegative : 0 ≤ dist fineZero parentZero :=
        dist_nonneg
      dsimp only [
        wz1PaperLineDistance, fineZero, parentZero,
        fineDirection, parentDirection]
      nlinarith

/--
An ordinary fine trace point in the central height window lies within
`5 * rho / 6` of the centered parent segment.
-/
theorem fineOrdinaryTrace_exists_centeredParent_axisPoint
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (fine : Kakeya.DeltaTube delta)
    (parent : Kakeya.DeltaTube rho)
    (fineLine : WZ1PaperTubeInLineClass fine)
    (parentLine : WZ1PaperTubeInLineClass parent)
    (parentCentered :
      wz2PaperCenteredLineTube (targetScale := rho) parent = parent)
    (ratioSmall : delta / rho ≤ 1 / 24)
    (parentClose : wz1PaperLineDistance fine parent ≤ rho / 2)
    (trace : Set Point3)
    (traceInFine : trace ⊆ fine.carrier)
    (traceInCentralWindow :
      ∀ point ∈ trace, |point (2 : Fin 3)| ≤ 1 / 4)
    {point : Point3}
    (pointInTrace : point ∈ trace) :
    ∃ axisPoint ∈
        Kakeya.unitSegment parent.base parent.direction,
      dist point axisPoint ≤ 5 * rho / 6 := by
  have pointInFine : point ∈ fine.carrier :=
    traceInFine pointInTrace
  rcases exists_closest_on_axis hdelta.le fine point pointInFine with
    ⟨parameter, _parameterMem, pointAxisDistance⟩
  let fineAxisPoint :=
    fine.base + parameter • fine.direction
  have fineAxisPointMem :
      fineAxisPoint ∈ tubeAxisLine fine := by
    exact ⟨parameter, rfl⟩
  let fineAtHeight :=
    wz1PaperAxisPointAtHeight fine (point (2 : Fin 3))
  let parentAtHeight :=
    wz1PaperAxisPointAtHeight parent (point (2 : Fin 3))
  have pointFineAtHeightDistance :
      dist point fineAtHeight ≤ 2 * delta := by
    have projection :=
      wz1Paper_axisPointAtHeight_dist_point_le_two_mul
        fineLine point fineAxisPoint fineAxisPointMem
    dsimp only [fineAtHeight]
    calc
      dist point
          (wz1PaperAxisPointAtHeight fine (point (2 : Fin 3))) =
          dist
            (wz1PaperAxisPointAtHeight fine (point (2 : Fin 3)))
            point :=
        dist_comm _ _
      _ ≤ 2 * dist point fineAxisPoint := projection
      _ ≤ 2 * delta := by gcongr
  have centralWindow :
      |point (2 : Fin 3)| ≤ 1 / 4 :=
    traceInCentralWindow point pointInTrace
  have fineParentAxisDistance :
      dist fineAtHeight parentAtHeight ≤
        (3 / 2 : ℝ) * wz1PaperLineDistance fine parent := by
    exact
      ordinaryTraceCenteredParent_axisPoint_dist_le
        fineLine parentLine centralWindow
  have parentAtHeightMem :
      parentAtHeight ∈
        Kakeya.unitSegment parent.base parent.direction := by
    exact
      ordinaryTraceCenteredParent_axisPoint_mem_segment
        parentLine parentCentered centralWindow
  have deltaBound : delta ≤ rho / 24 := by
    have multiplied := (div_le_iff₀ hrho).mp ratioSmall
    nlinarith
  have pointParentAtHeightDistance :
      dist point parentAtHeight ≤ 5 * rho / 6 := by
    calc
      dist point parentAtHeight ≤
          dist point fineAtHeight +
            dist fineAtHeight parentAtHeight :=
        dist_triangle _ _ _
      _ ≤ 2 * delta +
          (3 / 2 : ℝ) * wz1PaperLineDistance fine parent := by
        gcongr
      _ ≤ 5 * rho / 6 := by
        nlinarith
  exact
    ⟨parentAtHeight, parentAtHeightMem,
      pointParentAtHeightDistance⟩

/--
Strong-margin version used by exact coarse re-entry.

When the metric-parent construction is requested with distance constant
`1 / 100`, every central-window ordinary trace point lies within `rho / 10`
of the centered parent's unit axis segment.
-/
theorem fineOrdinaryTrace_exists_centeredParent_axisPoint_strong
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (fine : Kakeya.DeltaTube delta)
    (parent : Kakeya.DeltaTube rho)
    (fineLine : WZ1PaperTubeInLineClass fine)
    (parentLine : WZ1PaperTubeInLineClass parent)
    (parentCentered :
      wz2PaperCenteredLineTube (targetScale := rho) parent = parent)
    (ratioSmall : delta / rho ≤ 1 / 24)
    (parentClose : wz1PaperLineDistance fine parent ≤ rho / 100)
    (trace : Set Point3)
    (traceInFine : trace ⊆ fine.carrier)
    (traceInCentralWindow :
      ∀ point ∈ trace, |point (2 : Fin 3)| ≤ 1 / 4)
    {point : Point3}
    (pointInTrace : point ∈ trace) :
    ∃ axisPoint ∈
        Kakeya.unitSegment parent.base parent.direction,
      dist point axisPoint ≤ rho / 10 := by
  have pointInFine : point ∈ fine.carrier :=
    traceInFine pointInTrace
  rcases exists_closest_on_axis hdelta.le fine point pointInFine with
    ⟨parameter, _parameterMem, pointAxisDistance⟩
  let fineAxisPoint :=
    fine.base + parameter • fine.direction
  have fineAxisPointMem :
      fineAxisPoint ∈ tubeAxisLine fine :=
    ⟨parameter, rfl⟩
  let fineAtHeight :=
    wz1PaperAxisPointAtHeight fine (point (2 : Fin 3))
  let parentAtHeight :=
    wz1PaperAxisPointAtHeight parent (point (2 : Fin 3))
  have pointFineAtHeightDistance :
      dist point fineAtHeight ≤ 2 * delta := by
    have projection :=
      wz1Paper_axisPointAtHeight_dist_point_le_two_mul
        fineLine point fineAxisPoint fineAxisPointMem
    dsimp only [fineAtHeight]
    calc
      dist point
          (wz1PaperAxisPointAtHeight fine (point (2 : Fin 3))) =
          dist
            (wz1PaperAxisPointAtHeight fine (point (2 : Fin 3)))
            point :=
        dist_comm _ _
      _ ≤ 2 * dist point fineAxisPoint := projection
      _ ≤ 2 * delta := by gcongr
  have centralWindow :
      |point (2 : Fin 3)| ≤ 1 / 4 :=
    traceInCentralWindow point pointInTrace
  have fineParentAxisDistance :
      dist fineAtHeight parentAtHeight ≤
        (3 / 2 : ℝ) * wz1PaperLineDistance fine parent :=
    ordinaryTraceCenteredParent_axisPoint_dist_le
      fineLine parentLine centralWindow
  have parentAtHeightMem :
      parentAtHeight ∈
        Kakeya.unitSegment parent.base parent.direction :=
    ordinaryTraceCenteredParent_axisPoint_mem_segment
      parentLine parentCentered centralWindow
  have deltaBound : delta ≤ rho / 24 := by
    have multiplied := (div_le_iff₀ hrho).mp ratioSmall
    nlinarith
  have pointParentAtHeightDistance :
      dist point parentAtHeight ≤ rho / 10 := by
    calc
      dist point parentAtHeight ≤
          dist point fineAtHeight +
            dist fineAtHeight parentAtHeight :=
        dist_triangle _ _ _
      _ ≤ 2 * delta +
          (3 / 2 : ℝ) * wz1PaperLineDistance fine parent := by
        gcongr
      _ ≤ rho / 10 := by
        nlinarith
  exact
    ⟨parentAtHeight, parentAtHeightMem,
      pointParentAtHeightDistance⟩

/--
An ordinary fine trace in the central height window is contained in a
same-radius centered parent whose paper line is within `rho / 2`.
-/
theorem fineOrdinaryTrace_subset_sameRadius_centeredParent
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (fine : Kakeya.DeltaTube delta)
    (parent : Kakeya.DeltaTube rho)
    (fineLine : WZ1PaperTubeInLineClass fine)
    (parentLine : WZ1PaperTubeInLineClass parent)
    (parentCentered :
      wz2PaperCenteredLineTube (targetScale := rho) parent = parent)
    (ratioSmall : delta / rho ≤ 1 / 24)
    (parentClose : wz1PaperLineDistance fine parent ≤ rho / 2)
    (trace : Set Point3)
    (traceInFine : trace ⊆ fine.carrier)
    (traceInCentralWindow :
      ∀ point ∈ trace, |point (2 : Fin 3)| ≤ 1 / 4) :
    trace ⊆ parent.carrier := by
  intro point pointInTrace
  rcases
      fineOrdinaryTrace_exists_centeredParent_axisPoint
        hdelta hrho fine parent fineLine parentLine parentCentered
        ratioSmall parentClose trace traceInFine traceInCentralWindow
        pointInTrace
    with ⟨axisPoint, axisPointMem, pointAxisDistance⟩
  exact
    Metric.mem_cthickening_of_dist_le
      point axisPoint rho
      (Kakeya.unitSegment parent.base parent.direction)
      axisPointMem
      (pointAxisDistance.trans <| by
        nlinarith)

end Kakeya.Assouad
