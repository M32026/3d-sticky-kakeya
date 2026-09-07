import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance

/-!
# Localized ordinary centered-doubled fibers

Midpoint localization removes the high-altitude obstruction for ordinary
unit-segment tubes.  Containment in a centered doubled parent then forces a
fixed paper-line-distance bound, and sufficiently separated parents have
disjoint centered-doubled geometric fibers.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Fixed loss used by the localized ordinary centered-doubled-fiber bound. -/
def wz2PaperLocalizedDoubledFiberLineDistanceConstant : ℝ :=
  100

private def wz2PaperOrientedLowerEndpoint
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) : Point3 :=
  wz2PaperTubeMidpoint tube -
    (1 / 2 : ℝ) • wz1PaperDirection tube

private def wz2PaperOrientedUpperEndpoint
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) : Point3 :=
  wz2PaperTubeMidpoint tube +
    (1 / 2 : ℝ) • wz1PaperDirection tube

private lemma wz2PaperOrientedLowerEndpoint_mem_segment
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz2PaperOrientedLowerEndpoint tube ∈
      Kakeya.unitSegment tube.base tube.direction := by
  unfold wz2PaperOrientedLowerEndpoint wz2PaperTubeMidpoint
  unfold wz1PaperDirection
  split_ifs with hdirection
  · refine ⟨0, by norm_num, ?_⟩
    module
  · refine ⟨1, by norm_num, ?_⟩
    module

private lemma wz2PaperOrientedUpperEndpoint_mem_segment
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz2PaperOrientedUpperEndpoint tube ∈
      Kakeya.unitSegment tube.base tube.direction := by
  unfold wz2PaperOrientedUpperEndpoint wz2PaperTubeMidpoint
  unfold wz1PaperDirection
  split_ifs with hdirection
  · refine ⟨1, by norm_num, ?_⟩
    module
  · refine ⟨0, by norm_num, ?_⟩
    module

private lemma wz2PaperOrientedLowerEndpoint_mem_axis
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz2PaperOrientedLowerEndpoint tube ∈ tubeAxisLine tube := by
  rcases wz2PaperOrientedLowerEndpoint_mem_segment tube with
    ⟨parameter, _, hparameter⟩
  exact ⟨parameter, hparameter.symm⟩

private lemma wz2PaperOrientedUpperEndpoint_mem_axis
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz2PaperOrientedUpperEndpoint tube ∈ tubeAxisLine tube := by
  rcases wz2PaperOrientedUpperEndpoint_mem_segment tube with
    ⟨parameter, _, hparameter⟩
  exact ⟨parameter, hparameter.symm⟩

private lemma wz2PaperOrientedLowerEndpoint_mem_carrier
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hdelta : 0 ≤ delta) :
    wz2PaperOrientedLowerEndpoint tube ∈ tube.carrier := by
  exact
    Metric.mem_cthickening_of_dist_le
      (wz2PaperOrientedLowerEndpoint tube)
      (wz2PaperOrientedLowerEndpoint tube)
      delta
      (Kakeya.unitSegment tube.base tube.direction)
      (wz2PaperOrientedLowerEndpoint_mem_segment tube)
      (by simp [hdelta])

private lemma wz2PaperOrientedUpperEndpoint_mem_carrier
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hdelta : 0 ≤ delta) :
    wz2PaperOrientedUpperEndpoint tube ∈ tube.carrier := by
  exact
    Metric.mem_cthickening_of_dist_le
      (wz2PaperOrientedUpperEndpoint tube)
      (wz2PaperOrientedUpperEndpoint tube)
      delta
      (Kakeya.unitSegment tube.base tube.direction)
      (wz2PaperOrientedUpperEndpoint_mem_segment tube)
      (by simp [hdelta])

private lemma wz1PaperAxisPointAtHeight_eq_of_mem_axis
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hline : WZ1PaperTubeInLineClass tube)
    {point : Point3} (hpoint : point ∈ tubeAxisLine tube) :
    wz1PaperAxisPointAtHeight tube (point (2 : Fin 3)) = point := by
  have hdist :=
    wz1Paper_axisPointAtHeight_dist_le_of_axis_point
      hline (point (2 : Fin 3)) 0 hpoint (by simp)
  exact
    dist_eq_zero.mp
      (le_antisymm (by simpa using hdist) dist_nonneg)

private lemma
    wz2Paper_dist_axisPointAtHeight_le_four_mul_of_mem_centeredDoubled
    {rho : ℝ} {parent : Kakeya.DeltaTube rho}
    (hrho : 0 < rho)
    (hparent : WZ1PaperTubeInLineClass parent)
    {point : Point3}
    (hpoint :
      point ∈ wz2PaperCenteredDilatedCarrier (2 : ℝ) parent) :
    dist point
        (wz1PaperAxisPointAtHeight parent (point (2 : Fin 3))) ≤
      4 * rho := by
  rcases hpoint with ⟨source, hsource, rfl⟩
  rcases exists_closest_on_axis hrho.le parent source hsource with
    ⟨parameter, hparameter, hdist⟩
  let center := wz2PaperTubeMidpoint parent
  let axisPoint :=
    parent.base + parameter • parent.direction
  let doubledAxisPoint :=
    center + (2 : ℝ) • (axisPoint - center)
  have hdoubledAxisPoint :
      doubledAxisPoint ∈ tubeAxisLine parent := by
    refine ⟨2 * parameter - 1 / 2, ?_⟩
    dsimp only [doubledAxisPoint, axisPoint, center,
      wz2PaperTubeMidpoint]
    module
  have hdoubledDistance :
      dist
          (AffineMap.homothety center (2 : ℝ) source)
          doubledAxisPoint ≤
        2 * rho := by
    rw [dist_eq_norm]
    have hvector :
        AffineMap.homothety center (2 : ℝ) source -
            doubledAxisPoint =
          (2 : ℝ) • (source - axisPoint) := by
      ext coordinate
      dsimp only [doubledAxisPoint, axisPoint]
      simp only [AffineMap.homothety_apply, vadd_eq_add,
        vsub_eq_sub, PiLp.sub_apply, PiLp.add_apply,
        PiLp.smul_apply, smul_eq_mul]
      ring
    rw [hvector, norm_smul, Real.norm_eq_abs]
    norm_num
    simpa [dist_eq_norm] using
      (mul_le_mul_of_nonneg_left hdist (by norm_num : (0 : ℝ) ≤ 2))
  have hprojection :=
    wz1Paper_axisPointAtHeight_dist_point_le_two_mul
      hparent
      (AffineMap.homothety center (2 : ℝ) source)
      doubledAxisPoint
      hdoubledAxisPoint
  calc
    dist (AffineMap.homothety center (2 : ℝ) source)
        (wz1PaperAxisPointAtHeight parent
          ((AffineMap.homothety center (2 : ℝ) source) (2 : Fin 3))) =
        dist
          (wz1PaperAxisPointAtHeight parent
            ((AffineMap.homothety center (2 : ℝ) source) (2 : Fin 3)))
          (AffineMap.homothety center (2 : ℝ) source) := dist_comm _ _
    _ ≤
        2 * dist
          (AffineMap.homothety center (2 : ℝ) source)
          doubledAxisPoint := hprojection
    _ ≤ 4 * rho := by linarith

/--
For a line-class ordinary fine tube whose midpoint has norm at most `M`,
centered-doubled carrier containment forces paper line distance at most
`(16 * M + 44) * rho`.
-/
theorem wz2_paper_bounded_centered_doubled_containment_lineDistance_le
    {delta rho : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hfine : WZ1PaperTubeInLineClass fine)
    (hparent : WZ1PaperTubeInLineClass parent)
    (M : ℝ)
    (hfineLocal : ‖wz2PaperTubeMidpoint fine‖ ≤ M)
    (hcontained :
      fine.carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 parent) :
    wz1PaperLineDistance fine parent ≤
      (16 * M + 44) * rho := by
  let lower := wz2PaperOrientedLowerEndpoint fine
  let upper := wz2PaperOrientedUpperEndpoint fine
  let lowerHeight := lower (2 : Fin 3)
  let upperHeight := upper (2 : Fin 3)
  let fineZero := wz1TubeAxisZeroPoint fine
  let parentZero := wz1TubeAxisZeroPoint parent
  let fineDirection := wz1PaperDirection fine
  let parentDirection := wz1PaperDirection parent
  let fineVertical := fineDirection (2 : Fin 3)
  let parentVertical := parentDirection (2 : Fin 3)
  let fineSlope := fineVertical⁻¹ • fineDirection
  let parentSlope := parentVertical⁻¹ • parentDirection
  let parentLower :=
    wz1PaperAxisPointAtHeight parent lowerHeight
  let parentUpper :=
    wz1PaperAxisPointAtHeight parent upperHeight
  have hfineVertical : 1 / 2 ≤ fineVertical := hfine.1
  have hparentVertical : 1 / 2 ≤ parentVertical := hparent.1
  have hfineVerticalPos : 0 < fineVertical := by linarith
  have hparentVerticalPos : 0 < parentVertical := by linarith
  have hlowerCarrier : lower ∈ fine.carrier :=
    wz2PaperOrientedLowerEndpoint_mem_carrier fine hdelta.le
  have hupperCarrier : upper ∈ fine.carrier :=
    wz2PaperOrientedUpperEndpoint_mem_carrier fine hdelta.le
  have hlowerClose :
      dist lower parentLower ≤ 4 * rho := by
    exact
      wz2Paper_dist_axisPointAtHeight_le_four_mul_of_mem_centeredDoubled
        hrho hparent (hcontained hlowerCarrier)
  have hupperClose :
      dist upper parentUpper ≤ 4 * rho := by
    exact
      wz2Paper_dist_axisPointAtHeight_le_four_mul_of_mem_centeredDoubled
        hrho hparent (hcontained hupperCarrier)
  have hlowerFine :
      wz1PaperAxisPointAtHeight fine lowerHeight = lower := by
    exact
      wz1PaperAxisPointAtHeight_eq_of_mem_axis hfine
        (wz2PaperOrientedLowerEndpoint_mem_axis fine)
  have hupperFine :
      wz1PaperAxisPointAtHeight fine upperHeight = upper := by
    exact
      wz1PaperAxisPointAtHeight_eq_of_mem_axis hfine
        (wz2PaperOrientedUpperEndpoint_mem_axis fine)
  have hfineAxis :
      ∀ height : ℝ,
        wz1PaperAxisPointAtHeight fine height =
          fineZero + height • fineSlope := by
    intro height
    dsimp only [wz1PaperAxisPointAtHeight, fineZero,
      fineSlope, fineVertical, fineDirection]
    rw [div_eq_mul_inv, smul_smul]
  have hparentAxis :
      ∀ height : ℝ,
        wz1PaperAxisPointAtHeight parent height =
          parentZero + height • parentSlope := by
    intro height
    dsimp only [wz1PaperAxisPointAtHeight, parentZero,
      parentSlope, parentVertical, parentDirection]
    rw [div_eq_mul_inv, smul_smul]
  have hendpointDifference :
      upper - lower = fineDirection := by
    dsimp only [upper, lower, fineDirection,
      wz2PaperOrientedUpperEndpoint,
      wz2PaperOrientedLowerEndpoint]
    module
  have hheightDifference :
      upperHeight - lowerHeight = fineVertical := by
    have hcoordinate :=
      congrArg (fun point : Point3 => point (2 : Fin 3))
        hendpointDifference
    simpa [upperHeight, lowerHeight, fineVertical] using hcoordinate
  have herrorDifference :
      (upper - parentUpper) - (lower - parentLower) =
        fineVertical • (fineSlope - parentSlope) := by
    rw [← hupperFine, ← hlowerFine]
    rw [hfineAxis, hfineAxis]
    dsimp only [parentUpper, parentLower]
    rw [hparentAxis, hparentAxis]
    rw [← hheightDifference]
    module
  have hslopeScaled :
      fineVertical * ‖fineSlope - parentSlope‖ ≤
        8 * rho := by
    calc
      fineVertical * ‖fineSlope - parentSlope‖ =
          ‖fineVertical • (fineSlope - parentSlope)‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos hfineVerticalPos]
      _ =
          ‖(upper - parentUpper) -
            (lower - parentLower)‖ := by
        rw [herrorDifference]
      _ ≤
          ‖upper - parentUpper‖ +
            ‖lower - parentLower‖ :=
        norm_sub_le _ _
      _ ≤ 4 * rho + 4 * rho := by
        gcongr
        · simpa [dist_eq_norm] using hupperClose
        · simpa [dist_eq_norm] using hlowerClose
      _ = 8 * rho := by ring
  have hslope :
      ‖fineSlope - parentSlope‖ ≤ 16 * rho := by
    nlinarith [norm_nonneg (fineSlope - parentSlope)]
  have hfineVerticalLe : fineVertical ≤ 1 := by
    have hcoord :=
      abs_coord_two_le_norm fineDirection
    rw [abs_of_pos hfineVerticalPos,
      wz1PaperDirection_norm fine] at hcoord
    exact hcoord
  have hparentVerticalLe : parentVertical ≤ 1 := by
    have hcoord :=
      abs_coord_two_le_norm parentDirection
    rw [abs_of_pos hparentVerticalPos,
      wz1PaperDirection_norm parent] at hcoord
    exact hcoord
  have hfineSlopeNorm : 1 ≤ ‖fineSlope‖ := by
    change 1 ≤ ‖fineVertical⁻¹ • fineDirection‖
    rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hfineVerticalPos,
      wz1PaperDirection_norm fine, mul_one]
    exact
      (one_le_inv₀ hfineVerticalPos).mpr hfineVerticalLe
  have hparentSlopeNorm : 1 ≤ ‖parentSlope‖ := by
    change 1 ≤ ‖parentVertical⁻¹ • parentDirection‖
    rw [norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hparentVerticalPos,
      wz1PaperDirection_norm parent, mul_one]
    exact
      (one_le_inv₀ hparentVerticalPos).mpr hparentVerticalLe
  have hfineNormalize :
      NormedSpace.normalize fineSlope = fineDirection := by
    dsimp only [fineSlope]
    rw [NormedSpace.normalize_smul_of_pos
      (inv_pos.mpr hfineVerticalPos)]
    exact
      NormedSpace.normalize_eq_self_of_norm_eq_one
        (wz1PaperDirection_norm fine)
  have hparentNormalize :
      NormedSpace.normalize parentSlope = parentDirection := by
    dsimp only [parentSlope]
    rw [NormedSpace.normalize_smul_of_pos
      (inv_pos.mpr hparentVerticalPos)]
    exact
      NormedSpace.normalize_eq_self_of_norm_eq_one
        (wz1PaperDirection_norm parent)
  have hdirection :
      ‖fineDirection - parentDirection‖ ≤ 16 * rho := by
    rw [← hfineNormalize, ← hparentNormalize]
    exact
      (norm_normalize_sub_normalize_le_norm_sub
        hfineSlopeNorm hparentSlopeNorm).trans hslope
  have hlowerNorm : ‖lower‖ ≤ M + 1 / 2 := by
    calc
      ‖lower‖ ≤
          ‖wz2PaperTubeMidpoint fine‖ +
            ‖(1 / 2 : ℝ) • fineDirection‖ := by
        dsimp only [lower, fineDirection,
          wz2PaperOrientedLowerEndpoint]
        exact norm_sub_le _ _
      _ = ‖wz2PaperTubeMidpoint fine‖ + 1 / 2 := by
        rw [norm_smul, Real.norm_eq_abs,
          wz1PaperDirection_norm fine]
        norm_num
      _ ≤ M + 1 / 2 := by linarith
  have hlowerHeight : |lowerHeight| ≤ M + 1 / 2 := by
    have hcoordinate :=
      PiLp.norm_apply_le lower (2 : Fin 3)
    simpa [lowerHeight, Real.norm_eq_abs] using
      hcoordinate.trans hlowerNorm
  have hM : 0 ≤ M := by
    exact (norm_nonneg (wz2PaperTubeMidpoint fine)).trans hfineLocal
  have hlowerExpansion :
      lower = fineZero + lowerHeight • fineSlope := by
    rw [← hlowerFine]
    exact hfineAxis lowerHeight
  have hparentLowerExpansion :
      parentLower =
        parentZero + lowerHeight • parentSlope := by
    dsimp only [parentLower]
    exact hparentAxis lowerHeight
  have hzeroVector :
      fineZero - parentZero =
        (lower - parentLower) -
          lowerHeight • (fineSlope - parentSlope) := by
    rw [hlowerExpansion, hparentLowerExpansion]
    module
  have hzeroDistance :
      dist fineZero parentZero ≤ (16 * M + 12) * rho := by
    rw [dist_eq_norm, hzeroVector]
    calc
      ‖(lower - parentLower) -
          lowerHeight • (fineSlope - parentSlope)‖ ≤
          ‖lower - parentLower‖ +
            ‖lowerHeight • (fineSlope - parentSlope)‖ :=
        norm_sub_le _ _
      _ =
          ‖lower - parentLower‖ +
            |lowerHeight| *
              ‖fineSlope - parentSlope‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤
          4 * rho + (M + 1 / 2) * (16 * rho) := by
        gcongr
        simpa [dist_eq_norm] using hlowerClose
      _ = (16 * M + 12) * rho := by ring
  have hangle :
      InnerProductGeometry.angle fineDirection parentDirection ≤
        32 * rho := by
    calc
      InnerProductGeometry.angle fineDirection parentDirection ≤
          (Real.pi / 2) *
            ‖fineDirection - parentDirection‖ :=
        angle_le_pi_div_two_mul_norm_sub
          (wz1PaperDirection_norm fine)
          (wz1PaperDirection_norm parent)
      _ ≤ 2 * (16 * rho) := by
        gcongr
        linarith [Real.pi_lt_four]
      _ = 32 * rho := by ring
  dsimp only [wz1PaperLineDistance]
  linarith

/--
For the historical fixed local window `M = 3`, the general estimate is
weakened to the named constant `100`.
-/
theorem wz2_paper_localized_centered_doubled_containment_lineDistance_le
    {delta rho : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hfine : WZ1PaperTubeInLineClass fine)
    (hparent : WZ1PaperTubeInLineClass parent)
    (hfineLocal : ‖wz2PaperTubeMidpoint fine‖ ≤ 3)
    (hcontained :
      fine.carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 parent) :
    wz1PaperLineDistance fine parent ≤
      wz2PaperLocalizedDoubledFiberLineDistanceConstant * rho := by
  have hgeneral :=
    wz2_paper_bounded_centered_doubled_containment_lineDistance_le
      hdelta hrho hfine hparent 3 hfineLocal hcontained
  dsimp only [wz2PaperLocalizedDoubledFiberLineDistanceConstant]
  linarith

/--
A common child lying in the unit ball localizes the midpoint of every
radius-at-most-one ordinary parent that contains the child.
-/
theorem wz2_paper_midpoint_norm_le_three_of_unitBall_child
    {eta scale : ℝ}
    {child : Kakeya.DeltaTube eta}
    {target : Kakeya.DeltaTube scale}
    (heta : 0 ≤ eta)
    (hscale : 0 < scale)
    (hscaleOne : scale ≤ 1)
    (hchildUnit :
      child.carrier ⊆ Kakeya.DeltaTube.unitBall)
    (hchildTarget :
      child.carrier ⊆ target.carrier) :
    ‖wz2PaperTubeMidpoint target‖ ≤ 3 := by
  let witness := wz2PaperTubeMidpoint child
  have hwitnessChild : witness ∈ child.carrier :=
    wz2_paper_tubeMidpoint_mem_carrier child heta
  have hwitnessUnit :
      witness ∈ Kakeya.DeltaTube.unitBall :=
    hchildUnit hwitnessChild
  have hwitnessTarget : witness ∈ target.carrier :=
    hchildTarget hwitnessChild
  rcases exists_closest_on_axis hscale.le target witness hwitnessTarget with
    ⟨parameter, hparameter, hdist⟩
  let axisPoint :=
    target.base + parameter • target.direction
  have hmidpointAxis :
      dist (wz2PaperTubeMidpoint target) axisPoint ≤ 1 / 2 := by
    rw [dist_eq_norm]
    have hvector :
        wz2PaperTubeMidpoint target - axisPoint =
          (1 / 2 - parameter) • target.direction := by
      dsimp only [axisPoint, wz2PaperTubeMidpoint]
      module
    rw [hvector, norm_smul, Real.norm_eq_abs,
      target.direction_unit, mul_one]
    rw [abs_le]
    constructor <;> linarith [hparameter.1, hparameter.2]
  have hwitnessNorm : dist witness 0 ≤ 1 := by
    simpa [Kakeya.DeltaTube.unitBall,
      Metric.mem_closedBall] using hwitnessUnit
  calc
    ‖wz2PaperTubeMidpoint target‖ =
        dist (wz2PaperTubeMidpoint target) 0 := by
      simp [dist_zero_right]
    _ ≤
        dist (wz2PaperTubeMidpoint target) axisPoint +
          dist axisPoint witness +
            dist witness 0 := by
      calc
        dist (wz2PaperTubeMidpoint target) 0 ≤
            dist (wz2PaperTubeMidpoint target) axisPoint +
              dist axisPoint 0 :=
          dist_triangle _ _ _
        _ ≤
            dist (wz2PaperTubeMidpoint target) axisPoint +
              (dist axisPoint witness + dist witness 0) := by
          gcongr
          exact dist_triangle _ _ _
        _ =
            dist (wz2PaperTubeMidpoint target) axisPoint +
              dist axisPoint witness + dist witness 0 := by ring
    _ ≤ 1 / 2 + scale + 1 := by
      gcongr
      simpa [dist_comm] using hdist
    _ ≤ 3 := by linarith

/--
The localized line-distance bound derived from a common unit-ball child,
without assuming midpoint bounds separately.
-/
theorem
    wz2_paper_common_unitBall_child_centered_doubled_containment_lineDistance_le
    {eta delta rho : ℝ}
    {child : Kakeya.DeltaTube eta}
    {fine : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (heta : 0 < eta)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hdeltaOne : delta ≤ 1)
    (hfine : WZ1PaperTubeInLineClass fine)
    (hparent : WZ1PaperTubeInLineClass parent)
    (hchildUnit :
      child.carrier ⊆ Kakeya.DeltaTube.unitBall)
    (hchildFine :
      child.carrier ⊆ fine.carrier)
    (hcontained :
      fine.carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 parent) :
    wz1PaperLineDistance fine parent ≤
      wz2PaperLocalizedDoubledFiberLineDistanceConstant * rho := by
  apply
    wz2_paper_localized_centered_doubled_containment_lineDistance_le
      hdelta hrho hfine hparent
  · exact
      wz2_paper_midpoint_norm_le_three_of_unitBall_child
        heta.le hdelta hdeltaOne hchildUnit hchildFine
  · exact hcontained

/--
Parents separated by more than twice the localized loss have disjoint
ordinary centered-doubled fibers.
-/
theorem wz2_paper_localized_ordinary_dilatedFiberIndices_disjoint
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hfine : WZ1PaperIsLineClass fine)
    (hcoarse : WZ1PaperIsLineClass coarse)
    (hfineLocal :
      ∀ source,
        ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ 3)
    (hseparated :
      ∀ first second, first ≠ second →
        2 * wz2PaperLocalizedDoubledFiberLineDistanceConstant * rho <
          wz1PaperLineDistance
            (coarse.tube first) (coarse.tube second)) :
    ∀ first second, first ≠ second →
      Disjoint
        (wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse first)
        (wz2PaperOrdinaryDilatedFiberIndices 2 fine coarse second) := by
  intro first second hne
  rw [Finset.disjoint_left]
  intro source hfirst hsecond
  rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff] at hfirst hsecond
  have hfirstDistance :=
    wz2_paper_localized_centered_doubled_containment_lineDistance_le
      hdelta hrho (hfine source) (hcoarse first)
      (hfineLocal source) hfirst
  have hsecondDistance :=
    wz2_paper_localized_centered_doubled_containment_lineDistance_le
      hdelta hrho (hfine source) (hcoarse second)
      (hfineLocal source) hsecond
  have htriangle :=
    wz1PaperLineDistance_triangle
      (coarse.tube first) (fine.tube source) (coarse.tube second)
  have hsymmetry :
      wz1PaperLineDistance
          (coarse.tube first) (fine.tube source) =
        wz1PaperLineDistance
          (fine.tube source) (coarse.tube first) :=
    wz1PaperLineDistance_symm _ _
  rw [hsymmetry] at htriangle
  have hsep := hseparated first second hne
  linarith

end Kakeya.Assouad

end
