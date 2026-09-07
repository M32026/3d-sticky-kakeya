import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingRetubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OrdinaryDistinctWeightedCleanup
import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoverCarrierContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedDoubledFiber
import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement

/-!
# Paper-line control for Proposition 6.3 mild rescaling

The final similarity in `wz2_63.tex` is isotropic.  It multiplies the
distance between the height-zero points of two image lines by `scale` and
does not change their positively oriented directions.  The inverse estimate
below pays only for moving the source comparison plane from height zero to
the height of the centre of the selected box.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

attribute [local instance] Classical.propDecidable

/-- The height-zero point of an isotropically rescaled line is the image of
the source-axis point at the height of the centre. -/
lemma proposition63_isotropic_target_zeroPoint
    {sourceDelta targetDelta scale : ℝ}
    (hscale : 0 < scale)
    (center : Point3)
    (source : Kakeya.DeltaTube sourceDelta)
    (target : Kakeya.DeltaTube targetDelta)
    (hsourceLine : WZ1PaperTubeInLineClass source)
    (htargetLine : WZ1PaperTubeInLineClass target)
    (haxis : tubeAxisLine target =
      wz1IsotropicRescalingMap center scale '' tubeAxisLine source) :
    wz1TubeAxisZeroPoint target =
      wz1IsotropicRescalingMap center scale
        (wz1PaperAxisPointAtHeight source (center 2)) := by
  apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
    htargetLine.vertical
  · rw [haxis]
    exact ⟨wz1PaperAxisPointAtHeight source (center 2),
      wz1PaperAxisPointAtHeight_mem_axis source (center 2), rfl⟩
  · simp [wz1IsotropicRescalingMap,
      wz1PaperAxisPointAtHeight_coord_two hsourceLine]

/-- The positively oriented direction of the canonical target is exactly the
source paper direction. -/
lemma proposition63_isotropic_target_paperDirection
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta)
    (target : Kakeya.DeltaTube targetDelta)
    (hsourceLine : WZ1PaperTubeInLineClass source)
    (hdirection : target.direction = wz1PaperDirection source) :
    wz1PaperDirection target = wz1PaperDirection source := by
  change (if 0 ≤ target.direction 2 then
      target.direction else -target.direction) = _
  rw [if_pos]
  · exact hdirection
  · rw [hdirection]
    linarith [hsourceLine.1]

private lemma proposition63_abs_inv_le_two
    {value : ℝ} (hvalue : (1 / 2 : ℝ) ≤ value) :
    |value⁻¹| ≤ 2 := by
  have hpositive : 0 < value := by linarith
  rw [abs_inv, abs_of_pos hpositive]
  simpa [one_div] using
    ((div_le_iff₀ hpositive).2 (by linarith) : (1 : ℝ) / value ≤ 2)

private lemma proposition63_abs_inv_sub_inv_le_four_mul
    {first second : ℝ}
    (hfirst : (1 / 2 : ℝ) ≤ first)
    (hsecond : (1 / 2 : ℝ) ≤ second) :
    |first⁻¹ - second⁻¹| ≤ 4 * |first - second| := by
  have hfirstPos : 0 < first := by linarith
  have hsecondPos : 0 < second := by linarith
  have hidentity :
      first⁻¹ - second⁻¹ = (second - first) / (first * second) := by
    field_simp [hfirstPos.ne', hsecondPos.ne']
  rw [hidentity, abs_div, abs_mul, abs_of_pos hfirstPos,
    abs_of_pos hsecondPos, abs_sub_comm]
  have hdenominator : (1 / 4 : ℝ) ≤ first * second := by
    have hproduct := mul_le_mul hfirst hsecond
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by linarith : 0 ≤ first)
    norm_num at hproduct ⊢
    exact hproduct
  have hdenominatorPos : 0 < first * second := mul_pos hfirstPos hsecondPos
  calc
    |first - second| / (first * second) ≤
        |first - second| / (1 / 4 : ℝ) := by
      exact div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num)
        hdenominator
    _ = 4 * |first - second| := by ring

/-- On the positive vertical chart, the slope vectors of two oriented lines
are controlled directly by the chordal distance between their unit
directions. -/
lemma proposition63_paperSlope_sub_norm_le_six_norm_sub
    {firstDelta secondDelta : ℝ}
    (first : Kakeya.DeltaTube firstDelta)
    (second : Kakeya.DeltaTube secondDelta)
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second) :
    ‖(wz1PaperDirection first 2)⁻¹ • wz1PaperDirection first -
        (wz1PaperDirection second 2)⁻¹ • wz1PaperDirection second‖ ≤
      6 * ‖wz1PaperDirection first - wz1PaperDirection second‖ := by
  let firstDirection := wz1PaperDirection first
  let secondDirection := wz1PaperDirection second
  let firstVertical := firstDirection 2
  let secondVertical := secondDirection 2
  have hfirstVertical : (1 / 2 : ℝ) ≤ firstVertical := hfirst.1
  have hsecondVertical : (1 / 2 : ℝ) ≤ secondVertical := hsecond.1
  have hinvFirst : |firstVertical⁻¹| ≤ 2 :=
    proposition63_abs_inv_le_two hfirstVertical
  have hinvDifference :
      |firstVertical⁻¹ - secondVertical⁻¹| ≤
        4 * |firstVertical - secondVertical| :=
    proposition63_abs_inv_sub_inv_le_four_mul
      hfirstVertical hsecondVertical
  have hverticalDifference :
      |firstVertical - secondVertical| ≤
        ‖firstDirection - secondDirection‖ := by
    exact PiLp.norm_apply_le (firstDirection - secondDirection) 2
  have hdirectionDifference :
      ‖firstDirection - secondDirection‖ ≤
        InnerProductGeometry.angle firstDirection secondDirection :=
    unit_norm_sub_le_angle
      (wz1PaperDirection_norm first) (wz1PaperDirection_norm second)
  have hslopeIdentity :
      firstVertical⁻¹ • firstDirection -
          secondVertical⁻¹ • secondDirection =
        firstVertical⁻¹ • (firstDirection - secondDirection) +
          (firstVertical⁻¹ - secondVertical⁻¹) • secondDirection := by
    module
  rw [hslopeIdentity]
  calc
    ‖firstVertical⁻¹ • (firstDirection - secondDirection) +
          (firstVertical⁻¹ - secondVertical⁻¹) • secondDirection‖ ≤
        ‖firstVertical⁻¹ • (firstDirection - secondDirection)‖ +
          ‖(firstVertical⁻¹ - secondVertical⁻¹) • secondDirection‖ :=
      norm_add_le _ _
    _ = |firstVertical⁻¹| * ‖firstDirection - secondDirection‖ +
          |firstVertical⁻¹ - secondVertical⁻¹| := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        wz1PaperDirection_norm second, mul_one]
    _ ≤ 2 * ‖firstDirection - secondDirection‖ +
          4 * |firstVertical - secondVertical| := by gcongr
    _ ≤ 6 * ‖firstDirection - secondDirection‖ := by
      linarith

/-- On the positive vertical chart, the slope vectors of two oriented lines
are controlled by the angle between their unit directions. -/
lemma proposition63_paperSlope_sub_norm_le_six_angle
    {firstDelta secondDelta : ℝ}
    (first : Kakeya.DeltaTube firstDelta)
    (second : Kakeya.DeltaTube secondDelta)
    (hfirst : WZ1PaperTubeInLineClass first)
    (hsecond : WZ1PaperTubeInLineClass second) :
    ‖(wz1PaperDirection first 2)⁻¹ • wz1PaperDirection first -
        (wz1PaperDirection second 2)⁻¹ • wz1PaperDirection second‖ ≤
      6 * InnerProductGeometry.angle
        (wz1PaperDirection first) (wz1PaperDirection second) := by
  exact (proposition63_paperSlope_sub_norm_le_six_norm_sub
    first second hfirst hsecond).trans <| by
      gcongr
      exact unit_norm_sub_le_angle
        (wz1PaperDirection_norm first)
        (wz1PaperDirection_norm second)

/-- Pull back paper-line distance through one centered isotropic similarity.
The centre is only required to lie in the paper height window. -/
theorem proposition63_source_lineDistance_le_fourteen_mul_target
    {sourceDelta targetDelta scale : ℝ}
    (hscale : 1 ≤ scale)
    (center : Point3)
    (hcenterHeight : |center 2| ≤ 2)
    (sourceFirst sourceSecond : Kakeya.DeltaTube sourceDelta)
    (targetFirst targetSecond : Kakeya.DeltaTube targetDelta)
    (hsourceFirst : WZ1PaperTubeInLineClass sourceFirst)
    (hsourceSecond : WZ1PaperTubeInLineClass sourceSecond)
    (htargetFirst : WZ1PaperTubeInLineClass targetFirst)
    (htargetSecond : WZ1PaperTubeInLineClass targetSecond)
    (hfirstAxis : tubeAxisLine targetFirst =
      wz1IsotropicRescalingMap center scale '' tubeAxisLine sourceFirst)
    (hsecondAxis : tubeAxisLine targetSecond =
      wz1IsotropicRescalingMap center scale '' tubeAxisLine sourceSecond)
    (hfirstDirection : targetFirst.direction =
      wz1PaperDirection sourceFirst)
    (hsecondDirection : targetSecond.direction =
      wz1PaperDirection sourceSecond) :
    wz1PaperLineDistance sourceFirst sourceSecond ≤
      14 * wz1PaperLineDistance targetFirst targetSecond := by
  let sourceFirstPoint :=
    wz1PaperAxisPointAtHeight sourceFirst (center 2)
  let sourceSecondPoint :=
    wz1PaperAxisPointAtHeight sourceSecond (center 2)
  let sourceFirstDirection := wz1PaperDirection sourceFirst
  let sourceSecondDirection := wz1PaperDirection sourceSecond
  let sourceFirstVertical := sourceFirstDirection 2
  let sourceSecondVertical := sourceSecondDirection 2
  have htargetFirstZero := proposition63_isotropic_target_zeroPoint
    (lt_of_lt_of_le zero_lt_one hscale) center sourceFirst targetFirst
    hsourceFirst htargetFirst hfirstAxis
  have htargetSecondZero := proposition63_isotropic_target_zeroPoint
    (lt_of_lt_of_le zero_lt_one hscale) center sourceSecond targetSecond
    hsourceSecond htargetSecond hsecondAxis
  have htargetFirstPaper := proposition63_isotropic_target_paperDirection
    sourceFirst targetFirst hsourceFirst hfirstDirection
  have htargetSecondPaper := proposition63_isotropic_target_paperDirection
    sourceSecond targetSecond hsourceSecond hsecondDirection
  have hpointDistance :
      dist sourceFirstPoint sourceSecondPoint ≤
        wz1PaperLineDistance targetFirst targetSecond := by
    have hscaledDistance :
        dist (wz1IsotropicRescalingMap center scale sourceFirstPoint)
            (wz1IsotropicRescalingMap center scale sourceSecondPoint) =
          scale * dist sourceFirstPoint sourceSecondPoint := by
      simp only [wz1IsotropicRescalingMap, dist_eq_norm]
      rw [show
        scale • (sourceFirstPoint - center) -
            scale • (sourceSecondPoint - center) =
          scale • (sourceFirstPoint - sourceSecondPoint) by module,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hzeroPart :
        dist (wz1TubeAxisZeroPoint targetFirst)
            (wz1TubeAxisZeroPoint targetSecond) ≤
          wz1PaperLineDistance targetFirst targetSecond := by
      dsimp only [wz1PaperLineDistance]
      linarith [InnerProductGeometry.angle_nonneg
        (wz1PaperDirection targetFirst) (wz1PaperDirection targetSecond)]
    rw [htargetFirstZero, htargetSecondZero, hscaledDistance] at hzeroPart
    have hscaleMul :
        dist sourceFirstPoint sourceSecondPoint ≤
          scale * dist sourceFirstPoint sourceSecondPoint := by
      exact le_mul_of_one_le_left dist_nonneg hscale
    exact hscaleMul.trans hzeroPart
  have hangle :
      InnerProductGeometry.angle sourceFirstDirection sourceSecondDirection ≤
        wz1PaperLineDistance targetFirst targetSecond := by
    have hanglePart :
        InnerProductGeometry.angle
            (wz1PaperDirection targetFirst)
            (wz1PaperDirection targetSecond) ≤
          wz1PaperLineDistance targetFirst targetSecond := by
      dsimp only [wz1PaperLineDistance]
      linarith [dist_nonneg
        (x := wz1TubeAxisZeroPoint targetFirst)
        (y := wz1TubeAxisZeroPoint targetSecond)]
    simpa [sourceFirstDirection, sourceSecondDirection,
      htargetFirstPaper, htargetSecondPaper] using hanglePart
  have hslope := proposition63_paperSlope_sub_norm_le_six_angle
    sourceFirst sourceSecond hsourceFirst hsourceSecond
  have hfirstPointIdentity :
      sourceFirstPoint = wz1TubeAxisZeroPoint sourceFirst +
        (center 2) •
          ((sourceFirstVertical)⁻¹ • sourceFirstDirection) := by
    dsimp only [sourceFirstPoint, sourceFirstVertical, sourceFirstDirection,
      wz1PaperAxisPointAtHeight]
    rw [smul_smul]
    ring_nf
  have hsecondPointIdentity :
      sourceSecondPoint = wz1TubeAxisZeroPoint sourceSecond +
        (center 2) •
          ((sourceSecondVertical)⁻¹ • sourceSecondDirection) := by
    dsimp only [sourceSecondPoint, sourceSecondVertical, sourceSecondDirection,
      wz1PaperAxisPointAtHeight]
    rw [smul_smul]
    ring_nf
  have hzeroVector :
      wz1TubeAxisZeroPoint sourceFirst -
          wz1TubeAxisZeroPoint sourceSecond =
        (sourceFirstPoint - sourceSecondPoint) -
          (center 2) •
            ((sourceFirstVertical)⁻¹ • sourceFirstDirection -
              (sourceSecondVertical)⁻¹ • sourceSecondDirection) := by
    rw [hfirstPointIdentity, hsecondPointIdentity]
    module
  have hzeroDistance :
      dist (wz1TubeAxisZeroPoint sourceFirst)
          (wz1TubeAxisZeroPoint sourceSecond) ≤
        dist sourceFirstPoint sourceSecondPoint +
          12 * InnerProductGeometry.angle
            sourceFirstDirection sourceSecondDirection := by
    rw [dist_eq_norm, hzeroVector]
    calc
      ‖(sourceFirstPoint - sourceSecondPoint) -
          (center 2) •
            ((sourceFirstVertical)⁻¹ • sourceFirstDirection -
              (sourceSecondVertical)⁻¹ • sourceSecondDirection)‖ ≤
        ‖sourceFirstPoint - sourceSecondPoint‖ +
          ‖(center 2) •
            ((sourceFirstVertical)⁻¹ • sourceFirstDirection -
              (sourceSecondVertical)⁻¹ • sourceSecondDirection)‖ :=
        norm_sub_le _ _
      _ = dist sourceFirstPoint sourceSecondPoint +
          |center 2| *
            ‖(sourceFirstVertical)⁻¹ • sourceFirstDirection -
              (sourceSecondVertical)⁻¹ • sourceSecondDirection‖ := by
        rw [dist_eq_norm, norm_smul, Real.norm_eq_abs]
      _ ≤ dist sourceFirstPoint sourceSecondPoint +
          2 * (6 * InnerProductGeometry.angle
            sourceFirstDirection sourceSecondDirection) := by
        gcongr
      _ = dist sourceFirstPoint sourceSecondPoint +
          12 * InnerProductGeometry.angle
            sourceFirstDirection sourceSecondDirection := by ring
  dsimp only [wz1PaperLineDistance]
  calc
    dist (wz1TubeAxisZeroPoint sourceFirst)
          (wz1TubeAxisZeroPoint sourceSecond) +
        InnerProductGeometry.angle sourceFirstDirection sourceSecondDirection ≤
      dist sourceFirstPoint sourceSecondPoint +
        13 * InnerProductGeometry.angle
          sourceFirstDirection sourceSecondDirection := by linarith
    _ ≤ 14 * wz1PaperLineDistance targetFirst targetSecond := by
      linarith

/-- Forward paper-line control under the same centered isotropic similarity.
The height-zero displacement expands by `scale`; moving the comparison plane
to the height of the box center costs at most six angular units. -/
theorem proposition63_target_lineDistance_le_thirteen_mul_scale_source
    {sourceDelta targetDelta scale : ℝ}
    (hscale : 1 ≤ scale)
    (center : Point3)
    (hcenterHeight : |center 2| ≤ 2)
    (sourceFirst sourceSecond : Kakeya.DeltaTube sourceDelta)
    (targetFirst targetSecond : Kakeya.DeltaTube targetDelta)
    (hsourceFirst : WZ1PaperTubeInLineClass sourceFirst)
    (hsourceSecond : WZ1PaperTubeInLineClass sourceSecond)
    (htargetFirst : WZ1PaperTubeInLineClass targetFirst)
    (htargetSecond : WZ1PaperTubeInLineClass targetSecond)
    (hfirstAxis : tubeAxisLine targetFirst =
      wz1IsotropicRescalingMap center scale '' tubeAxisLine sourceFirst)
    (hsecondAxis : tubeAxisLine targetSecond =
      wz1IsotropicRescalingMap center scale '' tubeAxisLine sourceSecond)
    (hfirstDirection : targetFirst.direction =
      wz1PaperDirection sourceFirst)
    (hsecondDirection : targetSecond.direction =
      wz1PaperDirection sourceSecond) :
    wz1PaperLineDistance targetFirst targetSecond ≤
      13 * scale * wz1PaperLineDistance sourceFirst sourceSecond := by
  let sourceFirstPoint :=
    wz1PaperAxisPointAtHeight sourceFirst (center 2)
  let sourceSecondPoint :=
    wz1PaperAxisPointAtHeight sourceSecond (center 2)
  let sourceFirstDirection := wz1PaperDirection sourceFirst
  let sourceSecondDirection := wz1PaperDirection sourceSecond
  let sourceFirstVertical := sourceFirstDirection 2
  let sourceSecondVertical := sourceSecondDirection 2
  have htargetFirstZero := proposition63_isotropic_target_zeroPoint
    (lt_of_lt_of_le zero_lt_one hscale) center sourceFirst targetFirst
    hsourceFirst htargetFirst hfirstAxis
  have htargetSecondZero := proposition63_isotropic_target_zeroPoint
    (lt_of_lt_of_le zero_lt_one hscale) center sourceSecond targetSecond
    hsourceSecond htargetSecond hsecondAxis
  have htargetFirstPaper := proposition63_isotropic_target_paperDirection
    sourceFirst targetFirst hsourceFirst hfirstDirection
  have htargetSecondPaper := proposition63_isotropic_target_paperDirection
    sourceSecond targetSecond hsourceSecond hsecondDirection
  have hslope := proposition63_paperSlope_sub_norm_le_six_angle
    sourceFirst sourceSecond hsourceFirst hsourceSecond
  have hfirstPointIdentity :
      sourceFirstPoint = wz1TubeAxisZeroPoint sourceFirst +
        (center 2) •
          ((sourceFirstVertical)⁻¹ • sourceFirstDirection) := by
    dsimp only [sourceFirstPoint, sourceFirstVertical, sourceFirstDirection,
      wz1PaperAxisPointAtHeight]
    rw [smul_smul]
    ring_nf
  have hsecondPointIdentity :
      sourceSecondPoint = wz1TubeAxisZeroPoint sourceSecond +
        (center 2) •
          ((sourceSecondVertical)⁻¹ • sourceSecondDirection) := by
    dsimp only [sourceSecondPoint, sourceSecondVertical, sourceSecondDirection,
      wz1PaperAxisPointAtHeight]
    rw [smul_smul]
    ring_nf
  have hpointVector :
      sourceFirstPoint - sourceSecondPoint =
        (wz1TubeAxisZeroPoint sourceFirst -
          wz1TubeAxisZeroPoint sourceSecond) +
        (center 2) •
          ((sourceFirstVertical)⁻¹ • sourceFirstDirection -
            (sourceSecondVertical)⁻¹ • sourceSecondDirection) := by
    rw [hfirstPointIdentity, hsecondPointIdentity]
    module
  have hpointDistance :
      dist sourceFirstPoint sourceSecondPoint ≤
        dist (wz1TubeAxisZeroPoint sourceFirst)
            (wz1TubeAxisZeroPoint sourceSecond) +
          12 * InnerProductGeometry.angle
            sourceFirstDirection sourceSecondDirection := by
    rw [dist_eq_norm, hpointVector]
    calc
      ‖(wz1TubeAxisZeroPoint sourceFirst -
            wz1TubeAxisZeroPoint sourceSecond) +
          (center 2) •
            ((sourceFirstVertical)⁻¹ • sourceFirstDirection -
              (sourceSecondVertical)⁻¹ • sourceSecondDirection)‖ ≤
          ‖wz1TubeAxisZeroPoint sourceFirst -
              wz1TubeAxisZeroPoint sourceSecond‖ +
            ‖(center 2) •
              ((sourceFirstVertical)⁻¹ • sourceFirstDirection -
                (sourceSecondVertical)⁻¹ • sourceSecondDirection)‖ :=
        norm_add_le _ _
      _ = dist (wz1TubeAxisZeroPoint sourceFirst)
              (wz1TubeAxisZeroPoint sourceSecond) +
            |center 2| *
              ‖(sourceFirstVertical)⁻¹ • sourceFirstDirection -
                (sourceSecondVertical)⁻¹ • sourceSecondDirection‖ := by
        rw [dist_eq_norm, norm_smul, Real.norm_eq_abs]
      _ ≤ dist (wz1TubeAxisZeroPoint sourceFirst)
              (wz1TubeAxisZeroPoint sourceSecond) +
            2 * (6 * InnerProductGeometry.angle
              sourceFirstDirection sourceSecondDirection) := by
        gcongr
      _ = dist (wz1TubeAxisZeroPoint sourceFirst)
              (wz1TubeAxisZeroPoint sourceSecond) +
            12 * InnerProductGeometry.angle
              sourceFirstDirection sourceSecondDirection := by ring
  have hscaledDistance :
      dist (wz1IsotropicRescalingMap center scale sourceFirstPoint)
          (wz1IsotropicRescalingMap center scale sourceSecondPoint) =
        scale * dist sourceFirstPoint sourceSecondPoint := by
    simp only [wz1IsotropicRescalingMap, dist_eq_norm]
    rw [show
      scale • (sourceFirstPoint - center) -
          scale • (sourceSecondPoint - center) =
        scale • (sourceFirstPoint - sourceSecondPoint) by module,
      norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hsourceMetric :
      dist (wz1TubeAxisZeroPoint sourceFirst)
            (wz1TubeAxisZeroPoint sourceSecond) +
          InnerProductGeometry.angle
            sourceFirstDirection sourceSecondDirection =
        wz1PaperLineDistance sourceFirst sourceSecond := rfl
  have hangleNonnegative : 0 ≤ InnerProductGeometry.angle
      sourceFirstDirection sourceSecondDirection :=
    InnerProductGeometry.angle_nonneg _ _
  dsimp only [wz1PaperLineDistance]
  rw [htargetFirstZero, htargetSecondZero, hscaledDistance,
    htargetFirstPaper, htargetSecondPaper]
  calc
    scale * dist sourceFirstPoint sourceSecondPoint +
          InnerProductGeometry.angle sourceFirstDirection sourceSecondDirection ≤
        scale *
          (dist (wz1TubeAxisZeroPoint sourceFirst)
              (wz1TubeAxisZeroPoint sourceSecond) +
            12 * InnerProductGeometry.angle
              sourceFirstDirection sourceSecondDirection) +
          InnerProductGeometry.angle sourceFirstDirection sourceSecondDirection := by
      gcongr
    _ ≤ 13 * scale *
        (dist (wz1TubeAxisZeroPoint sourceFirst)
            (wz1TubeAxisZeroPoint sourceSecond) +
          InnerProductGeometry.angle
            sourceFirstDirection sourceSecondDirection) := by
      nlinarith [dist_nonneg
        (x := wz1TubeAxisZeroPoint sourceFirst)
        (y := wz1TubeAxisZeroPoint sourceSecond)]
    _ = 13 * scale *
        wz1PaperLineDistance sourceFirst sourceSecond := by
      rw [← hsourceMetric]

/-- A uniform degree bound for the ordinary centered-containment conflict
graph on the paper's one-line-per-source isotropic image family. -/
def proposition63MildRescalingConflictDegree
    (sourceDelta scale : ℝ) : ℕ :=
  (2 * Nat.ceil
      (8 * (1400 * (scale * sourceDelta)) / sourceDelta) + 1) ^ 5

/-- Every centered-containment conflict in the target pulls back to a bounded
paper-line neighbourhood in the source.  The resulting degree is finite by
the five-dimensional line packing used in the paper. -/
theorem proposition63_mild_rescaling_conflict_degree
    {sourceDelta scale : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hscale : 1 ≤ scale)
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (hsourceLine : WZ1PaperIsLineClass sourceFamily)
    (hsourceDistinct : WZ1PaperIsEssentiallyDistinct sourceFamily)
    {sourceShading : Kakeya.Streamlined.TubeShading sourceFamily}
    {center : Point3}
    (hcenterHeight : |center 2| ≤ 2)
    (raw : WZ1IsotropicTubeRediscretizationData
      (scale := scale) sourceFamily sourceShading center)
    (hrawLine : WZ1PaperIsLineClass raw.family)
    (reference : Fin
      (proposition63MildRescalingFamily hscale raw).card) :
    ((Finset.univ : Finset
        (Fin (proposition63MildRescalingFamily hscale raw).card)).filter
      (ordinaryContainmentConflict
        (proposition63MildRescalingFamily hscale raw) reference)).card ≤
      proposition63MildRescalingConflictDegree sourceDelta scale := by
  let targetFamily := proposition63MildRescalingFamily hscale raw
  let radius : ℝ := 1400 * (scale * sourceDelta)
  let targetConflict : Finset (Fin targetFamily.card) :=
    Finset.univ.filter
      (ordinaryContainmentConflict targetFamily reference)
  let sourceBall : Finset (Fin sourceFamily.card) :=
    Finset.univ.filter fun source =>
      wz1PaperLineDistance (sourceFamily.tube source)
        (sourceFamily.tube reference) ≤ radius
  have hsubset : targetConflict ⊆ sourceBall := by
    intro candidate hcandidate
    have hconflict := (Finset.mem_filter.mp hcandidate).2
    have htargetLine := proposition63MildRescalingFamily_lineClass
      hscale raw hrawLine
    have htargetDistance :
        wz1PaperLineDistance (targetFamily.tube candidate)
          (targetFamily.tube reference) ≤
        wz2PaperLocalizedDoubledFiberLineDistanceConstant *
          (scale * sourceDelta) := by
      rcases hconflict.2 with hforward | hbackward
      · rw [wz1PaperLineDistance_symm]
        exact
          wz2_paper_localized_centered_doubled_containment_lineDistance_le
            (mul_pos (lt_of_lt_of_le zero_lt_one hscale) hsourceDelta)
            (mul_pos (lt_of_lt_of_le zero_lt_one hscale) hsourceDelta)
            (htargetLine reference) (htargetLine candidate)
            (proposition63MildRescalingFamily_midpoint_local
              hscale raw hrawLine reference) hforward
      · exact
          wz2_paper_localized_centered_doubled_containment_lineDistance_le
            (mul_pos (lt_of_lt_of_le zero_lt_one hscale) hsourceDelta)
            (mul_pos (lt_of_lt_of_le zero_lt_one hscale) hsourceDelta)
            (htargetLine candidate) (htargetLine reference)
            (proposition63MildRescalingFamily_midpoint_local
              hscale raw hrawLine candidate) hbackward
    have hsourceDistance :=
      proposition63_source_lineDistance_le_fourteen_mul_target
        hscale center hcenterHeight
        (sourceFamily.tube candidate) (sourceFamily.tube reference)
        (targetFamily.tube candidate) (targetFamily.tube reference)
        (hsourceLine candidate) (hsourceLine reference)
        (htargetLine candidate) (htargetLine reference)
        (proposition63MildRescalingFamily_axis_provenance
          hscale raw candidate)
        (proposition63MildRescalingFamily_axis_provenance
          hscale raw reference)
        (proposition63MildRescalingFamily_direction_provenance
          hscale raw candidate)
        (proposition63MildRescalingFamily_direction_provenance
          hscale raw reference)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    dsimp only [radius]
    unfold wz2PaperLocalizedDoubledFiberLineDistanceConstant at htargetDistance
    linarith
  have hcard : targetConflict.card ≤ sourceBall.card :=
    Finset.card_le_card hsubset
  have hpacking := tube_packing_bound_general hsourceDistinct hsourceLine
    hsourceDelta radius (by
      dsimp only [radius]
      positivity) reference
  change targetConflict.card ≤
    proposition63MildRescalingConflictDegree sourceDelta scale
  exact hcard.trans <| by
    simpa [sourceBall, radius, proposition63MildRescalingConflictDegree]
      using hpacking

end Kakeya.Assouad.PureWZ2

end
