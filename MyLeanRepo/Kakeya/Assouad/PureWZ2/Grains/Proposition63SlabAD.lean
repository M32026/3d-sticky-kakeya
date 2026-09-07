import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63SlopeExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ChartRescaled
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CoarseParentSourceSampleGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.PaperAnchoredTransport
import MyLeanRepo.Kakeya.Assouad.WZ1.PerCellHorizontalizeAD
import MyLeanRepo.Kakeya.Assouad.WZ1.SecondChartHorizontalize
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralMapRelation
import MyLeanRepo.Kakeya.Assouad.PropStickyInnerParentCubeContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralRescalingBounds

/-!
# Slabwise global AD for Proposition 6.3

This file implements the paragraph from the local AD estimate at `p_z` to
the horizontal global-grain estimate on the corresponding retained slab.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Metric Set

private lemma point_dist_parent_paper_projection
    {delta rho : ℝ}
    {source : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 24)
    (hsourceLine : WZ1PaperTubeInLineClass source)
    (hparentLine : WZ1PaperTubeInLineClass parent)
    (hcover : WZ1PaperTubeCovers source parent)
    (point : Point3) (hpoint : point ∈ wz1PaperTubeCarrier source)
    (hpointNorm : ‖point‖ ≤ 3) :
    dist point
        (wz1TubeAxisZeroPoint parent +
          paperTubeHeight parent point • wz1PaperDirection parent) ≤
      6 * delta + 3 * rho := by
  let sourceZero := wz1TubeAxisZeroPoint source
  let parentZero := wz1TubeAxisZeroPoint parent
  let sourceDirection := wz1PaperDirection source
  let parentDirection := wz1PaperDirection parent
  rcases exists_dist_le_of_mem_cthickening_closed
      (isClosed_tubeAxisLine source) (by positivity : 0 ≤ 6 * delta)
      hpoint.1 with ⟨axisPoint, haxisPoint, hpointAxis⟩
  rcases wz1Paper_axis_exists_parameter hsourceLine haxisPoint with
    ⟨parameter, haxisPointEq⟩
  have hsourceZeroNorm : ‖sourceZero‖ ≤ 1 :=
    paperAxisZeroPoint_norm_le_one hsourceLine
  have hpointSourceZero : dist point sourceZero ≤ 4 := by
    rw [dist_eq_norm]
    exact (norm_sub_le point sourceZero).trans
      (by linarith)
  have hparameterDistance : dist axisPoint sourceZero = |parameter| := by
    calc
      dist axisPoint sourceZero = ‖parameter • sourceDirection‖ := by
        rw [dist_eq_norm, haxisPointEq]
        congr 1
        module
      _ = |parameter| * ‖sourceDirection‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = |parameter| := by
        rw [show ‖sourceDirection‖ = 1 by
          exact wz1PaperDirection_norm source, mul_one]
  have hparameter : |parameter| ≤ 5 := by
    rw [← hparameterDistance]
    calc
      dist axisPoint sourceZero ≤
          dist axisPoint point + dist point sourceZero := dist_triangle _ _ _
      _ ≤ 6 * delta + 4 := by
        rw [dist_comm axisPoint point]
        gcongr
      _ ≤ 5 := by nlinarith
  let comparisonPoint : Point3 :=
    parentZero + parameter • parentDirection
  have haxisComparison : dist axisPoint comparisonPoint ≤ 3 * rho := by
    rw [haxisPointEq, dist_eq_norm]
    have hdifference :
        sourceZero + parameter • sourceDirection - comparisonPoint =
          (sourceZero - parentZero) +
            parameter • (sourceDirection - parentDirection) := by
      dsimp only [comparisonPoint]
      module
    rw [hdifference]
    calc
      ‖(sourceZero - parentZero) +
          parameter • (sourceDirection - parentDirection)‖ ≤
        ‖sourceZero - parentZero‖ +
          ‖parameter • (sourceDirection - parentDirection)‖ :=
        norm_add_le _ _
      _ = dist sourceZero parentZero +
          |parameter| * ‖sourceDirection - parentDirection‖ := by
        rw [dist_eq_norm, norm_smul, Real.norm_eq_abs]
      _ ≤ rho / 2 + 5 * (rho / 2) := by
        gcongr
        · exact hcover.components.1
        · exact paper_cover_direction_alignment hcover
      _ = 3 * rho := by ring
  have hpointComparison : dist point comparisonPoint ≤
      6 * delta + 3 * rho := by
    calc
      dist point comparisonPoint ≤
          dist point axisPoint + dist axisPoint comparisonPoint :=
        dist_triangle _ _ _
      _ ≤ 6 * delta + 3 * rho := add_le_add hpointAxis haxisComparison
  let vector := point - parentZero
  let projectedPoint := parentZero +
    (inner ℝ vector parentDirection) • parentDirection
  have hprojectedPoint : projectedPoint =
      wz1TubeAxisZeroPoint parent +
        paperTubeHeight parent point • wz1PaperDirection parent := by
    rfl
  have hprojectionDifference :
      point - projectedPoint = perpPart parentDirection vector := by
    dsimp only [projectedPoint, vector, parentZero, parentDirection]
    unfold perpPart
    abel
  have hperpEq :
      perpPart parentDirection vector =
        perpPart parentDirection (point - comparisonPoint) := by
    unfold perpPart
    have hdirSelf :
        inner ℝ parentDirection parentDirection = 1 := by
      rw [real_inner_self_eq_norm_sq, wz1PaperDirection_norm]
      norm_num
    have hinnerShift :
        inner ℝ (point - comparisonPoint) parentDirection =
          inner ℝ vector parentDirection - parameter := by
      dsimp only [vector, comparisonPoint]
      rw [show point - (parentZero + parameter • parentDirection) =
          (point - parentZero) - parameter • parentDirection by module,
        inner_sub_left, inner_smul_left, hdirSelf]
      simp only [RCLike.star_def, RCLike.conj_to_real, mul_one]
    rw [hinnerShift]
    dsimp only [vector, comparisonPoint]
    module
  rw [← hprojectedPoint, dist_eq_norm]
  rw [hprojectionDifference, hperpEq]
  exact (perpPart_norm_le parentDirection
    (wz1PaperDirection_norm parent) (point - comparisonPoint)).trans
      (by simpa [dist_eq_norm] using hpointComparison)

private lemma shared_parent_dist_le_paper_height
    {delta rho : ℝ}
    {firstTube secondTube : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube rho}
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 24)
    (hfirstLine : WZ1PaperTubeInLineClass firstTube)
    (hsecondLine : WZ1PaperTubeInLineClass secondTube)
    (hparentLine : WZ1PaperTubeInLineClass parent)
    (hfirstCover : WZ1PaperTubeCovers firstTube parent)
    (hsecondCover : WZ1PaperTubeCovers secondTube parent)
    (first second : Point3)
    (hfirst : first ∈ wz1PaperTubeCarrier firstTube)
    (hsecond : second ∈ wz1PaperTubeCarrier secondTube)
    (hfirstNorm : ‖first‖ ≤ 3) (hsecondNorm : ‖second‖ ≤ 3) :
    dist first second ≤
      |paperTubeHeight parent first - paperTubeHeight parent second| +
        12 * delta + 6 * rho := by
  let firstProjection := wz1TubeAxisZeroPoint parent +
    paperTubeHeight parent first • wz1PaperDirection parent
  let secondProjection := wz1TubeAxisZeroPoint parent +
    paperTubeHeight parent second • wz1PaperDirection parent
  have hfirstProjection : dist first firstProjection ≤ 6 * delta + 3 * rho :=
    point_dist_parent_paper_projection hdelta hdeltaSmall hfirstLine
      hparentLine hfirstCover first hfirst hfirstNorm
  have hsecondProjection : dist secondProjection second ≤
      6 * delta + 3 * rho := by
    rw [dist_comm]
    exact point_dist_parent_paper_projection hdelta hdeltaSmall hsecondLine
      hparentLine hsecondCover second hsecond hsecondNorm
  have hbetween : dist firstProjection secondProjection =
      |paperTubeHeight parent first - paperTubeHeight parent second| := by
    rw [dist_eq_norm]
    have hdifference : firstProjection - secondProjection =
        (paperTubeHeight parent first - paperTubeHeight parent second) •
          wz1PaperDirection parent := by
      dsimp only [firstProjection, secondProjection]
      module
    rw [hdifference, norm_smul, wz1PaperDirection_norm, mul_one]
    exact Real.norm_eq_abs _
  calc
    dist first second ≤ dist first firstProjection +
        dist firstProjection secondProjection +
          dist secondProjection second := by
      linarith [dist_triangle first firstProjection second,
        dist_triangle firstProjection secondProjection second]
    _ ≤ (6 * delta + 3 * rho) +
        |paperTubeHeight parent first - paperTubeHeight parent second| +
          (6 * delta + 3 * rho) := by
      rw [hbetween]
      gcongr
    _ = |paperTubeHeight parent first - paperTubeHeight parent second| +
        12 * delta + 6 * rho := by ring

private lemma inner_longitudinalCompression_of_coord2_zero
    (point direction : Point3) (hdirection : direction 2 = 0) :
    inner ℝ (wz2PaperLongitudinalCompression point) direction =
      inner ℝ point direction := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [Fin.sum_univ_succ, wz2PaperLongitudinalCompression, hdirection]

private lemma horizontal_chart_direction_coord2
    (chart : WZ1HorizontalChart) (slope : ℝ) :
    chart.direction slope 2 = 0 := by
  cases chart <;>
    simp [WZ1HorizontalChart.direction, globalGrainDirection, point3]

namespace Proposition63ChartSelectionData

variable
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}

def sourceSlab
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta)) : Set Point3 :=
  selection.sourceShading.union ∩
    proposition63AxialSlab (coarse.tube input.parent) hrho
      (proposition63LiteralSliceWidth Delta) interval.1

def anchoredSourceSlab
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta)) : Set Point3 :=
  wz1AnchoredUnitRescalingMap data.parentChartTube rho hrho ''
    selection.sourceSlab interval

def literalSourceSlab
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta)) : Set Point3 :=
  wz2PaperLiteralUnitRescalingMap (coarse.tube input.parent) hrho ''
    selection.sourceSlab interval

lemma anchoredSourceSlab_height
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta)) :
    ∀ point ∈ selection.anchoredSourceSlab interval,
      point 2 ∈ Set.Icc
        (selection.intervalBase interval - Delta)
        (selection.intervalBase interval + Delta) := by
  intro point hpoint
  rcases hpoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  have hsourceSlab := hsourcePoint.2
  rw [data.parentChartMap_eq_paperMap]
  rw [wz1PaperUnitRescalingMap_coord2]
  change proposition63AxialCoordinate (coarse.tube input.parent) hrho
      sourcePoint ∈ Set.Ico
        ((interval.1 : ℝ) * proposition63LiteralSliceWidth Delta)
        (((interval.1 : ℝ) + 1) * proposition63LiteralSliceWidth Delta)
    at hsourceSlab
  have hscaledLower : selection.intervalBase interval ≤
      100 * proposition63AxialCoordinate
        (coarse.tube input.parent) hrho sourcePoint := by
    calc
      selection.intervalBase interval =
          100 * ((interval.1 : ℝ) *
            proposition63LiteralSliceWidth Delta) := by
        unfold intervalBase proposition63LiteralSliceWidth
        ring
      _ ≤ _ := by gcongr; exact hsourceSlab.1
  have hscaledUpper :
      100 * proposition63AxialCoordinate
          (coarse.tube input.parent) hrho sourcePoint ≤
        selection.intervalBase interval + Delta := by
    calc
      _ ≤ 100 * (((interval.1 : ℝ) + 1) *
          proposition63LiteralSliceWidth Delta) := by
        gcongr; exact hsourceSlab.2.le
      _ = _ := by unfold intervalBase proposition63LiteralSliceWidth; ring
  have hpaperEq : inner ℝ
      (sourcePoint - wz1TubeAxisZeroPoint (coarse.tube input.parent))
        (wz1PaperDirection (coarse.tube input.parent)) =
      100 * proposition63AxialCoordinate
        (coarse.tube input.parent) hrho sourcePoint := by
    rw [proposition63AxialCoordinate_eq]
    ring
  rw [hpaperEq]
  constructor <;> linarith

lemma horizontal_projection_literalSourceSlab_eq_anchoredSourceSlab
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (chart : WZ1HorizontalChart) (slope : ℝ) :
    scalarProjection (chart.direction slope)
        (selection.literalSourceSlab interval) =
      scalarProjection (chart.direction slope)
        (selection.anchoredSourceSlab interval) := by
  ext value
  constructor
  · rintro ⟨literalPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
    refine ⟨wz1AnchoredUnitRescalingMap data.parentChartTube rho hrho
      sourcePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
    rw [wz2_paper_literal_map_coordinate_relation
      (coarse.tube input.parent) hrho sourcePoint,
      ← data.parentChartMap_eq_paperMap sourcePoint]
    exact (inner_longitudinalCompression_of_coord2_zero _ _
      (horizontal_chart_direction_coord2 chart slope)).symm
  · rintro ⟨anchoredPoint, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
    refine ⟨wz2PaperLiteralUnitRescalingMap (coarse.tube input.parent)
      hrho sourcePoint, ⟨sourcePoint, hsourcePoint, rfl⟩, ?_⟩
    rw [wz2_paper_literal_map_coordinate_relation
      (coarse.tube input.parent) hrho sourcePoint,
      ← data.parentChartMap_eq_paperMap sourcePoint]
    exact inner_longitudinalCompression_of_coord2_zero _ _
      (horizontal_chart_direction_coord2 chart slope)

lemma sourceSlab_subset_localBall
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ selection.intervals) :
    selection.sourceSlab interval ⊆
      Metric.closedBall
        (data.anchorPoint interval (selection.intervals_subset hinterval))
        (50 * Delta) := by
  intro point hpoint
  let hretained := selection.intervals_subset hinterval
  let anchorPoint := data.anchorPoint interval hretained
  rcases hpoint.1 with ⟨index, hsource⟩
  have hpointCarrier := selection.sourceShading.subset_body index hsource
  have hanchorCarrier := data.commonSlice.shading.subset_body
    data.commonSlice.distinguished
    (data.anchorPoint_mem_commonSlice interval hretained)
  have hsourceLine : WZ1PaperTubeInLineClass
      (input.fiberFamily.family.tube index) :=
    cover.fine_line_class.subfamily input.fiberFamily index
  have hanchorLine : WZ1PaperTubeInLineClass data.anchorTube :=
    cover.fine_line_class.subfamily input.fiberFamily
      data.commonSlice.distinguished
  have hparentLine : WZ1PaperTubeInLineClass
      (coarse.tube input.parent) := cover.coarse_line_class input.parent
  have hsourceCover : WZ1PaperTubeCovers
      (input.fiberFamily.family.tube index)
      (coarse.tube input.parent) := by
    rw [input.fiberFamily.tube_eq]
    exact (mem_wz2PaperFullFiberIndices_iff input.parent
      (input.fiberFamily.embedding index)).mp
        (Finset.orderEmbOfFin_mem _ _ _)
  have hanchorCover := data.anchor_covers_parent
  have hcoordinate : |proposition63AxialCoordinate
        (coarse.tube input.parent) hrho point -
      proposition63AxialCoordinate
        (coarse.tube input.parent) hrho anchorPoint| <
      proposition63LiteralSliceWidth Delta := by
    have hpointInterval := hpoint.2
    have hanchorInterval := (data.anchorPoint_mem interval hretained).2
    rw [abs_lt]
    constructor <;> linarith [hpointInterval.1, hpointInterval.2,
      hanchorInterval.1, hanchorInterval.2]
  have hheight :
      |paperTubeHeight (coarse.tube input.parent) point -
        paperTubeHeight (coarse.tube input.parent) anchorPoint| < Delta := by
    have hpointEq := proposition63AxialCoordinate_eq
      (coarse.tube input.parent) hrho point
    have hanchorEq := proposition63AxialCoordinate_eq
      (coarse.tube input.parent) hrho anchorPoint
    have heq :
        paperTubeHeight (coarse.tube input.parent) point -
            paperTubeHeight (coarse.tube input.parent) anchorPoint =
          100 * (proposition63AxialCoordinate
              (coarse.tube input.parent) hrho point -
            proposition63AxialCoordinate
              (coarse.tube input.parent) hrho anchorPoint) := by
      unfold paperTubeHeight
      rw [hpointEq, hanchorEq]
      ring
    rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
    calc
      100 * |proposition63AxialCoordinate
          (coarse.tube input.parent) hrho point -
        proposition63AxialCoordinate
          (coarse.tube input.parent) hrho anchorPoint| <
        100 * proposition63LiteralSliceWidth Delta := by gcongr
      _ = Delta := by unfold proposition63LiteralSliceWidth; ring
  have hpointNorm := paperShadingPoint_norm_le_three
    (shading := selection.sourceShading) hpoint.1
  have hanchorNorm := paperShadingPoint_norm_le_three
    (shading := data.commonSlice.shading)
    ⟨data.commonSlice.distinguished,
      data.anchorPoint_mem_commonSlice interval hretained⟩
  have hdist := shared_parent_dist_le_paper_height hdelta
    (hdeltaDelta.trans (by nlinarith [hDeltaSmall, hDelta]))
    hsourceLine hanchorLine hparentLine hsourceCover hanchorCover
    point anchorPoint hpointCarrier hanchorCarrier hpointNorm hanchorNorm
  have hlinear : delta ≤ Delta :=
    hdeltaDelta.trans (by nlinarith [hDeltaSmall, hDelta])
  have hrhoTerm : 6 * rho = 6 * Delta := congrArg (fun value => 6 * value) hrhoDelta
  have hfinalStrict : dist point anchorPoint < 50 * Delta := by
    calc
      dist point anchorPoint ≤
          |paperTubeHeight (coarse.tube input.parent) point -
            paperTubeHeight (coarse.tube input.parent) anchorPoint| +
            12 * delta + 6 * rho := hdist
      _ < Delta + 12 * delta + 6 * rho := by gcongr
      _ = Delta + 12 * delta + 6 * Delta := by rw [hrhoTerm]
      _ < 50 * Delta := by nlinarith
  have hfinal : dist point anchorPoint ≤ 50 * Delta := hfinalStrict.le
  simpa [Metric.mem_closedBall, anchorPoint] using hfinal

end Proposition63ChartSelectionData

/-- The exact source piece whose local AD estimate is transported for one
retained interval. -/
def proposition63LocalSourceSet
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    (data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ data.retainedIntervals) : Set Point3 :=
  data.commonSlice.shading.union ∩
    Metric.closedBall (data.intervalPoint interval hinterval) (50 * Delta)

/-- Source local AD, transported to the normalized parent chart at the
paper scale `Delta`. -/
lemma proposition63_interval_transported_ad
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    (data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity)
    (hDelta : 0 < Delta)
    (hDeltaSmall : Delta ≤ 1 / 200)
    (hdeltaDelta : delta ≤ Delta ^ 2)
    (hdeltaRatio : delta / Delta ≤ 1 / 4)
    (hrhoDelta : rho = Delta)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ data.retainedIntervals) :
    PureWZ2PaperADSet1
      (scalarProjection (data.intervalTransportedNormal interval hinterval)
        (wz1AnchoredUnitRescalingMap data.parentChartTube rho hrho ''
          proposition63LocalSourceSet data interval hinterval))
      Delta (1 - sigma)
      (10 * ((10 * Kakeya.realRpowENN delta (-localLoss)) *
        ENNReal.ofReal 25000)) := by
  let certificate := Classical.choice
    (proposition63_interval_local_ad data hDelta hDeltaSmall
      hdeltaDelta hdeltaRatio hrhoDelta interval hinterval)
  have hnormalPos : 0 <
      ‖data.intervalTransportedRaw interval hinterval‖ :=
    hDelta.trans_le certificate.transported_raw_lower
  have hscale :
      (1 / ‖data.intervalTransportedRaw interval hinterval‖) *
          Delta ^ 2 ≤ Delta := by
    have hmul : Delta ^ 2 ≤
        ‖data.intervalTransportedRaw interval hinterval‖ * Delta := by
      nlinarith [certificate.transported_raw_lower]
    calc
      (1 / ‖data.intervalTransportedRaw interval hinterval‖) *
          Delta ^ 2 = Delta ^ 2 /
            ‖data.intervalTransportedRaw interval hinterval‖ := by ring
      _ ≤ Delta := (div_le_iff₀ hnormalPos).2
        (by simpa [mul_comm] using hmul)
  exact paper_transport_and_normalize_ad hrho data.parentChartTube
    certificate.source_ad hnormalPos hscale

private lemma paper_horizontalize_slab
    {E : Set Point3} {normal : Point3} {z scale alpha : ℝ} {C : ENNReal}
    (hscale : 0 < scale)
    (hscaleOne : scale ≤ 1)
    (hnorm : ‖normal‖ = 1)
    (hn0 : 1 / 3 ≤ |normal 0|)
    (hn2 : |normal 2| ≤ 1 / 10)
    (hslab : ∀ point ∈ E,
      point 2 ∈ Set.Icc (z - scale) (z + scale))
    (hAD : PureWZ2PaperADSet1
      (scalarProjection normal E) scale alpha C) :
    PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (normal 1 / normal 0)) E)
      scale alpha (800 * C) := by
  let a : ℝ := 1 / normal 0
  let b : ℝ := -normal 2 * z / normal 0
  let source := scalarProjection normal E
  let affineSet := (fun value : ℝ => a * value + b) '' source
  let target := scalarProjection
    (globalGrainDirection (normal 1 / normal 0)) E
  have hnormalZeroUpper : |normal 0| ≤ 1 :=
    (PiLp.norm_apply_le normal 0).trans_eq hnorm
  have hnormalZeroPos : 0 < |normal 0| := by linarith
  have haAbs : |a| = 1 / |normal 0| := by
    simp [a, abs_div]
  have haLower : 1 / 4 ≤ |a| := by
    rw [haAbs]
    have : (1 : ℝ) ≤ 1 / |normal 0| := by
      exact (le_div_iff₀ hnormalZeroPos).2 (by simpa using hnormalZeroUpper)
    linarith
  have haUpper : |a| ≤ 4 := by
    rw [haAbs]
    exact (div_le_iff₀ hnormalZeroPos).2 (by nlinarith)
  have haffine : PureWZ2PaperADSet1 affineSet scale alpha (100 * C) := by
    simpa only [affineSet, source] using
      (Kakeya.Assouad.PureWZ2PaperADSet1.affine
        (S := scalarProjection normal E) (delta := scale)
        (alpha := alpha) (C := C) hAD a b haLower haUpper hscaleOne)
  have htransfer : PureWZ2PaperADSet1 target scale alpha
      (8 * (100 * C)) := by
    apply Kakeya.Assouad.PureWZ2PaperADSet1.transfer_direction haffine
    rintro value ⟨point, hpoint, rfl⟩
    let u : ℝ := inner ℝ point normal
    let reference : ℝ := a * u + b
    have hu : u ∈ source := ⟨point, hpoint, rfl⟩
    have hreference : reference ∈ affineSet := ⟨u, hu, rfl⟩
    refine ⟨reference, hreference, ?_⟩
    have hn0Ne : normal 0 ≠ 0 := by
      exact abs_ne_zero.mp hnormalZeroPos.ne'
    have hsum : inner ℝ point normal =
        normal 0 * point 0 + normal 1 * point 1 + normal 2 * point 2 := by
      rw [PiLp.inner_apply]
      simp [Fin.sum_univ_succ, mul_comm]
      ring
    have hdir : inner ℝ point
        (globalGrainDirection (normal 1 / normal 0)) =
          point 0 + (normal 1 / normal 0) * point 1 := by
      rw [PiLp.inner_apply]
      simp [Fin.sum_univ_succ, globalGrainDirection]
    have hreferenceFormula : reference =
        point 0 + (normal 1 / normal 0) * point 1 +
          (normal 2 / normal 0) * (point 2 - z) := by
      dsimp only [reference, a, b, u]
      rw [hsum]
      field_simp [hn0Ne]
      ring
    change |inner ℝ point
      (globalGrainDirection (normal 1 / normal 0)) - reference| ≤ scale
    rw [hdir, hreferenceFormula]
    have hratio : |normal 2| / |normal 0| ≤ 3 / 10 := by
      calc
        |normal 2| / |normal 0| ≤ (1 / 10 : ℝ) / |normal 0| := by gcongr
        _ ≤ (1 / 10 : ℝ) / (1 / 3 : ℝ) := by gcongr
        _ = 3 / 10 := by norm_num
    have hheight : |point 2 - z| ≤ scale := by
      exact abs_le.mpr ⟨by linarith [(hslab point hpoint).1],
        by linarith [(hslab point hpoint).2]⟩
    rw [show point 0 + normal 1 / normal 0 * point 1 -
        (point 0 + normal 1 / normal 0 * point 1 +
          normal 2 / normal 0 * (point 2 - z)) =
        -(normal 2 / normal 0 * (point 2 - z)) by ring,
      abs_neg, abs_mul, abs_div]
    calc
      |normal 2| / |normal 0| * |point 2 - z| ≤
          (3 / 10 : ℝ) * scale := by gcongr
      _ ≤ scale := by nlinarith
  have hconstant : (8 : ENNReal) * (100 * C) = 800 * C := by ring
  simpa only [target, hconstant] using htransfer

private lemma paper_horizontalize_slab_second
    {E : Set Point3} {normal : Point3} {z scale alpha : ℝ} {C : ENNReal}
    (hscale : 0 < scale)
    (hscaleOne : scale ≤ 1)
    (hnorm : ‖normal‖ = 1)
    (hn1 : 1 / 3 ≤ |normal 1|)
    (hn2 : |normal 2| ≤ 1 / 10)
    (hslab : ∀ point ∈ E,
      point 2 ∈ Set.Icc (z - scale) (z + scale))
    (hAD : PureWZ2PaperADSet1
      (scalarProjection normal E) scale alpha C) :
    PureWZ2PaperADSet1
      (scalarProjection (point3 (normal 0 / normal 1) 1 0) E)
      scale alpha (800 * C) := by
  let a : ℝ := 1 / normal 1
  let b : ℝ := -normal 2 * z / normal 1
  let source := scalarProjection normal E
  let affineSet := (fun value : ℝ => a * value + b) '' source
  let target := scalarProjection (point3 (normal 0 / normal 1) 1 0) E
  have hnormalOneUpper : |normal 1| ≤ 1 :=
    (PiLp.norm_apply_le normal 1).trans_eq hnorm
  have hnormalOnePos : 0 < |normal 1| := by linarith
  have haAbs : |a| = 1 / |normal 1| := by
    simp [a, abs_div]
  have haLower : 1 / 4 ≤ |a| := by
    rw [haAbs]
    have : (1 : ℝ) ≤ 1 / |normal 1| := by
      exact (le_div_iff₀ hnormalOnePos).2 (by simpa using hnormalOneUpper)
    linarith
  have haUpper : |a| ≤ 4 := by
    rw [haAbs]
    exact (div_le_iff₀ hnormalOnePos).2 (by nlinarith)
  have haffine : PureWZ2PaperADSet1 affineSet scale alpha (100 * C) := by
    simpa only [affineSet, source] using
      (Kakeya.Assouad.PureWZ2PaperADSet1.affine
        (S := scalarProjection normal E) (delta := scale)
        (alpha := alpha) (C := C) hAD a b haLower haUpper hscaleOne)
  have htransfer : PureWZ2PaperADSet1 target scale alpha
      (8 * (100 * C)) := by
    apply Kakeya.Assouad.PureWZ2PaperADSet1.transfer_direction haffine
    rintro value ⟨point, hpoint, rfl⟩
    let u : ℝ := inner ℝ point normal
    let reference : ℝ := a * u + b
    have hu : u ∈ source := ⟨point, hpoint, rfl⟩
    have hreference : reference ∈ affineSet := ⟨u, hu, rfl⟩
    refine ⟨reference, hreference, ?_⟩
    have hn1Ne : normal 1 ≠ 0 := by
      exact abs_ne_zero.mp hnormalOnePos.ne'
    have hsum : inner ℝ point normal =
        normal 0 * point 0 + normal 1 * point 1 + normal 2 * point 2 := by
      rw [PiLp.inner_apply]
      simp [Fin.sum_univ_succ, mul_comm]
      ring
    have hdir : inner ℝ point (point3 (normal 0 / normal 1) 1 0) =
        (normal 0 / normal 1) * point 0 + point 1 := by
      rw [PiLp.inner_apply]
      simp [Fin.sum_univ_succ, point3]
    have hreferenceFormula : reference =
        (normal 0 / normal 1) * point 0 + point 1 +
          (normal 2 / normal 1) * (point 2 - z) := by
      dsimp only [reference, a, b, u]
      rw [hsum]
      field_simp [hn1Ne]
      ring
    change |inner ℝ point (point3 (normal 0 / normal 1) 1 0) - reference| ≤ scale
    rw [hdir, hreferenceFormula]
    have hratio : |normal 2| / |normal 1| ≤ 3 / 10 := by
      calc
        |normal 2| / |normal 1| ≤ (1 / 10 : ℝ) / |normal 1| := by gcongr
        _ ≤ (1 / 10 : ℝ) / (1 / 3 : ℝ) := by gcongr
        _ = 3 / 10 := by norm_num
    have hheight : |point 2 - z| ≤ scale := by
      exact abs_le.mpr ⟨by linarith [(hslab point hpoint).1],
        by linarith [(hslab point hpoint).2]⟩
    rw [show normal 0 / normal 1 * point 0 + point 1 -
        (normal 0 / normal 1 * point 0 + point 1 +
          normal 2 / normal 1 * (point 2 - z)) =
        -(normal 2 / normal 1 * (point 2 - z)) by ring,
      abs_neg, abs_mul, abs_div]
    calc
      |normal 2| / |normal 1| * |point 2 - z| ≤
          (3 / 10 : ℝ) * scale := by gcongr
      _ ≤ scale := by nlinarith
  have hconstant : (8 : ENNReal) * (100 * C) = 800 * C := by ring
  simpa only [target, hconstant] using htransfer

namespace Proposition63ChartSelectionData

/-- The chart-horizontal projection of one anchored source slab has the AD
bound supplied by the local estimate at its genuine anchor point. -/
lemma anchoredSourceSlab_chart_ad
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ selection.intervals) :
    PureWZ2PaperADSet1
      (scalarProjection
        (selection.chartLabel.chart.direction
          (slopeAtNormal selection.chartLabel.chart
            (data.intervalTransportedNormal interval
              (selection.intervals_subset hinterval))))
        (selection.anchoredSourceSlab interval))
      Delta (1 - sigma)
      (800 *
        (10 * ((10 * Kakeya.realRpowENN delta (-localLoss)) *
          ENNReal.ofReal 25000))) := by
  let hretained := selection.intervals_subset hinterval
  let normal := data.intervalTransportedNormal interval hretained
  let sourceSet := proposition63LocalSourceSet data interval hretained
  let C : ENNReal :=
    10 * ((10 * Kakeya.realRpowENN delta (-localLoss)) *
      ENNReal.ofReal 25000)
  let certificate := Classical.choice
    (proposition63_interval_local_ad data hDelta hDeltaSmall
      hdeltaDelta hdeltaRatio hrhoDelta interval hretained)
  have hpaper := proposition63_interval_transported_ad data hDelta hDeltaSmall
    hdeltaDelta hdeltaRatio hrhoDelta interval hretained
  have hsourceSubset : selection.sourceSlab interval ⊆ sourceSet := by
    intro point hpoint
    refine ⟨?_, selection.sourceSlab_subset_localBall hrhoDelta
      interval hinterval hpoint⟩
    exact paper_subshading_union_subset selection.source_sub_commonSlice
      hpoint.1
  have himageSubset : selection.anchoredSourceSlab interval ⊆
      wz1AnchoredUnitRescalingMap data.parentChartTube rho hrho '' sourceSet := by
    rintro point ⟨sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, hsourceSubset hsourcePoint, rfl⟩
  have hpaperSlab : PureWZ2PaperADSet1
      (scalarProjection normal (selection.anchoredSourceSlab interval))
      Delta (1 - sigma) C := by
    have hpaper' : PureWZ2PaperADSet1
        (scalarProjection normal
          (wz1AnchoredUnitRescalingMap data.parentChartTube rho hrho ''
            sourceSet)) Delta (1 - sigma) C := by
      simpa only [normal, sourceSet, C] using hpaper
    apply hpaper'.mono_set
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point, himageSubset hpoint, rfl⟩
  have hslab := selection.anchoredSourceSlab_height interval
  cases hchart : selection.chartLabel with
  | first =>
      have hresult := paper_horizontalize_slab
          hDelta (hDeltaSmall.trans (by norm_num))
          certificate.transported_unit
          (by simpa [normal, hchart, Proposition63ChartLabel.chart] using
            selection.interval_chart_bound hrhoDelta interval hinterval)
          (by simpa [normal] using certificate.transported_vertical)
          hslab hpaperSlab
      change PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection
          ((data.intervalTransportedNormal interval hretained) 1 /
            (data.intervalTransportedNormal interval hretained) 0))
          (selection.anchoredSourceSlab interval))
        Delta (1 - sigma) _
      simpa only [normal, C] using hresult
  | second =>
      have hresult := paper_horizontalize_slab_second
          hDelta (hDeltaSmall.trans (by norm_num))
          certificate.transported_unit
          (by simpa [normal, hchart, Proposition63ChartLabel.chart] using
            selection.interval_chart_bound hrhoDelta interval hinterval)
          (by simpa [normal] using certificate.transported_vertical)
          hslab hpaperSlab
      change PureWZ2PaperADSet1
        (scalarProjection (point3
          ((data.intervalTransportedNormal interval hretained) 0 /
            (data.intervalTransportedNormal interval hretained) 1) 1 0)
          (selection.anchoredSourceSlab interval))
        Delta (1 - sigma) _
      simpa only [normal, C] using hresult

/-- The longitudinal compression in the frozen literal map fixes every
horizontal projection, so the slab AD estimate passes unchanged from the
anchored chart to the actual literal image. -/
lemma literalSourceSlab_chart_ad
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ selection.intervals) :
    PureWZ2PaperADSet1
      (scalarProjection
        (selection.chartLabel.chart.direction
          (slopeAtNormal selection.chartLabel.chart
            (data.intervalTransportedNormal interval
              (selection.intervals_subset hinterval))))
        (selection.literalSourceSlab interval))
      Delta (1 - sigma)
      (800 *
        (10 * ((10 * Kakeya.realRpowENN delta (-localLoss)) *
          ENNReal.ofReal 25000))) := by
  rw [selection.horizontal_projection_literalSourceSlab_eq_anchoredSourceSlab
    interval selection.chartLabel.chart
    (slopeAtNormal selection.chartLabel.chart
      (data.intervalTransportedNormal interval
        (selection.intervals_subset hinterval)))]
  exact selection.anchoredSourceSlab_chart_ad hrhoDelta interval hinterval

/-- Rephrase the literal-slab estimate using the single Lipschitz extension
chosen for all retained intervals. -/
lemma literalSourceSlab_slope_ad
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (slopes : Proposition63SlopeData selection)
    (hrhoDelta : rho = Delta)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ selection.intervals) :
    PureWZ2PaperADSet1
      (scalarProjection
        (selection.chartLabel.chart.direction
          (slopes.slope (selection.intervalBase interval)))
        (selection.literalSourceSlab interval))
      Delta (1 - sigma)
      (800 *
        (10 * ((10 * Kakeya.realRpowENN delta (-localLoss)) *
          ENNReal.ofReal 25000))) := by
  rw [slopes.agrees interval hinterval]
  exact selection.literalSourceSlab_chart_ad hrhoDelta interval hinterval

end Proposition63ChartSelectionData

end Kakeya.Assouad.PureWZ2

end
