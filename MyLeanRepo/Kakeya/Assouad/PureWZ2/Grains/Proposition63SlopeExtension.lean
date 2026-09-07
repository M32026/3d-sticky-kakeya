import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ChartSelection

/-!
# Discrete slope and Lipschitz extension for Proposition 6.3

The selected interval bases are the paper heights `z ∈ mathcal Z`.  At each
base we use the genuine shaded point on `T₀`, take the ratio of the two
horizontal coordinates of its transported normal in the selected chart, and
then extend that ratio from the finite height set to all real heights.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Metric Set

attribute [local instance] Classical.propDecidable

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

/-- The paper height attached to one retained axial interval.  The frozen
literal map has longitudinal factor `1/100`, so an interval of literal width
`Delta/100` corresponds to a paper-height interval of width `Delta`. -/
def intervalBase
    (_selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta)) : ℝ :=
  (interval.1 : ℝ) * Delta

/-- The finite paper height set retained after selecting one chart. -/
def heightBases
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) : Finset ℝ :=
  selection.intervals.image selection.intervalBase

/-- Ambient version of the source plane map.  Only its values on the
common-slice union are used below. -/
def sourcePlaneMap
    (_selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) (point : Point3) : Point3 :=
  if hpoint : point ∈ data.commonSlice.shading.union then
    data.localGrains.planeMap ⟨point, hpoint⟩ else 0

/-- Genuine source anchor points indexed by the selected intervals. -/
def anchorSet
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) : Set Point3 :=
  {point | ∃ interval, ∃ hinterval : interval ∈ selection.intervals,
    point = data.anchorPoint interval
      (selection.intervals_subset hinterval)}

lemma anchorSet_subset_commonSlice
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    selection.anchorSet ⊆ data.commonSlice.shading.union := by
  rintro point ⟨interval, hinterval, rfl⟩
  exact ⟨data.commonSlice.distinguished,
    data.anchorPoint_mem_commonSlice interval
      (selection.intervals_subset hinterval)⟩

lemma sourcePlaneMap_lipschitzOn
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    LipschitzOnWith (Real.toNNReal coefficient) selection.sourcePlaneMap
      selection.anchorSet := by
  apply LipschitzOnWith.of_dist_le_mul
  intro first hfirst second hsecond
  have hfirstUnion := selection.anchorSet_subset_commonSlice hfirst
  have hsecondUnion := selection.anchorSet_subset_commonSlice hsecond
  have hbound := data.localGrains.planeMap_lipschitz.dist_le_mul
    ⟨first, hfirstUnion⟩ ⟨second, hsecondUnion⟩
  simpa [sourcePlaneMap, hfirstUnion, hsecondUnion, Subtype.dist_eq] using hbound

lemma sourcePlaneMap_interval_eq
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ selection.intervals) :
    selection.sourcePlaneMap
        (data.anchorPoint interval (selection.intervals_subset hinterval)) =
      data.intervalNormal interval (selection.intervals_subset hinterval) := by
  have hpoint : data.anchorPoint interval
      (selection.intervals_subset hinterval) ∈
        data.commonSlice.shading.union :=
    selection.anchorSet_subset_commonSlice ⟨interval, hinterval, rfl⟩
  simp [sourcePlaneMap, hpoint,
    Proposition63CommonSliceRescaledData.intervalNormal,
    Proposition63CommonSliceRescaledData.intervalPoint]

lemma transportedNormal_interval_eq
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ selection.intervals) :
    transportedNormal data.parentChartTube rho hrho selection.sourcePlaneMap
        (data.anchorPoint interval (selection.intervals_subset hinterval)) =
      data.intervalTransportedNormal interval
        (selection.intervals_subset hinterval) := by
  simp only [transportedNormal,
    Proposition63CommonSliceRescaledData.intervalTransportedNormal,
    Proposition63CommonSliceRescaledData.intervalTransportedRaw]
  rw [selection.sourcePlaneMap_interval_eq interval hinterval]

lemma anchorSet_plane_unit
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    ∀ point ∈ selection.anchorSet, ‖selection.sourcePlaneMap point‖ = 1 := by
  rintro point ⟨interval, hinterval, rfl⟩
  rw [selection.sourcePlaneMap_interval_eq interval hinterval]
  exact data.localGrains.planeMap_unit _

lemma anchorSet_transported_raw_strong
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    rho = Delta →
    ∀ point ∈ selection.anchorSet,
      50 * rho ≤ ‖wz1AnchoredUnitRescalingNormalLinear
        data.parentChartTube rho (selection.sourcePlaneMap point)‖ := by
  intro hrhoDelta point
  rintro ⟨interval, hinterval, rfl⟩
  let hretained := selection.intervals_subset hinterval
  let certificate := Classical.choice
    (proposition63_interval_local_ad data hDelta hDeltaSmall
      hdeltaDelta hdeltaRatio hrhoDelta interval hretained)
  simpa [hrhoDelta,
    Proposition63CommonSliceRescaledData.intervalTransportedRaw,
    selection.sourcePlaneMap_interval_eq interval hinterval] using
      certificate.transported_raw_strong

lemma anchorSet_chart_bound
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    rho = Delta →
    ∀ point ∈ selection.anchorSet,
      let normal := transportedNormal data.parentChartTube rho hrho
        selection.sourcePlaneMap point
      match selection.chartLabel.chart with
      | WZ1HorizontalChart.first => 1 / 3 ≤ |normal 0|
      | WZ1HorizontalChart.second => 1 / 3 ≤ |normal 1| := by
  intro hrhoDelta point
  rintro ⟨interval, hinterval, rfl⟩
  rw [selection.transportedNormal_interval_eq interval hinterval]
  exact selection.interval_chart_bound hrhoDelta interval hinterval

lemma anchorPoint_paper_height_error
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ selection.intervals) :
    |paperTubeHeight data.anchorTube
        (data.anchorPoint interval (selection.intervals_subset hinterval)) -
      selection.intervalBase interval| ≤ 5 * Delta := by
  let hretained := selection.intervals_subset hinterval
  let point := data.anchorPoint interval hretained
  have hpointUnion : point ∈ input.selectedFiber.union :=
    ⟨data.commonSlice.distinguished, (data.anchorPoint_mem interval hretained).1⟩
  have hcomparison := proposition63_paper_height_parent_error
    data hDelta hpointUnion
  have hslab := (data.anchorPoint_mem interval hretained).2
  change proposition63AxialCoordinate (coarse.tube input.parent) hrho point ∈
      Set.Ico ((interval.1 : ℝ) * proposition63LiteralSliceWidth Delta)
        (((interval.1 : ℝ) + 1) * proposition63LiteralSliceWidth Delta) at hslab
  have hscaledLower : selection.intervalBase interval ≤
      100 * proposition63AxialCoordinate
        (coarse.tube input.parent) hrho point := by
    calc
      selection.intervalBase interval =
          100 * ((interval.1 : ℝ) *
            proposition63LiteralSliceWidth Delta) := by
        unfold intervalBase proposition63LiteralSliceWidth
        ring
      _ ≤ 100 * proposition63AxialCoordinate
          (coarse.tube input.parent) hrho point := by
        gcongr
        exact hslab.1
  have hscaledUpper :
      100 * proposition63AxialCoordinate
          (coarse.tube input.parent) hrho point ≤
        selection.intervalBase interval + Delta := by
    calc
      100 * proposition63AxialCoordinate
          (coarse.tube input.parent) hrho point ≤
          100 * (((interval.1 : ℝ) + 1) *
            proposition63LiteralSliceWidth Delta) := by
        gcongr
        exact hslab.2.le
      _ = selection.intervalBase interval + Delta := by
        unfold intervalBase proposition63LiteralSliceWidth
        ring
  have hcomparison' :
      |paperTubeHeight data.anchorTube point -
        100 * proposition63AxialCoordinate
          (coarse.tube input.parent) hrho point| ≤ 4 * Delta :=
    hcomparison.trans_eq (by rw [hrhoDelta])
  rw [abs_le] at hcomparison' ⊢
  constructor <;> linarith

lemma intervalBase_separated
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {first second : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta)}
    (hne : first ≠ second) :
    Delta ≤ |selection.intervalBase first - selection.intervalBase second| := by
  have hvalueNe : first.1 ≠ second.1 := fun h => hne (Subtype.ext h)
  have hsubNe : first.1 - second.1 ≠ 0 := sub_ne_zero.mpr hvalueNe
  have honeInt : (1 : ℤ) ≤ |first.1 - second.1| := Int.one_le_abs hsubNe
  have honeReal : (1 : ℝ) ≤ |((first.1 - second.1 : ℤ) : ℝ)| := by
    exact_mod_cast honeInt
  rw [show selection.intervalBase first - selection.intervalBase second =
      ((first.1 - second.1 : ℤ) : ℝ) * Delta by
        simp only [intervalBase, Int.cast_sub]
        ring, abs_mul, abs_of_pos hDelta]
  nlinarith

lemma anchorPoint_dist_le_intervalBase
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta)
    (first second : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hfirst : first ∈ selection.intervals)
    (hsecond : second ∈ selection.intervals) :
    dist
        (data.anchorPoint first (selection.intervals_subset hfirst))
        (data.anchorPoint second (selection.intervals_subset hsecond)) ≤
      35 * |selection.intervalBase first - selection.intervalBase second| := by
  by_cases heq : first = second
  · subst second
    simp
  let hfirstRetained := selection.intervals_subset hfirst
  let hsecondRetained := selection.intervals_subset hsecond
  let firstPoint := data.anchorPoint first hfirstRetained
  let secondPoint := data.anchorPoint second hsecondRetained
  have hfirstBody := data.commonSlice.shading.subset_body
    data.commonSlice.distinguished
    (data.anchorPoint_mem_commonSlice first hfirstRetained)
  change firstPoint ∈ wz1PaperTubeCarrier
    (input.fiberFamily.family.tube data.commonSlice.distinguished) at hfirstBody
  have hfirstCarrier : firstPoint ∈ wz1PaperTubeCarrier data.anchorTube := by
    exact hfirstBody
  have hsecondBody := data.commonSlice.shading.subset_body
    data.commonSlice.distinguished
    (data.anchorPoint_mem_commonSlice second hsecondRetained)
  change secondPoint ∈ wz1PaperTubeCarrier
    (input.fiberFamily.family.tube data.commonSlice.distinguished) at hsecondBody
  have hsecondCarrier : secondPoint ∈ wz1PaperTubeCarrier data.anchorTube := by
    exact hsecondBody
  have hline : WZ1PaperTubeInLineClass data.anchorTube := by
    exact cover.fine_line_class.subfamily input.fiberFamily
      data.commonSlice.distinguished
  have htube := same_paper_tube_dist_le_paper_height_add_twenty_four_delta
    hdelta data.anchorTube hline hfirstCarrier hsecondCarrier
  have hfirstError := selection.anchorPoint_paper_height_error
    hrhoDelta first hfirst
  have hsecondError := selection.anchorPoint_paper_height_error
    hrhoDelta second hsecond
  have hheight :
      |paperTubeHeight data.anchorTube firstPoint -
          paperTubeHeight data.anchorTube secondPoint| ≤
        |selection.intervalBase first - selection.intervalBase second| +
          10 * Delta := by
    calc
      |paperTubeHeight data.anchorTube firstPoint -
          paperTubeHeight data.anchorTube secondPoint| =
          |(paperTubeHeight data.anchorTube firstPoint -
              selection.intervalBase first) +
            (selection.intervalBase first - selection.intervalBase second) +
            (selection.intervalBase second -
              paperTubeHeight data.anchorTube secondPoint)| := by
        congr 1
        ring
      _ ≤ |paperTubeHeight data.anchorTube firstPoint -
              selection.intervalBase first| +
            |selection.intervalBase first - selection.intervalBase second| +
            |selection.intervalBase second -
              paperTubeHeight data.anchorTube secondPoint| := by
        calc
          _ ≤ |(paperTubeHeight data.anchorTube firstPoint -
                selection.intervalBase first) +
              (selection.intervalBase first - selection.intervalBase second)| +
              |selection.intervalBase second -
                paperTubeHeight data.anchorTube secondPoint| := abs_add_le _ _
          _ ≤ (|paperTubeHeight data.anchorTube firstPoint -
                selection.intervalBase first| +
              |selection.intervalBase first - selection.intervalBase second|) +
              |selection.intervalBase second -
                paperTubeHeight data.anchorTube secondPoint| := by
            gcongr
            exact abs_add_le _ _
      _ ≤ 5 * Delta +
            |selection.intervalBase first - selection.intervalBase second| +
            5 * Delta := by
        gcongr
        simpa [abs_sub_comm] using hsecondError
      _ = |selection.intervalBase first - selection.intervalBase second| +
            10 * Delta := by ring
  have hdeltaDeltaLinear : delta ≤ Delta := by
    calc
      delta ≤ Delta ^ 2 := hdeltaDelta
      _ ≤ Delta := by nlinarith [hDeltaSmall, hDelta]
  have hseparated := selection.intervalBase_separated heq
  calc
    dist firstPoint secondPoint ≤
        |paperTubeHeight data.anchorTube firstPoint -
          paperTubeHeight data.anchorTube secondPoint| + 24 * delta := htube
    _ ≤ (|selection.intervalBase first - selection.intervalBase second| +
          10 * Delta) + 24 * delta := by gcongr
    _ ≤ 35 * |selection.intervalBase first -
          selection.intervalBase second| := by
      nlinarith [abs_nonneg
        (selection.intervalBase first - selection.intervalBase second)]

lemma interval_slope_pair_bound
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta)
    (first second : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hfirst : first ∈ selection.intervals)
    (hsecond : second ∈ selection.intervals) :
    |slopeAtNormal selection.chartLabel.chart
        (data.intervalTransportedNormal first
          (selection.intervals_subset hfirst)) -
      slopeAtNormal selection.chartLabel.chart
        (data.intervalTransportedNormal second
          (selection.intervals_subset hsecond))| ≤
      (2520 * (Real.toNNReal coefficient : ℝ)) *
        |selection.intervalBase first - selection.intervalBase second| := by
  have hfirstAnchor : data.anchorPoint first
      (selection.intervals_subset hfirst) ∈ selection.anchorSet :=
    ⟨first, hfirst, rfl⟩
  have hsecondAnchor : data.anchorPoint second
      (selection.intervals_subset hsecond) ∈ selection.anchorSet :=
    ⟨second, hsecond, rfl⟩
  have hratio := slopeAtNormal_transported_pair_bound hrho
    data.parentChartTube selection.chartLabel.chart selection.sourcePlaneMap
    (Real.toNNReal coefficient) selection.sourcePlaneMap_lipschitzOn
    selection.anchorSet_plane_unit
    (selection.anchorSet_transported_raw_strong hrhoDelta)
    (selection.anchorSet_chart_bound hrhoDelta)
    (data.anchorPoint first (selection.intervals_subset hfirst)) hfirstAnchor
    (data.anchorPoint second (selection.intervals_subset hsecond)) hsecondAnchor
  rw [selection.transportedNormal_interval_eq first hfirst,
    selection.transportedNormal_interval_eq second hsecond] at hratio
  calc
    _ ≤ (72 * (Real.toNNReal coefficient : ℝ)) *
        dist
          (data.anchorPoint first (selection.intervals_subset hfirst))
          (data.anchorPoint second (selection.intervals_subset hsecond)) :=
      hratio
    _ ≤ (72 * (Real.toNNReal coefficient : ℝ)) *
        (35 * |selection.intervalBase first -
          selection.intervalBase second|) := by
      gcongr
      exact selection.anchorPoint_dist_le_intervalBase hrhoDelta
        first second hfirst hsecond
    _ = (2520 * (Real.toNNReal coefficient : ℝ)) *
        |selection.intervalBase first - selection.intervalBase second| := by
      ring

lemma intervalBase_injective
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) :
    Function.Injective selection.intervalBase := by
  intro first second heq
  have hDeltaNe : Delta ≠ 0 := hDelta.ne'
  have hcast : (first.1 : ℝ) = (second.1 : ℝ) := by
    apply mul_right_cancel₀ hDeltaNe
    exact heq
  have hvalue : first.1 = second.1 := by exact_mod_cast hcast
  exact Subtype.ext hvalue

/-- Recover the unique selected interval associated to a retained paper
height. -/
def intervalAtHeight
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (height : ℝ) (hheight : height ∈ selection.heightBases) :
    commonSliceIntervalType (proposition63LiteralSliceWidth Delta) :=
  Classical.choose (Finset.mem_image.mp hheight)

lemma intervalAtHeight_mem
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (height : ℝ) (hheight : height ∈ selection.heightBases) :
    selection.intervalAtHeight height hheight ∈ selection.intervals :=
  (Classical.choose_spec (Finset.mem_image.mp hheight)).1

lemma intervalBase_intervalAtHeight
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (height : ℝ) (hheight : height ∈ selection.heightBases) :
    selection.intervalBase (selection.intervalAtHeight height hheight) = height :=
  (Classical.choose_spec (Finset.mem_image.mp hheight)).2

/-- The transported normal-ratio slope on the selected finite height set,
extended arbitrarily by zero before applying the Lipschitz extension theorem. -/
def discreteSlope
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) (height : ℝ) : ℝ :=
  if hheight : height ∈ selection.heightBases then
    let interval := selection.intervalAtHeight height hheight
    let hinterval := selection.intervalAtHeight_mem height hheight
    slopeAtNormal selection.chartLabel.chart
      (data.intervalTransportedNormal interval
        (selection.intervals_subset hinterval))
  else 0

lemma discreteSlope_intervalBase
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ selection.intervals) :
    selection.discreteSlope (selection.intervalBase interval) =
      slopeAtNormal selection.chartLabel.chart
        (data.intervalTransportedNormal interval
          (selection.intervals_subset hinterval)) := by
  have hheight : selection.intervalBase interval ∈ selection.heightBases :=
    Finset.mem_image.mpr ⟨interval, hinterval, rfl⟩
  simp only [discreteSlope, hheight, dif_pos]
  have hsame : selection.intervalAtHeight
      (selection.intervalBase interval) hheight = interval :=
    selection.intervalBase_injective
      (selection.intervalBase_intervalAtHeight _ hheight)
  congr 2

lemma discreteSlope_lipschitzOn
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta) :
    LipschitzOnWith (2520 * Real.toNNReal coefficient)
      selection.discreteSlope selection.heightBases := by
  apply LipschitzOnWith.of_dist_le_mul
  intro first hfirst second hsecond
  let firstInterval := selection.intervalAtHeight first hfirst
  let secondInterval := selection.intervalAtHeight second hsecond
  have hfirstInterval := selection.intervalAtHeight_mem first hfirst
  have hsecondInterval := selection.intervalAtHeight_mem second hsecond
  have hpair := selection.interval_slope_pair_bound hrhoDelta
    firstInterval secondInterval hfirstInterval hsecondInterval
  have hfirstBase := selection.intervalBase_intervalAtHeight first hfirst
  have hsecondBase := selection.intervalBase_intervalAtHeight second hsecond
  rw [hfirstBase, hsecondBase] at hpair
  rw [Real.dist_eq]
  rw [show selection.discreteSlope first =
      slopeAtNormal selection.chartLabel.chart
        (data.intervalTransportedNormal firstInterval
          (selection.intervals_subset hfirstInterval)) by
        simpa [firstInterval, hfirstBase] using
          selection.discreteSlope_intervalBase firstInterval hfirstInterval]
  rw [show selection.discreteSlope second =
      slopeAtNormal selection.chartLabel.chart
        (data.intervalTransportedNormal secondInterval
          (selection.intervals_subset hsecondInterval)) by
        simpa [secondInterval, hsecondBase] using
          selection.discreteSlope_intervalBase secondInterval hsecondInterval]
  simpa [Real.dist_eq] using hpair

lemma interval_slope_bound
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta))
    (hinterval : interval ∈ selection.intervals) :
    |slopeAtNormal selection.chartLabel.chart
      (data.intervalTransportedNormal interval
        (selection.intervals_subset hinterval))| ≤ 3 := by
  let normal := data.intervalTransportedNormal interval
    (selection.intervals_subset hinterval)
  let certificate := Classical.choice
    (proposition63_interval_local_ad data hDelta hDeltaSmall
      hdeltaDelta hdeltaRatio hrhoDelta interval
      (selection.intervals_subset hinterval))
  have hunit : ‖normal‖ = 1 := certificate.transported_unit
  have hchart := selection.interval_chart_bound hrhoDelta interval hinterval
  cases hlabel : selection.chartLabel with
  | first =>
      have hnumerator : |normal 1| ≤ 1 :=
        (PiLp.norm_apply_le normal 1).trans_eq hunit
      have hdenominator : 1 / 3 ≤ |normal 0| := by
        simpa [normal, Proposition63ChartLabel.chart, hlabel] using hchart
      change |normal 1 / normal 0| ≤ 3
      rw [abs_div]
      calc
        |normal 1| / |normal 0| ≤ 1 / |normal 0| := by gcongr
        _ ≤ 1 / (1 / 3 : ℝ) := by gcongr
        _ = 3 := by norm_num
  | second =>
      have hnumerator : |normal 0| ≤ 1 :=
        (PiLp.norm_apply_le normal 0).trans_eq hunit
      have hdenominator : 1 / 3 ≤ |normal 1| := by
        simpa [normal, Proposition63ChartLabel.chart, hlabel] using hchart
      change |normal 0 / normal 1| ≤ 3
      rw [abs_div]
      calc
        |normal 0| / |normal 1| ≤ 1 / |normal 1| := by gcongr
        _ ≤ 1 / (1 / 3 : ℝ) := by gcongr
        _ = 3 := by norm_num

/-- The paper's global slope after Kirszbraun extension and clipping. -/
structure Proposition63SlopeData
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio) where
  slope : ℝ → ℝ
  lipschitz : LipschitzWith
    (2520 * Real.toNNReal coefficient) slope
  bounded : ∀ height, |slope height| ≤ 3
  agrees : ∀ interval, ∀ hinterval : interval ∈ selection.intervals,
    slope (selection.intervalBase interval) =
      slopeAtNormal selection.chartLabel.chart
        (data.intervalTransportedNormal interval
          (selection.intervals_subset hinterval))

theorem slope_extension
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta) :
    Nonempty (Proposition63SlopeData selection) := by
  let K : NNReal := 2520 * Real.toNNReal coefficient
  let hLip : LipschitzOnWith K selection.discreteSlope
      selection.heightBases := selection.discreteSlope_lipschitzOn hrhoDelta
  let slope := extendAndClip selection.discreteSlope
    (selection.heightBases : Set ℝ) K hLip
  have hslopeLip : LipschitzWith K slope :=
    extendAndClip_lipschitz selection.discreteSlope
      selection.heightBases K hLip
  have hslopeBound : ∀ height, |slope height| ≤ 3 :=
    extendAndClip_bound selection.discreteSlope selection.heightBases K hLip
  refine ⟨{ slope := slope
            lipschitz := hslopeLip
            bounded := hslopeBound
            agrees := ?_ }⟩
  intro interval hinterval
  have hheight : selection.intervalBase interval ∈ selection.heightBases :=
    Finset.mem_image.mpr ⟨interval, hinterval, rfl⟩
  have hrawEq := selection.discreteSlope_intervalBase interval hinterval
  have hrawBound :
      |selection.discreteSlope (selection.intervalBase interval)| ≤ 3 := by
    rw [hrawEq]
    exact selection.interval_slope_bound hrhoDelta interval hinterval
  let extension : ℝ → ℝ := Classical.choose hLip.extend_real
  have hextensionEq :
      selection.discreteSlope (selection.intervalBase interval) =
        extension (selection.intervalBase interval) :=
    (Classical.choose_spec hLip.extend_real).2 hheight
  have hleft : -3 ≤
      selection.discreteSlope (selection.intervalBase interval) :=
    (abs_le.mp hrawBound).1
  have hright :
      selection.discreteSlope (selection.intervalBase interval) ≤ 3 :=
    (abs_le.mp hrawBound).2
  change max (min (extension (selection.intervalBase interval)) 3) (-3) = _
  rw [← hextensionEq, min_eq_left hright, max_eq_left hleft, hrawEq]

end Proposition63ChartSelectionData

end Kakeya.Assouad.PureWZ2

end
