import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63SlabAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalCellDecomposition
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperADGeneralizedThickening
import MyLeanRepo.Kakeya.Assouad.WZ1.GlobalGrainDirectionGeometry

/-!
# Exact horizontal slices for Proposition 6.3

This file starts the passage from the retained source slabs to exact slices
of the public literal-rescaled shading.  The literal map compresses the
longitudinal coordinate by `1 / 100`; consequently the paper slope at public
height `z` is evaluated at `100 * z`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Metric Set

private lemma horizontalChartDirection_norm_le_four
    (chart : WZ1HorizontalChart) {slope : ℝ} (hslope : |slope| ≤ 3) :
    ‖chart.direction slope‖ ≤ 4 := by
  calc
    ‖chart.direction slope‖ =
        ‖chart.isometry (globalGrainDirection slope)‖ := by
      rw [chart.isometry_globalGrainDirection]
    _ = ‖globalGrainDirection slope‖ := chart.isometry.norm_map _
    _ ≤ 4 := globalGrainDirection_norm_le_4 hslope

private lemma horizontalChartProjection_slope_diff
    (chart : WZ1HorizontalChart) (point : Point3) (first second : ℝ) :
    |inner ℝ point (chart.direction first) -
        inner ℝ point (chart.direction second)| ≤
      ‖point‖ * |first - second| := by
  cases chart with
  | first =>
      rw [show inner ℝ point
          (WZ1HorizontalChart.direction WZ1HorizontalChart.first first) -
          inner ℝ point
            (WZ1HorizontalChart.direction WZ1HorizontalChart.first second) =
          point 1 * (first - second) by
        simp [WZ1HorizontalChart.direction, globalGrainDirection,
          PiLp.inner_apply, Fin.sum_univ_succ]
        ring, abs_mul]
      gcongr
      exact PiLp.norm_apply_le point 1
  | second =>
      rw [show inner ℝ point
          (WZ1HorizontalChart.direction WZ1HorizontalChart.second first) -
          inner ℝ point
            (WZ1HorizontalChart.direction WZ1HorizontalChart.second second) =
          point 0 * (first - second) by
        simp [WZ1HorizontalChart.direction, point3, PiLp.inner_apply,
          Fin.sum_univ_succ]
        ring, abs_mul]
      gcongr
      exact PiLp.norm_apply_le point 0

/-- The common paper-AD constant supplied by every retained Proposition 6.3
source slab after horizontalization. -/
def proposition63SlabADConstant (delta localLoss : ℝ) : ENNReal :=
  800 *
    (10 * ((10 * Kakeya.realRpowENN delta (-localLoss)) *
      ENNReal.ofReal 25000))

/-- Projection error from cubical saturation and replacement of the discrete
slab slope by the Lipschitz slope at the exact public height. -/
def proposition63ExactSliceError
    (delta rho Delta coefficient : ℝ) : ℝ :=
  4 * ((2520 * (Real.toNNReal coefficient : ℝ)) *
      (Delta + 100 * (delta / rho))) +
    4 * (delta / rho) * Real.sqrt 3

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

/-- Retained source intervals that can contribute to the exact public slice
at literal height `height`.  The comparison is made in the uncompressed
paper height coordinate. -/
def nearbyIntervals
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (height : ℝ) : Finset
      (commonSliceIntervalType (proposition63LiteralSliceWidth Delta)) :=
  selection.intervals.filter fun interval =>
    |100 * height - selection.intervalBase interval| ≤
      Delta + 100 * (delta / rho)

lemma mem_nearbyIntervals_iff
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (height : ℝ)
    (interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta)) :
    interval ∈ selection.nearbyIntervals height ↔
      interval ∈ selection.intervals ∧
        |100 * height - selection.intervalBase interval| ≤
          Delta + 100 * (delta / rho) := by
  simp [nearbyIntervals]

/-- At a fixed public height only an absolute number of retained intervals
can occur.  This is the formal bounded-cardinality `mathcal Z(z_0)` from the
paper. -/
lemma nearbyIntervals_card_le
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta)
    (height : ℝ) :
    (selection.nearbyIntervals height).card ≤ 203 := by
  have hratioDelta : delta / rho ≤ Delta := by
    rw [hrhoDelta]
    exact (div_le_iff₀ hDelta).2 (by
      simpa [pow_two, mul_comm] using hdeltaDelta)
  let center : ℤ := ⌊(100 * height) / Delta⌋
  let target : Finset ℤ := Finset.Icc (center - 101) (center + 101)
  have hmap : Set.MapsTo
      (fun interval : commonSliceIntervalType
        (proposition63LiteralSliceWidth Delta) => interval.1)
      (selection.nearbyIntervals height : Set _) (target : Set ℤ) := by
    intro interval hinterval
    have hclose := (selection.mem_nearbyIntervals_iff height interval).1 hinterval |>.2
    have hclose' :
        |100 * height - selection.intervalBase interval| ≤ 101 * Delta := by
      calc
        _ ≤ Delta + 100 * (delta / rho) := hclose
        _ ≤ Delta + 100 * Delta := by gcongr
        _ = 101 * Delta := by ring
    have hbounds := abs_le.mp hclose'
    have hcenterLower : (center : ℝ) * Delta ≤ 100 * height := by
      have := Int.floor_le ((100 * height) / Delta)
      dsimp only [center]
      exact (le_div_iff₀ hDelta).1 this
    have hcenterUpper : 100 * height < ((center : ℝ) + 1) * Delta := by
      have := Int.lt_floor_add_one ((100 * height) / Delta)
      dsimp only [center]
      exact (div_lt_iff₀ hDelta).1 this
    have hlowerReal : ((center - 101 : ℤ) : ℝ) ≤ (interval.1 : ℝ) := by
      have hmul : (((center - 101 : ℤ) : ℝ) * Delta) ≤
          (interval.1 : ℝ) * Delta := by
        simp only [Int.cast_sub, Int.cast_ofNat]
        unfold intervalBase at hbounds
        nlinarith [hbounds.2]
      exact le_of_mul_le_mul_right hmul hDelta
    have hupperReal : (interval.1 : ℝ) < ((center + 102 : ℤ) : ℝ) := by
      have hmul : (interval.1 : ℝ) * Delta <
          (((center + 102 : ℤ) : ℝ) * Delta) := by
        simp only [Int.cast_add, Int.cast_ofNat]
        unfold intervalBase at hbounds
        nlinarith [hbounds.1]
      exact lt_of_mul_lt_mul_right hmul hDelta.le
    have hlower : center - 101 ≤ interval.1 := by exact_mod_cast hlowerReal
    have hupperStrict : interval.1 < center + 102 := by exact_mod_cast hupperReal
    have hupper : interval.1 ≤ center + 101 := by omega
    exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩
  have hinjective : Set.InjOn
      (fun interval : commonSliceIntervalType
        (proposition63LiteralSliceWidth Delta) => interval.1)
      (selection.nearbyIntervals height : Set _) := by
    intro first _ second _ heq
    exact Subtype.ext heq
  have hcard := Finset.card_le_card_of_injOn
    (fun interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta) => interval.1)
    hmap hinjective
  have htargetCard : target.card = 203 := by
    have hle : center - 101 ≤ center + 101 + 1 := by omega
    have hcardInt : (target.card : ℤ) =
        (center + 101) + 1 - (center - 101) := by
      exact Int.card_Icc_of_le (center - 101) (center + 101) hle
    have : (target.card : ℤ) = 203 := by
      rw [hcardInt]
      ring
    exact_mod_cast this
  simpa [htargetCard] using hcard

/-- A public point at literal height `height` comes from one retained source
slab.  Its projection in the common chart and the slope at paper height
`100 * height` is uniformly close to the corresponding slab projection. -/
lemma public_horizontal_slice_near_literal_slab
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss)
    (slopes : Proposition63SlopeData selection)
    (height : ℝ) :
    scalarProjection
        (selection.chartLabel.chart.direction
          (slopes.slope (100 * height)))
        (horizontalSlice rescaled.publicShading.union height) ⊆
      {value | ∃ interval ∈ selection.intervals,
        ∃ reference ∈ scalarProjection
          (selection.chartLabel.chart.direction
            (slopes.slope (selection.intervalBase interval)))
          (selection.literalSourceSlab interval),
        |value - reference| ≤
            proposition63ExactSliceError delta rho Delta coefficient ∧
          |100 * height - selection.intervalBase interval| ≤
            Delta + 100 * (delta / rho)} := by
  rintro value ⟨publicPoint, hpublicPoint, rfl⟩
  have hpublicLiteral : publicPoint ∈
      rescaled.literalImage.targetShading.union := by
    rw [← rescaled.publicShading_union_eq]
    exact hpublicPoint.1
  rcases hpublicLiteral with ⟨publicIndex, hpublicIndex⟩
  rw [rescaled.literalImage.target_carrier_eq publicIndex] at hpublicIndex
  rcases hpublicIndex with ⟨literalPoint, hliteralPoint, hgrid⟩
  rcases hliteralPoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  let literalAnchor := wz2PaperLiteralUnitRescalingMap
    (coarse.tube input.parent) hrho sourcePoint
  have hsourceUnion : sourcePoint ∈ selection.sourceShading.union :=
    ⟨input.frozenRescaled.familyData.sourceIndex publicIndex, hsourcePoint⟩
  have hsourceRegion : sourcePoint ∈
      proposition63IntervalRegion (coarse.tube input.parent) hrho
        selection.intervals := hsourcePoint.2
  rcases Set.mem_iUnion₂.mp hsourceRegion with
    ⟨interval, hinterval, hsourceSlab⟩
  have hliteralAnchor : literalAnchor ∈ selection.literalSourceSlab interval :=
    ⟨sourcePoint, ⟨hsourceUnion, hsourceSlab⟩, rfl⟩
  let reference := inner ℝ literalAnchor
    (selection.chartLabel.chart.direction
      (slopes.slope (selection.intervalBase interval)))
  refine ⟨interval, hinterval, reference,
    ⟨literalAnchor, hliteralAnchor, rfl⟩, ?_⟩
  have hliteralTarget : literalAnchor ∈
      rescaled.literalImage.targetShading.carrier publicIndex := by
    rw [rescaled.literalImage.target_carrier_eq publicIndex]
    exact ⟨literalAnchor, ⟨sourcePoint, hsourcePoint, rfl⟩, rfl⟩
  have hliteralNorm : ‖literalAnchor‖ ≤ 3 :=
    paperShadingPoint_norm_le_three
      (shading := rescaled.literalImage.targetShading)
      ⟨publicIndex, hliteralTarget⟩
  have hpointDistance : dist publicPoint literalAnchor ≤
      (delta / rho) * Real.sqrt 3 := by
    exact wz1PaperGridCube_diameter (div_pos hdelta hrho)
      (wz1PaperGridIndex (delta / rho) literalAnchor)
      ((mem_wz1PaperGridCube _ _ publicPoint).2 hgrid)
      ((mem_wz1PaperGridCube _ _ literalAnchor).2 rfl)
  have hheightGrid : |height - literalAnchor 2| < delta / rho := by
    have h := samePaperGridIndex_coord_two_lt
      (div_pos hdelta hrho) hgrid
    rw [hpublicPoint.2] at h
    exact h
  let anchoredPoint :=
    wz1AnchoredUnitRescalingMap data.parentChartTube rho hrho sourcePoint
  have hanchoredPoint : anchoredPoint ∈
      selection.anchoredSourceSlab interval :=
    ⟨sourcePoint, ⟨hsourceUnion, hsourceSlab⟩, rfl⟩
  have hanchoredHeight : anchoredPoint 2 ∈ Set.Icc
      (selection.intervalBase interval - Delta)
      (selection.intervalBase interval + Delta) :=
    selection.anchoredSourceSlab_height interval anchoredPoint hanchoredPoint
  have hliteralHeight :
      literalAnchor 2 = (1 / 100 : ℝ) * anchoredPoint 2 := by
    dsimp only [literalAnchor, anchoredPoint]
    rw [wz2_paper_literal_map_coordinate_relation,
      ← data.parentChartMap_eq_paperMap sourcePoint]
    simp [wz2PaperLongitudinalCompression]
  have hscaledLiteral : anchoredPoint 2 = 100 * literalAnchor 2 := by
    nlinarith [hliteralHeight]
  have hheightClose :
      |100 * height - selection.intervalBase interval| ≤
        Delta + 100 * (delta / rho) := by
    calc
      |100 * height - selection.intervalBase interval| =
          |100 * (height - literalAnchor 2) +
            (anchoredPoint 2 - selection.intervalBase interval)| := by
        rw [hscaledLiteral]
        ring
      _ ≤ |100 * (height - literalAnchor 2)| +
          |anchoredPoint 2 - selection.intervalBase interval| :=
        abs_add_le _ _
      _ ≤ 100 * (delta / rho) + Delta := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hheightGrid.le (by norm_num)
        · exact abs_le.mpr ⟨by linarith [hanchoredHeight.1],
            by linarith [hanchoredHeight.2]⟩
      _ = Delta + 100 * (delta / rho) := by ring
  have hslopeDistance :
      |slopes.slope (100 * height) -
          slopes.slope (selection.intervalBase interval)| ≤
        (2520 * (Real.toNNReal coefficient : ℝ)) *
          (Delta + 100 * (delta / rho)) := by
    have hlip := slopes.lipschitz.dist_le_mul
      (100 * height) (selection.intervalBase interval)
    rw [Real.dist_eq, Real.dist_eq] at hlip
    calc
      _ ≤ (2520 * (Real.toNNReal coefficient : ℝ)) *
          |100 * height - selection.intervalBase interval| := by
        simpa using hlip
      _ ≤ (2520 * (Real.toNNReal coefficient : ℝ)) *
          (Delta + 100 * (delta / rho)) :=
        mul_le_mul_of_nonneg_left hheightClose (by positivity)
  have hdirNorm : ‖selection.chartLabel.chart.direction
      (slopes.slope (100 * height))‖ ≤ 4 :=
    horizontalChartDirection_norm_le_four _ (slopes.bounded _)
  have hspatial :
      |inner ℝ publicPoint
          (selection.chartLabel.chart.direction
            (slopes.slope (100 * height))) -
        inner ℝ literalAnchor
          (selection.chartLabel.chart.direction
            (slopes.slope (100 * height)))| ≤
        4 * (delta / rho) * Real.sqrt 3 := by
    rw [← inner_sub_left]
    calc
      |inner ℝ (publicPoint - literalAnchor)
          (selection.chartLabel.chart.direction
            (slopes.slope (100 * height)))| ≤
          ‖publicPoint - literalAnchor‖ *
            ‖selection.chartLabel.chart.direction
              (slopes.slope (100 * height))‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ((delta / rho) * Real.sqrt 3) * 4 := by
        gcongr
        simpa [dist_eq_norm] using hpointDistance
      _ = 4 * (delta / rho) * Real.sqrt 3 := by ring
  have hslopePart :
      |inner ℝ literalAnchor
          (selection.chartLabel.chart.direction
            (slopes.slope (100 * height))) -
        inner ℝ literalAnchor
          (selection.chartLabel.chart.direction
            (slopes.slope (selection.intervalBase interval)))| ≤
        4 * ((2520 * (Real.toNNReal coefficient : ℝ)) *
          (Delta + 100 * (delta / rho))) := by
    calc
      _ ≤ ‖literalAnchor‖ *
          |slopes.slope (100 * height) -
            slopes.slope (selection.intervalBase interval)| :=
        horizontalChartProjection_slope_diff _ _ _ _
      _ ≤ 3 * ((2520 * (Real.toNNReal coefficient : ℝ)) *
          (Delta + 100 * (delta / rho))) := by gcongr
      _ ≤ 4 * ((2520 * (Real.toNNReal coefficient : ℝ)) *
          (Delta + 100 * (delta / rho))) := by
        apply mul_le_mul_of_nonneg_right (by norm_num)
        exact mul_nonneg (by positivity) (by positivity)
  have htriangle := abs_sub_le
    (inner ℝ publicPoint
      (selection.chartLabel.chart.direction
        (slopes.slope (100 * height))))
    (inner ℝ literalAnchor
      (selection.chartLabel.chart.direction
        (slopes.slope (100 * height))))
    (inner ℝ literalAnchor
      (selection.chartLabel.chart.direction
        (slopes.slope (selection.intervalBase interval))))
  dsimp only [reference]
  exact ⟨htriangle.trans (by
    unfold proposition63ExactSliceError
    linarith), hheightClose⟩

/-- The exact public slice is contained in a fixed-radius thickening of the
finite union of nearby retained slab projections. -/
lemma public_horizontal_slice_subset_nearby_thickening
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss)
    (slopes : Proposition63SlopeData selection)
    (height : ℝ) :
    scalarProjection
        (selection.chartLabel.chart.direction
          (slopes.slope (100 * height)))
        (horizontalSlice rescaled.publicShading.union height) ⊆
      Metric.cthickening
        (proposition63ExactSliceError delta rho Delta coefficient)
        {value | ∃ interval ∈ selection.nearbyIntervals height,
          value ∈ scalarProjection
            (selection.chartLabel.chart.direction
              (slopes.slope (selection.intervalBase interval)))
            (selection.literalSourceSlab interval)} := by
  intro value hvalue
  rcases selection.public_horizontal_slice_near_literal_slab
      rescaled slopes height hvalue with
    ⟨interval, hinterval, reference, hreference, hclose, hheightClose⟩
  have hnear : interval ∈ selection.nearbyIntervals height := by
    exact (selection.mem_nearbyIntervals_iff height interval).2
      ⟨hinterval, hheightClose⟩
  exact Metric.mem_cthickening_of_dist_le value reference _ _
    ⟨interval, hnear, hreference⟩ (by simpa [Real.dist_eq] using hclose)

/-- The union of all nearby retained slab projections has paper AD with a
constant depending only on the absolute neighbor bound and the slab constant. -/
lemma nearby_literal_slabs_ad
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (slopes : Proposition63SlopeData selection)
    (hrhoDelta : rho = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (height : ℝ) :
    PureWZ2PaperADSet1
      {value | ∃ interval ∈ selection.nearbyIntervals height,
        value ∈ scalarProjection
          (selection.chartLabel.chart.direction
            (slopes.slope (selection.intervalBase interval)))
          (selection.literalSourceSlab interval)}
      Delta (1 - sigma)
      (204 * (1 + proposition63SlabADConstant delta localLoss)) := by
  let sourceConstant := proposition63SlabADConstant delta localLoss
  let targetConstant : ENNReal := 1 + sourceConstant
  have hsourceTop : sourceConstant ≠ ⊤ := by
    simp [sourceConstant, proposition63SlabADConstant,
      Kakeya.realRpowENN, ENNReal.mul_eq_top]
  have htargetOne : (1 : ENNReal) ≤ targetConstant := by
    exact le_add_right le_rfl
  have htargetTop : targetConstant ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨by norm_num, hsourceTop⟩
  have hpiece : ∀ interval ∈ selection.nearbyIntervals height,
      PureWZ2PaperADSet1
        (scalarProjection
          (selection.chartLabel.chart.direction
            (slopes.slope (selection.intervalBase interval)))
          (selection.literalSourceSlab interval))
        Delta (1 - sigma) targetConstant := by
    intro interval hinterval
    have hselected :=
      (selection.mem_nearbyIntervals_iff height interval).1 hinterval |>.1
    have hAD := selection.literalSourceSlab_slope_ad
      slopes hrhoDelta interval hselected
    apply hAD.mono_const
    · exact le_add_left le_rfl
    · exact htargetTop
  have hunion := PureWZ2PaperADSet1.finset_biUnion
    hDelta (by linarith) (by linarith) htargetOne htargetTop hpiece
  have hnearCard := selection.nearbyIntervals_card_le hrhoDelta height
  have hcard : (selection.nearbyIntervals height).card + 1 ≤ 204 := by
    omega
  have hconstant :
      (((selection.nearbyIntervals height).card : ENNReal) + 1) *
          targetConstant ≤ 204 * targetConstant := by
    gcongr
    exact_mod_cast hcard
  have hfixed := hunion.mono_const hconstant
    (ENNReal.mul_ne_top (by norm_num) htargetTop)
  simpa only [sourceConstant, targetConstant] using hfixed

/-- Exact public slices inherit paper AD from the bounded union of retained
slab projections.  The explicit thickening factor is later absorbed into the
chosen output loss. -/
lemma public_horizontal_slice_chart_ad
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss)
    (slopes : Proposition63SlopeData selection)
    (hrhoDelta : rho = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (height : ℝ) :
    PureWZ2PaperADSet1
      (scalarProjection
        (selection.chartLabel.chart.direction
          (slopes.slope (100 * height)))
        (horizontalSlice rescaled.publicShading.union height))
      Delta (1 - sigma)
      ((2 * (Nat.ceil
          (proposition63ExactSliceError delta rho Delta coefficient / Delta) +
        1) : ENNReal) ^ 2 *
          (204 * (1 + proposition63SlabADConstant delta localLoss))) := by
  have hsource := selection.nearby_literal_slabs_ad slopes hrhoDelta
    hsigma hsigmaOne height
  apply _root_.Kakeya.Assouad.PureWZ2PaperADSet1.generalized_thickening hsource
  · intro value hvalue
    rcases selection.public_horizontal_slice_near_literal_slab
        rescaled slopes height hvalue with
      ⟨interval, hinterval, reference, hreference, hclose, hheightClose⟩
    have hnear : interval ∈ selection.nearbyIntervals height :=
      (selection.mem_nearbyIntervals_iff height interval).2
        ⟨hinterval, hheightClose⟩
    exact ⟨reference, ⟨interval, hnear, hreference⟩, hclose⟩
  · unfold proposition63ExactSliceError
    have hratio : 0 < delta / rho := div_pos hdelta hrho
    have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    positivity

end Proposition63ChartSelectionData

end Kakeya.Assouad.PureWZ2

end
