import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9GenericFirstChartDenseRoot
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9CoarseGlobalAbsorption

/-!
# Proposition 6.3 M9: global slices after whole-cell saturation

The whole-cell source is larger than the interval-restricted chart source, so
the old global-slice theorem cannot be applied by a false subshading claim.
Instead every retained source cell supplies a same-cell chart witness.  After
literal rescaling, the whole-cell public point is uniformly close to the old
charted public shading, which is the only extra error paid below.
-/

noncomputable section
namespace Kakeya.Assouad.PureWZ2
open Metric Set

namespace Proposition63FirstChartData

variable
    {delta Delta sigma stickyLoss localLoss commonSliceLoss chartLoss
      tau epsilon₁ epsilon₃ coefficient initialInputLoss initialOutputLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {firstScale : WZ2PaperRequestedScale delta}
    {logExponent normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialOutputLoss) initialSource normalizationExponent)
    {firstSticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      initialNormalized.croppedRefined firstScale logExponent}
    {retainedFactor : ENNReal}
    (first : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := coefficient)
      firstSticky Delta retainedFactor)

/-- Extra distance paid when the source is saturated by whole original
`delta`-cells and the literal image is then saturated at scale
`delta / firstScale`. -/
def wholeCellPublicError : ℝ :=
  (101 / 100 : ℝ) * (delta / firstScale.1) * Real.sqrt 3

/-- Intervals which can contribute after the whole-cell source and one later
coarse-cell replacement. -/
def wholeCellCoarseNearbyIntervals (height : ℝ) : Finset
    (commonSliceIntervalType (proposition63LiteralSliceWidth Delta)) :=
  first.chartSelection.intervals.filter fun interval =>
    |100 * height - first.chartSelection.intervalBase interval| ≤
      101 * Delta + 100 * (delta / firstScale.1) + delta * Real.sqrt 3

theorem wholeCellCoarseNearbyIntervals_card_le
    (hfirstScale : firstScale.1 = Delta)
    (height : ℝ) :
    (wholeCellCoarseNearbyIntervals initialNormalized first height).card ≤
      405 := by
  have ratioLe : delta / firstScale.1 ≤ Delta := by
    rw [hfirstScale]
    exact (div_le_iff₀ first.Delta_pos).2
      (by simpa [pow_two] using first.delta_le_Delta_sq)
  have sqrtThree : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sqrt_nonneg 3,
      Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have deltaSqrtLe : delta * Real.sqrt 3 ≤ Delta := by
    have deltaLe : delta ≤ Delta / 200 := by
      calc
        delta ≤ Delta ^ 2 := first.delta_le_Delta_sq
        _ ≤ Delta / 200 := by
          nlinarith [first.Delta_pos, first.Delta_small]
    nlinarith [first.delta_pos]
  let center : ℤ := ⌊(100 * height) / Delta⌋
  let target : Finset ℤ := Finset.Icc (center - 202) (center + 202)
  have hmap : Set.MapsTo
      (fun interval : commonSliceIntervalType
        (proposition63LiteralSliceWidth Delta) => interval.1)
      (wholeCellCoarseNearbyIntervals initialNormalized first height : Set _)
      (target : Set ℤ) := by
    intro interval hinterval
    have hclose := (Finset.mem_filter.mp hinterval).2
    have hclose' :
        |100 * height - first.chartSelection.intervalBase interval| ≤
          202 * Delta := by
      calc
        _ ≤ 101 * Delta + 100 * (delta / firstScale.1) +
              delta * Real.sqrt 3 := hclose
        _ ≤ 101 * Delta + 100 * Delta + Delta := by gcongr
        _ = 202 * Delta := by ring
    have hbounds := abs_le.mp hclose'
    have hcenterLower : (center : ℝ) * Delta ≤ 100 * height := by
      have h := Int.floor_le ((100 * height) / Delta)
      dsimp only [center]
      exact (le_div_iff₀ first.Delta_pos).1 h
    have hcenterUpper : 100 * height < ((center : ℝ) + 1) * Delta := by
      have h := Int.lt_floor_add_one ((100 * height) / Delta)
      dsimp only [center]
      exact (div_lt_iff₀ first.Delta_pos).1 h
    have hlowerReal : ((center - 202 : ℤ) : ℝ) ≤ (interval.1 : ℝ) := by
      have hmul : (((center - 202 : ℤ) : ℝ) * Delta) ≤
          (interval.1 : ℝ) * Delta := by
        simp only [Int.cast_sub, Int.cast_ofNat]
        unfold Proposition63ChartSelectionData.intervalBase at hbounds
        nlinarith [hbounds.2]
      exact le_of_mul_le_mul_right hmul first.Delta_pos
    have hupperReal : (interval.1 : ℝ) < ((center + 203 : ℤ) : ℝ) := by
      have hmul : (interval.1 : ℝ) * Delta <
          (((center + 203 : ℤ) : ℝ) * Delta) := by
        simp only [Int.cast_add, Int.cast_ofNat]
        unfold Proposition63ChartSelectionData.intervalBase at hbounds
        nlinarith [hbounds.1]
      exact lt_of_mul_lt_mul_right hmul first.Delta_pos.le
    have hlower : center - 202 ≤ interval.1 := by exact_mod_cast hlowerReal
    have hupper : interval.1 ≤ center + 202 := by
      have : interval.1 < center + 203 := by exact_mod_cast hupperReal
      omega
    exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩
  have hinjective : Set.InjOn
      (fun interval : commonSliceIntervalType
        (proposition63LiteralSliceWidth Delta) => interval.1)
      (wholeCellCoarseNearbyIntervals initialNormalized first height : Set _) := by
    intro left _ right _ heq
    exact Subtype.ext heq
  have hcard := Finset.card_le_card_of_injOn
    (fun interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta) => interval.1) hmap hinjective
  have targetCard : target.card = 405 := by
    have hle : center - 202 ≤ center + 202 + 1 := by omega
    have hcardInt : (target.card : ℤ) =
        (center + 202) + 1 - (center - 202) :=
      Int.card_Icc_of_le (center - 202) (center + 202) hle
    exact_mod_cast (show (target.card : ℤ) = 405 by
      rw [hcardInt]
      ring)
  simpa [targetCard] using hcard

/-- The finite union of old source slabs retains paper AD after whole-cell
saturation; only the number of relevant intervals changes. -/
theorem wholeCellCoarseNearbySlabs_ad
    (slopes : first.chartSelection.Proposition63SlopeData)
    (hfirstScale : firstScale.1 = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (height : ℝ) :
    PureWZ2PaperADSet1
      {value | ∃ interval ∈
          wholeCellCoarseNearbyIntervals initialNormalized first height,
        value ∈ scalarProjection
          (first.chartSelection.chartLabel.chart.direction
            (slopes.slope (first.chartSelection.intervalBase interval)))
          (first.chartSelection.literalSourceSlab interval)}
      Delta (1 - sigma)
      (500 * (1 +
        proposition63SlabADConstant delta localLoss)) := by
  let sourceConstant :=
    proposition63SlabADConstant delta localLoss
  let targetConstant : ENNReal := 1 + sourceConstant
  have sourceTop : sourceConstant ≠ ⊤ := by
    simp [sourceConstant,
      proposition63SlabADConstant,
      Kakeya.realRpowENN, ENNReal.mul_eq_top]
  have targetOne : (1 : ENNReal) ≤ targetConstant := le_add_right le_rfl
  have targetTop : targetConstant ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨by norm_num, sourceTop⟩
  have piece : ∀ interval ∈
      wholeCellCoarseNearbyIntervals initialNormalized first height,
      PureWZ2PaperADSet1
        (scalarProjection
          (first.chartSelection.chartLabel.chart.direction
            (slopes.slope (first.chartSelection.intervalBase interval)))
          (first.chartSelection.literalSourceSlab interval))
        Delta (1 - sigma) targetConstant := by
    intro interval hinterval
    have selected := (Finset.mem_filter.mp hinterval).1
    exact (first.chartSelection.literalSourceSlab_slope_ad slopes hfirstScale
      interval selected).mono_const (le_add_left le_rfl) targetTop
  have unionAD := PureWZ2PaperADSet1.finset_biUnion
    first.Delta_pos (by linarith) (by linarith) targetOne targetTop piece
  have cardBound := wholeCellCoarseNearbyIntervals_card_le
    initialNormalized first hfirstScale height
  have constantBound :
      (((wholeCellCoarseNearbyIntervals initialNormalized first height).card :
          ENNReal) + 1) *
          targetConstant ≤ 500 * targetConstant := by
    gcongr
    exact_mod_cast (show
      (wholeCellCoarseNearbyIntervals initialNormalized first height).card + 1
        ≤ 500 by omega)
  exact unionAD.mono_const constantBound
    (ENNReal.mul_ne_top (by norm_num) targetTop)

/- Temporarily placed after the point-to-slab bridge in the downstream
coarse module; retained here as design documentation.

/-- A Lemma-4.4 coarse point is close to the bounded union of source slabs
even when the Lemma-4.3 source is the canonical whole-cell trace ambient. -/
theorem lemma44_horizontal_slice_subset_wholeCell_thickening
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := chartLoss)
      (first.wholeCellShading initialNormalized)
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos)
    (massLower :
      Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
          output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2)) *
          (first.wholeCellOrdinaryTrace initialNormalized).mass)
    (slopes : first.chartSelection.Proposition63SlopeData)
    {lemma43SourceLoss lemma43Loss sticky2Loss lemma44Loss : ℝ}
    {secondFamily : Kakeya.Streamlined.TubeFamily (delta / firstScale.1)}
    {secondScale : WZ2PaperRequestedScale (delta / firstScale.1)}
    {lemma43Source : WZ1PaperTubeShading secondFamily}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) lemma43Source (secondScale.1 / 2)}
    {secondSticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sticky2Loss)
      lemma43.shading secondScale 61}
    (lemma44 : Proposition63Lemma44Data lemma43 secondSticky lemma44Loss)
    (hsourceUnion : lemma43Source.union ⊆
      (first.wholeCellTraceAmbient initialNormalized output massLower).union)
    (hfirstScale : firstScale.1 = Delta)
    (hsecondScale : secondScale.1 = Delta)
    (height : ℝ) :
    ∀ value ∈ scalarProjection
      (globalGrainDirection (slopes.slope (100 * height)))
      (horizontalSlice lemma44.coarseShading.union height),
      ∃ reference ∈
        {value | ∃ interval ∈
            wholeCellCoarseNearbyIntervals initialNormalized first height,
          value ∈ scalarProjection
            (first.chartSelection.chartLabel.chart.direction
              (slopes.slope (first.chartSelection.intervalBase interval)))
            (first.chartSelection.literalSourceSlab interval)},
        |value - reference| ≤
          Proposition63ChartSelectionData.proposition63WholeCellCoarseExactSliceError
            delta firstScale.1 Delta coefficient := by
  rintro value ⟨point, hpoint, rfl⟩
  rcases lemma44.coarse_point_has_fine_witness point hpoint.1 with
    ⟨finePoint, hfinePoint, sameCell⟩
  have fineSource : finePoint ∈
      (first.wholeCellTraceAmbient initialNormalized output massLower).union := by
    rcases hfinePoint with ⟨index, hindex⟩
    apply hsourceUnion
    exact ⟨secondSticky.selected.embedding index,
      lemma44.fine_subshading index finePoint hindex⟩
  rcases first.wholeCell_point_near_literal_slab initialNormalized output
      massLower slopes hfirstScale finePoint fineSource with
    ⟨interval, hinterval, reference, hreference, fineProjection, fineHeight⟩
  have pointCell : point ∈ wz1PaperGridCube secondScale.1
      (wz1PaperGridIndex secondScale.1 point) :=
    (mem_wz1PaperGridCube _ _ _).2 rfl
  have fineCell : finePoint ∈ wz1PaperGridCube secondScale.1
      (wz1PaperGridIndex secondScale.1 point) :=
    (mem_wz1PaperGridCube _ _ _).2 sameCell
  have pointDistance : dist point finePoint ≤ Real.sqrt 3 * Delta := by
    have raw := wz1PaperGridCube_diameter
      (by simpa [hsecondScale] using first.Delta_pos)
      (wz1PaperGridIndex secondScale.1 point) pointCell fineCell
    simpa [hsecondScale, mul_comm] using raw
  have heightDistance : |point 2 - finePoint 2| < Delta := by
    have raw := samePaperGridIndex_coord_two_lt
      (by simpa [hsecondScale] using first.Delta_pos) sameCell.symm
    simpa [hsecondScale, abs_sub_comm] using raw
  have near : interval ∈
      wholeCellCoarseNearbyIntervals initialNormalized first height := by
    apply Finset.mem_filter.mpr
    refine ⟨hinterval, ?_⟩
    rw [← hpoint.2]
    calc
      |100 * point 2 - first.chartSelection.intervalBase interval| =
          |100 * (point 2 - finePoint 2) +
            (100 * finePoint 2 -
              first.chartSelection.intervalBase interval)| := by
        ring_nf
      _ ≤ |100 * (point 2 - finePoint 2)| +
          |100 * finePoint 2 -
            first.chartSelection.intervalBase interval| := abs_add_le _ _
      _ ≤ 100 * Delta +
          (Delta + 100 * (delta / firstScale.1) + delta * Real.sqrt 3) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
        exact add_le_add
          (mul_le_mul_of_nonneg_left heightDistance.le (by norm_num))
          fineHeight
      _ = 101 * Delta + 100 * (delta / firstScale.1) +
          delta * Real.sqrt 3 := by ring
  refine ⟨reference, ⟨interval, near, hreference⟩, ?_⟩
  let pointDirection := globalGrainDirection (slopes.slope (100 * height))
  let fineDirection := globalGrainDirection (slopes.slope (100 * finePoint 2))
  have pointDirectionNorm : ‖pointDirection‖ ≤ 4 :=
    globalGrainDirection_norm_le_4 (slopes.bounded _)
  have fineNorm : ‖finePoint‖ ≤ 3 := paperShadingPoint_norm_le_three fineSource
  have spatial :
      |inner ℝ point pointDirection - inner ℝ finePoint pointDirection| ≤
        4 * (Real.sqrt 3 * Delta) := by
    rw [← inner_sub_left]
    calc
      _ ≤ ‖point - finePoint‖ * ‖pointDirection‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (Real.sqrt 3 * Delta) * 4 := by
        gcongr
        simpa [dist_eq_norm] using pointDistance
      _ = _ := by ring
  have slopeDistance :
      |slopes.slope (100 * height) - slopes.slope (100 * finePoint 2)| ≤
        252000 * (Real.toNNReal coefficient : ℝ) * Delta := by
    have lip := slopes.lipschitz.dist_le_mul
      (100 * height) (100 * finePoint 2)
    rw [Real.dist_eq, Real.dist_eq] at lip
    calc
      _ ≤ (2520 * (Real.toNNReal coefficient : ℝ)) *
          |100 * height - 100 * finePoint 2| := by simpa using lip
      _ = (252000 * (Real.toNNReal coefficient : ℝ)) *
          |point 2 - finePoint 2| := by
        rw [hpoint.2, show 100 * point 2 - 100 * finePoint 2 =
          100 * (point 2 - finePoint 2) by ring, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 100)]
        ring
      _ ≤ _ := by gcongr
  have directionDifference : ‖pointDirection - fineDirection‖ =
      |slopes.slope (100 * height) - slopes.slope (100 * finePoint 2)| := by
    have heq : pointDirection - fineDirection =
        (slopes.slope (100 * height) - slopes.slope (100 * finePoint 2)) •
          EuclideanSpace.single (1 : Fin 3) 1 := by
      ext coordinate
      fin_cases coordinate <;>
        simp [pointDirection, fineDirection, globalGrainDirection]
    rw [heq, norm_smul]
    simp [Real.norm_eq_abs]
  have slopeProjection :
      |inner ℝ finePoint pointDirection - inner ℝ finePoint fineDirection| ≤
        3 * (252000 * (Real.toNNReal coefficient : ℝ) * Delta) := by
    rw [← inner_sub_right]
    calc
      _ ≤ ‖finePoint‖ * ‖pointDirection - fineDirection‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ _ := by rw [directionDifference]; gcongr
  have triangle := abs_sub_le (inner ℝ point pointDirection)
    (inner ℝ finePoint pointDirection) reference
  have triangleTwo := abs_sub_le (inner ℝ finePoint pointDirection)
    (inner ℝ finePoint fineDirection) reference
  have total : |inner ℝ point pointDirection - reference| ≤
      4 * (Real.sqrt 3 * Delta) +
        (3 * (252000 * (Real.toNNReal coefficient : ℝ) * Delta) +
          Proposition63ChartSelectionData.proposition63WholeCellExactSliceError
            delta firstScale.1 Delta coefficient) := by
    exact triangle.trans <| add_le_add spatial <|
      triangleTwo.trans (add_le_add slopeProjection fineProjection)
  simpa [pointDirection, fineDirection,
    Proposition63ChartSelectionData.proposition63WholeCellCoarseExactSliceError,
    add_assoc, add_left_comm, add_comm] using total

/-- The whole-cell source gives the same global slice conclusion with its
honest enlarged constant. -/
theorem lemma44_horizontal_slice_wholeCell_ad
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := chartLoss)
      (first.wholeCellShading initialNormalized)
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos)
    (massLower :
      Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
          output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2)) *
          (first.wholeCellOrdinaryTrace initialNormalized).mass)
    (slopes : first.chartSelection.Proposition63SlopeData)
    {lemma43SourceLoss lemma43Loss sticky2Loss lemma44Loss : ℝ}
    {secondFamily : Kakeya.Streamlined.TubeFamily (delta / firstScale.1)}
    {secondScale : WZ2PaperRequestedScale (delta / firstScale.1)}
    {lemma43Source : WZ1PaperTubeShading secondFamily}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) lemma43Source (secondScale.1 / 2)}
    {secondSticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sticky2Loss)
      lemma43.shading secondScale 61}
    (lemma44 : Proposition63Lemma44Data lemma43 secondSticky lemma44Loss)
    (hsourceUnion : lemma43Source.union ⊆
      (first.wholeCellTraceAmbient initialNormalized output massLower).union)
    (hfirstScale : firstScale.1 = Delta)
    (hsecondScale : secondScale.1 = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (height : ℝ) :
    PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (slopes.slope (100 * height)))
        (horizontalSlice lemma44.coarseShading.union height))
      secondScale.1 (1 - sigma)
      (Proposition63ChartSelectionData.proposition63WholeCellCoarseGlobalADConstant
        delta firstScale.1 Delta localLoss coefficient) := by
  have sourceAD := first.wholeCellCoarseNearbySlabs_ad initialNormalized slopes
    hfirstScale hsigma hsigmaOne height
  have close := first.lemma44_horizontal_slice_subset_wholeCell_thickening
    initialNormalized output massLower slopes lemma44 hsourceUnion hfirstScale
      hsecondScale height
  have thick := sourceAD.generalized_thickening close (by
    unfold Proposition63ChartSelectionData.proposition63WholeCellCoarseExactSliceError
      Proposition63ChartSelectionData.proposition63WholeCellExactSliceError
    have ratioPos : 0 < delta / firstScale.1 :=
      div_pos first.delta_pos (first.delta_pos.trans_le firstScale.2.1)
    positivity)
  simpa only [hsecondScale,
    Proposition63ChartSelectionData.proposition63WholeCellCoarseGlobalADConstant]
    using thick

-/

/-- A point in the public image of the whole-cell shading is close to a point
of the original interval-selected chart image. -/
theorem wholeCellTraceAmbient_close_normalized
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := chartLoss)
      (first.wholeCellShading initialNormalized)
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos)
    (massLower :
      Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
          output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2)) *
          (first.wholeCellOrdinaryTrace initialNormalized).mass)
    (hfirstScale : firstScale.1 = Delta)
    (point : Point3)
    (hpoint : point ∈
      (first.wholeCellTraceAmbient initialNormalized output massLower).union) :
    ∃ oldPoint ∈
        (first.chartSelection.normalizedShading first.chartRescaled).union,
      dist point oldPoint ≤
        wholeCellPublicError (delta := delta) (firstScale := firstScale) := by
  let chart := first.chartSelection.chartLabel.chart
  change point ∈ (chart.transportPaperShading
    (output.rescalingCertificate.publicShading
      output.literalShading.targetShading)).union at hpoint
  rw [chart.transportPaperShading_union] at hpoint
  rcases hpoint with ⟨publicPoint, hpublicPoint, rfl⟩
  have hpublicLiteral : publicPoint ∈ output.literalShading.targetShading.union := by
    rw [← output.rescalingCertificate.publicShading_union_eq]
    exact hpublicPoint
  rcases hpublicLiteral with ⟨publicIndex, hpublicIndex⟩
  rw [output.literalShading.target_carrier_eq publicIndex] at hpublicIndex
  rcases hpublicIndex with ⟨literalPoint, hliteralPoint, htargetGrid⟩
  rcases hliteralPoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  change sourcePoint ∈ first.chartSelection.saturated.carrier
    (output.familyData.sourceIndex publicIndex) at hsourcePoint
  rw [first.chartSelection.saturated_carrier] at hsourcePoint
  rcases Set.mem_iUnion₂.mp hsourcePoint.2 with
    ⟨cell, hcell, hsourceCell⟩
  rcases Proposition63ChartSelectionData.selectedCell_source_slab_witness
      first.chartSelection hfirstScale cell hcell with
    ⟨tube, witness, hwitnessSource, hwitnessCell, interval, hinterval,
      hwitnessSlab, _hchart, _hchartBound⟩
  let literalWitness := wz2PaperLiteralUnitRescalingMap
    (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos witness
  rcases first.metricFiber.frozenRescaled.familyData.sourceIndex_bijective.2
      tube with ⟨oldIndex, holdIndex⟩
  have holdLiteral : literalWitness ∈
      first.chartRescaled.literalImage.targetShading.carrier oldIndex := by
    rw [first.chartRescaled.literalImage.target_carrier_eq oldIndex]
    exact ⟨literalWitness,
      ⟨witness, by simpa only [holdIndex] using hwitnessSource, rfl⟩, rfl⟩
  have holdPublic : literalWitness ∈ first.chartRescaled.publicShading.union := by
    rw [first.chartRescaled.publicShading_union_eq]
    exact ⟨oldIndex, holdLiteral⟩
  refine ⟨chart.isometry literalWitness, ?_, ?_⟩
  · change chart.isometry literalWitness ∈
      (chart.transportPaperShading first.chartRescaled.publicShading).union
    rw [chart.transportPaperShading_union]
    exact ⟨literalWitness, holdPublic, rfl⟩
  · change dist (chart.isometry publicPoint)
        (chart.isometry literalWitness) ≤ _
    change dist (chart.isometry.toIsometryEquiv publicPoint)
        (chart.isometry.toIsometryEquiv literalWitness) ≤ _
    rw [chart.isometry.toIsometryEquiv.dist_eq]
    have htargetDistance :
        dist publicPoint
            (wz2PaperLiteralUnitRescalingMap
              (firstSticky.coarse.tube first.metricFiber.parent)
              firstSticky.coarse_extremal.delta_pos sourcePoint) ≤
          (delta / firstScale.1) * Real.sqrt 3 := by
      apply wz1PaperGridCube_diameter
        (div_pos first.delta_pos
          (first.delta_pos.trans_le firstScale.2.1))
        (wz1PaperGridIndex (delta / firstScale.1)
          (wz2PaperLiteralUnitRescalingMap
            (firstSticky.coarse.tube first.metricFiber.parent)
            firstSticky.coarse_extremal.delta_pos sourcePoint))
      · exact (mem_wz1PaperGridCube _ _ _).2 htargetGrid
      · exact (mem_wz1PaperGridCube _ _ _).2 rfl
    have hsourceDistance : dist sourcePoint witness ≤ delta * Real.sqrt 3 :=
      wz1PaperGridCube_diameter first.delta_pos cell hsourceCell hwitnessCell
    have himageDistance :
        dist
            (wz2PaperLiteralUnitRescalingMap
              (firstSticky.coarse.tube first.metricFiber.parent)
              firstSticky.coarse_extremal.delta_pos sourcePoint)
            literalWitness ≤
          (delta / firstScale.1) * Real.sqrt 3 / 100 := by
      rw [dist_eq_norm, wz2PaperLiteralUnitRescalingMap_sub]
      calc
        _ ≤ ‖sourcePoint - witness‖ / (100 * firstScale.1) :=
          wz2PaperLiteralUnitRescalingLinear_norm_le
            (firstSticky.coarse.tube first.metricFiber.parent)
            firstSticky.coarse_extremal.delta_pos firstScale.2.2 _
        _ ≤ (delta * Real.sqrt 3) / (100 * firstScale.1) := by
          exact div_le_div_of_nonneg_right
            (by simpa [dist_eq_norm] using hsourceDistance)
            (mul_pos (by norm_num)
              (first.delta_pos.trans_le firstScale.2.1)).le
        _ = (delta / firstScale.1) * Real.sqrt 3 / 100 := by
          field_simp [(first.delta_pos.trans_le firstScale.2.1).ne']
    calc
      dist publicPoint literalWitness ≤
          dist publicPoint
              (wz2PaperLiteralUnitRescalingMap
                (firstSticky.coarse.tube first.metricFiber.parent)
                firstSticky.coarse_extremal.delta_pos sourcePoint) +
            dist
              (wz2PaperLiteralUnitRescalingMap
                (firstSticky.coarse.tube first.metricFiber.parent)
                firstSticky.coarse_extremal.delta_pos sourcePoint)
              literalWitness := dist_triangle _ _ _
      _ ≤ (delta / firstScale.1) * Real.sqrt 3 +
            (delta / firstScale.1) * Real.sqrt 3 / 100 := by gcongr
      _ = wholeCellPublicError (delta := delta) (firstScale := firstScale) := by
        unfold wholeCellPublicError
        ring

/-- A whole-cell public point retains a genuine interval/slab witness.  The
projection and height errors include exactly the two whole-cell same-grid
displacements. -/
theorem wholeCell_point_near_literal_slab
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := chartLoss)
      (first.wholeCellShading initialNormalized)
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos)
    (massLower :
      Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
          output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2)) *
          (first.wholeCellOrdinaryTrace initialNormalized).mass)
    (slopes : first.chartSelection.Proposition63SlopeData)
    (hfirstScale : firstScale.1 = Delta)
    (point : Point3)
    (hpoint : point ∈
      (first.wholeCellTraceAmbient initialNormalized output massLower).union) :
    ∃ interval ∈ first.chartSelection.intervals,
      ∃ reference ∈ scalarProjection
        (first.chartSelection.chartLabel.chart.direction
          (slopes.slope (first.chartSelection.intervalBase interval)))
        (first.chartSelection.literalSourceSlab interval),
      |inner ℝ point
          (globalGrainDirection (slopes.slope (100 * point 2))) - reference| ≤
          Proposition63ChartSelectionData.proposition63WholeCellExactSliceError
            delta firstScale.1 Delta coefficient ∧
      |100 * point 2 - first.chartSelection.intervalBase interval| ≤
        Delta + 100 * (delta / firstScale.1) + delta * Real.sqrt 3 := by
  let chart := first.chartSelection.chartLabel.chart
  change point ∈ (chart.transportPaperShading
    (output.rescalingCertificate.publicShading
      output.literalShading.targetShading)).union at hpoint
  rw [chart.transportPaperShading_union] at hpoint
  rcases hpoint with ⟨publicPoint, hpublicPoint, rfl⟩
  have hpublicLiteral : publicPoint ∈ output.literalShading.targetShading.union := by
    rw [← output.rescalingCertificate.publicShading_union_eq]
    exact hpublicPoint
  rcases hpublicLiteral with ⟨publicIndex, hpublicIndex⟩
  rw [output.literalShading.target_carrier_eq publicIndex] at hpublicIndex
  rcases hpublicIndex with ⟨literalPoint, hliteralPoint, htargetGrid⟩
  rcases hliteralPoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  change sourcePoint ∈ first.chartSelection.saturated.carrier
    (output.familyData.sourceIndex publicIndex) at hsourcePoint
  rw [first.chartSelection.saturated_carrier] at hsourcePoint
  rcases Set.mem_iUnion₂.mp hsourcePoint.2 with
    ⟨cell, hcell, hsourceCell⟩
  rcases Proposition63ChartSelectionData.selectedCell_source_slab_witness
      first.chartSelection hfirstScale cell hcell with
    ⟨tube, witness, hwitnessSource, hwitnessCell, interval, hinterval,
      hwitnessSlab, _hchart, _hchartBound⟩
  let literalSource := wz2PaperLiteralUnitRescalingMap
    (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos sourcePoint
  let literalWitness := wz2PaperLiteralUnitRescalingMap
    (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos witness
  have hliteralWitness : literalWitness ∈
      first.chartSelection.literalSourceSlab interval :=
    ⟨witness, ⟨⟨tube, hwitnessSource⟩, hwitnessSlab⟩, rfl⟩
  let reference := inner ℝ literalWitness
    (first.chartSelection.chartLabel.chart.direction
      (slopes.slope (first.chartSelection.intervalBase interval)))
  refine ⟨interval, hinterval, reference, ⟨literalWitness,
    hliteralWitness, rfl⟩, ?_⟩
  have targetDistance : dist publicPoint literalSource ≤
        (delta / firstScale.1) * Real.sqrt 3 := by
      apply wz1PaperGridCube_diameter
        (div_pos first.delta_pos
          (first.delta_pos.trans_le firstScale.2.1))
        (wz1PaperGridIndex (delta / firstScale.1) literalSource)
      · exact (mem_wz1PaperGridCube _ _ _).2 htargetGrid
      · exact (mem_wz1PaperGridCube _ _ _).2 rfl
  have sourceDistance : dist sourcePoint witness ≤ delta * Real.sqrt 3 :=
    wz1PaperGridCube_diameter first.delta_pos cell hsourceCell hwitnessCell
  have imageDistance : dist literalSource literalWitness ≤
        (delta / firstScale.1) * Real.sqrt 3 / 100 := by
      rw [dist_eq_norm, wz2PaperLiteralUnitRescalingMap_sub]
      calc
        _ ≤ ‖sourcePoint - witness‖ / (100 * firstScale.1) :=
          wz2PaperLiteralUnitRescalingLinear_norm_le
            (firstSticky.coarse.tube first.metricFiber.parent)
            firstSticky.coarse_extremal.delta_pos firstScale.2.2 _
        _ ≤ (delta * Real.sqrt 3) / (100 * firstScale.1) := by
          exact div_le_div_of_nonneg_right
            (by simpa [dist_eq_norm] using sourceDistance)
            (mul_pos (by norm_num)
              (first.delta_pos.trans_le firstScale.2.1)).le
        _ = _ := by
          field_simp [(first.delta_pos.trans_le firstScale.2.1).ne']
  have totalDistance : dist publicPoint literalWitness ≤
        wholeCellPublicError (delta := delta) (firstScale := firstScale) := by
      calc
        _ ≤ dist publicPoint literalSource + dist literalSource literalWitness :=
          dist_triangle _ _ _
        _ ≤ (delta / firstScale.1) * Real.sqrt 3 +
            (delta / firstScale.1) * Real.sqrt 3 / 100 := by gcongr
        _ = _ := by unfold wholeCellPublicError; ring
  have directionNorm : ‖globalGrainDirection
        (slopes.slope (100 * (chart.isometry publicPoint) 2))‖ ≤ 4 :=
      globalGrainDirection_norm_le_4 (slopes.bounded _)
  have totalDistanceNonneg :
        0 ≤ wholeCellPublicError (delta := delta)
          (firstScale := firstScale) := by
      unfold wholeCellPublicError
      exact mul_nonneg
        (mul_nonneg (by norm_num)
          (div_nonneg first.delta_pos.le
            (first.delta_pos.trans_le firstScale.2.1).le))
        (Real.sqrt_nonneg 3)
  have mappedDistance :
        ‖chart.isometry publicPoint - chart.isometry literalWitness‖ ≤
          wholeCellPublicError (delta := delta)
            (firstScale := firstScale) := by
      calc
        ‖chart.isometry publicPoint - chart.isometry literalWitness‖ =
            dist (chart.isometry publicPoint)
              (chart.isometry literalWitness) := by rw [dist_eq_norm]
        _ = dist publicPoint literalWitness := by
          change dist (chart.isometry.toIsometryEquiv publicPoint)
              (chart.isometry.toIsometryEquiv literalWitness) = _
          exact chart.isometry.toIsometryEquiv.dist_eq _ _
        _ ≤ _ := totalDistance
  have spatial :
        |inner ℝ (chart.isometry publicPoint)
              (globalGrainDirection
                (slopes.slope (100 * (chart.isometry publicPoint) 2))) -
            inner ℝ (chart.isometry literalWitness)
              (globalGrainDirection
                (slopes.slope (100 * (chart.isometry publicPoint) 2)))| ≤
          4 * wholeCellPublicError (delta := delta)
            (firstScale := firstScale) := by
      rw [← inner_sub_left]
      calc
        _ ≤ ‖chart.isometry publicPoint - chart.isometry literalWitness‖ *
            ‖globalGrainDirection
              (slopes.slope (100 * (chart.isometry publicPoint) 2))‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ wholeCellPublicError (delta := delta)
              (firstScale := firstScale) * 4 := by
          apply mul_le_mul
          · exact mappedDistance
          · exact directionNorm
          · positivity
          · exact totalDistanceNonneg
        _ = _ := by ring
  have literalWitnessNorm : ‖chart.isometry literalWitness‖ ≤ 3 := by
      apply paperShadingPoint_norm_le_three
      change chart.isometry literalWitness ∈
        (chart.transportPaperShading first.chartRescaled.publicShading).union
      rw [chart.transportPaperShading_union]
      rcases first.metricFiber.frozenRescaled.familyData.sourceIndex_bijective.2
          tube with ⟨oldIndex, holdIndex⟩
      have holdLiteral : literalWitness ∈
          first.chartRescaled.literalImage.targetShading.carrier oldIndex := by
        rw [first.chartRescaled.literalImage.target_carrier_eq oldIndex]
        exact ⟨literalWitness,
          ⟨witness, by simpa only [holdIndex] using hwitnessSource, rfl⟩, rfl⟩
      have holdPublic : literalWitness ∈ first.chartRescaled.publicShading.union := by
        have hEq := first.chartRescaled.publicShading_union_eq
        rw [hEq]
        exact ⟨oldIndex, holdLiteral⟩
      exact ⟨literalWitness, holdPublic, rfl⟩
  have heightClose :
        |100 * (chart.isometry publicPoint) 2 -
            first.chartSelection.intervalBase interval| ≤
          Delta + 100 * (delta / firstScale.1) + delta * Real.sqrt 3 := by
      have targetHeight :
          |publicPoint 2 - literalSource 2| < delta / firstScale.1 := by
        have := samePaperGridIndex_coord_two_lt
          (div_pos first.delta_pos
            (first.delta_pos.trans_le firstScale.2.1)) htargetGrid
        simpa [literalSource, abs_sub_comm] using this
      have sourceHeight :
          |literalSource 2 - literalWitness 2| ≤
            delta * Real.sqrt 3 / 100 := by
        simpa [literalSource, literalWitness, proposition63AxialCoordinate]
          using proposition63AxialCoordinate_sub_le_of_mem_same_gridCube
            first.delta_pos
            (firstSticky.coarse.tube first.metricFiber.parent)
            firstSticky.coarse_extremal.delta_pos cell
            hsourceCell hwitnessCell
      have witnessHeight : literalWitness 2 ∈ Set.Icc
          (first.chartSelection.intervalBase interval / 100)
          (first.chartSelection.intervalBase interval / 100 + Delta / 100) := by
        change proposition63AxialCoordinate
            (firstSticky.coarse.tube first.metricFiber.parent)
            firstSticky.coarse_extremal.delta_pos witness ∈ _
        change proposition63AxialCoordinate
            (firstSticky.coarse.tube first.metricFiber.parent)
            firstSticky.coarse_extremal.delta_pos witness ∈
          Set.Ico ((interval.1 : ℝ) *
            proposition63LiteralSliceWidth Delta)
            (((interval.1 : ℝ) + 1) *
              proposition63LiteralSliceWidth Delta) at hwitnessSlab
        constructor
        · calc
            first.chartSelection.intervalBase interval / 100 =
                (interval.1 : ℝ) *
                  proposition63LiteralSliceWidth Delta := by
              unfold Proposition63ChartSelectionData.intervalBase
                proposition63LiteralSliceWidth
              ring
            _ ≤ _ := hwitnessSlab.1
        · calc
            _ ≤ ((interval.1 : ℝ) + 1) *
                proposition63LiteralSliceWidth Delta := hwitnessSlab.2.le
            _ = first.chartSelection.intervalBase interval / 100 +
                Delta / 100 := by
              unfold Proposition63ChartSelectionData.intervalBase
                proposition63LiteralSliceWidth
              ring
      have chartCoord : ∀ z : Point3, (chart.isometry z) 2 = z 2 :=
        fun z => chart.isometry_preserves_coord2 z
      rw [chartCoord]
      have triangle := abs_sub_le (100 * publicPoint 2)
        (100 * literalSource 2)
        (first.chartSelection.intervalBase interval)
      have secondTriangle := abs_sub_le (100 * literalSource 2)
        (100 * literalWitness 2)
        (first.chartSelection.intervalBase interval)
      have witnessBound :
          |100 * literalWitness 2 -
              first.chartSelection.intervalBase interval| ≤ Delta := by
        rw [abs_le]
        constructor <;> linarith [witnessHeight.1, witnessHeight.2]
      calc
        _ ≤ |100 * publicPoint 2 - 100 * literalSource 2| +
            |100 * literalSource 2 -
              first.chartSelection.intervalBase interval| := triangle
        _ ≤ 100 * (delta / firstScale.1) +
            (100 * (delta * Real.sqrt 3 / 100) + Delta) := by
          apply add_le_add
          · rw [show 100 * publicPoint 2 - 100 * literalSource 2 =
                100 * (publicPoint 2 - literalSource 2) by ring,
              abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
            exact mul_le_mul_of_nonneg_left targetHeight.le (by norm_num)
          · exact secondTriangle.trans <| add_le_add
              (by
                rw [show 100 * literalSource 2 - 100 * literalWitness 2 =
                    100 * (literalSource 2 - literalWitness 2) by ring,
                  abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
                exact mul_le_mul_of_nonneg_left sourceHeight (by norm_num))
              witnessBound
        _ = _ := by ring
  have slopeDistance :
        |slopes.slope (100 * (chart.isometry publicPoint) 2) -
            slopes.slope (first.chartSelection.intervalBase interval)| ≤
          (2520 * (Real.toNNReal coefficient : ℝ)) *
            (Delta + 100 * (delta / firstScale.1) +
              delta * Real.sqrt 3) := by
      have lip := slopes.lipschitz.dist_le_mul
        (100 * (chart.isometry publicPoint) 2)
        (first.chartSelection.intervalBase interval)
      rw [Real.dist_eq, Real.dist_eq] at lip
      exact lip.trans (mul_le_mul_of_nonneg_left heightClose (by positivity))
  have directionDifference :
        ‖globalGrainDirection
            (slopes.slope (100 * (chart.isometry publicPoint) 2)) -
          globalGrainDirection
            (slopes.slope (first.chartSelection.intervalBase interval))‖ =
        |slopes.slope (100 * (chart.isometry publicPoint) 2) -
          slopes.slope (first.chartSelection.intervalBase interval)| := by
      have heq :
          globalGrainDirection
                (slopes.slope (100 * (chart.isometry publicPoint) 2)) -
              globalGrainDirection
                (slopes.slope
                  (first.chartSelection.intervalBase interval)) =
            (slopes.slope (100 * (chart.isometry publicPoint) 2) -
              slopes.slope (first.chartSelection.intervalBase interval)) •
                EuclideanSpace.single (1 : Fin 3) 1 := by
        ext coordinate
        fin_cases coordinate <;>
          simp [globalGrainDirection, point3]
      rw [heq, norm_smul]
      simp [Real.norm_eq_abs]
  have slopePart :
        |inner ℝ (chart.isometry literalWitness)
              (globalGrainDirection
                (slopes.slope (100 * (chart.isometry publicPoint) 2))) -
            inner ℝ (chart.isometry literalWitness)
              (globalGrainDirection
                (slopes.slope (first.chartSelection.intervalBase interval)))| ≤
          3 * ((2520 * (Real.toNNReal coefficient : ℝ)) *
            (Delta + 100 * (delta / firstScale.1) +
              delta * Real.sqrt 3)) := by
      rw [← inner_sub_right]
      calc
        _ ≤ ‖chart.isometry literalWitness‖ *
            ‖globalGrainDirection
                (slopes.slope (100 * (chart.isometry publicPoint) 2)) -
              globalGrainDirection
                (slopes.slope
                  (first.chartSelection.intervalBase interval))‖ :=
          abs_real_inner_le_norm _ _
        _ ≤ 3 * ((2520 * (Real.toNNReal coefficient : ℝ)) *
            (Delta + 100 * (delta / firstScale.1) +
              delta * Real.sqrt 3)) := by
          rw [directionDifference]
          gcongr
  have triangle := abs_sub_le
      (inner ℝ (chart.isometry publicPoint)
        (globalGrainDirection
          (slopes.slope (100 * (chart.isometry publicPoint) 2))))
      (inner ℝ (chart.isometry literalWitness)
        (globalGrainDirection
          (slopes.slope (100 * (chart.isometry publicPoint) 2))))
      reference
  have referenceEq : inner ℝ (chart.isometry literalWitness)
        (globalGrainDirection
          (slopes.slope (first.chartSelection.intervalBase interval))) =
        reference := by
      dsimp only [reference]
      have hdir : chart.isometry
          (chart.direction
            (slopes.slope (first.chartSelection.intervalBase interval))) =
          globalGrainDirection
            (slopes.slope (first.chartSelection.intervalBase interval)) := by
        rw [← chart.isometry_globalGrainDirection]
        exact chart.isometry_involutive _
      rw [← hdir]
      exact chart.isometry.inner_map_map literalWitness _
  have secondBound :
      |inner ℝ (chart.isometry literalWitness)
            (globalGrainDirection
              (slopes.slope (100 * (chart.isometry publicPoint) 2))) -
          reference| ≤
        3 * ((2520 * (Real.toNNReal coefficient : ℝ)) *
          (Delta + 100 * (delta / firstScale.1) +
            delta * Real.sqrt 3)) := by
    rw [← referenceEq]
    exact slopePart
  have projectionBound :
        |inner ℝ (chart.isometry publicPoint)
              (globalGrainDirection
                (slopes.slope (100 * (chart.isometry publicPoint) 2))) -
            reference| ≤
          Proposition63ChartSelectionData.proposition63WholeCellExactSliceError
            delta firstScale.1 Delta coefficient := by
      have slopeTermNonneg :
          0 ≤ (2520 * (Real.toNNReal coefficient : ℝ)) *
            (Delta + 100 * (delta / firstScale.1) +
              delta * Real.sqrt 3) := by
        apply mul_nonneg (by positivity)
        exact add_nonneg
          (add_nonneg first.Delta_pos.le
            (mul_nonneg (by norm_num)
              (div_nonneg first.delta_pos.le
                (first.delta_pos.trans_le firstScale.2.1).le)))
          (mul_nonneg first.delta_pos.le (Real.sqrt_nonneg 3))
      calc
        _ ≤
            |inner ℝ (chart.isometry publicPoint)
                (globalGrainDirection
                  (slopes.slope (100 * (chart.isometry publicPoint) 2))) -
              inner ℝ (chart.isometry literalWitness)
                (globalGrainDirection
                  (slopes.slope (100 * (chart.isometry publicPoint) 2)))| +
            |inner ℝ (chart.isometry literalWitness)
                (globalGrainDirection
                  (slopes.slope (100 * (chart.isometry publicPoint) 2))) -
              reference| := triangle
        _ ≤ 4 * wholeCellPublicError (delta := delta)
              (firstScale := firstScale) +
            3 * ((2520 * (Real.toNNReal coefficient : ℝ)) *
              (Delta + 100 * (delta / firstScale.1) +
                delta * Real.sqrt 3)) := add_le_add spatial secondBound
        _ ≤ Proposition63ChartSelectionData.proposition63WholeCellExactSliceError
              delta firstScale.1 Delta coefficient := by
          unfold Proposition63ChartSelectionData.proposition63WholeCellExactSliceError
            wholeCellPublicError
          nlinarith
  exact ⟨projectionBound, heightClose⟩

end Proposition63FirstChartData
end Kakeya.Assouad.PureWZ2
end
