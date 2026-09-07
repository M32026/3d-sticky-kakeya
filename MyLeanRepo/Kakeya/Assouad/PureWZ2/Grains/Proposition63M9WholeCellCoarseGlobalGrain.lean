import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9WholeCellGlobalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9RobustRootAdapter

/-! # Coarse global slices for the M9 whole-cell source -/

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

/-- A Lemma-4.4 coarse point is close to the bounded union of old source
slabs even when its source is the canonical whole-cell trace ambient. -/
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
              first.chartSelection.intervalBase interval)| := by ring_nf
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
        apply mul_le_mul
        · simpa [dist_eq_norm] using pointDistance
        · exact pointDirectionNorm
        · positivity
        · exact mul_nonneg (Real.sqrt_nonneg 3) first.Delta_pos.le
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
        rw [show height = point 2 from hpoint.2.symm,
          show 100 * point 2 - 100 * finePoint 2 =
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
    have ratioPos : 0 < delta / firstScale.1 :=
      div_pos first.delta_pos (first.delta_pos.trans_le firstScale.2.1)
    have deltaNonneg : 0 ≤ delta := first.delta_pos.le
    have DeltaNonneg : 0 ≤ Delta := first.Delta_pos.le
    have coefficientNonneg : 0 ≤ (Real.toNNReal coefficient : ℝ) := by positivity
    have sqrtPos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    change 0 <
      Proposition63ChartSelectionData.proposition63WholeCellExactSliceError
          delta firstScale.1 Delta coefficient +
        4 * (Real.sqrt 3 * Delta) +
        3 * (252000 * (Real.toNNReal coefficient : ℝ) * Delta)
    unfold Proposition63ChartSelectionData.proposition63WholeCellExactSliceError
    positivity)
  simpa only [hsecondScale,
    Proposition63ChartSelectionData.proposition63WholeCellCoarseGlobalADConstant]
    using thick

end Proposition63FirstChartData

variable
    {delta Delta sigma stickyLoss localLoss commonSliceLoss chartLoss
      tau epsilon₁ epsilon₃ coefficient initialInputLoss initialOutputLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {firstScale : WZ2PaperRequestedScale delta}
    {logExponent normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialOutputLoss) initialSource normalizationExponent}
    {firstSticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      initialNormalized.croppedRefined firstScale logExponent}
    {retainedFactor : ENNReal}
    {first : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := coefficient)
      firstSticky Delta retainedFactor}

/-- Direct pre-grain constructor once the whole-cell global AD cost has been
absorbed.  Local grains and the global slope remain attached to the same
outer robust middle. -/
theorem Proposition63M9RobustMiddleData.preGrainWholeCellWithPlaneMap
    {outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {denseNormalizationExponent : ℕ}
    {output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := chartLoss)
      (first.wholeCellShading initialNormalized)
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos}
    {massLower :
      Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
          output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2)) *
          (first.wholeCellOrdinaryTrace initialNormalized).mass}
    {pre : Proposition63PreLemma43DenseRootData
      (first.wholeCellTraceOrdinarySource initialNormalized output massLower)
      (first.wholeCellTraceAmbient initialNormalized output massLower)
      cutoff.twoCall.schedule.first.sourceLoss
      cutoff.twoCall.schedule.first.normalizationLoss
      denseNormalizationExponent}
    {hr : 0 < delta / firstScale.1}
    {hrRobust : delta / firstScale.1 ≤ cutoff.twoCall.rootCutoff}
    (middle : Proposition63M9RobustMiddleData cutoff
      (pre.robustRoot cutoff hr hrRobust) hr hrRobust)
    (slopes : first.chartSelection.Proposition63SlopeData)
    (hfirstScale : firstScale.1 = Delta)
    (hsecondScale :
      (cutoff.twoCall.secondQRequested hr hrRobust).1 = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hglobalCost :
      Proposition63ChartSelectionData.proposition63WholeCellCoarseGlobalADConstant
          delta firstScale.1 Delta localLoss coefficient ≤
        Kakeya.realRpowENN
          (cutoff.twoCall.secondQRequested hr hrRobust).1
          (-hierarchy.preGrainLoss)) :
    ∃ preGrain : PureWZ2GeneralPreGrainData
        middle.second.lemma412.shading sigma hierarchy.preGrainLoss
        (Real.toNNReal (Real.rpow
          (cutoff.twoCall.secondQRequested hr hrRobust).1
          (-hierarchy.lemma47Loss)))
        (252000 * Real.toNNReal coefficient) 1,
      (∀ point, preGrain.planeMap point =
          middle.second.lemma412.localGrains.planeMap point) ∧
        ∀ height, preGrain.slope height = slopes.slope (100 * height) := by
  let normalizedSlope : ℝ → ℝ := fun height => slopes.slope (100 * height)
  have slopeLipschitz : LipschitzWith
      (252000 * Real.toNNReal coefficient) normalizedSlope := by
    apply LipschitzWith.of_dist_le_mul
    intro left right
    have raw := slopes.lipschitz.dist_le_mul (100 * left) (100 * right)
    change dist (slopes.slope (100 * left)) (slopes.slope (100 * right)) ≤
      ((252000 * Real.toNNReal coefficient : NNReal) : ℝ) * dist left right
    calc
      _ ≤ ((2520 * Real.toNNReal coefficient : NNReal) : ℝ) *
          dist (100 * left) (100 * right) := raw
      _ = _ := by
        simp only [Real.dist_eq]
        rw [show 100 * left - 100 * right = 100 * (left - right) by ring,
          abs_mul]
        norm_num
        ring
  have sourceUnion : middle.preparation.prepared.restrictedLemma43.shading.union ⊆
      (first.wholeCellTraceAmbient initialNormalized output massLower).union :=
    middle.preparation.prepared.restrictedLemma43_union_subset_source.trans
      pre.denseUnionSubsetAmbient
  have targetTop : Kakeya.realRpowENN
      (cutoff.twoCall.secondQRequested hr hrRobust).1
      (-hierarchy.preGrainLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  refine ⟨{
    planeMap := middle.second.lemma412.localGrains.planeMap
    planeMap_lipschitz := middle.second.lemma412.localGrains.planeMap_lipschitz
    planeMap_unit := middle.second.lemma412.localGrains.planeMap_unit
    planeMap_incidence := by
      intro index point hpoint
      simpa using middle.second.lemma412.localGrains.planeMap_incidence
        index point hpoint
    slope := normalizedSlope
    slope_lipschitz := slopeLipschitz.lipschitzOnWith
    local_ad := middle.second.lemma412.localGrains.local_ad
    global_ad := ?_
  }, ?_, ?_⟩
  · intro height hheight
    have sourceAD := first.lemma44_horizontal_slice_wholeCell_ad
      initialNormalized output massLower slopes middle.second.lemma44 sourceUnion
        hfirstScale hsecondScale hsigma hsigmaOne height
    have selected : PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (normalizedSlope height))
          (horizontalSlice middle.second.lemma412.shading.union height))
        (cutoff.twoCall.secondQRequested hr hrRobust).1 (1 - sigma)
        (Proposition63ChartSelectionData.proposition63WholeCellCoarseGlobalADConstant
          delta firstScale.1 Delta localLoss coefficient) := by
      have sourceAD' : PureWZ2PaperADSet1
          (scalarProjection
            (globalGrainDirection (normalizedSlope height))
            (horizontalSlice middle.second.lemma44.coarseShading.union height))
          (cutoff.twoCall.secondQRequested hr hrRobust).1 (1 - sigma)
          (Proposition63ChartSelectionData.proposition63WholeCellCoarseGlobalADConstant
            delta firstScale.1 Delta localLoss coefficient) := by
        simpa only [hsecondScale] using sourceAD
      apply sourceAD'.mono_set
      apply Set.image_mono
      apply Set.inter_subset_inter_left
      rintro point ⟨index, hpoint⟩
      exact ⟨index, middle.second.lemma47.subshading index
        (middle.second.lemma412.subshading index hpoint)⟩
    exact selected.mono_const hglobalCost targetTop
  · intro point
    rfl
  · intro height
    rfl

/-- Compatibility projection of the construction-aware whole-cell pre-grain
producer. -/
theorem Proposition63M9RobustMiddleData.preGrainWholeCell
    {outputLoss : ℝ}
    {hierarchy : Proposition63M9PreRuntimeHierarchy sigma outputLoss}
    {cutoff : Proposition63M9PreNode3CutoffData hierarchy}
    {denseNormalizationExponent : ℕ}
    {output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := chartLoss)
      (first.wholeCellShading initialNormalized)
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos}
    {massLower :
      Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
          output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2)) *
          (first.wholeCellOrdinaryTrace initialNormalized).mass}
    {pre : Proposition63PreLemma43DenseRootData
      (first.wholeCellTraceOrdinarySource initialNormalized output massLower)
      (first.wholeCellTraceAmbient initialNormalized output massLower)
      cutoff.twoCall.schedule.first.sourceLoss
      cutoff.twoCall.schedule.first.normalizationLoss
      denseNormalizationExponent}
    {hr : 0 < delta / firstScale.1}
    {hrRobust : delta / firstScale.1 ≤ cutoff.twoCall.rootCutoff}
    (middle : Proposition63M9RobustMiddleData cutoff
      (pre.robustRoot cutoff hr hrRobust) hr hrRobust)
    (slopes : first.chartSelection.Proposition63SlopeData)
    (hfirstScale : firstScale.1 = Delta)
    (hsecondScale :
      (cutoff.twoCall.secondQRequested hr hrRobust).1 = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hglobalCost :
      Proposition63ChartSelectionData.proposition63WholeCellCoarseGlobalADConstant
          delta firstScale.1 Delta localLoss coefficient ≤
        Kakeya.realRpowENN
          (cutoff.twoCall.secondQRequested hr hrRobust).1
          (-hierarchy.preGrainLoss)) :
    Nonempty (PureWZ2GeneralPreGrainData
      middle.second.lemma412.shading sigma hierarchy.preGrainLoss
      (Real.toNNReal (Real.rpow
        (cutoff.twoCall.secondQRequested hr hrRobust).1
        (-hierarchy.lemma47Loss)))
      (252000 * Real.toNNReal coefficient) 1) := by
  rcases middle.preGrainWholeCellWithPlaneMap slopes hfirstScale hsecondScale
      hsigma hsigmaOne hglobalCost with ⟨preGrain, _, _⟩
  exact ⟨preGrain⟩

end Kakeya.Assouad.PureWZ2
end
