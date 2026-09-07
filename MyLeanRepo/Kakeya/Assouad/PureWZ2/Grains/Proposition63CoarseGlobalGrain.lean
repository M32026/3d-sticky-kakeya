import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma412
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63GlobalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperADGeneralizedThickening
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GeneralPreGrainData

/-!
# Global slice AD on the Proposition 6.3 Lemma 4.4 coarse pair

Every coarse cube retained by Lemma 4.4 contains a point of the fine
chart-normalized shading.  The fine point belongs to one of the retained
Proposition 6.3 slabs.  Same-cell geometry and the Lipschitz slope therefore
place the exact coarse slice in a fixed thickening of only finitely many
neighboring slab projections.  This is the paper's argument in lines
269--315.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

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

/-- Intervals which can contribute to a coarse exact slice after moving once
inside a `Delta`-cube. -/
def coarseNearbyIntervals
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (height : ℝ) : Finset
      (commonSliceIntervalType (proposition63LiteralSliceWidth Delta)) :=
  selection.intervals.filter fun interval =>
    |100 * height - selection.intervalBase interval| ≤
      101 * Delta + 100 * (delta / rho)

lemma coarseNearbyIntervals_card_le
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta)
    (height : ℝ) :
    (selection.coarseNearbyIntervals height).card ≤ 403 := by
  have hratioDelta : delta / rho ≤ Delta := by
    rw [hrhoDelta]
    exact (div_le_iff₀ hDelta).2 (by
      simpa [pow_two, mul_comm] using hdeltaDelta)
  let center : ℤ := ⌊(100 * height) / Delta⌋
  let target : Finset ℤ := Finset.Icc (center - 201) (center + 201)
  have hmap : Set.MapsTo
      (fun interval : commonSliceIntervalType
        (proposition63LiteralSliceWidth Delta) => interval.1)
      (selection.coarseNearbyIntervals height : Set _) (target : Set ℤ) := by
    intro interval hinterval
    have hclose := (Finset.mem_filter.mp hinterval).2
    have hclose' :
        |100 * height - selection.intervalBase interval| ≤ 201 * Delta := by
      calc
        _ ≤ 101 * Delta + 100 * (delta / rho) := hclose
        _ ≤ 101 * Delta + 100 * Delta := by gcongr
        _ = 201 * Delta := by ring
    have hbounds := abs_le.mp hclose'
    have hcenterLower : (center : ℝ) * Delta ≤ 100 * height := by
      have := Int.floor_le ((100 * height) / Delta)
      dsimp only [center]
      exact (le_div_iff₀ hDelta).1 this
    have hcenterUpper : 100 * height < ((center : ℝ) + 1) * Delta := by
      have := Int.lt_floor_add_one ((100 * height) / Delta)
      dsimp only [center]
      exact (div_lt_iff₀ hDelta).1 this
    have hlowerReal : ((center - 201 : ℤ) : ℝ) ≤ (interval.1 : ℝ) := by
      have hmul : (((center - 201 : ℤ) : ℝ) * Delta) ≤
          (interval.1 : ℝ) * Delta := by
        simp only [Int.cast_sub, Int.cast_ofNat]
        unfold intervalBase at hbounds
        nlinarith [hbounds.2]
      exact le_of_mul_le_mul_right hmul hDelta
    have hupperReal : (interval.1 : ℝ) < ((center + 202 : ℤ) : ℝ) := by
      have hmul : (interval.1 : ℝ) * Delta <
          (((center + 202 : ℤ) : ℝ) * Delta) := by
        simp only [Int.cast_add, Int.cast_ofNat]
        unfold intervalBase at hbounds
        nlinarith [hbounds.1]
      exact lt_of_mul_lt_mul_right hmul hDelta.le
    have hlower : center - 201 ≤ interval.1 := by exact_mod_cast hlowerReal
    have hupperStrict : interval.1 < center + 202 := by
      exact_mod_cast hupperReal
    have hupper : interval.1 ≤ center + 201 := by omega
    exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩
  have hinjective : Set.InjOn
      (fun interval : commonSliceIntervalType
        (proposition63LiteralSliceWidth Delta) => interval.1)
      (selection.coarseNearbyIntervals height : Set _) := by
    intro first _ second _ heq
    exact Subtype.ext heq
  have hcard := Finset.card_le_card_of_injOn
    (fun interval : commonSliceIntervalType
      (proposition63LiteralSliceWidth Delta) => interval.1)
    hmap hinjective
  have htargetCard : target.card = 403 := by
    have hle : center - 201 ≤ center + 201 + 1 := by omega
    have hcardInt : (target.card : ℤ) =
        (center + 201) + 1 - (center - 201) :=
      Int.card_Icc_of_le (center - 201) (center + 201) hle
    have : (target.card : ℤ) = 403 := by
      rw [hcardInt]
      ring
    exact_mod_cast this
  simpa [htargetCard] using hcard

/-- A point of the chart-normalized fine shading has the same slab
provenance as its inverse-chart public point. -/
lemma normalized_point_near_literal_slab
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {rescaledLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection rescaledLoss)
    (slopes : Proposition63SlopeData selection)
    (point : Point3)
    (hpoint : point ∈ (selection.normalizedShading rescaled).union) :
    ∃ interval ∈ selection.intervals,
      ∃ reference ∈ scalarProjection
        (selection.chartLabel.chart.direction
          (slopes.slope (selection.intervalBase interval)))
        (selection.literalSourceSlab interval),
      |inner ℝ point
          (globalGrainDirection (slopes.slope (100 * point 2))) -
        reference| ≤
          proposition63ExactSliceError delta rho Delta coefficient ∧
      |100 * point 2 - selection.intervalBase interval| ≤
        Delta + 100 * (delta / rho) := by
  change point ∈
    (selection.chartLabel.chart.transportPaperShading
      rescaled.publicShading).union at hpoint
  rw [selection.chartLabel.chart.transportPaperShading_union] at hpoint
  rcases hpoint with ⟨publicPoint, hpublicPoint, rfl⟩
  have hslice : publicPoint ∈
      horizontalSlice rescaled.publicShading.union (publicPoint 2) :=
    ⟨hpublicPoint, rfl⟩
  rcases selection.public_horizontal_slice_near_literal_slab
      rescaled slopes (publicPoint 2)
      ⟨publicPoint, hslice, rfl⟩ with
    ⟨interval, hinterval, reference, hreference, hclose, hheight⟩
  refine ⟨interval, hinterval, reference, hreference, ?_, ?_⟩
  · have hdirection : selection.chartLabel.chart.isometry
        (selection.chartLabel.chart.direction
          (slopes.slope (100 * publicPoint 2))) =
        globalGrainDirection (slopes.slope (100 * publicPoint 2)) := by
      rw [← selection.chartLabel.chart.isometry_globalGrainDirection]
      exact selection.chartLabel.chart.isometry_involutive _
    have hinner : inner ℝ
        (selection.chartLabel.chart.isometry publicPoint)
        (globalGrainDirection (slopes.slope (100 * publicPoint 2))) =
      inner ℝ publicPoint
        (selection.chartLabel.chart.direction
          (slopes.slope (100 * publicPoint 2))) := by
      rw [← hdirection]
      exact selection.chartLabel.chart.isometry.inner_map_map _ _
    simpa [hinner, selection.chartLabel.chart.isometry_preserves_coord2]
      using hclose
  · simpa [selection.chartLabel.chart.isometry_preserves_coord2] using hheight

/-- The finite union of source slabs relevant to one coarse exact slice has
paper AD with a uniform absolute loss. -/
lemma coarse_nearby_literal_slabs_ad
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (slopes : Proposition63SlopeData selection)
    (hrhoDelta : rho = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (height : ℝ) :
    PureWZ2PaperADSet1
      {value | ∃ interval ∈ selection.coarseNearbyIntervals height,
        value ∈ scalarProjection
          (selection.chartLabel.chart.direction
            (slopes.slope (selection.intervalBase interval)))
          (selection.literalSourceSlab interval)}
      Delta (1 - sigma)
      (404 * (1 + proposition63SlabADConstant delta localLoss)) := by
  let sourceConstant := proposition63SlabADConstant delta localLoss
  let targetConstant : ENNReal := 1 + sourceConstant
  have hsourceTop : sourceConstant ≠ ⊤ := by
    simp [sourceConstant, proposition63SlabADConstant,
      Kakeya.realRpowENN, ENNReal.mul_eq_top]
  have htargetOne : (1 : ENNReal) ≤ targetConstant :=
    le_add_right le_rfl
  have htargetTop : targetConstant ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨by norm_num, hsourceTop⟩
  have hpiece : ∀ interval ∈ selection.coarseNearbyIntervals height,
      PureWZ2PaperADSet1
        (scalarProjection
          (selection.chartLabel.chart.direction
            (slopes.slope (selection.intervalBase interval)))
          (selection.literalSourceSlab interval))
        Delta (1 - sigma) targetConstant := by
    intro interval hinterval
    have hselected := (Finset.mem_filter.mp hinterval).1
    have hAD := selection.literalSourceSlab_slope_ad
      slopes hrhoDelta interval hselected
    exact hAD.mono_const (le_add_left le_rfl) htargetTop
  have hunion := PureWZ2PaperADSet1.finset_biUnion
    hDelta (by linarith) (by linarith) htargetOne htargetTop hpiece
  have hcard := selection.coarseNearbyIntervals_card_le hrhoDelta height
  have hconstant :
      (((selection.coarseNearbyIntervals height).card : ENNReal) + 1) *
          targetConstant ≤ 404 * targetConstant := by
    gcongr
    exact_mod_cast (show
      (selection.coarseNearbyIntervals height).card + 1 ≤ 404 by omega)
  have hfixed := hunion.mono_const hconstant
    (ENNReal.mul_ne_top (by norm_num) htargetTop)
  simpa only [sourceConstant, targetConstant] using hfixed

/-- Total projection error when a coarse exact-slice point is replaced by
its Lemma 4.4 fine witness in the same `Delta`-cube. -/
def proposition63CoarseExactSliceError
    (delta rho Delta coefficient : ℝ) : ℝ :=
  proposition63ExactSliceError delta rho Delta coefficient +
    4 * (Real.sqrt 3 * Delta) +
    3 * (252000 * (Real.toNNReal coefficient : ℝ) * Delta)

/-- The pre-absorption global AD constant on the Lemma 4.4 coarse pair. -/
def proposition63CoarseGlobalADConstant
    (delta rho Delta localLoss coefficient : ℝ) : ENNReal :=
  (2 * (Nat.ceil
      (proposition63CoarseExactSliceError
        delta rho Delta coefficient / Delta) + 1) : ENNReal) ^ 2 *
    (404 * (1 + proposition63SlabADConstant delta localLoss))

/-- The exact slice of the Lemma 4.4 coarse shading is contained in a fixed
thickening of the bounded union of the original fine slab projections. -/
lemma lemma44_horizontal_slice_subset_coarse_nearby_thickening_of_source_union
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {rescaledLoss lemma43SourceLoss lemma43Loss sticky2Loss lemma44Loss : ℝ}
    {logExponent : ℕ}
    (rescaled : Proposition63ChartRescaledData selection rescaledLoss)
    (slopes : Proposition63SlopeData selection)
    {secondScale : WZ2PaperRequestedScale (delta / rho)}
    {secondFamily : Kakeya.Streamlined.TubeFamily (delta / rho)}
    {lemma43Source : WZ1PaperTubeShading secondFamily}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss)
      lemma43Source (secondScale.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sticky2Loss)
      lemma43.shading secondScale logExponent}
    (lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss)
    (hsourceUnion : lemma43Source.union ⊆
      (selection.normalizedShading rescaled).union)
    (hsecondDelta : secondScale.1 = Delta)
    (height : ℝ) :
    ∀ value ∈ scalarProjection
      (globalGrainDirection (slopes.slope (100 * height)))
      (horizontalSlice lemma44.coarseShading.union height),
      ∃ reference ∈
        {value | ∃ interval ∈ selection.coarseNearbyIntervals height,
          value ∈ scalarProjection
            (selection.chartLabel.chart.direction
              (slopes.slope (selection.intervalBase interval)))
            (selection.literalSourceSlab interval)},
        |value - reference| ≤
          proposition63CoarseExactSliceError
            delta rho Delta coefficient := by
  rintro value ⟨point, hpoint, rfl⟩
  rcases lemma44.coarse_point_has_fine_witness point hpoint.1 with
    ⟨finePoint, hfinePoint, hsameCell⟩
  have hfineSource : finePoint ∈
      (selection.normalizedShading rescaled).union := by
    rcases hfinePoint with ⟨index, hindex⟩
    apply hsourceUnion
    exact ⟨sticky.selected.embedding index,
      lemma44.fine_subshading index finePoint hindex⟩
  rcases selection.normalized_point_near_literal_slab rescaled slopes
      finePoint hfineSource with
    ⟨interval, hinterval, reference, hreference, hfineProjection,
      hfineHeight⟩
  have hpointCell : point ∈ wz1PaperGridCube secondScale.1
      (wz1PaperGridIndex secondScale.1 point) :=
    (mem_wz1PaperGridCube _ _ _).2 rfl
  have hfineCell : finePoint ∈ wz1PaperGridCube secondScale.1
      (wz1PaperGridIndex secondScale.1 point) :=
    (mem_wz1PaperGridCube _ _ _).2 hsameCell
  have hpointDistance : dist point finePoint ≤ Real.sqrt 3 * Delta := by
    have hraw := wz1PaperGridCube_diameter
      (by simpa [hsecondDelta] using hDelta)
      (wz1PaperGridIndex secondScale.1 point) hpointCell hfineCell
    simpa [hsecondDelta, mul_comm] using hraw
  have hheightDistance : |point 2 - finePoint 2| < Delta := by
    have hraw := samePaperGridIndex_coord_two_lt
      (by simpa [hsecondDelta] using hDelta) hsameCell.symm
    simpa [hsecondDelta, abs_sub_comm] using hraw
  have hnear : interval ∈ selection.coarseNearbyIntervals height := by
    apply Finset.mem_filter.mpr
    refine ⟨hinterval, ?_⟩
    rw [← hpoint.2]
    calc
      |100 * point 2 - selection.intervalBase interval| =
          |100 * (point 2 - finePoint 2) +
            (100 * finePoint 2 - selection.intervalBase interval)| := by
              rw [hpoint.2]
              ring
      _ ≤ |100 * (point 2 - finePoint 2)| +
          |100 * finePoint 2 - selection.intervalBase interval| :=
        abs_add_le _ _
      _ ≤ 100 * Delta + (Delta + 100 * (delta / rho)) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
        exact add_le_add
          (mul_le_mul_of_nonneg_left hheightDistance.le (by norm_num))
          hfineHeight
      _ = 101 * Delta + 100 * (delta / rho) := by ring
  refine ⟨reference, ⟨interval, hnear, hreference⟩, ?_⟩
  let pointDirection :=
    globalGrainDirection (slopes.slope (100 * height))
  let fineDirection :=
    globalGrainDirection (slopes.slope (100 * finePoint 2))
  have hpointDirectionNorm : ‖pointDirection‖ ≤ 4 :=
    globalGrainDirection_norm_le_4 (slopes.bounded _)
  have hfineNorm : ‖finePoint‖ ≤ 3 :=
    paperShadingPoint_norm_le_three hfineSource
  have hspatial :
      |inner ℝ point pointDirection - inner ℝ finePoint pointDirection| ≤
        4 * (Real.sqrt 3 * Delta) := by
    rw [← inner_sub_left]
    calc
      |inner ℝ (point - finePoint) pointDirection| ≤
          ‖point - finePoint‖ * ‖pointDirection‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (Real.sqrt 3 * Delta) * 4 := by
        gcongr
        simpa [dist_eq_norm] using hpointDistance
      _ = 4 * (Real.sqrt 3 * Delta) := by ring
  have hslopeDistance :
      |slopes.slope (100 * height) -
          slopes.slope (100 * finePoint 2)| ≤
        252000 * (Real.toNNReal coefficient : ℝ) * Delta := by
    have hlip := slopes.lipschitz.dist_le_mul
      (100 * height) (100 * finePoint 2)
    rw [Real.dist_eq, Real.dist_eq] at hlip
    calc
      |slopes.slope (100 * height) -
          slopes.slope (100 * finePoint 2)| ≤
        (2520 * (Real.toNNReal coefficient : ℝ)) *
          |100 * height - 100 * finePoint 2| := by simpa using hlip
      _ = (252000 * (Real.toNNReal coefficient : ℝ)) *
          |point 2 - finePoint 2| := by
        have hheightEq : height = point 2 := hpoint.2.symm
        rw [hheightEq, show 100 * point 2 - 100 * finePoint 2 =
          100 * (point 2 - finePoint 2) by ring, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 100)]
        ring
      _ ≤ 252000 * (Real.toNNReal coefficient : ℝ) * Delta := by
        gcongr
  have hdirectionDifference : ‖pointDirection - fineDirection‖ =
      |slopes.slope (100 * height) -
        slopes.slope (100 * finePoint 2)| := by
    have heq : pointDirection - fineDirection =
        (slopes.slope (100 * height) -
          slopes.slope (100 * finePoint 2)) •
            EuclideanSpace.single (1 : Fin 3) 1 := by
      ext coordinate
      fin_cases coordinate <;>
        simp [pointDirection, fineDirection, globalGrainDirection]
    rw [heq, norm_smul]
    simp [Real.norm_eq_abs]
  have hslopeProjection :
      |inner ℝ finePoint pointDirection -
          inner ℝ finePoint fineDirection| ≤
        3 * (252000 * (Real.toNNReal coefficient : ℝ) * Delta) := by
    rw [← inner_sub_right]
    calc
      |inner ℝ finePoint (pointDirection - fineDirection)| ≤
          ‖finePoint‖ * ‖pointDirection - fineDirection‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ 3 * (252000 * (Real.toNNReal coefficient : ℝ) * Delta) := by
        rw [hdirectionDifference]
        gcongr
  have htriangle := abs_sub_le
    (inner ℝ point pointDirection)
    (inner ℝ finePoint pointDirection) reference
  have htriangleTwo := abs_sub_le
    (inner ℝ finePoint pointDirection)
    (inner ℝ finePoint fineDirection) reference
  have htotal :
      |inner ℝ point pointDirection - reference| ≤
        4 * (Real.sqrt 3 * Delta) +
          (3 * (252000 * (Real.toNNReal coefficient : ℝ) * Delta) +
            proposition63ExactSliceError delta rho Delta coefficient) := by
    exact htriangle.trans <| add_le_add hspatial <|
      htriangleTwo.trans (add_le_add hslopeProjection hfineProjection)
  simpa [pointDirection, fineDirection, proposition63CoarseExactSliceError,
    add_assoc, add_left_comm, add_comm] using htotal

/-- The same coarse-slice containment when the second Lemma 4.3 is run on
the full first normalized family. -/
lemma lemma44_horizontal_slice_subset_coarse_nearby_thickening
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {rescaledLoss lemma43Loss sticky2Loss lemma44Loss : ℝ}
    {logExponent : ℕ}
    (rescaled : Proposition63ChartRescaledData selection rescaledLoss)
    (slopes : Proposition63SlopeData selection)
    {secondScale : WZ2PaperRequestedScale (delta / rho)}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := rescaledLoss)
      (targetLoss := lemma43Loss)
      (selection.normalizedShading rescaled) (secondScale.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sticky2Loss)
      lemma43.shading secondScale logExponent}
    (lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss)
    (hsecondDelta : secondScale.1 = Delta)
    (height : ℝ) :
    ∀ value ∈ scalarProjection
      (globalGrainDirection (slopes.slope (100 * height)))
      (horizontalSlice lemma44.coarseShading.union height),
      ∃ reference ∈
        {value | ∃ interval ∈ selection.coarseNearbyIntervals height,
          value ∈ scalarProjection
            (selection.chartLabel.chart.direction
              (slopes.slope (selection.intervalBase interval)))
            (selection.literalSourceSlab interval)},
        |value - reference| ≤
          proposition63CoarseExactSliceError
            delta rho Delta coefficient := by
  exact selection.lemma44_horizontal_slice_subset_coarse_nearby_thickening_of_source_union
    rescaled slopes lemma44 (fun _ hpoint => hpoint) hsecondDelta height

/-- Exact-slice AD on the Lemma 4.4 coarse shading. -/
theorem lemma44_horizontal_slice_ad_of_source_union
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {rescaledLoss lemma43SourceLoss lemma43Loss sticky2Loss lemma44Loss : ℝ}
    {logExponent : ℕ}
    (rescaled : Proposition63ChartRescaledData selection rescaledLoss)
    (slopes : Proposition63SlopeData selection)
    {secondScale : WZ2PaperRequestedScale (delta / rho)}
    {secondFamily : Kakeya.Streamlined.TubeFamily (delta / rho)}
    {lemma43Source : WZ1PaperTubeShading secondFamily}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss)
      lemma43Source (secondScale.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sticky2Loss)
      lemma43.shading secondScale logExponent}
    (lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss)
    (hsourceUnion : lemma43Source.union ⊆
      (selection.normalizedShading rescaled).union)
    (hsecondDelta : secondScale.1 = Delta)
    (hrhoDelta : rho = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (height : ℝ) :
    PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (slopes.slope (100 * height)))
        (horizontalSlice lemma44.coarseShading.union height))
      secondScale.1 (1 - sigma)
      (proposition63CoarseGlobalADConstant
        delta rho Delta localLoss coefficient) := by
  have hsource := selection.coarse_nearby_literal_slabs_ad
    slopes hrhoDelta hsigma hsigmaOne height
  have hclose :=
    selection.lemma44_horizontal_slice_subset_coarse_nearby_thickening_of_source_union
      rescaled slopes lemma44 hsourceUnion hsecondDelta height
  have hthick := hsource.generalized_thickening hclose
    (by
      unfold proposition63CoarseExactSliceError proposition63ExactSliceError
      have hratio : 0 < delta / rho := div_pos hdelta hrho
      positivity)
  simpa only [hsecondDelta, proposition63CoarseGlobalADConstant] using hthick

/-- Exact-slice AD in the unchanged-family special case. -/
theorem lemma44_horizontal_slice_ad
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {rescaledLoss lemma43Loss sticky2Loss lemma44Loss : ℝ}
    {logExponent : ℕ}
    (rescaled : Proposition63ChartRescaledData selection rescaledLoss)
    (slopes : Proposition63SlopeData selection)
    {secondScale : WZ2PaperRequestedScale (delta / rho)}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := rescaledLoss)
      (targetLoss := lemma43Loss)
      (selection.normalizedShading rescaled) (secondScale.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sticky2Loss)
      lemma43.shading secondScale logExponent}
    (lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss)
    (hsecondDelta : secondScale.1 = Delta)
    (hrhoDelta : rho = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (height : ℝ) :
    PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (slopes.slope (100 * height)))
        (horizontalSlice lemma44.coarseShading.union height))
      secondScale.1 (1 - sigma)
      (proposition63CoarseGlobalADConstant
        delta rho Delta localLoss coefficient) := by
  exact selection.lemma44_horizontal_slice_ad_of_source_union
    rescaled slopes lemma44 (fun _ hpoint => hpoint) hsecondDelta hrhoDelta
    hsigma hsigmaOne height

/-- Combine the paper's global slice argument with its Lemma 4.12 local
grains on the same final coarse shading.  This is the direct input to the
popular-box mild rescaling. -/
theorem proposition63_lemma412_pregrain_of_source_union
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {rescaledLoss lemma43SourceLoss lemma43Loss sticky2Loss lemma44Loss lemma47Loss
      outputLoss coefficient47 : ℝ}
    {logExponent : ℕ}
    (rescaled : Proposition63ChartRescaledData selection rescaledLoss)
    (slopes : Proposition63SlopeData selection)
    {secondScale : WZ2PaperRequestedScale (delta / rho)}
    {secondFamily : Kakeya.Streamlined.TubeFamily (delta / rho)}
    {lemma43Source : WZ1PaperTubeShading secondFamily}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss)
      lemma43Source (secondScale.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sticky2Loss)
      lemma43.shading secondScale logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    {lemma47 : Proposition63Lemma47Data
      lemma44 lemma47Loss coefficient47}
    (lemma412 : Proposition63Lemma412OutputData lemma47 outputLoss)
    (hsourceUnion : lemma43Source.union ⊆
      (selection.normalizedShading rescaled).union)
    (hsecondDelta : secondScale.1 = Delta)
    (hrhoDelta : rho = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hglobalCost : proposition63CoarseGlobalADConstant
        delta rho Delta localLoss coefficient ≤
      Kakeya.realRpowENN secondScale.1 (-outputLoss)) :
    Nonempty (PureWZ2GeneralPreGrainData lemma412.shading sigma outputLoss
      (Real.toNNReal coefficient47)
      (252000 * Real.toNNReal coefficient) 1) := by
  let normalizedSlope : ℝ → ℝ := fun height => slopes.slope (100 * height)
  have hslopeLipschitz :
      LipschitzWith (252000 * Real.toNNReal coefficient)
        normalizedSlope := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    have hraw := slopes.lipschitz.dist_le_mul
      (100 * first) (100 * second)
    change dist (slopes.slope (100 * first))
        (slopes.slope (100 * second)) ≤
      ((252000 * Real.toNNReal coefficient : NNReal) : ℝ) *
        dist first second
    calc
      dist (slopes.slope (100 * first)) (slopes.slope (100 * second)) ≤
          ((2520 * Real.toNNReal coefficient : NNReal) : ℝ) *
            dist (100 * first) (100 * second) := hraw
      _ = ((252000 * Real.toNNReal coefficient : NNReal) : ℝ) *
            dist first second := by
        simp only [Real.dist_eq]
        rw [show 100 * first - 100 * second =
          100 * (first - second) by ring, abs_mul]
        norm_num
        ring
  have htargetTop : Kakeya.realRpowENN
      secondScale.1 (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  refine ⟨{
    planeMap := lemma412.localGrains.planeMap
    planeMap_lipschitz := lemma412.localGrains.planeMap_lipschitz
    planeMap_unit := lemma412.localGrains.planeMap_unit
    planeMap_incidence := by
      intro index point hpoint
      simpa using lemma412.localGrains.planeMap_incidence index point hpoint
    slope := normalizedSlope
    slope_lipschitz := hslopeLipschitz.lipschitzOnWith
    local_ad := lemma412.localGrains.local_ad
    global_ad := ?_
  }⟩
  intro height hheight
  have hsource := selection.lemma44_horizontal_slice_ad_of_source_union
    rescaled slopes lemma44 hsourceUnion hsecondDelta hrhoDelta
      hsigma hsigmaOne height
  have hselected :
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (normalizedSlope height))
          (horizontalSlice lemma412.shading.union height))
        secondScale.1 (1 - sigma)
        (proposition63CoarseGlobalADConstant
          delta rho Delta localLoss coefficient) := by
    apply hsource.mono_set
    apply Set.image_mono
    apply Set.inter_subset_inter_left
    rintro point ⟨index, hpoint⟩
    exact ⟨index, lemma47.subshading index
      (lemma412.subshading index hpoint)⟩
  exact hselected.mono_const hglobalCost htargetTop

/-- The unchanged-family specialization of the pregrain bridge. -/
theorem proposition63_lemma412_pregrain
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {rescaledLoss lemma43Loss sticky2Loss lemma44Loss lemma47Loss
      outputLoss coefficient47 : ℝ}
    {logExponent : ℕ}
    (rescaled : Proposition63ChartRescaledData selection rescaledLoss)
    (slopes : Proposition63SlopeData selection)
    {secondScale : WZ2PaperRequestedScale (delta / rho)}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := rescaledLoss)
      (targetLoss := lemma43Loss)
      (selection.normalizedShading rescaled) (secondScale.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sticky2Loss)
      lemma43.shading secondScale logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    {lemma47 : Proposition63Lemma47Data
      lemma44 lemma47Loss coefficient47}
    (lemma412 : Proposition63Lemma412OutputData lemma47 outputLoss)
    (hsecondDelta : secondScale.1 = Delta)
    (hrhoDelta : rho = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hglobalCost : proposition63CoarseGlobalADConstant
        delta rho Delta localLoss coefficient ≤
      Kakeya.realRpowENN secondScale.1 (-outputLoss)) :
    Nonempty (PureWZ2GeneralPreGrainData lemma412.shading sigma outputLoss
      (Real.toNNReal coefficient47)
      (252000 * Real.toNNReal coefficient) 1) := by
  exact selection.proposition63_lemma412_pregrain_of_source_union
    rescaled slopes lemma412 (fun _ hpoint => hpoint) hsecondDelta hrhoDelta
    hsigma hsigmaOne hglobalCost

/-- Final frozen grain configuration when the two finite-planiness
coefficients have already been chosen below one.  This is the `L = 1` case
of the paper's final normalization: all preceding geometric refinements and
both AD conclusions are retained, while no rediscretization of the tube
family is needed. -/
theorem proposition63_coarse_direct_grain_configuration
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {rescaledLoss lemma43Loss sticky2Loss lemma44Loss lemma47Loss
      outputLoss coefficient47 : ℝ}
    {logExponent : ℕ}
    (rescaled : Proposition63ChartRescaledData selection rescaledLoss)
    (slopes : Proposition63SlopeData selection)
    {secondScale : WZ2PaperRequestedScale (delta / rho)}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := rescaledLoss)
      (targetLoss := lemma43Loss)
      (selection.normalizedShading rescaled) (secondScale.1 / 2)}
    {sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := sticky2Loss)
      lemma43.shading secondScale logExponent}
    {lemma44 : Proposition63Lemma44Data lemma43 sticky lemma44Loss}
    {lemma47 : Proposition63Lemma47Data
      lemma44 lemma47Loss coefficient47}
    (lemma412 : Proposition63Lemma412OutputData lemma47 outputLoss)
    (hsecondDelta : secondScale.1 = Delta)
    (hrhoDelta : rho = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hglobalCost : proposition63CoarseGlobalADConstant
        delta rho Delta localLoss coefficient ≤
      Kakeya.realRpowENN secondScale.1 (-outputLoss))
    (hplaneOne : (Real.toNNReal coefficient47 : NNReal) ≤ 1)
    (hslopeOne :
      (252000 * Real.toNNReal coefficient : NNReal) ≤ 1) :
    Nonempty (PureWZ2GrainConfiguration
      sigma outputLoss secondScale.1) := by
  rcases selection.proposition63_lemma412_pregrain
      rescaled slopes lemma412 hsecondDelta hrhoDelta hsigma hsigmaOne
      hglobalCost with ⟨preGrains⟩
  let localGrains : PureWZ2LocalGrainData lemma412.shading sigma
      (Kakeya.realRpowENN secondScale.1 (-outputLoss)) :=
    { planeMap := preGrains.planeMap
      planeMap_lipschitz := preGrains.planeMap_lipschitz.weaken hplaneOne
      planeMap_unit := preGrains.planeMap_unit
      planeMap_incidence := by
        intro index point hpoint
        simpa using preGrains.planeMap_incidence index point hpoint
      local_ad := preGrains.local_ad }
  let globalGrains : PureWZ2LipschitzGlobalGrainData
      lemma412.shading sigma
      (Kakeya.realRpowENN secondScale.1 (-outputLoss)) :=
    PureWZ2LipschitzGlobalGrainData.ofRealFunction preGrains.slope
      (preGrains.slope_lipschitz.weaken hslopeOne) preGrains.global_ad
  exact ⟨{
    family := sticky.coarse
    shading := lemma412.shading
    line_class := sticky.cover.coarse_line_class
    cubical := lemma412.cubical
    extremal := lemma412.extremal
    top_level_cwa := lemma412.top_level_cwa
    globalGrains := globalGrains
    localGrains := localGrains
  }⟩

end Proposition63ChartSelectionData

end Kakeya.Assouad.PureWZ2

end
