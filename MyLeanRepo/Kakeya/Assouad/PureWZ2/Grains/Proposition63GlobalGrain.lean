import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63NearbyCover

/-!
# The genuine normalized global grain in Proposition 6.3

The exact-slice argument produces a slope on the public rescaled fibre before
the final mild rescaling.  Its Lipschitz constant is not yet one: the literal
height normalization composes the paper slope with `height ↦ 100 * height`.
This file records that genuine slope, refines the exact-slice AD estimate from
the distinguished scale `Delta` to the fine radius `delta / rho`, and makes
the resulting package stable under later carrierwise shading restrictions.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

/-- Global-grain data before the final mild rescaling, with its actual
Lipschitz constant exposed. -/
structure Proposition63RelaxedGlobalGrainData
    {fineScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily fineScale}
    (shading : WZ1PaperTubeShading family)
    (sigma : ℝ) (C : ENNReal) (K : NNReal) where
  slope : ℝ → ℝ
  slope_lipschitz : LipschitzWith K slope
  slope_bounded : ∀ height, |slope height| ≤ 3
  global_ad :
    ∀ height ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope height))
          (horizontalSlice shading.union height))
        fineScale (1 - sigma) C

/-- The exact-slice AD constant at the distinguished scale `Delta`. -/
def proposition63ExactSliceADConstant
    (delta rho Delta localLoss coefficient : ℝ) : ENNReal :=
  (2 * (Nat.ceil
      (proposition63ExactSliceError delta rho Delta coefficient / Delta) + 1) :
      ENNReal) ^ 2 *
    (204 * (1 + proposition63SlabADConstant delta localLoss))

/-- The explicit cost of refining the exact-slice AD estimate from `Delta`
to the normalized fine radius `delta / rho`. -/
def proposition63FineGlobalADConstant
    (delta rho Delta localLoss coefficient : ℝ) : ENNReal :=
  10 * ((10 *
      proposition63ExactSliceADConstant
        delta rho Delta localLoss coefficient) *
    ENNReal.ofReal (10 * Delta / (delta / rho)))

namespace Proposition63RelaxedGlobalGrainData

/-- Restrict a relaxed global grain to a carrierwise paper subshading while
retaining the same genuine slope and constants. -/
def restrict
    {fineScale sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily fineScale}
    {source selected : WZ1PaperTubeShading family}
    {C : ENNReal} {K : NNReal}
    (data : Proposition63RelaxedGlobalGrainData source sigma C K)
    (hsub : PaperIsSubshading selected source) :
    Proposition63RelaxedGlobalGrainData selected sigma C K := by
  have hunion : selected.union ⊆ source.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hsub index hpoint⟩
  exact
    { slope := data.slope
      slope_lipschitz := data.slope_lipschitz
      slope_bounded := data.slope_bounded
      global_ad := by
        intro height hheight
        apply (data.global_ad height hheight).mono_set
        exact Set.image_mono (Set.inter_subset_inter_left _ hunion) }

end Proposition63RelaxedGlobalGrainData

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

/-- The scalar projection of a normalized paper slice along the genuine
Proposition 6.3 direction remains in the bridge window `[-4,4]`. -/
lemma normalized_public_projection_bounded
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss)
    (slopes : Proposition63SlopeData selection)
    (height : ℝ) :
    scalarProjection
        (globalGrainDirection (slopes.slope (100 * height)))
        (horizontalSlice (selection.normalizedShading rescaled).union height)
      ⊆ Set.Icc (-4 : ℝ) 4 := by
  rintro value ⟨point, hpoint, rfl⟩
  rcases hpoint.1 with ⟨index, hindex⟩
  have hbox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 :=
    ((selection.normalizedShading rescaled).subset_body index hindex).2
  have hcoordinates :
      |point 0| ≤ 1 ∧ |point 1| ≤ 1 ∧ |point 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hbox
  have hinner :
      inner ℝ point
          (globalGrainDirection (slopes.slope (100 * height))) =
        point 0 + slopes.slope (100 * height) * point 1 := by
    rw [PiLp.inner_apply]
    simp [globalGrainDirection, Fin.sum_univ_succ]
  change inner ℝ point
      (globalGrainDirection (slopes.slope (100 * height))) ∈
    Set.Icc (-4 : ℝ) 4
  rw [hinner]
  have hslope := slopes.bounded (100 * height)
  have hproduct :
      |slopes.slope (100 * height) * point 1| ≤ 3 := by
    rw [abs_mul]
    calc
      |slopes.slope (100 * height)| * |point 1|
          ≤ 3 * 1 := mul_le_mul hslope hcoordinates.2.1
            (abs_nonneg _) (by norm_num)
      _ = 3 := by norm_num
  have hbound :
      |point 0 + slopes.slope (100 * height) * point 1| ≤ 4 := by
    calc
      |point 0 + slopes.slope (100 * height) * point 1|
          ≤ |point 0| + |slopes.slope (100 * height) * point 1| :=
            abs_add_le _ _
      _ ≤ 1 + 3 := add_le_add hcoordinates.1 hproduct
      _ = 4 := by norm_num
  exact abs_le.mp hbound

/-- The genuine global slope and exact-slice AD package on the whole
normalized public fibre.  The factor `100` in the literal height coordinate
raises the slope Lipschitz constant from `2520 * coefficient` to
`252000 * coefficient`. -/
theorem proposition63_global_grain
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss)
    (slopes : Proposition63SlopeData selection)
    (hrhoDelta : rho = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    Nonempty
      (Proposition63RelaxedGlobalGrainData
        (selection.normalizedShading rescaled) sigma
        (proposition63FineGlobalADConstant
          delta rho Delta localLoss coefficient)
        (252000 * Real.toNNReal coefficient)) := by
  let normalizedSlope : ℝ → ℝ :=
    fun height => slopes.slope (100 * height)
  have hslopeLipschitz :
      LipschitzWith (252000 * Real.toNNReal coefficient)
        normalizedSlope := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    have hraw := slopes.lipschitz.dist_le_mul
      (100 * first) (100 * second)
    change dist (slopes.slope (100 * first)) (slopes.slope (100 * second)) ≤
      ((252000 * Real.toNNReal coefficient : NNReal) : ℝ) *
        dist first second
    calc
      dist (slopes.slope (100 * first)) (slopes.slope (100 * second))
          ≤ ((2520 * Real.toNNReal coefficient : NNReal) : ℝ) *
              dist (100 * first) (100 * second) := hraw
      _ = ((252000 * Real.toNNReal coefficient : NNReal) : ℝ) *
              dist first second := by
        simp only [Real.dist_eq]
        rw [show 100 * first - 100 * second =
          100 * (first - second) by ring, abs_mul]
        norm_num
        ring
  have hglobal : ∀ height ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (normalizedSlope height))
          (horizontalSlice
            (selection.normalizedShading rescaled).union height))
        (delta / rho) (1 - sigma)
        (proposition63FineGlobalADConstant
          delta rho Delta localLoss coefficient) := by
    intro height _
    have hsource := selection.normalized_public_horizontal_slice_ad
      rescaled slopes hrhoDelta hsigma hsigmaOne height
    have hbounded := selection.normalized_public_projection_bounded
      rescaled slopes height
    have hrefined := paper_ad_weaken_minimum_scale
      hbounded hsource (div_pos hdelta hrho)
      (selection.rescaledFine_le_Delta hrhoDelta)
      (hDeltaSmall.trans (by norm_num))
    simpa only [normalizedSlope, proposition63FineGlobalADConstant,
      proposition63ExactSliceADConstant] using hrefined
  exact ⟨{
    slope := normalizedSlope
    slope_lipschitz := hslopeLipschitz
    slope_bounded := fun height => slopes.bounded (100 * height)
    global_ad := hglobal
  }⟩

end Proposition63ChartSelectionData

end Kakeya.Assouad.PureWZ2

end
