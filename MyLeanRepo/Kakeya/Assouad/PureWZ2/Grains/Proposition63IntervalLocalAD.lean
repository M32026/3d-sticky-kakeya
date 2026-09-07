import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63CommonSliceAnchoring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperADScaleRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredTransportGeometricBounds
import MyLeanRepo.Kakeya.Assouad.WZ1.TransportedNormalBounds
import MyLeanRepo.Kakeya.Assouad.WZ1.GlobalPlaninessTransportStatements
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DirectionAlignment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiScaleLocalAD

/-!
# Intervalwise local AD in Proposition 6.3

At the genuine anchor point `p_z` selected in each retained interval, invoke
the every-scale local AD estimate at scale `4 * Delta^2`, refine its minimum
scale to `Delta^2`, and form the normalized inverse-transpose normal in the
positive paper chart of the frozen parent tube.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

/-- Reorienting a paper direction changes the inner product only by sign. -/
private lemma abs_inner_direction_eq_paperDirection
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) (normal : Point3) :
    |inner ℝ tube.direction normal| =
      |inner ℝ (wz1PaperDirection tube) normal| := by
  by_cases h : 0 ≤ tube.direction (2 : Fin 3)
  · rw [wz1PaperDirection, if_pos h]
  · rw [wz1PaperDirection, if_neg h]
    simp [inner_neg_left, abs_neg]

private lemma one_third_horizontal_of_unit_and_vertical
    {x y z : ℝ}
    (hsum : x ^ 2 + y ^ 2 + z ^ 2 = 1)
    (hz : z ^ 2 ≤ (1 / 10 : ℝ) ^ 2) :
    1 / 3 ≤ |x| ∨ 1 / 3 ≤ |y| := by
  have hhorizontal : (99 / 100 : ℝ) ≤ x ^ 2 + y ^ 2 := by
    nlinarith
  rcases le_total (x ^ 2) (y ^ 2) with hxy | hyx
  · right
    have hySq : (1 / 3 : ℝ) ^ 2 ≤ y ^ 2 := by nlinarith
    have hyAbs : |(1 / 3 : ℝ)| ≤ |y| := sq_le_sq.mp hySq
    simpa using hyAbs
  · left
    have hxSq : (1 / 3 : ℝ) ^ 2 ≤ x ^ 2 := by nlinarith
    have hxAbs : |(1 / 3 : ℝ)| ≤ |x| := sq_le_sq.mp hxSq
    simpa using hxAbs

namespace Proposition63CommonSliceRescaledData

def intervalPoint
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
    (hinterval : interval ∈ data.retainedIntervals) :
    {point : Point3 // point ∈ data.commonSlice.shading.union} :=
  ⟨data.anchorPoint interval hinterval,
    ⟨data.commonSlice.distinguished,
      data.anchorPoint_mem_commonSlice interval hinterval⟩⟩

def intervalNormal
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
    (hinterval : interval ∈ data.retainedIntervals) : Point3 :=
  data.localGrains.planeMap (data.intervalPoint interval hinterval)

/-- A radius-`delta` carrier for the positive parent chart.  Its midpoint is
the parent's axis-zero point, so its anchored affine map is exactly the
historical parent paper map at the supplied transverse scale.  The radius is
only a type index; the map depends on the base and direction. -/
def parentChartTube
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
    (_data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity) :
    Kakeya.DeltaTube delta where
  base := wz1TubeAxisZeroPoint (coarse.tube input.parent) -
    (1 / 2 : ℝ) • wz1PaperDirection (coarse.tube input.parent)
  direction := wz1PaperDirection (coarse.tube input.parent)
  direction_unit := wz1PaperDirection_norm (coarse.tube input.parent)

@[simp] lemma parentChartTube_midpoint
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
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity) :
    data.parentChartTube.base +
        (1 / 2 : ℝ) • data.parentChartTube.direction =
      wz1TubeAxisZeroPoint (coarse.tube input.parent) := by
  simp [parentChartTube]

/-- The auxiliary anchored map is exactly the uncompressed parent paper map. -/
lemma parentChartMap_eq_paperMap
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
    (point : Point3) :
    wz1AnchoredUnitRescalingMap data.parentChartTube rho hrho point =
      wz1PaperUnitRescalingMap (coarse.tube input.parent) hrho point := by
  unfold wz1AnchoredUnitRescalingMap wz1PaperUnitRescalingMap
  rw [data.parentChartTube_midpoint]
  rfl

lemma anchor_covers_parent
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
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity) :
    WZ1PaperTubeCovers data.anchorTube (coarse.tube input.parent) := by
  rw [anchorTube, input.fiberFamily.tube_eq]
  apply (mem_wz2PaperFullFiberIndices_iff input.parent
    (input.fiberFamily.embedding data.commonSlice.distinguished)).mp
  exact Finset.orderEmbOfFin_mem _ _ _

def intervalTransportedRaw
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
    (hinterval : interval ∈ data.retainedIntervals) : Point3 :=
  wz1AnchoredUnitRescalingNormalLinear data.parentChartTube rho
    (data.intervalNormal interval hinterval)

def intervalTransportedNormal
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
    (hinterval : interval ∈ data.retainedIntervals) : Point3 :=
  (1 / ‖data.intervalTransportedRaw interval hinterval‖) •
    data.intervalTransportedRaw interval hinterval

end Proposition63CommonSliceRescaledData

structure Proposition63IntervalLocalADData
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
    (hinterval : interval ∈ data.retainedIntervals) where
  source_ad : PureWZ2PaperADSet1
    (scalarProjection (data.intervalNormal interval hinterval)
      (data.commonSlice.shading.union ∩
        Metric.closedBall (data.intervalPoint interval hinterval : Point3)
          (50 * Delta)))
    (Delta ^ 2) (1 - sigma)
    (10 * ((10 * Kakeya.realRpowENN delta (-localLoss)) *
      ENNReal.ofReal 25000))
  source_incidence :
    |inner ℝ (data.anchorTube.direction)
      (data.intervalNormal interval hinterval)| ≤ initial.incidence
  parent_incidence :
    |inner ℝ (data.intervalNormal interval hinterval)
      data.parentChartTube.direction| ≤ initial.incidence + rho / 2
  transported_raw_upper :
    ‖data.intervalTransportedRaw interval hinterval‖ ≤ 1
  transported_raw_lower :
    Delta ≤ ‖data.intervalTransportedRaw interval hinterval‖
  transported_raw_strong :
    50 * Delta ≤ ‖data.intervalTransportedRaw interval hinterval‖
  transported_unit :
    ‖data.intervalTransportedNormal interval hinterval‖ = 1
  transported_vertical :
    |(data.intervalTransportedNormal interval hinterval) 2| ≤ 1 / 10
  chart_available :
    1 / 3 ≤ |(data.intervalTransportedNormal interval hinterval) 0| ∨
    1 / 3 ≤ |(data.intervalTransportedNormal interval hinterval) 1|

theorem proposition63_interval_local_ad
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
    Nonempty (Proposition63IntervalLocalADData data interval hinterval) := by
  let point := data.intervalPoint interval hinterval
  let normal := data.intervalNormal interval hinterval
  have hnormalUnit : ‖normal‖ = 1 :=
    data.localGrains.planeMap_unit point
  have hcriticalPos : 0 < 2500 * Delta ^ 2 := by positivity
  have hcriticalOne : 2500 * Delta ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg Delta]
  have hdeltaCritical : delta ≤ 2500 * Delta ^ 2 :=
    hdeltaDelta.trans (by nlinarith [sq_nonneg Delta])
  have hsqrt : Real.sqrt (2500 * Delta ^ 2) = 50 * Delta := by
    rw [show 2500 * Delta ^ 2 = (50 * Delta) ^ 2 by ring,
      Real.sqrt_sq_eq_abs, abs_of_pos (by positivity : 0 < 50 * Delta)]
  have hsourceADCritical := data.localGrains.local_ad
    (2500 * Delta ^ 2) hdeltaCritical hcriticalOne point
  rw [hsqrt] at hsourceADCritical
  have hbounded :
      scalarProjection normal
          (data.commonSlice.shading.union ∩
            Metric.closedBall (point : Point3) (50 * Delta)) ⊆
        Set.Icc (-4 : ℝ) 4 := by
    apply scalarProjection_bounded
      (Z := data.commonSlice.shading) hnormalUnit
    intro value hvalue
    rcases hvalue with ⟨sourcePoint, hsourcePoint, rfl⟩
    exact ⟨sourcePoint, hsourcePoint.1, rfl⟩
  have hsourceAD := paper_ad_weaken_minimum_scale hbounded
    hsourceADCritical (sq_pos_of_pos hDelta)
    (by nlinarith [sq_nonneg Delta]) hcriticalOne
  have hsourceIncidence :
      |inner ℝ data.anchorTube.direction normal| ≤
        initial.incidence := by
    exact data.localGrains.planeMap_incidence
      data.commonSlice.distinguished
      (data.anchorPoint interval hinterval)
      (data.anchorPoint_mem_commonSlice interval hinterval)
  have hsourcePaperIncidence :
      |inner ℝ normal (wz1PaperDirection data.anchorTube)| ≤
        initial.incidence := by
    have hp :
        |inner ℝ (wz1PaperDirection data.anchorTube) normal| ≤
          initial.incidence := by
      rw [← abs_inner_direction_eq_paperDirection data.anchorTube normal]
      exact hsourceIncidence
    simpa [real_inner_comm] using hp
  have halignment :
      ‖wz1PaperDirection (coarse.tube input.parent) -
        wz1PaperDirection data.anchorTube‖ ≤ rho / 2 := by
    simpa [norm_sub_rev] using
      paper_cover_direction_alignment data.anchor_covers_parent
  have hparentIncidence :
      |inner ℝ normal data.parentChartTube.direction| ≤
        initial.incidence + rho / 2 := by
    have hdecomp : inner ℝ normal data.parentChartTube.direction =
        inner ℝ normal (wz1PaperDirection data.anchorTube) +
          inner ℝ normal (wz1PaperDirection (coarse.tube input.parent) -
            wz1PaperDirection data.anchorTube) := by
      simp only [Proposition63CommonSliceRescaledData.parentChartTube,
        inner_sub_right]
      ring
    rw [hdecomp]
    calc
      |inner ℝ normal (wz1PaperDirection data.anchorTube) +
          inner ℝ normal (wz1PaperDirection (coarse.tube input.parent) -
            wz1PaperDirection data.anchorTube)| ≤
        |inner ℝ normal (wz1PaperDirection data.anchorTube)| +
          |inner ℝ normal (wz1PaperDirection (coarse.tube input.parent) -
            wz1PaperDirection data.anchorTube)| := abs_add_le _ _
      _ ≤ initial.incidence + ‖normal‖ *
          ‖wz1PaperDirection (coarse.tube input.parent) -
            wz1PaperDirection data.anchorTube‖ :=
        add_le_add hsourcePaperIncidence (abs_real_inner_le_norm _ _)
      _ ≤ initial.incidence + rho / 2 := by
        rw [hnormalUnit, one_mul]
        gcongr
  have hgeom := transported_normal_geometric_bounds_weak
    data.parentChartTube normal hnormalUnit hparentIncidence
    (by rw [hrhoDelta]; linarith : 100 * rho ≤ 1)
    (by
      rw [hrhoDelta]
      linarith [rebalanced.incidence_le_parent_half])
    (add_nonneg initial.incidence_nonnegative (half_pos hrho).le) hrho
  let vpar : ℝ := inner ℝ normal data.parentChartTube.direction
  have hvpar : |vpar| ≤ initial.incidence + Delta / 2 := by
    simpa [vpar, hrhoDelta] using hparentIncidence
  have hvparSq : vpar ^ 2 ≤
      (initial.incidence + Delta / 2) ^ 2 := by
    rw [← sq_abs]
    gcongr
  have hvparThreeQuarters : vpar ^ 2 ≤ 3 / 4 := by
    have hsmall : initial.incidence + Delta / 2 ≤ Delta := by
      calc
        initial.incidence + Delta / 2 ≤ Delta / 2 + Delta / 2 := by
          gcongr
          simpa [hrhoDelta] using rebalanced.incidence_le_parent_half
        _ = Delta := by ring
    have habsDelta : |vpar| ≤ Delta := hvpar.trans hsmall
    have hsquare : vpar ^ 2 ≤ Delta ^ 2 := by
      rw [← sq_abs]
      exact sq_le_sq₀ (abs_nonneg vpar) hDelta.le |>.2 habsDelta
    have hDeltaSquare : Delta ^ 2 ≤ 1 / 40000 := by
      nlinarith [sq_nonneg (Delta - 1 / 200)]
    exact hsquare.trans (hDeltaSquare.trans (by norm_num))
  let Nv := data.intervalTransportedRaw interval hinterval
  have hnormSq : ‖Nv‖ ^ 2 =
      (100 * Delta) ^ 2 * (1 - vpar ^ 2) + vpar ^ 2 := by
    subst rho
    simpa [Nv, vpar,
      Proposition63CommonSliceRescaledData.intervalTransportedRaw]
      using transported_normal_norm_sq data.parentChartTube hDelta
        normal hnormalUnit
  have hstrong : 50 * Delta ≤ ‖Nv‖ := by
    have hfactor : 1 / 4 ≤ 1 - vpar ^ 2 := by linarith
    have hmain : (50 * Delta) ^ 2 ≤ ‖Nv‖ ^ 2 := by
      rw [hnormSq]
      have hmul : (100 * Delta) ^ 2 * (1 / 4 : ℝ) ≤
          (100 * Delta) ^ 2 * (1 - vpar ^ 2) := by gcongr
      nlinarith [sq_nonneg vpar]
    nlinarith [norm_nonneg Nv]
  have hrawPos : 0 < ‖data.intervalTransportedRaw interval hinterval‖ :=
    by rw [← hrhoDelta] at hDelta; exact hDelta.trans_le hgeom.2.1
  have htransportedUnit :
      ‖data.intervalTransportedNormal interval hinterval‖ = 1 := by
    simp [Proposition63CommonSliceRescaledData.intervalTransportedNormal,
      norm_smul, hrawPos.ne']
  have hchart :
      1 / 3 ≤ |(data.intervalTransportedNormal interval hinterval) 0| ∨
      1 / 3 ≤ |(data.intervalTransportedNormal interval hinterval) 1| := by
    have hnormSq' :
        (data.intervalTransportedNormal interval hinterval 0) ^ 2 +
        (data.intervalTransportedNormal interval hinterval 1) ^ 2 +
        (data.intervalTransportedNormal interval hinterval 2) ^ 2 = 1 := by
      have h := EuclideanSpace.real_norm_sq_eq
        (data.intervalTransportedNormal interval hinterval)
      rw [htransportedUnit] at h
      norm_num at h
      simpa [Fin.sum_univ_succ, add_assoc] using h.symm
    have hverticalSq :
        (data.intervalTransportedNormal interval hinterval 2) ^ 2 ≤
          (1 / 10 : ℝ) ^ 2 := by
      exact sq_le_sq.mpr (by
        rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 10)]
        exact hgeom.2.2)
    exact one_third_horizontal_of_unit_and_vertical hnormSq' hverticalSq
  have hcost :
      ENNReal.ofReal (10 * (2500 * Delta ^ 2) / Delta ^ 2) = 25000 := by
    have hreal : 10 * (2500 * Delta ^ 2) / Delta ^ 2 = (25000 : ℝ) := by
      field_simp [hDelta.ne']
      ring
    rw [hreal]
    norm_num
  rw [hcost] at hsourceAD
  exact ⟨{
    source_ad := by simpa [point, normal] using hsourceAD
    source_incidence := hsourceIncidence
    parent_incidence := hparentIncidence
    transported_raw_upper := hgeom.1
    transported_raw_lower := by
      simpa [hrhoDelta, normal,
        Proposition63CommonSliceRescaledData.intervalTransportedRaw] using
          hgeom.2.1
    transported_raw_strong := by simpa [Nv] using hstrong
    transported_unit := htransportedUnit
    transported_vertical := hgeom.2.2
    chart_available := hchart
  }⟩

end Kakeya.Assouad.PureWZ2

end
