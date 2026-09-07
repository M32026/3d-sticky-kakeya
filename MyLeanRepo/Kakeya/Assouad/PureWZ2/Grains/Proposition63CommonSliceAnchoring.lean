import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63CommonSliceRescaled
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalLocalVolume

/-!
# Discrete heights and anchor points for Proposition 6.3

For every retained axial interval choose a genuine point of the distinguished
tube shading.  The frozen literal rescaling sends that point into the exact
horizontal interval.  Cubical saturation enlarges the interval by at most
one target-grid side on either end.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

attribute [local instance] Classical.propDecidable

namespace Proposition63CommonSliceRescaledData

def retainedHeightBases
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
    Finset ℝ :=
  data.retainedIntervals.image fun interval => (interval.1 : ℝ) * Delta

lemma retained_interval_nonempty
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
    (input.selectedFiber.carrier data.commonSlice.distinguished ∩
      proposition63AxialSlab (coarse.tube input.parent) hrho
        (proposition63LiteralSliceWidth Delta)
        interval.1).Nonempty := by
  exact (data.mem_retainedIntervals_iff interval).1 hinterval

def anchorPoint
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
  Classical.choose (data.retained_interval_nonempty interval hinterval)

lemma anchorPoint_mem
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
    data.anchorPoint interval hinterval ∈
        input.selectedFiber.carrier data.commonSlice.distinguished ∧
      data.anchorPoint interval hinterval ∈
        proposition63AxialSlab (coarse.tube input.parent) hrho
          (proposition63LiteralSliceWidth Delta)
          interval.1 :=
  Classical.choose_spec (data.retained_interval_nonempty interval hinterval)

lemma anchorPoint_mem_commonSlice
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
    data.anchorPoint interval hinterval ∈
      data.commonSlice.shading.carrier data.commonSlice.distinguished := by
  refine ⟨(data.anchorPoint_mem interval hinterval).1, ?_⟩
  exact proposition63AxialAnchorRegion_mem_of_interval
    (Delta := proposition63LiteralSliceWidth Delta) interval
    ((data.mem_retainedIntervals_iff interval).1 hinterval)
    (data.anchorPoint_mem interval hinterval).2

lemma anchorPoint_image_height
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
    (wz2PaperLiteralUnitRescalingMap
      (coarse.tube input.parent) hrho
      (data.anchorPoint interval hinterval)) (2 : Fin 3) ∈
        Set.Ico ((interval.1 : ℝ) * proposition63LiteralSliceWidth Delta)
          (((interval.1 : ℝ) + 1) *
            proposition63LiteralSliceWidth Delta) :=
  (data.anchorPoint_mem interval hinterval).2

/-- Any source point surviving the common-slice refinement lies in one
retained axial interval. -/
lemma sourcePoint_mem_retained_interval
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
    {tube : Fin input.fiberFamily.family.card} {point : Point3}
    (hpoint : point ∈ data.commonSlice.shading.carrier tube) :
    ∃ interval ∈ data.retainedIntervals,
      point ∈ proposition63AxialSlab
        (coarse.tube input.parent) hrho
          (proposition63LiteralSliceWidth Delta) interval.1 := by
  rcases Set.mem_iUnion.mp hpoint.2 with ⟨interval, hinterval⟩
  by_cases hmeets : proposition63AxialPartitionMeets
      (Delta := proposition63LiteralSliceWidth Delta) input.selectedFiber
      (coarse.tube input.parent) hrho
      data.commonSlice.distinguished interval
  · rw [if_pos hmeets] at hinterval
    exact ⟨interval, (data.mem_retainedIntervals_iff interval).2 hmeets,
      hinterval⟩
  · rw [if_neg hmeets] at hinterval
    exact False.elim hinterval

end Proposition63CommonSliceRescaledData

/-- Equal target grid indices force the third coordinates to differ by less
than one grid side. -/
lemma samePaperGridIndex_coord_two_lt
    {scale : ℝ} (hscale : 0 < scale) {first second : Point3}
    (hindex : wz1PaperGridIndex scale first =
      wz1PaperGridIndex scale second) :
    |first (2 : Fin 3) - second (2 : Fin 3)| < scale := by
  have hfloor : Int.floor (first 2 / scale) =
      Int.floor (second 2 / scale) := by
    have h := congrArg (fun index : ℤ × ℤ × ℤ => index.2.2) hindex
    simpa [wz1PaperGridIndex, gridIndex] using h
  have hunit := Int.abs_sub_lt_one_of_floor_eq_floor hfloor
  have hquotient : |(first 2 - second 2) / scale| < 1 := by
    rw [sub_div]
    exact hunit
  rw [abs_div, abs_of_pos hscale] at hquotient
  exact (div_lt_one hscale).1 hquotient

/-- Provenance for every point in the refreshed literal image: it comes from
one source point in a retained interval, and its height differs from that
source image by less than the target grid side. -/
theorem proposition63_literal_point_retained_slab
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
    (hscale : 0 < delta / rho)
    {target : Fin input.frozenRescaled.familyData.targetFamily.card}
    {point : Point3}
    (hpoint : point ∈ data.literalImage.targetShading.carrier target) :
    ∃ interval ∈ data.retainedIntervals, ∃ sourcePoint : Point3,
      sourcePoint ∈ data.commonSlice.shading.carrier
        (input.frozenRescaled.familyData.sourceIndex target) ∧
      sourcePoint ∈ proposition63AxialSlab
        (coarse.tube input.parent) hrho
          (proposition63LiteralSliceWidth Delta) interval.1 ∧
      |point 2 - (wz2PaperLiteralUnitRescalingMap
        (coarse.tube input.parent) hrho sourcePoint) 2| < delta / rho := by
  rw [data.literalImage.target_carrier_eq target] at hpoint
  rcases hpoint with ⟨imagePoint, ⟨sourcePoint, hsource, rfl⟩, hgrid⟩
  rcases data.sourcePoint_mem_retained_interval hsource with
    ⟨interval, hinterval, hslab⟩
  exact ⟨interval, hinterval, sourcePoint, hsource, hslab,
    samePaperGridIndex_coord_two_lt hscale hgrid⟩

/-- Every literal-image point lies in the target-grid thickening of one
retained horizontal interval. -/
theorem proposition63_literal_point_height_bounds
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
    (hscale : 0 < delta / rho)
    {target : Fin input.frozenRescaled.familyData.targetFamily.card}
    {point : Point3}
    (hpoint : point ∈ data.literalImage.targetShading.carrier target) :
    ∃ interval ∈ data.retainedIntervals,
      (interval.1 : ℝ) * proposition63LiteralSliceWidth Delta -
          delta / rho < point 2 ∧
      point 2 < ((interval.1 : ℝ) + 1) *
          proposition63LiteralSliceWidth Delta + delta / rho := by
  rcases proposition63_literal_point_retained_slab data hscale hpoint with
    ⟨interval, hinterval, sourcePoint, _hsource, hslab, hheight⟩
  have hsourceHeight := hslab
  change (wz2PaperLiteralUnitRescalingMap
      (coarse.tube input.parent) hrho sourcePoint) 2 ∈
    Set.Ico ((interval.1 : ℝ) * proposition63LiteralSliceWidth Delta)
      (((interval.1 : ℝ) + 1) *
        proposition63LiteralSliceWidth Delta) at hsourceHeight
  have hdifference := abs_lt.mp hheight
  exact ⟨interval, hinterval, by linarith [hsourceHeight.1, hdifference.1],
    by linarith [hsourceHeight.2, hdifference.2]⟩

/-- The public rescaled shading is a pure reindexing of the literal shading,
so it has the same retained-slab provenance. -/
theorem proposition63_public_point_height_bounds
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
    (hscale : 0 < delta / rho)
    {publicIndex : Fin
      input.frozenRescaled.rescalingCertificate.publicFamily.card}
    {point : Point3}
    (hpoint : point ∈
      (input.frozenRescaled.rescalingCertificate.publicShading
        data.literalImage.targetShading).carrier publicIndex) :
    ∃ interval ∈ data.retainedIntervals,
      (interval.1 : ℝ) * proposition63LiteralSliceWidth Delta -
          delta / rho < point 2 ∧
      point 2 < ((interval.1 : ℝ) + 1) *
          proposition63LiteralSliceWidth Delta + delta / rho := by
  exact proposition63_literal_point_height_bounds data hscale hpoint

end Kakeya.Assouad.PureWZ2

end
