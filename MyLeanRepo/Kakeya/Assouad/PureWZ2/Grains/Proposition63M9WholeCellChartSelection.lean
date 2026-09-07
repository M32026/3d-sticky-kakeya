import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ChartRescaled
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalSlabLower

/-!
# Whole-cell witnesses for the Proposition 6.3 chart selection

The chart-selected source is an actual restriction to the selected axial
intervals.  Consequently, a literal `delta`-cell meeting one of its tube
carriers has a genuine selected-interval witness.  The whole cell need not
lie in that interval: what survives uniformly on the cell is only the axial
coordinate drift bound proved below.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

/-- The frozen literal axial coordinate changes by at most
`delta * sqrt 3 / 100` across one literal `delta`-cell. -/
lemma proposition63AxialCoordinate_sub_le_of_mem_same_gridCube
    {delta rho : ℝ} (hdelta : 0 < delta)
    (anchor : Kakeya.DeltaTube rho) (hrho : 0 < rho)
    (cell : ℤ × ℤ × ℤ) {first second : Point3}
    (hfirst : first ∈ wz1PaperGridCube delta cell)
    (hsecond : second ∈ wz1PaperGridCube delta cell) :
    |proposition63AxialCoordinate anchor hrho first -
        proposition63AxialCoordinate anchor hrho second| ≤
      delta * Real.sqrt 3 / 100 := by
  have hdist : dist first second ≤ delta * Real.sqrt 3 :=
    wz1PaperGridCube_diameter hdelta cell hfirst hsecond
  have hinner :
      |inner ℝ (first - second) (wz1PaperDirection anchor)| ≤
        dist first second := by
    calc
      |inner ℝ (first - second) (wz1PaperDirection anchor)| ≤
          ‖first - second‖ * ‖wz1PaperDirection anchor‖ :=
        abs_real_inner_le_norm _ _
      _ = dist first second := by
        rw [wz1PaperDirection_norm, mul_one, dist_eq_norm]
  rw [proposition63AxialCoordinate_eq,
    proposition63AxialCoordinate_eq]
  have hrewrite :
      (1 / 100 : ℝ) *
          inner ℝ (first - wz1TubeAxisZeroPoint anchor)
            (wz1PaperDirection anchor) -
        (1 / 100 : ℝ) *
          inner ℝ (second - wz1TubeAxisZeroPoint anchor)
            (wz1PaperDirection anchor) =
      (1 / 100 : ℝ) *
        inner ℝ (first - second) (wz1PaperDirection anchor) := by
    rw [← mul_sub, ← inner_sub_left]
    congr 2
    abel
  rw [hrewrite, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)]
  calc
    (1 / 100 : ℝ) *
        |inner ℝ (first - second) (wz1PaperDirection anchor)| ≤
      (1 / 100 : ℝ) * dist first second := by gcongr
    _ ≤ (1 / 100 : ℝ) * (delta * Real.sqrt 3) := by gcongr
    _ = delta * Real.sqrt 3 / 100 := by ring

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

/-- A literal `delta`-cell meeting the common-slice shading has a genuine
retained-interval witness on the same tube.  Every other point of that cell
stays axially close to the witness; no whole-cell slab containment is
asserted. -/
theorem exists_retainedInterval_witness_of_gridCube_meets_commonSlice
    (tube : Fin input.fiberFamily.family.card)
    (cell : ℤ × ℤ × ℤ)
    (hmeets : (wz1PaperGridCube delta cell ∩
      data.commonSlice.shading.carrier tube).Nonempty) :
    ∃ interval, ∃ _hinterval : interval ∈ data.retainedIntervals,
      ∃ witness : Point3,
        witness ∈ wz1PaperGridCube delta cell ∧
        witness ∈ data.commonSlice.shading.carrier tube ∧
        witness ∈ proposition63AxialSlab
          (coarse.tube input.parent) hrho
          (proposition63LiteralSliceWidth Delta) interval.1 ∧
        ∀ point ∈ wz1PaperGridCube delta cell,
          |proposition63AxialCoordinate (coarse.tube input.parent) hrho point -
              proposition63AxialCoordinate (coarse.tube input.parent) hrho
                witness| ≤
            delta * Real.sqrt 3 / 100 := by
  rcases hmeets with ⟨witness, hwitnessCell, hwitnessCommonSlice⟩
  have hwitnessRegion : witness ∈
      proposition63AxialAnchorRegion
        (Delta := proposition63LiteralSliceWidth Delta) input.selectedFiber
        (coarse.tube input.parent) hrho data.commonSlice.distinguished := by
    exact hwitnessCommonSlice.2
  rcases Set.mem_iUnion.mp hwitnessRegion with
    ⟨interval, hwitnessInterval⟩
  by_cases hintervalMeets : proposition63AxialPartitionMeets
      input.selectedFiber (coarse.tube input.parent) hrho
        data.commonSlice.distinguished interval
  · rw [if_pos hintervalMeets] at hwitnessInterval
    have hinterval : interval ∈ data.retainedIntervals :=
      (data.mem_retainedIntervals_iff interval).2 hintervalMeets
    refine ⟨interval, hinterval, witness, hwitnessCell,
      hwitnessCommonSlice, hwitnessInterval, ?_⟩
    intro point hpointCell
    exact proposition63AxialCoordinate_sub_le_of_mem_same_gridCube
      hdelta (coarse.tube input.parent) hrho cell hpointCell hwitnessCell
  · rw [if_neg hintervalMeets] at hwitnessInterval
    exact hwitnessInterval.elim

/-- A literal `delta`-cell meeting an active chart-selected tube has a
genuine witness in a selected retained interval.  Other points of the same
cell stay axially close to that witness; no containment of the whole cell in
the witness slab is asserted. -/
theorem exists_retainedInterval_witness_of_gridCube_meets_source
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (tube : Fin input.fiberFamily.family.card)
    (cell : ℤ × ℤ × ℤ)
    (hmeets : (wz1PaperGridCube delta cell ∩
      selection.sourceShading.carrier tube).Nonempty) :
    ∃ interval, ∃ _hinterval : interval ∈ selection.intervals,
      ∃ witness : Point3,
        witness ∈ wz1PaperGridCube delta cell ∧
        witness ∈ data.commonSlice.shading.carrier tube ∧
        witness ∈ proposition63AxialSlab
          (coarse.tube input.parent) hrho
          (proposition63LiteralSliceWidth Delta) interval.1 ∧
        ∀ point ∈ wz1PaperGridCube delta cell,
          |proposition63AxialCoordinate (coarse.tube input.parent) hrho point -
              proposition63AxialCoordinate (coarse.tube input.parent) hrho
                witness| ≤
            delta * Real.sqrt 3 / 100 := by
  rcases hmeets with ⟨witness, hwitnessCell, hwitnessSource⟩
  change witness ∈ input.selectedFiber.carrier tube ∩
    proposition63IntervalRegion (coarse.tube input.parent) hrho
      selection.intervals at hwitnessSource
  rcases Set.mem_iUnion₂.mp hwitnessSource.2 with
    ⟨interval, hinterval, hwitnessSlab⟩
  refine ⟨interval, hinterval, witness, hwitnessCell,
    selection.source_sub_commonSlice tube hwitnessSource, hwitnessSlab, ?_⟩
  intro point hpointCell
  exact proposition63AxialCoordinate_sub_le_of_mem_same_gridCube
    hdelta (coarse.tube input.parent) hrho cell hpointCell hwitnessCell

end Proposition63ChartSelectionData

end Kakeya.Assouad.PureWZ2

end
