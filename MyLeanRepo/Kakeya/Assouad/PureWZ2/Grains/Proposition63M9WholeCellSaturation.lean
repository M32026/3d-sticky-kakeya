import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9WholeCellChartSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RebalancedFiniteRefinement

/-!
# Whole-cell saturation of the Proposition 6.3 chart source

Starting from the existing interval-based chart selection, retain every
literal cell meeting its source shading, and restrict every tube of the
selected metric fibre by the same spatial cell union.  This keeps the source
without asserting that the saturated shading remains inside the old interval
restriction.
-/

noncomputable section
namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

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
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)

/-- All literal fine cells meeting the interval-selected chart source. -/
def selectedCells : Finset (ℤ × ℤ × ℤ) :=
  wz1PaperActiveCells selection.sourceShading hdelta

/-- Saturate the selected chart source by its active literal cells, using one
common spatial restriction for every tube of the selected metric fibre. -/
def saturated : WZ1PaperTubeShading input.fiberFamily.family :=
  coarseWholeCellRestriction input.selectedFiber selection.selectedCells

@[simp] theorem saturated_carrier
    (tube : Fin input.fiberFamily.family.card) :
    selection.saturated.carrier tube =
      input.selectedFiber.carrier tube ∩
        ⋃ cell ∈ selection.selectedCells, wz1PaperGridCube delta cell :=
  rfl

/-- Every point of the interval-selected source survives its whole-cell
saturation. -/
theorem sourceShading_sub_saturated :
    PaperIsSubshading selection.sourceShading selection.saturated := by
  intro tube point hpoint
  have hselected : point ∈ input.selectedFiber.carrier tube :=
    (selection.source_sub_commonSlice tube hpoint) |>
      data.commonSlice.subshading tube
  have hbody := selection.sourceShading.subset_body tube hpoint
  have hcellWindow : wz1PaperGridIndex delta point ∈
      wz1PaperGridIndicesInWindow delta hdelta :=
    paper_point_gridIndex_in_window hdelta hbody.2
  have hcellMeets :
      (selection.sourceShading.union ∩
        wz1PaperGridCube delta (wz1PaperGridIndex delta point)).Nonempty :=
    ⟨point, ⟨tube, hpoint⟩,
      (mem_wz1PaperGridCube delta _ point).mpr rfl⟩
  have hcell : wz1PaperGridIndex delta point ∈ selection.selectedCells :=
    (mem_wz1PaperActiveCells selection.sourceShading hdelta _).2
      ⟨hcellWindow, hcellMeets⟩
  exact ⟨hselected, Set.mem_iUnion₂.mpr
    ⟨wz1PaperGridIndex delta point, hcell,
      (mem_wz1PaperGridCube delta _ point).mpr rfl⟩⟩

theorem sourceShading_mass_le_saturated_mass :
    selection.sourceShading.mass ≤ selection.saturated.mass := by
  apply Finset.sum_le_sum
  intro tube _
  exact MeasureTheory.measure_mono (selection.sourceShading_sub_saturated tube)

theorem saturated_sub_selectedFiber :
    PaperIsSubshading selection.saturated input.selectedFiber :=
  coarseWholeCellRestriction_subshading _ _

theorem saturated_cubical :
    WZ1PaperIsCubicalShading selection.saturated := by
  exact coarseWholeCellRestriction_cubical
    (restrictPaperShading_cubical input.fiberFamily rebalanced.cubical) _

/-- On every point retained by the common spatial restriction, all source
selected-fibre memberships survive simultaneously. -/
theorem saturated_pointMultiplicity_eq :
    ∀ point ∈ selection.saturated.union,
      selection.saturated.pointMultiplicity point =
        input.selectedFiber.pointMultiplicity point := by
  classical
  intro point hpoint
  rcases hpoint with ⟨tube, hpointTube⟩
  have hregion : point ∈
      ⋃ cell ∈ selection.selectedCells, wz1PaperGridCube delta cell :=
    hpointTube.2
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro index _
  rw [selection.saturated_carrier]
  exact and_iff_left hregion

/-- Every saturated cell has a genuine source-shading tube witness and hence
a selected retained interval carrying the global chart label.  The final
estimate applies to every point of the cell, without claiming interval
containment of the whole cell. -/
theorem selectedCell_source_chart_geometry
    (hrhoDelta : rho = Delta)
    (cell : ℤ × ℤ × ℤ)
    (hcell : cell ∈ selection.selectedCells) :
    ∃ tube : Fin input.fiberFamily.family.card,
      ∃ sourcePoint : Point3,
        sourcePoint ∈ selection.sourceShading.carrier tube ∧
        sourcePoint ∈ wz1PaperGridCube delta cell ∧
        ∃ interval, ∃ hinterval : interval ∈ selection.intervals,
          proposition63IntervalChartLabel data hDelta hDeltaSmall
              hdeltaDelta hdeltaRatio interval = selection.chartLabel ∧
          (match selection.chartLabel.chart with
          | WZ1HorizontalChart.first =>
              1 / 3 ≤ |(data.intervalTransportedNormal interval
                (selection.intervals_subset hinterval)) 0|
          | WZ1HorizontalChart.second =>
              1 / 3 ≤ |(data.intervalTransportedNormal interval
                (selection.intervals_subset hinterval)) 1|) ∧
          ∃ witness : Point3,
            witness ∈ wz1PaperGridCube delta cell ∧
            witness ∈ data.commonSlice.shading.carrier tube ∧
            witness ∈ proposition63AxialSlab
              (coarse.tube input.parent) hrho
              (proposition63LiteralSliceWidth Delta) interval.1 ∧
            ∀ point ∈ wz1PaperGridCube delta cell,
              |proposition63AxialCoordinate
                  (coarse.tube input.parent) hrho point -
                proposition63AxialCoordinate
                  (coarse.tube input.parent) hrho witness| ≤
                delta * Real.sqrt 3 / 100 := by
  have hactive :=
    (mem_wz1PaperActiveCells selection.sourceShading hdelta cell).1 hcell
  rcases hactive.2 with ⟨sourcePoint, hsourceUnion, hsourceCell⟩
  rcases hsourceUnion with ⟨tube, hsourceTube⟩
  have hmeets : (wz1PaperGridCube delta cell ∩
      selection.sourceShading.carrier tube).Nonempty :=
    ⟨sourcePoint, hsourceCell, hsourceTube⟩
  rcases selection.exists_retainedInterval_witness_of_gridCube_meets_source
      tube cell hmeets with
    ⟨interval, hinterval, witness, hwitnessCell, hwitnessCommon,
      hwitnessSlab, hclose⟩
  have hlabel := (Finset.mem_filter.mp hinterval).2
  have hchart : proposition63IntervalChartLabel data hDelta hDeltaSmall
      hdeltaDelta hdeltaRatio interval = selection.chartLabel := by
    simpa [Proposition63ChartSelectionData.intervals] using hlabel
  refine ⟨tube, sourcePoint, hsourceTube, hsourceCell, interval, hinterval,
    hchart, selection.interval_chart_bound hrhoDelta interval hinterval,
    witness, hwitnessCell, hwitnessCommon, hwitnessSlab, hclose⟩

/-- Same-witness form of `selectedCell_source_chart_geometry`.  This exposes
the source-shading membership which is needed when the whole-cell saturation
is rescaled again: the literal image of the witness is then an actual member
of `literalSourceSlab`, not merely of the larger common slice. -/
theorem selectedCell_source_slab_witness
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    (hrhoDelta : rho = Delta)
    (cell : ℤ × ℤ × ℤ)
    (hcell : cell ∈ selection.selectedCells) :
    ∃ tube : Fin input.fiberFamily.family.card,
      ∃ witness : Point3,
        witness ∈ selection.sourceShading.carrier tube ∧
        witness ∈ wz1PaperGridCube delta cell ∧
        ∃ interval, ∃ hinterval : interval ∈ selection.intervals,
          witness ∈ proposition63AxialSlab
            (coarse.tube input.parent) hrho
            (proposition63LiteralSliceWidth Delta) interval.1 ∧
          proposition63IntervalChartLabel data hDelta hDeltaSmall
              hdeltaDelta hdeltaRatio interval = selection.chartLabel ∧
          (match selection.chartLabel.chart with
          | WZ1HorizontalChart.first =>
              1 / 3 ≤ |(data.intervalTransportedNormal interval
                (selection.intervals_subset hinterval)) 0|
          | WZ1HorizontalChart.second =>
              1 / 3 ≤ |(data.intervalTransportedNormal interval
                (selection.intervals_subset hinterval)) 1|) := by
  have hactive :=
    (mem_wz1PaperActiveCells selection.sourceShading hdelta cell).1 hcell
  rcases hactive.2 with ⟨witness, hwitnessUnion, hwitnessCell⟩
  rcases hwitnessUnion with ⟨tube, hwitnessSource⟩
  have hmeets : (wz1PaperGridCube delta cell ∩
      selection.sourceShading.carrier tube).Nonempty :=
    ⟨witness, hwitnessCell, hwitnessSource⟩
  rcases selection.exists_retainedInterval_witness_of_gridCube_meets_source
      tube cell hmeets with
    ⟨interval, hinterval, sourceWitness, hsourceWitnessCell,
      hsourceWitnessCommon, hsourceWitnessSlab, _⟩
  have hsourceWitnessSource :
      sourceWitness ∈ selection.sourceShading.carrier tube := by
    change sourceWitness ∈ input.selectedFiber.carrier tube ∩
      proposition63IntervalRegion (coarse.tube input.parent) hrho
        selection.intervals
    exact ⟨data.commonSlice.subshading tube hsourceWitnessCommon,
      Set.mem_iUnion₂.mpr ⟨interval, hinterval, hsourceWitnessSlab⟩⟩
  have hlabel := (Finset.mem_filter.mp hinterval).2
  have hchart : proposition63IntervalChartLabel data hDelta hDeltaSmall
      hdeltaDelta hdeltaRatio interval = selection.chartLabel := by
    simpa [Proposition63ChartSelectionData.intervals] using hlabel
  exact ⟨tube, sourceWitness, hsourceWitnessSource, hsourceWitnessCell,
    interval, hinterval, hsourceWitnessSlab, hchart,
    selection.interval_chart_bound hrhoDelta interval hinterval⟩

end Proposition63ChartSelectionData
end Kakeya.Assouad.PureWZ2
end
