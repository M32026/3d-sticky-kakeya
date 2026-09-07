import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Ordinary trace of a dense cubical subshading

Every whole grid cell contained in `pureWZ2DenseCubicalization tube source`
carries the defining fixed fraction of the source mass.  Consequently, any
measurable cubical subset of that dense cubicalization has an ordinary trace
inside `source` with the same relative lower bound.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem pureWZ2_dense_cubical_trace
    {delta : ℝ}
    (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (source finalCarrier : Set Point3)
    (sourceMeasurable : MeasurableSet source)
    (finalMeasurable : MeasurableSet finalCarrier)
    (finalCubical :
      ∀ point ∈ finalCarrier,
        wz1PaperGridCube delta
            (wz1PaperGridIndex delta point) ⊆
          finalCarrier)
    (finalSubset :
      finalCarrier ⊆
        pureWZ2DenseCubicalization tube source) :
    (100 : ENNReal)⁻¹ *
          volume source *
          (volume tube.carrier)⁻¹ *
          volume finalCarrier ≤
      volume (source ∩ finalCarrier) := by
  let cells : Finset (ℤ × ℤ × ℤ) :=
    (wz1PaperGridIndicesInWindow delta hdelta).filter fun cell =>
      (finalCarrier ∩ wz1PaperGridCube delta cell).Nonempty
  have finalSubsetPaper :
      finalCarrier ⊆ wz1PaperTubeCarrier tube :=
    finalSubset.trans fun point hpoint => hpoint.1 <|
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) point).mpr rfl
  have finalSubsetBox :
      finalCarrier ⊆ Kakeya.Streamlined.axisBox 2 2 2 :=
    fun point hpoint => (finalSubsetPaper hpoint).2
  have finalEq :
      finalCarrier =
        ⋃ cell ∈ cells, wz1PaperGridCube delta cell := by
    apply Set.Subset.antisymm
    · intro point hpoint
      let cell := wz1PaperGridIndex delta point
      have cellWindow :
          cell ∈ wz1PaperGridIndicesInWindow delta hdelta :=
        paper_point_gridIndex_in_window hdelta (finalSubsetBox hpoint)
      have pointCell :
          point ∈ wz1PaperGridCube delta cell :=
        (mem_wz1PaperGridCube delta cell point).mpr rfl
      have cellActive : cell ∈ cells := by
        apply Finset.mem_filter.mpr
        exact ⟨cellWindow, ⟨point, hpoint, pointCell⟩⟩
      exact Set.mem_iUnion₂.mpr
        ⟨cell, cellActive, pointCell⟩
    · intro point hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨cell, hcell, pointCell⟩
      rcases (Finset.mem_filter.mp hcell).2 with
        ⟨sourcePoint, sourcePointFinal, sourcePointCell⟩
      have sameCell :
          wz1PaperGridIndex delta point =
            wz1PaperGridIndex delta sourcePoint := by
        exact
          ((mem_wz1PaperGridCube delta cell point).mp pointCell).trans
            ((mem_wz1PaperGridCube delta cell sourcePoint).mp
              sourcePointCell).symm
      exact
        finalCubical sourcePoint sourcePointFinal <|
          (mem_wz1PaperGridCube delta
            (wz1PaperGridIndex delta sourcePoint) point).mpr
              sameCell
  have cellBound :
      ∀ cell ∈ cells,
        (100 : ENNReal)⁻¹ *
              volume source *
              (volume tube.carrier)⁻¹ *
              volume (wz1PaperGridCube delta cell) ≤
          volume
            (source ∩ wz1PaperGridCube delta cell) := by
    intro cell hcell
    rcases (Finset.mem_filter.mp hcell).2 with
      ⟨point, pointFinal, pointCell⟩
    have pointDense := finalSubset pointFinal
    have pointIndex :
        wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp pointCell
    simpa [pointIndex] using pointDense.2
  have cellsDisjoint :
      Set.PairwiseDisjoint (↑cells)
        (fun cell => wz1PaperGridCube delta cell) := by
    intro first _ second _ hne
    exact wz1PaperGridCube_disjoint hne
  have cellsMeasurable :
      ∀ cell ∈ cells,
        MeasurableSet (wz1PaperGridCube delta cell) :=
    fun cell _ => wz1PaperGridCube_measurable cell
  have traceDisjoint :
      Set.PairwiseDisjoint (↑cells)
        (fun cell => source ∩ wz1PaperGridCube delta cell) := by
    intro first hfirst second hsecond hne
    exact
      (cellsDisjoint hfirst hsecond hne).mono
        Set.inter_subset_right Set.inter_subset_right
  have traceMeasurable :
      ∀ cell ∈ cells,
        MeasurableSet
          (source ∩ wz1PaperGridCube delta cell) :=
    fun cell _ =>
      sourceMeasurable.inter
        (wz1PaperGridCube_measurable cell)
  have traceEq :
      source ∩ finalCarrier =
        ⋃ cell ∈ cells,
          source ∩ wz1PaperGridCube delta cell := by
    rw [finalEq, Set.inter_iUnion]
    congr 1
    funext cell
    rw [Set.inter_iUnion]
  let threshold : ENNReal :=
    (100 : ENNReal)⁻¹ *
      volume source *
      (volume tube.carrier)⁻¹
  calc
    (100 : ENNReal)⁻¹ *
          volume source *
          (volume tube.carrier)⁻¹ *
          volume finalCarrier =
        threshold *
          ∑ cell ∈ cells,
            volume (wz1PaperGridCube delta cell) := by
      rw [finalEq,
        MeasureTheory.measure_biUnion_finset
          cellsDisjoint cellsMeasurable]
    _ =
        ∑ cell ∈ cells,
          threshold *
            volume (wz1PaperGridCube delta cell) := by
      rw [Finset.mul_sum]
    _ ≤
        ∑ cell ∈ cells,
          volume
            (source ∩ wz1PaperGridCube delta cell) := by
      exact Finset.sum_le_sum fun cell hcell => by
        simpa [threshold] using cellBound cell hcell
    _ =
        volume
          (⋃ cell ∈ cells,
            source ∩ wz1PaperGridCube delta cell) := by
      exact
        (MeasureTheory.measure_biUnion_finset
          traceDisjoint traceMeasurable).symm
    _ = volume (source ∩ finalCarrier) := by
      rw [traceEq]

end Kakeya.Assouad

end
