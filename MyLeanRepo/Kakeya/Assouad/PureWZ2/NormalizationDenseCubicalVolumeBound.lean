import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationTopLevelAssembly

/-!
# Aggregate volume bound for normalization dense cubicalization

For finitely many indexed tubes and source sets, assume every source has
density at least `lambda` inside its tube and that one finite set of paper
grid cells covers every cropped paper carrier.  Then the union of the
canonical dense cubicalizations expands the source union's volume by at most
`100 * lambda⁻¹`.

The proof assigns each globally active grid cell to one tube whose dense
cubicalization contains the whole cell.  It then sums the defining density
inequality over the disjoint grid partition.  In particular, it does not sum
the source sets tube by tube, which would lose control when they overlap.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/--
The finite indexed union of canonical dense cubicalizations has volume at
most `100 * lambda⁻¹` times the volume of the corresponding source union.
-/
theorem pureWZ2_denseCubicalization_iUnion_volume_upper
    {delta : ℝ}
    (hdelta : 0 < delta)
    {n : ℕ}
    (tubes : Fin n → Kakeya.DeltaTube delta)
    (sources : Fin n → Set Point3)
    (lambda : ENNReal)
    (lambda_pos : 0 < lambda)
    (lambda_ne_top : lambda ≠ ⊤)
    (allCells : Finset (ℤ × ℤ × ℤ))
    (paperCarrierCover :
      ∀ index,
        wz1PaperTubeCarrier (tubes index) ⊆
          ⋃ cell ∈ allCells,
            wz1PaperGridCube delta cell)
    (perTubeDensity :
      ∀ index,
        lambda * volume (tubes index).carrier ≤
          volume (sources index))
    (sourceMeasurable :
      ∀ index, MeasurableSet (sources index)) :
    volume
        (⋃ index,
          pureWZ2DenseCubicalization
            (tubes index) (sources index)) ≤
      100 * lambda⁻¹ *
        volume (⋃ index, sources index) := by
  let denseUnion : Set Point3 :=
    ⋃ index,
      pureWZ2DenseCubicalization
        (tubes index) (sources index)
  let sourceUnion : Set Point3 := ⋃ index, sources index
  have sourceUnionMeasurable : MeasurableSet sourceUnion :=
    MeasurableSet.iUnion sourceMeasurable
  have denseUnionCubical :
      ∀ point ∈ denseUnion,
        wz1PaperGridCube delta
            (wz1PaperGridIndex delta point) ⊆
          denseUnion := by
    intro point pointDense
    rcases Set.mem_iUnion.mp pointDense with
      ⟨index, pointIndex⟩
    exact
      (pureWZ2DenseCubicalization_cubical_topLevel
        (tubes index) (sources index)
        point pointIndex).trans
          (Set.subset_iUnion
            (fun index =>
              pureWZ2DenseCubicalization
                (tubes index) (sources index))
            index)
  let activeCells : Finset (ℤ × ℤ × ℤ) :=
    allCells.filter fun cell =>
      wz1PaperGridCube delta cell ⊆ denseUnion
  have denseUnion_eq :
      denseUnion =
        ⋃ cell ∈ activeCells,
          wz1PaperGridCube delta cell := by
    apply Set.Subset.antisymm
    · intro point pointDense
      let cell := wz1PaperGridIndex delta point
      have pointCell :
          point ∈ wz1PaperGridCube delta cell :=
        (mem_wz1PaperGridCube delta cell point).mpr rfl
      have cellSubset :
          wz1PaperGridCube delta cell ⊆ denseUnion :=
        denseUnionCubical point pointDense
      have cellMemAll : cell ∈ allCells := by
        rcases Set.mem_iUnion.mp pointDense with
          ⟨index, pointIndex⟩
        have pointPaper :
            point ∈ wz1PaperTubeCarrier (tubes index) :=
          pureWZ2DenseCubicalization_subset_paperCarrier_topLevel
            (tubes index) (sources index) pointIndex
        rcases Set.mem_iUnion₂.mp
            (paperCarrierCover index pointPaper) with
          ⟨coverCell, coverCellMem, pointCoverCell⟩
        have cellEq : cell = coverCell := by
          exact
            ((mem_wz1PaperGridCube delta coverCell point).mp
              pointCoverCell)
        simpa [cellEq] using coverCellMem
      have cellActive : cell ∈ activeCells := by
        exact Finset.mem_filter.mpr ⟨cellMemAll, cellSubset⟩
      exact Set.mem_iUnion₂.mpr
        ⟨cell, cellActive, pointCell⟩
    · intro point pointActive
      rcases Set.mem_iUnion₂.mp pointActive with
        ⟨cell, cellActive, pointCell⟩
      exact
        (Finset.mem_filter.mp cellActive).2 pointCell
  have activeCellOwner :
      ∀ cell ∈ activeCells,
        ∃ index : Fin n,
          wz1PaperGridCube delta cell ⊆
            pureWZ2DenseCubicalization
              (tubes index) (sources index) := by
    intro cell cellActive
    have cellSubset :
        wz1PaperGridCube delta cell ⊆ denseUnion :=
      (Finset.mem_filter.mp cellActive).2
    have cellNonempty :
        (wz1PaperGridCube delta cell).Nonempty := by
      by_contra cellEmpty
      have cellEqEmpty :
          wz1PaperGridCube delta cell = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp cellEmpty
      have cellVolumePos :=
        wz1PaperGridCube_volume_pos hdelta cell
      rw [cellEqEmpty] at cellVolumePos
      simpa using cellVolumePos
    rcases cellNonempty with ⟨point, pointCell⟩
    have pointDense := cellSubset pointCell
    rcases Set.mem_iUnion.mp pointDense with
      ⟨index, pointIndex⟩
    have pointCellIndex :
        wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp pointCell
    refine ⟨index, ?_⟩
    rw [← pointCellIndex]
    exact
      pureWZ2DenseCubicalization_cubical_topLevel
        (tubes index) (sources index)
        point pointIndex
  have activeCellDensity :
      ∀ cell ∈ activeCells,
        (100 : ENNReal)⁻¹ * lambda *
              volume (wz1PaperGridCube delta cell) ≤
          volume
            (sourceUnion ∩
              wz1PaperGridCube delta cell) := by
    intro cell cellActive
    rcases activeCellOwner cell cellActive with
      ⟨index, cellSubset⟩
    have cellNonempty :
        (wz1PaperGridCube delta cell).Nonempty := by
      by_contra cellEmpty
      have cellEqEmpty :
          wz1PaperGridCube delta cell = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp cellEmpty
      have cellVolumePos :=
        wz1PaperGridCube_volume_pos hdelta cell
      rw [cellEqEmpty] at cellVolumePos
      simpa using cellVolumePos
    rcases cellNonempty with ⟨point, pointCell⟩
    have pointDense := cellSubset pointCell
    have pointCellIndex :
        wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp pointCell
    have selectedCellDensity :
        (100 : ENNReal)⁻¹ *
              volume (sources index) *
              (volume (tubes index).carrier)⁻¹ *
              volume (wz1PaperGridCube delta cell) ≤
          volume
            (sources index ∩
              wz1PaperGridCube delta cell) := by
      simpa [pureWZ2DenseCubicalization,
        pointCellIndex] using pointDense.2
    have tubeVolumePos :
        0 < volume (tubes index).carrier :=
      wz2_paper_ordinary_tube_volume_pos
        (tubes index) hdelta
    have tubeVolumeNeTop :
        volume (tubes index).carrier ≠ ⊤ :=
      wz2_paper_ordinary_tube_volume_ne_top
        (tubes index) hdelta
    have densityRatio :
        lambda ≤
          volume (sources index) *
            (volume (tubes index).carrier)⁻¹ := by
      calc
        lambda =
            (lambda * volume (tubes index).carrier) *
              (volume (tubes index).carrier)⁻¹ := by
          rw [mul_assoc,
            ENNReal.mul_inv_cancel
              tubeVolumePos.ne' tubeVolumeNeTop,
            mul_one]
        _ ≤
            volume (sources index) *
              (volume (tubes index).carrier)⁻¹ := by
          exact
            mul_le_mul_right'
              (perTubeDensity index)
              (volume (tubes index).carrier)⁻¹
    have sourceIntersectionMono :
        volume
              (sources index ∩
                wz1PaperGridCube delta cell) ≤
          volume
              (sourceUnion ∩
                wz1PaperGridCube delta cell) := by
      apply measure_mono
      exact Set.inter_subset_inter
        (Set.subset_iUnion sources index)
        Set.Subset.rfl
    calc
      (100 : ENNReal)⁻¹ * lambda *
            volume (wz1PaperGridCube delta cell) ≤
          (100 : ENNReal)⁻¹ *
              (volume (sources index) *
                (volume (tubes index).carrier)⁻¹) *
              volume (wz1PaperGridCube delta cell) := by
        gcongr
      _ =
          (100 : ENNReal)⁻¹ *
              volume (sources index) *
              (volume (tubes index).carrier)⁻¹ *
              volume (wz1PaperGridCube delta cell) := by
        ring
      _ ≤
          volume
            (sources index ∩
              wz1PaperGridCube delta cell) :=
        selectedCellDensity
      _ ≤
          volume
            (sourceUnion ∩
              wz1PaperGridCube delta cell) :=
        sourceIntersectionMono
  have activeCellsDisjoint :
      Set.PairwiseDisjoint (↑activeCells)
        (fun cell => wz1PaperGridCube delta cell) := by
    intro first _ second _ distinct
    exact wz1PaperGridCube_disjoint distinct
  have activeCellsMeasurable :
      ∀ cell ∈ activeCells,
        MeasurableSet (wz1PaperGridCube delta cell) :=
    fun cell _ => wz1PaperGridCube_measurable cell
  have denseUnionVolume :
      volume denseUnion =
        ∑ cell ∈ activeCells,
          volume (wz1PaperGridCube delta cell) := by
    rw [denseUnion_eq]
    exact
      MeasureTheory.measure_biUnion_finset
        activeCellsDisjoint activeCellsMeasurable
  have sourceDenseIntersection_eq :
      sourceUnion ∩ denseUnion =
        ⋃ cell ∈ activeCells,
          sourceUnion ∩
            wz1PaperGridCube delta cell := by
    rw [denseUnion_eq, Set.inter_iUnion]
    congr 1
    funext cell
    rw [Set.inter_iUnion]
  have sourceCellsDisjoint :
      Set.PairwiseDisjoint (↑activeCells)
        (fun cell =>
          sourceUnion ∩
            wz1PaperGridCube delta cell) := by
    intro first firstMem second secondMem distinct
    exact
      (activeCellsDisjoint
        firstMem secondMem distinct).mono
          Set.inter_subset_right Set.inter_subset_right
  have sourceCellsMeasurable :
      ∀ cell ∈ activeCells,
        MeasurableSet
          (sourceUnion ∩
            wz1PaperGridCube delta cell) :=
    fun cell _ =>
      sourceUnionMeasurable.inter
        (wz1PaperGridCube_measurable cell)
  have sourceDenseIntersectionVolume :
      volume (sourceUnion ∩ denseUnion) =
        ∑ cell ∈ activeCells,
          volume
            (sourceUnion ∩
              wz1PaperGridCube delta cell) := by
    rw [sourceDenseIntersection_eq]
    exact
      MeasureTheory.measure_biUnion_finset
        sourceCellsDisjoint sourceCellsMeasurable
  have aggregateDensity :
      (100 : ENNReal)⁻¹ * lambda *
            volume denseUnion ≤
        volume (sourceUnion ∩ denseUnion) := by
    calc
      (100 : ENNReal)⁻¹ * lambda *
            volume denseUnion =
          (100 : ENNReal)⁻¹ * lambda *
            ∑ cell ∈ activeCells,
              volume
                (wz1PaperGridCube delta cell) := by
        rw [denseUnionVolume]
      _ =
          ∑ cell ∈ activeCells,
            ((100 : ENNReal)⁻¹ * lambda *
              volume
                (wz1PaperGridCube delta cell)) := by
        rw [Finset.mul_sum]
      _ ≤
          ∑ cell ∈ activeCells,
            volume
              (sourceUnion ∩
                wz1PaperGridCube delta cell) := by
        exact Finset.sum_le_sum fun cell cellMem =>
          activeCellDensity cell cellMem
      _ =
          volume (sourceUnion ∩ denseUnion) :=
        sourceDenseIntersectionVolume.symm
  have aggregateSource :
      (100 : ENNReal)⁻¹ * lambda *
            volume denseUnion ≤
        volume sourceUnion :=
    aggregateDensity.trans
      (measure_mono Set.inter_subset_left)
  have hundredCancel :
      (100 : ENNReal) * (100 : ENNReal)⁻¹ = 1 := by
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
  have lambdaCancel : lambda⁻¹ * lambda = 1 :=
    ENNReal.inv_mul_cancel lambda_pos.ne' lambda_ne_top
  have rescaledAggregate :
      100 * lambda⁻¹ *
          ((100 : ENNReal)⁻¹ * lambda *
            volume denseUnion) =
        volume denseUnion := by
    calc
      100 * lambda⁻¹ *
          ((100 : ENNReal)⁻¹ * lambda *
            volume denseUnion) =
        (100 * (100 : ENNReal)⁻¹) *
          (lambda⁻¹ * lambda) *
          volume denseUnion := by
        ring
      _ = volume denseUnion := by
        rw [hundredCancel, lambdaCancel]
        simp
  change volume denseUnion ≤
    100 * lambda⁻¹ * volume sourceUnion
  rw [← rescaledAggregate]
  gcongr

/--
Canonical-shading wrapper for the global dense-cubical union estimate.

This hides the definitionally equal but syntactically distinct index types of
`TubeFamily`, `BodyFamily`, and the cropped paper shading.
-/
theorem pureWZ2NormalizationCroppedShading_union_volume_upper
    {delta : ℝ}
    (hdelta : 0 < delta)
    {ordinaryFamily croppedFamily :
      Kakeya.Streamlined.TubeFamily delta}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (indexEquiv :
      Fin ordinaryFamily.card ≃ Fin croppedFamily.card)
    (ordinaryRefined :
      Kakeya.Streamlined.TubeShading ordinaryFamily)
    (lambda : ENNReal)
    (lambda_pos : 0 < lambda)
    (lambda_ne_top : lambda ≠ ⊤)
    (allCells : Finset (ℤ × ℤ × ℤ))
    (paperCarrierCover :
      ∀ index,
        wz1PaperTubeCarrier (croppedFamily.tube index) ⊆
          ⋃ cell ∈ allCells,
            wz1PaperGridCube delta cell)
    (perTubeDensity :
      ∀ index,
        lambda * volume (croppedFamily.tube index).carrier ≤
          volume
            (frame ''
              ordinaryRefined.carrier (indexEquiv.symm index))) :
    volume
        (pureWZ2NormalizationCroppedShading
          frame indexEquiv ordinaryRefined).union ≤
      100 * lambda⁻¹ *
        volume (frame '' ordinaryRefined.union) := by
  have raw :=
    pureWZ2_denseCubicalization_iUnion_volume_upper
      hdelta croppedFamily.tube
      (fun index =>
        frame ''
          ordinaryRefined.carrier (indexEquiv.symm index))
      lambda lambda_pos lambda_ne_top allCells
      paperCarrierCover perTubeDensity
      (fun index =>
        frame.toHomeomorph.measurableEmbedding
          |>.measurableSet_image'
            (ordinaryRefined.measurable_carrier
              (indexEquiv.symm index)))
  have croppedUnion :
      (pureWZ2NormalizationCroppedShading
          frame indexEquiv ordinaryRefined).union =
        ⋃ index : Fin croppedFamily.card,
          pureWZ2DenseCubicalization
            (croppedFamily.tube index)
            (frame ''
              ordinaryRefined.carrier
                (indexEquiv.symm index)) := by
    ext point
    constructor
    · rintro ⟨index, pointMem⟩
      let tubeIndex : Fin croppedFamily.card :=
        ⟨index.1, index.2⟩
      refine Set.mem_iUnion.mpr ⟨tubeIndex, ?_⟩
      change
        point ∈
          pureWZ2DenseCubicalization
            (croppedFamily.tube tubeIndex)
            (frame ''
              ordinaryRefined.carrier
                (indexEquiv.symm tubeIndex)) at pointMem
      exact pointMem
    · intro pointMem
      rcases Set.mem_iUnion.mp pointMem with
        ⟨index, indexMem⟩
      let shadingIndex :
          Fin (wz1PaperBodyFamily croppedFamily).card :=
        ⟨index.1, index.2⟩
      refine ⟨shadingIndex, ?_⟩
      change
        point ∈
          pureWZ2DenseCubicalization
            (croppedFamily.tube shadingIndex)
            (frame ''
              ordinaryRefined.carrier
                (indexEquiv.symm shadingIndex))
      change
        point ∈
          pureWZ2DenseCubicalization
            (croppedFamily.tube index)
            (frame ''
              ordinaryRefined.carrier
                (indexEquiv.symm index)) at indexMem
      exact indexMem
  have sourceUnion :
      (⋃ index : Fin croppedFamily.card,
          frame ''
            ordinaryRefined.carrier
              (indexEquiv.symm index)) =
        frame '' ordinaryRefined.union := by
    ext point
    constructor
    · intro pointMem
      rcases Set.mem_iUnion.mp pointMem with
        ⟨index, sourcePoint, sourceMem, rfl⟩
      exact
        ⟨sourcePoint,
          ⟨indexEquiv.symm index, sourceMem⟩,
          rfl⟩
    · rintro ⟨sourcePoint, ⟨index, sourceMem⟩, rfl⟩
      exact
        Set.mem_iUnion.mpr
          ⟨indexEquiv index, by
            simpa using
              (show frame sourcePoint ∈
                  frame '' ordinaryRefined.carrier index
                from ⟨sourcePoint, sourceMem, rfl⟩)⟩
  calc
    volume
        (pureWZ2NormalizationCroppedShading
          frame indexEquiv ordinaryRefined).union =
      volume
        (⋃ index : Fin croppedFamily.card,
          pureWZ2DenseCubicalization
            (croppedFamily.tube index)
            (frame ''
              ordinaryRefined.carrier
                (indexEquiv.symm index))) := by
      rw [croppedUnion]
    _ ≤
        100 * lambda⁻¹ *
          volume
            (⋃ index : Fin croppedFamily.card,
              frame ''
                ordinaryRefined.carrier
                  (indexEquiv.symm index)) :=
      raw
    _ =
        100 * lambda⁻¹ *
          volume (frame '' ordinaryRefined.union) := by
      rw [sourceUnion]

end Kakeya.Assouad

end
