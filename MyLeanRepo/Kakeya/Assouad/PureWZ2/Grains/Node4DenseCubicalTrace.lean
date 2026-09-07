import MyLeanRepo.Kakeya.Assouad.PureWZ2.DenseCubicalTrace
import MyLeanRepo.Kakeya.Assouad.WZ1.ShadingPruningMass
import MyLeanRepo.Kakeya.Assouad.TubeVolumeRatio
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.SameAxisThickening
import MyLeanRepo.Kakeya.Assouad.Hairbrush.HomogeneousTwoEndsHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalSlabLower

/-! Node 4-only dense-cubical trace infrastructure. -/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Regard the literal dense cubicalization of one ordinary shading as a
cropped paper shading.  Every selected cell lies in the cropped tube by
definition. -/
noncomputable def pureWZ2DenseCubicalShading
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family) :
    WZ1PaperTubeShading family where
  carrier index := pureWZ2DenseCubicalization
    (family.tube index) (ordinary.carrier index)
  measurable_carrier index := by
    let selectedCells : Set (ℤ × ℤ × ℤ) :=
      {cell | wz1PaperGridCube delta cell ⊆
          wz1PaperTubeCarrier (family.tube index) ∧
        (100 : ENNReal)⁻¹ * volume (ordinary.carrier index) *
              (volume (family.tube index).carrier)⁻¹ *
              volume (wz1PaperGridCube delta cell) ≤
            volume (ordinary.carrier index ∩
              wz1PaperGridCube delta cell)}
    have heq : pureWZ2DenseCubicalization
        (family.tube index) (ordinary.carrier index) =
      ⋃ cell : selectedCells, wz1PaperGridCube delta cell.1 := by
      ext point
      constructor
      · intro hpoint
        let cell := wz1PaperGridIndex delta point
        refine Set.mem_iUnion.mpr
          ⟨⟨cell, hpoint⟩,
            (mem_wz1PaperGridCube delta cell point).mpr rfl⟩
      · intro hpoint
        rcases Set.mem_iUnion.mp hpoint with ⟨cell, hcell⟩
        have hindex : wz1PaperGridIndex delta point = cell.1 :=
          (mem_wz1PaperGridCube delta cell.1 point).mp hcell
        change
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
              wz1PaperTubeCarrier (family.tube index) ∧
            (100 : ENNReal)⁻¹ * volume (ordinary.carrier index) *
                (volume (family.tube index).carrier)⁻¹ *
                volume (wz1PaperGridCube delta
                  (wz1PaperGridIndex delta point)) ≤
              volume (ordinary.carrier index ∩
                wz1PaperGridCube delta
                  (wz1PaperGridIndex delta point))
        rw [hindex]
        exact cell.property
    rw [heq]
    exact MeasurableSet.iUnion fun cell =>
      wz1PaperGridCube_measurable cell.1
  subset_body index point hpoint :=
    hpoint.1 <|
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) point).mpr rfl

theorem pureWZ2DenseCubicalShading_cubical
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family) :
    WZ1PaperIsCubicalShading
      (pureWZ2DenseCubicalShading ordinary) := by
  intro index point hpoint other hother
  change other ∈ pureWZ2DenseCubicalization
    (family.tube index) (ordinary.carrier index)
  have hindex : wz1PaperGridIndex delta other =
      wz1PaperGridIndex delta point :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) other).mp hother
  change
    wz1PaperGridCube delta (wz1PaperGridIndex delta other) ⊆
        wz1PaperTubeCarrier (family.tube index) ∧
      (100 : ENNReal)⁻¹ * volume (ordinary.carrier index) *
          (volume (family.tube index).carrier)⁻¹ *
          volume (wz1PaperGridCube delta
            (wz1PaperGridIndex delta other)) ≤
        volume (ordinary.carrier index ∩
          wz1PaperGridCube delta (wz1PaperGridIndex delta other))
  rwa [hindex]

/-- If an ordinary source is contained in a whole-cell cropped shading and
has positive mass on every tube, then its dense cubicalization is still a
subshading of that cropped shading. -/
theorem pureWZ2DenseCubicalShading_sub_cubical
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    (hdelta : 0 < delta)
    (hordinary : ∀ index, ordinary.carrier index ⊆ cropped.carrier index)
    (hcubical : WZ1PaperIsCubicalShading cropped)
    (hpositive : ∀ index, 0 < volume (ordinary.carrier index)) :
    PaperIsSubshading (pureWZ2DenseCubicalShading ordinary) cropped := by
  intro index point hpoint
  let cell := wz1PaperGridIndex delta point
  have hpointCell : point ∈ wz1PaperGridCube delta cell :=
    (mem_wz1PaperGridCube delta cell point).mpr rfl
  have hthresholdPos : 0 <
      (100 : ENNReal)⁻¹ * volume (ordinary.carrier index) *
        (volume (family.tube index).carrier)⁻¹ *
          volume (wz1PaperGridCube delta cell) := by
    have htubeTop : volume (family.tube index).carrier ≠ ⊤ :=
      wz2_paper_ordinary_tube_volume_ne_top (family.tube index) hdelta
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos (by norm_num) (hpositive index).ne').ne'
        (ENNReal.inv_pos.mpr htubeTop).ne').ne'
      (wz1PaperGridCube_volume_pos hdelta cell).ne'
  have hintersectionPos : 0 <
      volume (ordinary.carrier index ∩ wz1PaperGridCube delta cell) :=
    hthresholdPos.trans_le hpoint.2
  have hintersection :
      (ordinary.carrier index ∩ wz1PaperGridCube delta cell).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty.mp hempty, measure_empty] at hintersectionPos
    exact lt_irrefl 0 hintersectionPos
  rcases hintersection with ⟨sourcePoint, hsourceOrdinary, hsourceCell⟩
  have hsourceCropped := hordinary index hsourceOrdinary
  have hwhole := hcubical index sourcePoint hsourceCropped
  have hsourceIndex : wz1PaperGridIndex delta sourcePoint = cell :=
    (mem_wz1PaperGridCube delta cell sourcePoint).mp hsourceCell
  exact hwhole <| by
    rwa [hsourceIndex]

/-- Whole-cell provenance supplies exactly the crop-boundary hypothesis used
by dense-cell averaging. -/
theorem pureWZ2GridCube_subset_paperTube_of_sub_cubical
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    (hordinary : ∀ index, ordinary.carrier index ⊆ cropped.carrier index)
    (hcubical : WZ1PaperIsCubicalShading cropped)
    (index : Fin family.card) (cell : ℤ × ℤ × ℤ)
    (hcell :
      (ordinary.carrier index ∩ wz1PaperGridCube delta cell).Nonempty) :
    wz1PaperGridCube delta cell ⊆
      wz1PaperTubeCarrier (family.tube index) := by
  rcases hcell with ⟨sourcePoint, hsourceOrdinary, hsourceCell⟩
  have hsourceCropped := hordinary index hsourceOrdinary
  have hwhole := hcubical index sourcePoint hsourceCropped
  have hsourceIndex : wz1PaperGridIndex delta sourcePoint = cell :=
    (mem_wz1PaperGridCube delta cell sourcePoint).mp hsourceCell
  intro point hpoint
  exact cropped.subset_body index <| hwhole <| by
    rwa [hsourceIndex]

theorem pureWZ2DenseCubicalization_measurable
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta)
    (ordinary : Set Point3) :
    MeasurableSet (pureWZ2DenseCubicalization tube ordinary) := by
  let selectedCells : Set (ℤ × ℤ × ℤ) :=
    {cell | wz1PaperGridCube delta cell ⊆
        wz1PaperTubeCarrier tube ∧
      (100 : ENNReal)⁻¹ * volume ordinary *
            (volume tube.carrier)⁻¹ *
            volume (wz1PaperGridCube delta cell) ≤
          volume (ordinary ∩ wz1PaperGridCube delta cell)}
  have heq : pureWZ2DenseCubicalization tube ordinary =
      ⋃ cell : selectedCells, wz1PaperGridCube delta cell.1 := by
    ext point
    constructor
    · intro hpoint
      let cell := wz1PaperGridIndex delta point
      exact Set.mem_iUnion.mpr
        ⟨⟨cell, hpoint⟩,
          (mem_wz1PaperGridCube delta cell point).mpr rfl⟩
    · intro hpoint
      rcases Set.mem_iUnion.mp hpoint with ⟨cell, hcell⟩
      have hindex : wz1PaperGridIndex delta point = cell.1 :=
        (mem_wz1PaperGridCube delta cell.1 point).mp hcell
      change
        wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperTubeCarrier tube ∧
          (100 : ENNReal)⁻¹ * volume ordinary *
              (volume tube.carrier)⁻¹ *
              volume (wz1PaperGridCube delta
                (wz1PaperGridIndex delta point)) ≤
            volume (ordinary ∩ wz1PaperGridCube delta
              (wz1PaperGridIndex delta point))
      rw [hindex]
      exact cell.property
  rw [heq]
  exact MeasurableSet.iUnion fun cell =>
    wz1PaperGridCube_measurable cell.1

/-- Fine grid cells meeting one ordinary carrier inside the paper window. -/
def pureWZ2OrdinaryActiveCells
    {delta : ℝ}
    (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (ordinary : Set Point3) : Finset (ℤ × ℤ × ℤ) :=
  (wz1PaperGridIndicesInWindow delta hdelta).filter fun cell =>
    (ordinary ∩ wz1PaperGridCube delta cell).Nonempty

/-- The good cells in the literal dense cubicalization. -/
def pureWZ2OrdinaryDenseCells
    {delta : ℝ}
    (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (ordinary : Set Point3) : Finset (ℤ × ℤ × ℤ) :=
  (pureWZ2OrdinaryActiveCells hdelta tube ordinary).filter fun cell =>
    wz1PaperGridCube delta cell ⊆ wz1PaperTubeCarrier tube ∧
      (100 : ENNReal)⁻¹ * volume ordinary *
            (volume tube.carrier)⁻¹ *
            volume (wz1PaperGridCube delta cell) ≤
        volume (ordinary ∩ wz1PaperGridCube delta cell)

theorem ordinary_eq_biUnion_activeCells
    {delta : ℝ}
    (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (ordinary : Set Point3)
    (hcellContained : ∀ cell,
      (ordinary ∩ wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆ wz1PaperTubeCarrier tube) :
    ordinary = ⋃ cell ∈ pureWZ2OrdinaryActiveCells hdelta tube ordinary,
      ordinary ∩ wz1PaperGridCube delta cell := by
  ext point
  constructor
  · intro hpoint
    let cell := wz1PaperGridIndex delta point
    have hpointCell : point ∈ wz1PaperGridCube delta cell :=
      (mem_wz1PaperGridCube delta cell point).mpr rfl
    have hcellPaper := hcellContained cell ⟨point, hpoint, hpointCell⟩
    have hwindow : cell ∈ wz1PaperGridIndicesInWindow delta hdelta :=
      paper_point_gridIndex_in_window hdelta (hcellPaper hpointCell).2
    have hactive : cell ∈
        pureWZ2OrdinaryActiveCells hdelta tube ordinary := by
      exact Finset.mem_filter.mpr
        ⟨hwindow, ⟨point, hpoint, hpointCell⟩⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, hactive, hpoint, hpointCell⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, _hcell, hpoint⟩
    exact hpoint.1

theorem ordinary_inter_denseCubicalization_eq_biUnion_denseCells
    {delta : ℝ}
    (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (ordinary : Set Point3)
    (hcellContained : ∀ cell,
      (ordinary ∩ wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆ wz1PaperTubeCarrier tube) :
    ordinary ∩ pureWZ2DenseCubicalization tube ordinary =
      ⋃ cell ∈ pureWZ2OrdinaryDenseCells hdelta tube ordinary,
        ordinary ∩ wz1PaperGridCube delta cell := by
  ext point
  constructor
  · rintro ⟨hordinary, hdense⟩
    let cell := wz1PaperGridIndex delta point
    have hpointCell : point ∈ wz1PaperGridCube delta cell :=
      (mem_wz1PaperGridCube delta cell point).mpr rfl
    have hcellPaper := hcellContained cell
      ⟨point, hordinary, hpointCell⟩
    have hwindow : cell ∈ wz1PaperGridIndicesInWindow delta hdelta :=
      paper_point_gridIndex_in_window hdelta (hcellPaper hpointCell).2
    have hactive : cell ∈ pureWZ2OrdinaryActiveCells
        hdelta tube ordinary :=
      Finset.mem_filter.mpr
        ⟨hwindow, ⟨point, hordinary, hpointCell⟩⟩
    have hgood : cell ∈ pureWZ2OrdinaryDenseCells
        hdelta tube ordinary := by
      apply Finset.mem_filter.mpr
      exact ⟨hactive, hdense⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, hgood, hordinary, hpointCell⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpoint⟩
    have hgood := (Finset.mem_filter.mp hcell).2
    have hindex : wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp hpoint.2
    refine ⟨hpoint.1, ?_⟩
    simpa [pureWZ2DenseCubicalization, hindex] using hgood

/-- Summing the defining bad-cell inequalities bounds the ordinary mass lost
by dense cubicalization by one hundredth of the average-density coefficient
times the total volume of active fine cells. -/
theorem pureWZ2DenseCubicalization_bad_mass_bound
    {delta : ℝ}
    (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (ordinary : Set Point3)
    (hordinaryMeasurable : MeasurableSet ordinary)
    (hcellContained : ∀ cell,
      (ordinary ∩ wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆ wz1PaperTubeCarrier tube) :
    volume ordinary ≤
      volume (ordinary ∩ pureWZ2DenseCubicalization tube ordinary) +
        (100 : ENNReal)⁻¹ * volume ordinary *
          (volume tube.carrier)⁻¹ *
            volume
              (⋃ cell ∈ pureWZ2OrdinaryActiveCells hdelta tube ordinary,
                wz1PaperGridCube delta cell) := by
  let active := pureWZ2OrdinaryActiveCells hdelta tube ordinary
  let good := pureWZ2OrdinaryDenseCells hdelta tube ordinary
  let bad := active \ good
  let piece : (ℤ × ℤ × ℤ) → Set Point3 := fun cell =>
    ordinary ∩ wz1PaperGridCube delta cell
  have hactiveEq : ordinary = ⋃ cell ∈ active, piece cell := by
    simpa [active, piece] using
      ordinary_eq_biUnion_activeCells hdelta tube ordinary hcellContained
  have hgoodEq : ordinary ∩ pureWZ2DenseCubicalization tube ordinary =
      ⋃ cell ∈ good, piece cell := by
    simpa [good, piece] using
      ordinary_inter_denseCubicalization_eq_biUnion_denseCells
        hdelta tube ordinary hcellContained
  have hbadEq : ordinary \ pureWZ2DenseCubicalization tube ordinary =
      ⋃ cell ∈ bad, piece cell := by
    ext point
    constructor
    · rintro ⟨hpointOrdinary, hpointDense⟩
      have hpointActive : point ∈ ⋃ cell ∈ active, piece cell := by
        rw [← hactiveEq]
        exact hpointOrdinary
      rcases Set.mem_iUnion₂.mp hpointActive with
        ⟨cell, hcellActive, hpointPiece⟩
      have hcellBad : cell ∈ bad := by
        apply Finset.mem_sdiff.mpr
        refine ⟨hcellActive, ?_⟩
        intro hcellGood
        apply hpointDense
        have hpointGood : point ∈ ⋃ other ∈ good, piece other :=
          Set.mem_iUnion₂.mpr ⟨cell, hcellGood, hpointPiece⟩
        have hinter : point ∈
            ordinary ∩ pureWZ2DenseCubicalization tube ordinary := by
          rw [hgoodEq]
          exact hpointGood
        exact hinter.2
      exact Set.mem_iUnion₂.mpr ⟨cell, hcellBad, hpointPiece⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨cell, hcellBad, hpointPiece⟩
      have hpointOrdinary : point ∈ ordinary := hpointPiece.1
      refine ⟨hpointOrdinary, ?_⟩
      intro hpointDense
      have hpointGood : point ∈ ⋃ other ∈ good, piece other := by
        rw [← hgoodEq]
        exact ⟨hpointOrdinary, hpointDense⟩
      rcases Set.mem_iUnion₂.mp hpointGood with
        ⟨other, hotherGood, hpointOther⟩
      have hsame : cell = other := by
        by_contra hne
        exact Set.disjoint_left.mp
          (wz1PaperGridCube_disjoint hne)
          hpointPiece.2 hpointOther.2
      exact (Finset.mem_sdiff.mp hcellBad).2 (hsame ▸ hotherGood)
  have hbadPiece : ∀ cell ∈ bad,
      volume (piece cell) ≤
        (100 : ENNReal)⁻¹ * volume ordinary *
          (volume tube.carrier)⁻¹ *
            volume (wz1PaperGridCube delta cell) := by
    intro cell hcell
    have hnotGood := (Finset.mem_sdiff.mp hcell).2
    have hactive := (Finset.mem_sdiff.mp hcell).1
    have hpaper := hcellContained cell
      ((Finset.mem_filter.mp hactive).2)
    have hnotThreshold :
        ¬ (100 : ENNReal)⁻¹ * volume ordinary *
              (volume tube.carrier)⁻¹ *
              volume (wz1PaperGridCube delta cell) ≤
            volume (piece cell) := by
      intro hthreshold
      apply hnotGood
      apply Finset.mem_filter.mpr
      exact ⟨hactive, hpaper, hthreshold⟩
    exact (not_le.mp hnotThreshold).le
  have hbadVolume : volume
      (ordinary \ pureWZ2DenseCubicalization tube ordinary) ≤
      ∑ cell ∈ bad, volume (piece cell) := by
    rw [hbadEq]
    exact MeasureTheory.measure_biUnion_finset_le bad piece
  have hsumBad : (∑ cell ∈ bad, volume (piece cell)) ≤
      (100 : ENNReal)⁻¹ * volume ordinary *
        (volume tube.carrier)⁻¹ *
          ∑ cell ∈ bad, volume (wz1PaperGridCube delta cell) := by
    calc
      (∑ cell ∈ bad, volume (piece cell)) ≤
          ∑ cell ∈ bad,
            ((100 : ENNReal)⁻¹ * volume ordinary *
              (volume tube.carrier)⁻¹) *
                volume (wz1PaperGridCube delta cell) := by
        exact Finset.sum_le_sum fun cell hcell => hbadPiece cell hcell
      _ = (100 : ENNReal)⁻¹ * volume ordinary *
          (volume tube.carrier)⁻¹ *
            ∑ cell ∈ bad, volume (wz1PaperGridCube delta cell) := by
        rw [Finset.mul_sum]
  have hbadCellsVolume :
      ∑ cell ∈ bad, volume (wz1PaperGridCube delta cell) ≤
        volume (⋃ cell ∈ active, wz1PaperGridCube delta cell) := by
    have hcard : bad.card ≤ active.card :=
      Finset.card_le_card (Finset.sdiff_subset)
    calc
      ∑ cell ∈ bad, volume (wz1PaperGridCube delta cell) =
          ∑ _cell ∈ bad,
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
        apply Finset.sum_congr rfl
        intro cell _
        exact wz1PaperGridCube_volume_eq hdelta cell (0, 0, 0)
      _ =
          (bad.card : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
        simp [Finset.sum_const]
      _ ≤ (active.card : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
        gcongr
      _ = volume (⋃ cell ∈ active, wz1PaperGridCube delta cell) := by
        exact (wz1PaperGridCube_volume_biUnion hdelta active).symm
  have hdenseMeasurable : MeasurableSet
      (pureWZ2DenseCubicalization tube ordinary) :=
    pureWZ2DenseCubicalization_measurable tube ordinary
  have hsplit :
      volume (ordinary ∩ pureWZ2DenseCubicalization tube ordinary) +
          volume (ordinary \ pureWZ2DenseCubicalization tube ordinary) =
        volume ordinary :=
    MeasureTheory.measure_inter_add_sdiff ordinary hdenseMeasurable
  have hbadFinal :
      volume (ordinary \ pureWZ2DenseCubicalization tube ordinary) ≤
        (100 : ENNReal)⁻¹ * volume ordinary *
          (volume tube.carrier)⁻¹ *
            volume (⋃ cell ∈ active, wz1PaperGridCube delta cell) :=
    hbadVolume.trans <| hsumBad.trans <| by
      exact mul_le_mul_left' hbadCellsVolume _
  calc
    volume ordinary =
        volume (ordinary ∩ pureWZ2DenseCubicalization tube ordinary) +
          volume (ordinary \ pureWZ2DenseCubicalization tube ordinary) := by
      exact hsplit.symm
    _ ≤ volume (ordinary ∩ pureWZ2DenseCubicalization tube ordinary) +
        ((100 : ENNReal)⁻¹ * volume ordinary *
          (volume tube.carrier)⁻¹ *
            volume
              (⋃ cell ∈ active, wz1PaperGridCube delta cell)) := by
      exact add_le_add_right hbadFinal _
    _ = _ := by simp only [active]

/-- Every fine grid cell meeting an ordinary tube lies in the same-axis tube
whose radius is enlarged by the cell diameter. -/
theorem pureWZ2OrdinaryActiveCells_subset_sameAxisTube
    {delta : ℝ} (hdelta : 0 < delta)
    (tube : Kakeya.DeltaTube delta)
    (cell : ℤ × ℤ × ℤ)
    (hcell : (tube.carrier ∩ wz1PaperGridCube delta cell).Nonempty) :
    wz1PaperGridCube delta cell ⊆
      (sameAxisTube (rho := delta * (1 + Real.sqrt 3)) tube).carrier := by
  rcases hcell with ⟨sourcePoint, hsourceTube, hsourceCell⟩
  intro point hpointCell
  have hsegmentCompact :
      IsCompact (Kakeya.unitSegment tube.base tube.direction) :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  rcases exists_dist_le_of_mem_cthickening_closed
      hsegmentCompact.isClosed hdelta.le hsourceTube with
    ⟨axisPoint, haxisPoint, hsourceAxis⟩
  have hpointSource : dist point sourcePoint ≤ delta * Real.sqrt 3 :=
    wz1PaperGridCube_diameter hdelta cell hpointCell hsourceCell
  have hpointAxis :
      dist point axisPoint ≤ delta * (1 + Real.sqrt 3) := by
    calc
      dist point axisPoint ≤ dist point sourcePoint +
          dist sourcePoint axisPoint := dist_triangle _ _ _
      _ ≤ delta * Real.sqrt 3 + delta := by gcongr
      _ = delta * (1 + Real.sqrt 3) := by ring
  exact Metric.mem_cthickening_of_dist_le point axisPoint
    (delta * (1 + Real.sqrt 3))
    (Kakeya.unitSegment tube.base tube.direction)
    haxisPoint hpointAxis

theorem pureWZ2OrdinaryActiveCells_union_volume_bound
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaSmall : delta * (1 + Real.sqrt 3) ≤ 1)
    (tube : Kakeya.DeltaTube delta) :
    volume
        (⋃ cell ∈ pureWZ2OrdinaryActiveCells hdelta tube tube.carrier,
          wz1PaperGridCube delta cell) ≤
      27 * Kakeya.deltaTubeVolume delta := by
  let enlarged : Kakeya.DeltaTube (delta * (1 + Real.sqrt 3)) :=
    sameAxisTube tube
  have hunion :
      (⋃ cell ∈ pureWZ2OrdinaryActiveCells hdelta tube tube.carrier,
        wz1PaperGridCube delta cell) ⊆ enlarged.carrier := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    exact pureWZ2OrdinaryActiveCells_subset_sameAxisTube hdelta tube cell
      ((Finset.mem_filter.mp hcell).2) hpointCell
  have hscale : delta ≤ delta * (1 + Real.sqrt 3) := by
    have hsqrt : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    nlinarith
  have hratio := deltaTubeVolume_ratio_bound_cylinder hdelta hscale
    hdeltaSmall
  calc
    volume
        (⋃ cell ∈ pureWZ2OrdinaryActiveCells hdelta tube tube.carrier,
          wz1PaperGridCube delta cell) ≤ volume enlarged.carrier :=
      measure_mono hunion
    _ = Kakeya.deltaTubeVolume (delta * (1 + Real.sqrt 3)) :=
      tube_volume_scaling.1 _ enlarged
    _ ≤ 3 * Kakeya.realRpowENN (delta * (1 + Real.sqrt 3)) 2 *
          (Kakeya.realRpowENN delta 2)⁻¹ *
            Kakeya.deltaTubeVolume delta := hratio
    _ ≤ 27 * Kakeya.deltaTubeVolume delta := by
      have hsqrt : Real.sqrt 3 ≤ 2 := by
        nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
          Real.sqrt_nonneg 3]
      have hratioPower :
          Kakeya.realRpowENN (delta * (1 + Real.sqrt 3)) 2 ≤
            9 * Kakeya.realRpowENN delta 2 := by
        simp only [Kakeya.realRpowENN]
        rw [show Real.rpow (delta * (1 + Real.sqrt 3)) 2 =
            (delta * (1 + Real.sqrt 3)) ^ 2 by
          exact Real.rpow_two _,
          show Real.rpow delta 2 = delta ^ 2 by
            exact Real.rpow_two _]
        have hreal :
            (delta * (1 + Real.sqrt 3)) ^ 2 ≤ 9 * delta ^ 2 := by
          have hfactor : 1 + Real.sqrt 3 ≤ 3 := by linarith
          have hfactorNonneg : 0 ≤ 1 + Real.sqrt 3 := by positivity
          have hscaled : delta * (1 + Real.sqrt 3) ≤ 3 * delta := by
            simpa [mul_comm] using
              mul_le_mul_of_nonneg_left hfactor hdelta.le
          have hscaledNonneg : 0 ≤ delta * (1 + Real.sqrt 3) := by positivity
          nlinarith
        calc
          ENNReal.ofReal ((delta * (1 + Real.sqrt 3)) ^ 2) ≤
              ENNReal.ofReal (9 * delta ^ 2) :=
            ENNReal.ofReal_mono hreal
          _ = 9 * ENNReal.ofReal (delta ^ 2) := by
            rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9)]
            norm_num
      have hdeltaPowerZero : Kakeya.realRpowENN delta 2 ≠ 0 := by
        simp [Kakeya.realRpowENN, hdelta.ne']
      have hdeltaPowerTop : Kakeya.realRpowENN delta 2 ≠ ⊤ := by
        simp [Kakeya.realRpowENN]
      calc
        3 * Kakeya.realRpowENN (delta * (1 + Real.sqrt 3)) 2 *
              (Kakeya.realRpowENN delta 2)⁻¹ *
                Kakeya.deltaTubeVolume delta ≤
            3 * (9 * Kakeya.realRpowENN delta 2) *
              (Kakeya.realRpowENN delta 2)⁻¹ *
                Kakeya.deltaTubeVolume delta := by gcongr
        _ = 27 * Kakeya.deltaTubeVolume delta := by
          rw [show 3 * (9 * Kakeya.realRpowENN delta 2) *
              (Kakeya.realRpowENN delta 2)⁻¹ =
                27 * (Kakeya.realRpowENN delta 2 *
                  (Kakeya.realRpowENN delta 2)⁻¹) by ring,
            ENNReal.mul_inv_cancel hdeltaPowerZero hdeltaPowerTop, mul_one]
        _ = 27 * Kakeya.deltaTubeVolume delta := rfl

/-- A source supported on a deeply interior reference tube has no grid-cell
loss at the paper crop boundary.  The target tube may have a different
unit-segment representative, but it must encode the same full axis. -/
theorem pureWZ2GridCube_subset_paperTube_of_reference_margin
    {delta : ℝ} (hdelta : 0 < delta)
    (tube reference : Kakeya.DeltaTube delta)
    (haxis : tubeAxisLine reference = tubeAxisLine tube)
    (hmargin :
      ‖wz2PaperTubeMidpoint reference‖ +
          (1 / 2 + delta * (1 + Real.sqrt 3)) ≤ 1)
    (ordinary : Set Point3)
    (hordinary : ordinary ⊆ reference.carrier)
    (cell : ℤ × ℤ × ℤ)
    (hcell : (ordinary ∩ wz1PaperGridCube delta cell).Nonempty) :
    wz1PaperGridCube delta cell ⊆ wz1PaperTubeCarrier tube := by
  rcases hcell with ⟨sourcePoint, hsourceOrdinary, hsourceCell⟩
  have hsourceReference : sourcePoint ∈ reference.carrier :=
    hordinary hsourceOrdinary
  intro point hpointCell
  have henlarged : point ∈
      (sameAxisTube (rho := delta * (1 + Real.sqrt 3)) reference).carrier :=
    pureWZ2OrdinaryActiveCells_subset_sameAxisTube hdelta reference cell
      ⟨sourcePoint, hsourceReference, hsourceCell⟩ hpointCell
  constructor
  · have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    have hradius : delta * (1 + Real.sqrt 3) ≤ 6 * delta := by
      nlinarith
    have hnearReferenceLine : point ∈
        Metric.cthickening (delta * (1 + Real.sqrt 3))
          (tubeAxisLine reference) :=
      Metric.cthickening_subset_of_subset
        (delta * (1 + Real.sqrt 3))
        (wz2_paper_unitSegment_subset_axisLine reference) henlarged
    rw [haxis] at hnearReferenceLine
    exact Metric.cthickening_mono hradius
      (tubeAxisLine tube) hnearReferenceLine
  · have hradiusPos : 0 < delta * (1 + Real.sqrt 3) := by
      positivity
    have hpointMidpoint :
        dist point (wz2PaperTubeMidpoint reference) ≤
          1 / 2 + delta * (1 + Real.sqrt 3) := by
      simpa [wz2PaperTubeMidpoint] using
        tube_subset_midpoint_closedBall hradiusPos
          (sameAxisTube
            (rho := delta * (1 + Real.sqrt 3)) reference) henlarged
    have hmidpointOrigin :
        dist (wz2PaperTubeMidpoint reference) 0 =
          ‖wz2PaperTubeMidpoint reference‖ := by
      simp [dist_eq_norm]
    have hpointNorm : ‖point‖ ≤ 1 := by
      calc
        ‖point‖ = dist point 0 := by simp [dist_eq_norm]
        _ ≤ dist point (wz2PaperTubeMidpoint reference) +
              dist (wz2PaperTubeMidpoint reference) 0 :=
          dist_triangle _ _ _
        _ ≤ (1 / 2 + delta * (1 + Real.sqrt 3)) +
              ‖wz2PaperTubeMidpoint reference‖ := by
          rw [hmidpointOrigin]
          gcongr
        _ ≤ 1 := by linarith
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq]
    norm_num
    exact
      ⟨(PiLp.norm_apply_le point 0).trans hpointNorm,
        (PiLp.norm_apply_le point 1).trans hpointNorm,
        (PiLp.norm_apply_le point 2).trans hpointNorm⟩

/-- Dense cubicalization retains at least `73/100` of every ordinary tube
carrier.  The constant is inessential; it comes from the crude volume ratio
between one tube and the same-axis tube enlarged by one cell diameter. -/
theorem pureWZ2DenseCubicalization_trace_retention
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaSmall : delta * (1 + Real.sqrt 3) ≤ 1)
    (tube : Kakeya.DeltaTube delta)
    (ordinary : Set Point3)
    (hordinaryMeasurable : MeasurableSet ordinary)
    (hordinary : ordinary ⊆ tube.carrier)
    (hcellContained : ∀ cell,
      (ordinary ∩ wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆ wz1PaperTubeCarrier tube) :
    (73 / 100 : ENNReal) * volume ordinary ≤
      volume (ordinary ∩ pureWZ2DenseCubicalization tube ordinary) := by
  have hmass := pureWZ2DenseCubicalization_bad_mass_bound hdelta tube
    ordinary hordinaryMeasurable hcellContained
  have hactiveVolume := pureWZ2OrdinaryActiveCells_union_volume_bound
    hdelta hdeltaSmall tube
  have hactiveSubset :
      pureWZ2OrdinaryActiveCells hdelta tube ordinary ⊆
        pureWZ2OrdinaryActiveCells hdelta tube tube.carrier := by
    intro cell hcell
    rw [pureWZ2OrdinaryActiveCells, Finset.mem_filter] at hcell ⊢
    rcases hcell with ⟨hwindow, point, hpointOrdinary, hpointCell⟩
    exact ⟨hwindow, point, hordinary hpointOrdinary, hpointCell⟩
  have hunionSubset :
      (⋃ cell ∈ pureWZ2OrdinaryActiveCells hdelta tube ordinary,
          wz1PaperGridCube delta cell) ⊆
        ⋃ cell ∈ pureWZ2OrdinaryActiveCells hdelta tube tube.carrier,
          wz1PaperGridCube delta cell := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    exact Set.mem_iUnion₂.mpr
      ⟨cell, hactiveSubset hcell, hpointCell⟩
  have hactiveOrdinaryVolume :
      volume
          (⋃ cell ∈ pureWZ2OrdinaryActiveCells hdelta tube ordinary,
            wz1PaperGridCube delta cell) ≤
        27 * Kakeya.deltaTubeVolume delta :=
    (measure_mono hunionSubset).trans hactiveVolume
  have herror :
      (100 : ENNReal)⁻¹ * volume ordinary *
          (volume tube.carrier)⁻¹ *
            volume
              (⋃ cell ∈ pureWZ2OrdinaryActiveCells hdelta tube ordinary,
                wz1PaperGridCube delta cell) ≤
        (27 / 100 : ENNReal) * volume ordinary := by
    calc
      (100 : ENNReal)⁻¹ * volume ordinary *
            (volume tube.carrier)⁻¹ *
              volume
                (⋃ cell ∈ pureWZ2OrdinaryActiveCells hdelta tube ordinary,
                  wz1PaperGridCube delta cell) ≤
          (100 : ENNReal)⁻¹ * volume ordinary *
            (volume tube.carrier)⁻¹ *
              (27 * Kakeya.deltaTubeVolume delta) := by
        gcongr
      _ = (27 / 100 : ENNReal) * volume ordinary := by
        have htubeZero : volume tube.carrier ≠ 0 :=
          (wz2_paper_ordinary_tube_volume_pos tube hdelta).ne'
        have htubeTop : volume tube.carrier ≠ ⊤ :=
          wz2_paper_ordinary_tube_volume_ne_top tube hdelta
        rw [← tube_volume_scaling.1 delta tube]
        change
          (100 : ENNReal)⁻¹ * volume ordinary *
                (volume tube.carrier)⁻¹ *
                  (27 * volume tube.carrier) =
            (27 / 100 : ENNReal) * volume ordinary
        rw [show
          (100 : ENNReal)⁻¹ * volume ordinary *
                (volume tube.carrier)⁻¹ *
                  (27 * volume tube.carrier) =
              ((100 : ENNReal)⁻¹ * 27) * volume ordinary *
                ((volume tube.carrier)⁻¹ * volume tube.carrier) by
          ring, ENNReal.inv_mul_cancel htubeZero htubeTop, mul_one]
        simp only [div_eq_mul_inv]
        ac_rfl
  have hsourceFinite : volume ordinary ≠ ⊤ :=
    ne_top_of_le_ne_top
      (wz2_paper_ordinary_tube_volume_ne_top tube hdelta)
      (measure_mono hordinary)
  have hpartition :
      (73 / 100 : ENNReal) + 27 / 100 = 1 := by
    have hseventyThree :
        (73 / 100 : ENNReal) = ENNReal.ofReal (73 / 100 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
      norm_num
    have htwentySeven :
        (27 / 100 : ENNReal) = ENNReal.ofReal (27 / 100 : ℝ) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100)]
      norm_num
    rw [hseventyThree, htwentySeven,
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num
  apply retained_mass_of_error_le_fraction
      hsourceFinite (ENNReal.div_ne_top (by norm_num) (by norm_num))
      hpartition hmass
  exact herror

/-- The per-tube dense-cell estimate summed over a genuine ordinary tube
shading. -/
theorem pureWZ2DenseCubicalShading_mass_retention
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaSmall : delta * (1 + Real.sqrt 3) ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (hcellContained : ∀ index cell,
      (ordinary.carrier index ∩
        wz1PaperGridCube delta cell).Nonempty →
      wz1PaperGridCube delta cell ⊆
        wz1PaperTubeCarrier (family.tube index)) :
    (73 / 100 : ENNReal) * ordinary.mass ≤
      ∑ index : Fin family.card,
        volume (ordinary.carrier index ∩
          (pureWZ2DenseCubicalShading ordinary).carrier index) := by
  change
    (73 / 100 : ENNReal) *
        (∑ index : Fin family.card, volume (ordinary.carrier index)) ≤
      ∑ index : Fin family.card,
        volume (ordinary.carrier index ∩
          pureWZ2DenseCubicalization
            (family.tube index) (ordinary.carrier index))
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun index _ =>
    pureWZ2DenseCubicalization_trace_retention hdelta hdeltaSmall
      (family.tube index) (ordinary.carrier index)
      (ordinary.measurable_carrier index)
      (ordinary.subset_body index) (hcellContained index)

end Kakeya.Assouad

end
