import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64IsotropicPlaneMap
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperGridCubeVolume
import MyLeanRepo.Kakeya.Assouad.WZ1.GridCellPruning

/-!
# Cubical volume upper bounds for Proposition 6.4

This file isolates the finite cell-count argument behind the upper union-volume
bound.  A cubical source union is partitioned by its active source cells.  If
the image of each such cell lies in one target-scale ball, then the final
target-grid saturation uses only a uniformly bounded number of cells over each
source cell.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

private theorem gridCell_sqrtThree_eq_paperGridCube_local
    {scale : ℝ} (hscale : 0 < scale)
    (cell : ℤ × ℤ × ℤ) :
    gridCell (Real.sqrt 3 * scale) cell =
      wz1PaperGridCube scale cell := by
  have hsqrt : Real.sqrt 3 ≠ 0 := by positivity
  have hside :
      gridSide ((Real.sqrt 3 * scale) / 2) = scale := by
    simp only [gridSide]
    field_simp [hsqrt]
  ext point
  simp [gridCell, rhoGridIndex, wz1PaperGridCube,
    wz1PaperGridIndex, hside]

private theorem paper_abs_floor_sub_le
    {first second : ℝ} {radius : ℕ}
    (h : |first - second| ≤ (radius : ℝ)) :
    |(Int.floor first : ℤ) - Int.floor second| ≤ (radius : ℤ) := by
  have hforward : (Int.floor first : ℤ) - Int.floor second ≤ radius := by
    by_contra hnot
    have hlarge : (radius : ℤ) + 1 ≤
        (Int.floor first : ℤ) - Int.floor second := by omega
    have hcast : (radius : ℝ) + 1 ≤
        (Int.floor first : ℝ) - Int.floor second := by exact_mod_cast hlarge
    linarith [Int.floor_le first, Int.lt_floor_add_one second,
      (abs_le.mp h).2]
  have hbackward : -(radius : ℤ) ≤
      (Int.floor first : ℤ) - Int.floor second := by
    by_contra hnot
    have hlarge : (radius : ℤ) + 1 ≤
        (Int.floor second : ℤ) - Int.floor first := by omega
    have hcast : (radius : ℝ) + 1 ≤
        (Int.floor second : ℝ) - Int.floor first := by exact_mod_cast hlarge
    linarith [Int.floor_le second, Int.lt_floor_add_one first,
      (abs_le.mp h).1]
  exact abs_le.mpr ⟨hbackward, hforward⟩

private theorem gridCellsIntersecting_finset_cover_bound_local
    {tau : ℝ} {source : Set Point3}
    {indexType : Type*} [DecidableEq indexType]
    (indices : Finset indexType) (piece : indexType → Set Point3)
    (hcover : source ⊆ ⋃ index ∈ indices, piece index)
    (bound : ℕ)
    (hpiece : ∀ index ∈ indices,
      (gridCellsIntersecting tau (piece index)).Finite ∧
        Set.ncard (gridCellsIntersecting tau (piece index)) ≤ bound) :
    (gridCellsIntersecting tau source).Finite ∧
      Set.ncard (gridCellsIntersecting tau source) ≤ indices.card * bound := by
  let cells (index : indexType) : Finset (ℤ × ℤ × ℤ) :=
    if hindex : index ∈ indices then (hpiece index hindex).1.toFinset else ∅
  let allCells := indices.biUnion cells
  have hsubset : gridCellsIntersecting tau source ⊆
      (allCells : Set (ℤ × ℤ × ℤ)) := by
    rintro cell ⟨point, hpointCell, hpointSource⟩
    rcases Set.mem_iUnion₂.mp (hcover hpointSource) with
      ⟨index, hindex, hpointPiece⟩
    refine Finset.mem_biUnion.mpr ⟨index, hindex, ?_⟩
    have hcell : cell ∈ gridCellsIntersecting tau (piece index) :=
      ⟨point, hpointCell, hpointPiece⟩
    simp only [cells, dif_pos hindex]
    exact (Set.Finite.mem_toFinset (hpiece index hindex).1).2 hcell
  refine ⟨allCells.finite_toSet.subset hsubset, ?_⟩
  calc
    Set.ncard (gridCellsIntersecting tau source) ≤ allCells.card := by
      simpa using Set.ncard_le_ncard hsubset allCells.finite_toSet
    _ ≤ ∑ index ∈ indices, (cells index).card := Finset.card_biUnion_le
    _ ≤ ∑ _index ∈ indices, bound := by
      apply Finset.sum_le_sum
      intro index hindex
      simp only [cells, dif_pos hindex]
      rw [← Set.ncard_eq_toFinset_card
        (gridCellsIntersecting tau (piece index)) (hpiece index hindex).1]
      exact (hpiece index hindex).2
    _ = indices.card * bound := by simp [Finset.sum_const]

/-- Paper-grid cells meeting a set whose three coordinate widths are bounded
relative to one reference point occupy a finite rectangular index box. -/
theorem paperGridCellsIntersecting_coordinate_box_bound
    {scale : ℝ} (hscale : 0 < scale)
    (source : Set Point3) (center : Point3)
    (firstRadius secondRadius thirdRadius : ℕ)
    (hcoordinate : ∀ point ∈ source,
      |point 0 - center 0| ≤ (firstRadius : ℝ) * scale ∧
      |point 1 - center 1| ≤ (secondRadius : ℝ) * scale ∧
      |point 2 - center 2| ≤ (thirdRadius : ℝ) * scale) :
    (gridCellsIntersecting (Real.sqrt 3 * scale) source).Finite ∧
      Set.ncard (gridCellsIntersecting (Real.sqrt 3 * scale) source) ≤
        (2 * firstRadius + 1) *
          ((2 * secondRadius + 1) * (2 * thirdRadius + 1)) := by
  let centerIndex := wz1PaperGridIndex scale center
  let first := Finset.Icc
    (centerIndex.1 - (firstRadius : ℤ))
    (centerIndex.1 + (firstRadius : ℤ))
  let second := Finset.Icc
    (centerIndex.2.1 - (secondRadius : ℤ))
    (centerIndex.2.1 + (secondRadius : ℤ))
  let third := Finset.Icc
    (centerIndex.2.2 - (thirdRadius : ℤ))
    (centerIndex.2.2 + (thirdRadius : ℤ))
  let cells : Finset (ℤ × ℤ × ℤ) := first ×ˢ (second ×ˢ third)
  have hsubset :
      gridCellsIntersecting (Real.sqrt 3 * scale) source ⊆
        (cells : Set (ℤ × ℤ × ℤ)) := by
    intro cell hcell
    rcases hcell with ⟨point, hpointCell, hpointSource⟩
    have hpointPaper : point ∈ wz1PaperGridCube scale cell := by
      rw [← gridCell_sqrtThree_eq_paperGridCube_local hscale]
      exact hpointCell
    have hpointIndex : wz1PaperGridIndex scale point = cell :=
      (mem_wz1PaperGridCube scale cell point).mp hpointPaper
    have hbounds := hcoordinate point hpointSource
    have hscaled (coordinate : Fin 3) (radius : ℕ)
        (hbound : |point coordinate - center coordinate| ≤
          (radius : ℝ) * scale) :
        |point coordinate / scale - center coordinate / scale| ≤
          (radius : ℝ) := by
      rw [← sub_div, abs_div, abs_of_pos hscale]
      calc
        |point coordinate - center coordinate| / scale ≤
            ((radius : ℝ) * scale) / scale := by gcongr
        _ = radius := by field_simp [hscale.ne']
    have hfloor0 := paper_abs_floor_sub_le
      (hscaled 0 firstRadius hbounds.1)
    have hfloor1 := paper_abs_floor_sub_le
      (hscaled 1 secondRadius hbounds.2.1)
    have hfloor2 := paper_abs_floor_sub_le
      (hscaled 2 thirdRadius hbounds.2.2)
    have hpoint0 : ⌊point 0 / scale⌋ = cell.1 := by
      simpa [wz1PaperGridIndex, gridIndex] using congrArg Prod.fst hpointIndex
    have hpoint1 : ⌊point 1 / scale⌋ = cell.2.1 := by
      simpa [wz1PaperGridIndex, gridIndex] using
        congrArg (fun index : ℤ × ℤ × ℤ => index.2.1) hpointIndex
    have hpoint2 : ⌊point 2 / scale⌋ = cell.2.2 := by
      simpa [wz1PaperGridIndex, gridIndex] using
        congrArg (fun index : ℤ × ℤ × ℤ => index.2.2) hpointIndex
    have hcenter0 : ⌊center 0 / scale⌋ = centerIndex.1 := rfl
    have hcenter1 : ⌊center 1 / scale⌋ = centerIndex.2.1 := rfl
    have hcenter2 : ⌊center 2 / scale⌋ = centerIndex.2.2 := rfl
    rw [hpoint0, hcenter0] at hfloor0
    rw [hpoint1, hcenter1] at hfloor1
    rw [hpoint2, hcenter2] at hfloor2
    rcases abs_le.mp hfloor0 with ⟨hfloor0Lower, hfloor0Upper⟩
    rcases abs_le.mp hfloor1 with ⟨hfloor1Lower, hfloor1Upper⟩
    rcases abs_le.mp hfloor2 with ⟨hfloor2Lower, hfloor2Upper⟩
    apply Finset.mem_product.mpr
    constructor
    · simp only [first, Finset.mem_Icc]
      constructor <;> omega
    · apply Finset.mem_product.mpr
      constructor
      · simp only [second, Finset.mem_Icc]
        constructor <;> omega
      · simp only [third, Finset.mem_Icc]
        constructor <;> omega
  have hfirst : first.card = 2 * firstRadius + 1 := by
    simp [first] <;> omega
  have hsecond : second.card = 2 * secondRadius + 1 := by
    simp [second] <;> omega
  have hthird : third.card = 2 * thirdRadius + 1 := by
    simp [third] <;> omega
  refine ⟨cells.finite_toSet.subset hsubset, ?_⟩
  calc
    Set.ncard (gridCellsIntersecting (Real.sqrt 3 * scale) source) ≤
        Set.ncard (cells : Set (ℤ × ℤ × ℤ)) :=
      Set.ncard_le_ncard hsubset cells.finite_toSet
    _ = cells.card := by simp
    _ = (2 * firstRadius + 1) *
        ((2 * secondRadius + 1) * (2 * thirdRadius + 1)) := by
      rw [Finset.card_product, Finset.card_product, hfirst, hsecond, hthird]

/-- Cell-count form of the cubical image-volume estimate. -/
theorem wz1PaperCubicalSaturation_image_volume_upper_of_cell_count
    {sourceDelta targetDelta ratio : ℝ}
    {family : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading family)
    (sourceSet : Set Point3)
    (map : Point3 → Point3)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : 0 < targetDelta)
    (hratio : 0 ≤ ratio)
    (htargetScale : targetDelta = ratio * sourceDelta)
    (hcubical : WZ1PaperIsCubicalShading sourceShading)
    (hsourceSet : sourceSet ⊆ sourceShading.union)
    (cellBound : ℕ)
    (hcellBound : ∀ cell ∈ wz1PaperActiveCells sourceShading hsourceDelta,
      (gridCellsIntersecting (Real.sqrt 3 * targetDelta)
        (map '' (sourceSet ∩ wz1PaperGridCube sourceDelta cell))).Finite ∧
      Set.ncard (gridCellsIntersecting (Real.sqrt 3 * targetDelta)
        (map '' (sourceSet ∩ wz1PaperGridCube sourceDelta cell))) ≤
          cellBound) :
    volume (wz1PaperCubicalSaturation targetDelta (map '' sourceSet)) ≤
      (cellBound : ENNReal) * ENNReal.ofReal (ratio ^ 3) *
        volume sourceShading.union := by
  let sourceCells := wz1PaperActiveCells sourceShading hsourceDelta
  let imageSet := map '' sourceSet
  let targetTau := Real.sqrt 3 * targetDelta
  let targetPiece : (ℤ × ℤ × ℤ) → Set Point3 := fun cell =>
    map '' (sourceSet ∩ wz1PaperGridCube sourceDelta cell)
  have himageCover : imageSet ⊆
      ⋃ cell ∈ sourceCells, targetPiece cell := by
    rintro targetPoint ⟨sourcePoint, hsourcePoint, rfl⟩
    have hsourceUnion := hsourceSet hsourcePoint
    rw [hcubical.union_eq_activeCells hsourceDelta] at hsourceUnion
    rcases Set.mem_iUnion₂.mp hsourceUnion with
      ⟨cell, hcell, hsourceCell⟩
    exact Set.mem_iUnion₂.mpr ⟨cell, hcell,
      ⟨sourcePoint, ⟨hsourcePoint, hsourceCell⟩, rfl⟩⟩
  have htargetCells := gridCellsIntersecting_finset_cover_bound_local
    (tau := targetTau) sourceCells targetPiece himageCover cellBound
    (fun cell hcell => hcellBound cell hcell)
  let targetCells : Finset (ℤ × ℤ × ℤ) := htargetCells.1.toFinset
  have htargetCard : targetCells.card ≤ sourceCells.card * cellBound := by
    rw [← Set.ncard_eq_toFinset_card
      (gridCellsIntersecting targetTau imageSet) htargetCells.1]
    exact htargetCells.2
  have hsaturation :
      wz1PaperCubicalSaturation targetDelta imageSet =
        ⋃ cell ∈ targetCells, wz1PaperGridCube targetDelta cell := by
    ext point
    constructor
    · rintro ⟨imagePoint, himagePoint, hsameCell⟩
      let cell := wz1PaperGridIndex targetDelta point
      have hpointCell : point ∈ wz1PaperGridCube targetDelta cell :=
        (mem_wz1PaperGridCube targetDelta cell point).mpr rfl
      have himageCell : imagePoint ∈ wz1PaperGridCube targetDelta cell :=
        (mem_wz1PaperGridCube targetDelta cell imagePoint).mpr hsameCell.symm
      have hcellIntersects :
          cell ∈ gridCellsIntersecting targetTau imageSet := by
        refine ⟨imagePoint, ?_, himagePoint⟩
        rw [gridCell_sqrtThree_eq_paperGridCube_local htargetDelta]
        exact himageCell
      exact Set.mem_iUnion₂.mpr ⟨cell, by
        simpa [targetCells] using hcellIntersects, hpointCell⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
      have hcellIntersects :
          cell ∈ gridCellsIntersecting targetTau imageSet := by
        simpa [targetCells] using hcell
      rcases hcellIntersects with
        ⟨imagePoint, himageTargetCell, himagePoint⟩
      have himageCell :
          imagePoint ∈ wz1PaperGridCube targetDelta cell := by
        rw [← gridCell_sqrtThree_eq_paperGridCube_local htargetDelta]
        exact himageTargetCell
      exact ⟨imagePoint, himagePoint,
        ((mem_wz1PaperGridCube targetDelta cell point).mp hpointCell).trans
          ((mem_wz1PaperGridCube targetDelta cell imagePoint).mp
            himageCell).symm⟩
  have htargetVolume :
      volume (wz1PaperCubicalSaturation targetDelta imageSet) =
        (targetCells.card : ENNReal) * ENNReal.ofReal (targetDelta ^ 3) := by
    rw [hsaturation, wz1PaperGridCube_volume_biUnion htargetDelta,
      wz1PaperGridCube_volume_exact htargetDelta]
  have hsourceVolume :
      volume sourceShading.union =
        (sourceCells.card : ENNReal) * ENNReal.ofReal (sourceDelta ^ 3) := by
    rw [hcubical.union_eq_activeCells hsourceDelta,
      wz1PaperGridCube_volume_biUnion hsourceDelta,
      wz1PaperGridCube_volume_exact hsourceDelta]
  have htargetCube : ENNReal.ofReal (targetDelta ^ 3) =
      ENNReal.ofReal (ratio ^ 3) * ENNReal.ofReal (sourceDelta ^ 3) := by
    rw [htargetScale, mul_pow, ENNReal.ofReal_mul (pow_nonneg hratio 3)]
  rw [htargetVolume, htargetCube, hsourceVolume]
  have htargetCardENN :
      (targetCells.card : ENNReal) ≤
        (sourceCells.card : ENNReal) * (cellBound : ENNReal) := by
    exact_mod_cast htargetCard
  calc
    (targetCells.card : ENNReal) *
          (ENNReal.ofReal (ratio ^ 3) *
            ENNReal.ofReal (sourceDelta ^ 3)) ≤
        ((sourceCells.card : ENNReal) * (cellBound : ENNReal)) *
          (ENNReal.ofReal (ratio ^ 3) *
            ENNReal.ofReal (sourceDelta ^ 3)) := by gcongr
    _ = (cellBound : ENNReal) * ENNReal.ofReal (ratio ^ 3) *
        ((sourceCells.card : ENNReal) *
          ENNReal.ofReal (sourceDelta ^ 3)) := by ring

/-- A target-grid saturation of an image of a subset of a cubical source has
controlled volume when every source cell maps into one target-scale ball. -/
theorem wz1PaperCubicalSaturation_image_volume_upper_of_cubical_source
    {sourceDelta targetDelta ratio : ℝ}
    {family : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading family)
    (sourceSet : Set Point3)
    (map : Point3 → Point3)
    (hsourceDelta : 0 < sourceDelta)
    (htargetDelta : 0 < targetDelta)
    (hratio : 0 ≤ ratio)
    (htargetScale : targetDelta = ratio * sourceDelta)
    (hcubical : WZ1PaperIsCubicalShading sourceShading)
    (hsourceSet : sourceSet ⊆ sourceShading.union)
    (hcellImage : ∀ cell : ℤ × ℤ × ℤ,
      map '' (sourceSet ∩ wz1PaperGridCube sourceDelta cell) ⊆
        Metric.closedBall (map (cellCorner sourceDelta cell)) targetDelta) :
    volume (wz1PaperCubicalSaturation targetDelta (map '' sourceSet)) ≤
      (13 ^ 3 : ENNReal) * ENNReal.ofReal (ratio ^ 3) *
        volume sourceShading.union := by
  let sourceCells := wz1PaperActiveCells sourceShading hsourceDelta
  let imageSet := map '' sourceSet
  let targetTau := Real.sqrt 3 * targetDelta
  let targetPiece : (ℤ × ℤ × ℤ) → Set Point3 := fun cell =>
    Metric.closedBall (map (cellCorner sourceDelta cell)) targetDelta
  have htargetTau : 0 < targetTau := by
    dsimp only [targetTau]
    positivity
  have htargetRadius : targetDelta ≤ 3 * targetTau := by
    have hsqrt : 1 ≤ Real.sqrt 3 := by
      rw [Real.one_le_sqrt]
      norm_num
    dsimp only [targetTau]
    nlinarith
  have himageCover : imageSet ⊆
      ⋃ cell ∈ sourceCells, targetPiece cell := by
    rintro targetPoint ⟨sourcePoint, hsourcePoint, rfl⟩
    have hsourceUnion := hsourceSet hsourcePoint
    rw [hcubical.union_eq_activeCells hsourceDelta] at hsourceUnion
    rcases Set.mem_iUnion₂.mp hsourceUnion with
      ⟨cell, hcell, hsourceCell⟩
    exact Set.mem_iUnion₂.mpr ⟨cell, hcell,
      hcellImage cell ⟨sourcePoint, ⟨hsourcePoint, hsourceCell⟩, rfl⟩⟩
  have htargetCells := gridCellsIntersecting_finset_cover_bound_local
    (tau := targetTau) sourceCells targetPiece himageCover (13 ^ 3)
    (fun cell _ => gridCellsIntersecting_ball_bound htargetTau
      (map (cellCorner sourceDelta cell)) htargetRadius)
  let targetCells : Finset (ℤ × ℤ × ℤ) := htargetCells.1.toFinset
  have htargetCellsCoe :
      (targetCells : Set (ℤ × ℤ × ℤ)) =
        gridCellsIntersecting targetTau imageSet := by
    exact Set.Finite.coe_toFinset htargetCells.1
  have htargetCard : targetCells.card ≤ sourceCells.card * 13 ^ 3 := by
    rw [← Set.ncard_eq_toFinset_card
      (gridCellsIntersecting targetTau imageSet) htargetCells.1]
    exact htargetCells.2
  have hsaturation :
      wz1PaperCubicalSaturation targetDelta imageSet =
        ⋃ cell ∈ targetCells, wz1PaperGridCube targetDelta cell := by
    ext point
    constructor
    · rintro ⟨imagePoint, himagePoint, hsameCell⟩
      let cell := wz1PaperGridIndex targetDelta point
      have hpointCell : point ∈ wz1PaperGridCube targetDelta cell :=
        (mem_wz1PaperGridCube targetDelta cell point).mpr rfl
      have himageCell : imagePoint ∈ wz1PaperGridCube targetDelta cell :=
        (mem_wz1PaperGridCube targetDelta cell imagePoint).mpr hsameCell.symm
      have hcellIntersects :
          cell ∈ gridCellsIntersecting targetTau imageSet := by
        refine ⟨imagePoint, ?_, himagePoint⟩
        rw [gridCell_sqrtThree_eq_paperGridCube_local htargetDelta]
        exact himageCell
      have hcell : cell ∈ targetCells := by
        simpa [targetCells] using hcellIntersects
      exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpointCell⟩
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
      have hcellIntersects :
          cell ∈ gridCellsIntersecting targetTau imageSet := by
        simpa [targetCells] using hcell
      rcases hcellIntersects with
        ⟨imagePoint, himageTargetCell, himagePoint⟩
      have himageCell :
          imagePoint ∈ wz1PaperGridCube targetDelta cell := by
        rw [← gridCell_sqrtThree_eq_paperGridCube_local htargetDelta]
        exact himageTargetCell
      exact ⟨imagePoint, himagePoint,
        ((mem_wz1PaperGridCube targetDelta cell point).mp hpointCell).trans
          ((mem_wz1PaperGridCube targetDelta cell imagePoint).mp
            himageCell).symm⟩
  have htargetVolume :
      volume (wz1PaperCubicalSaturation targetDelta imageSet) =
        (targetCells.card : ENNReal) * ENNReal.ofReal (targetDelta ^ 3) := by
    rw [hsaturation, wz1PaperGridCube_volume_biUnion htargetDelta,
      wz1PaperGridCube_volume_exact htargetDelta]
  have hsourceVolume :
      volume sourceShading.union =
        (sourceCells.card : ENNReal) * ENNReal.ofReal (sourceDelta ^ 3) := by
    rw [hcubical.union_eq_activeCells hsourceDelta,
      wz1PaperGridCube_volume_biUnion hsourceDelta,
      wz1PaperGridCube_volume_exact hsourceDelta]
  have htargetCube : ENNReal.ofReal (targetDelta ^ 3) =
      ENNReal.ofReal (ratio ^ 3) * ENNReal.ofReal (sourceDelta ^ 3) := by
    rw [htargetScale, mul_pow, ENNReal.ofReal_mul (pow_nonneg hratio 3)]
  rw [htargetVolume, htargetCube, hsourceVolume]
  have htargetCardENN :
      (targetCells.card : ENNReal) ≤
        (sourceCells.card : ENNReal) * (13 ^ 3 : ENNReal) := by
    exact_mod_cast htargetCard
  calc
    (targetCells.card : ENNReal) *
          (ENNReal.ofReal (ratio ^ 3) *
            ENNReal.ofReal (sourceDelta ^ 3)) ≤
        ((sourceCells.card : ENNReal) * (13 ^ 3 : ENNReal)) *
          (ENNReal.ofReal (ratio ^ 3) *
            ENNReal.ofReal (sourceDelta ^ 3)) := by gcongr
    _ = (13 ^ 3 : ENNReal) * ENNReal.ofReal (ratio ^ 3) *
        ((sourceCells.card : ENNReal) *
          ENNReal.ofReal (sourceDelta ^ 3)) := by ring

/-- Cubical saturation is monotone in its source set. -/
theorem wz1PaperCubicalSaturation_mono
    {scale : ℝ} {first second : Set Point3}
    (hsubset : first ⊆ second) :
    wz1PaperCubicalSaturation scale first ⊆
      wz1PaperCubicalSaturation scale second := by
  rintro point ⟨sourcePoint, hsourcePoint, hcell⟩
  exact ⟨sourcePoint, hsubset hsourcePoint, hcell⟩

/-- The exact Proposition-6.4 affine map followed by its fixed isotropic
dilation. -/
def pureWZ2Proposition64CombinedMap
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation center : Point3) (scale : ℝ) (point : Point3) : Point3 :=
  pureWZ2Proposition64IsotropicMap center scale
    (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight halfHeight
      normalization translation point)

/-- The final-grid saturation of a subset of a cubical source shading has the
expected fixed horizontal cell cost and the sole vertical cost `O(h⁻¹)`. -/
theorem pureWZ2Proposition64CombinedSaturation_volume_upper
    {sourceDelta finalDelta halfHeight normalization scale : ℝ}
    (g : ℝ → ℝ) (slabCenter anchorHeight : ℝ)
    (translation center : Point3)
    {family : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading family)
    (sourceSet : Set Point3)
    (hsourceDelta : 0 < sourceDelta)
    (hfinalDelta : 0 < finalDelta)
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 9 ≤ normalization)
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hscale : 1 ≤ scale)
    (hfinalScale : finalDelta = 45 * scale * sourceDelta)
    (hcubical : WZ1PaperIsCubicalShading sourceShading)
    (hsourceSet : sourceSet ⊆ sourceShading.union) :
    volume (wz1PaperCubicalSaturation finalDelta
      (pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
        normalization translation center scale '' sourceSet)) ≤
      (((3 * 3 *
          (2 * Nat.ceil (2 / (45 * halfHeight)) + 1) : ℕ) : ENNReal) *
        ENNReal.ofReal ((45 * scale) ^ 3)) *
          volume sourceShading.union := by
  have hscalePos : 0 < scale := lt_of_lt_of_le zero_lt_one hscale
  have hnormalizationPos : 0 < normalization := by linarith
  apply wz1PaperCubicalSaturation_image_volume_upper_of_cell_count
    sourceShading sourceSet
    (pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
      normalization translation center scale)
    hsourceDelta hfinalDelta (by positivity : 0 ≤ 45 * scale)
    hfinalScale hcubical hsourceSet
    (3 * 3 * (2 * Nat.ceil (2 / (45 * halfHeight)) + 1))
  intro cell _hcell
  have hbound := paperGridCellsIntersecting_coordinate_box_bound
    hfinalDelta
    (pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
      normalization translation center scale ''
        (sourceSet ∩ wz1PaperGridCube sourceDelta cell))
    (pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
      normalization translation center scale
        (cellCorner sourceDelta cell))
    1 1 (Nat.ceil (2 / (45 * halfHeight))) (by
  rintro targetPoint ⟨sourcePoint, hsourcePoint, rfl⟩
  have hsourcePointCell := hsourcePoint.2
  have hcornerCell := cellCorner_mem_gridCube hsourceDelta cell
  have hdistance :
      dist sourcePoint (cellCorner sourceDelta cell) < 2 * sourceDelta :=
    wz1_paper_grid_cube_diameter_lt_two_rho hsourceDelta
      hsourcePointCell hcornerCell
  have hcoordinateDistance (coordinate : Fin 3) :
      |sourcePoint coordinate - cellCorner sourceDelta cell coordinate| ≤
        dist sourcePoint (cellCorner sourceDelta cell) := by
    simpa [Real.dist_eq] using
      PiLp.dist_apply_le sourcePoint (cellCorner sourceDelta cell) coordinate
  have hzero :
      |sourcePoint 0 - cellCorner sourceDelta cell 0| ≤ 2 * sourceDelta :=
    (hcoordinateDistance 0).trans hdistance.le
  have hone :
      |sourcePoint 1 - cellCorner sourceDelta cell 1| ≤ 2 * sourceDelta :=
    (hcoordinateDistance 1).trans hdistance.le
  have htwo :
      |sourcePoint 2 - cellCorner sourceDelta cell 2| ≤ 2 * sourceDelta :=
    (hcoordinateDistance 2).trans hdistance.le
  have hmapZero :
      |pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
          normalization translation center scale sourcePoint 0 -
        pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
          normalization translation center scale
            (cellCorner sourceDelta cell) 0| ≤ finalDelta := by
    have hnumerator :
        |(sourcePoint 0 - cellCorner sourceDelta cell 0) +
            g anchorHeight *
              (sourcePoint 1 - cellCorner sourceDelta cell 1)| ≤
          18 * sourceDelta := by
      calc
        _ ≤ |sourcePoint 0 - cellCorner sourceDelta cell 0| +
              |g anchorHeight| *
                |sourcePoint 1 - cellCorner sourceDelta cell 1| := by
          simpa [abs_mul] using abs_add_le
            (sourcePoint 0 - cellCorner sourceDelta cell 0)
            (g anchorHeight *
              (sourcePoint 1 - cellCorner sourceDelta cell 1))
        _ ≤ 2 * sourceDelta + 8 * (2 * sourceDelta) := by gcongr
        _ = 18 * sourceDelta := by ring
    rw [show
      pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
            normalization translation center scale sourcePoint 0 -
          pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
            normalization translation center scale
              (cellCorner sourceDelta cell) 0 =
        scale *
          (((sourcePoint 0 - cellCorner sourceDelta cell 0) +
              g anchorHeight *
                (sourcePoint 1 - cellCorner sourceDelta cell 1)) /
            normalization) by
      simp [pureWZ2Proposition64CombinedMap,
        pureWZ2Proposition64IsotropicMap,
        pureWZ2Proposition64TranslatedMap, pureWZ2Proposition64Map, point3]
      ring]
    rw [abs_mul, abs_div, abs_of_pos hscalePos,
      abs_of_pos hnormalizationPos]
    calc
      scale *
          (|(sourcePoint 0 - cellCorner sourceDelta cell 0) +
              g anchorHeight *
                (sourcePoint 1 - cellCorner sourceDelta cell 1)| /
            normalization) ≤
        scale * ((18 * sourceDelta) / normalization) := by gcongr
      _ ≤ scale * ((18 * sourceDelta) / 9) := by gcongr
      _ ≤ finalDelta := by
        rw [hfinalScale]
        have hnonneg : 0 ≤ scale * sourceDelta :=
          mul_nonneg hscalePos.le hsourceDelta.le
        nlinarith
  have hmapOne :
      |pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
          normalization translation center scale sourcePoint 1 -
        pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
          normalization translation center scale
            (cellCorner sourceDelta cell) 1| ≤ finalDelta := by
    rw [show
      pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
            normalization translation center scale sourcePoint 1 -
          pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
            normalization translation center scale
              (cellCorner sourceDelta cell) 1 =
        scale * (sourcePoint 1 - cellCorner sourceDelta cell 1) by
      simp [pureWZ2Proposition64CombinedMap,
        pureWZ2Proposition64IsotropicMap,
        pureWZ2Proposition64TranslatedMap, pureWZ2Proposition64Map, point3]
      ring]
    rw [abs_mul, abs_of_pos hscalePos]
    calc
      scale * |sourcePoint 1 - cellCorner sourceDelta cell 1| ≤
          scale * (2 * sourceDelta) := by gcongr
      _ ≤ finalDelta := by
        rw [hfinalScale]
        have hnonneg : 0 ≤ scale * sourceDelta :=
          mul_nonneg hscalePos.le hsourceDelta.le
        nlinarith
  have hmapTwo :
      |pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
          normalization translation center scale sourcePoint 2 -
        pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
          normalization translation center scale
            (cellCorner sourceDelta cell) 2| ≤
        (Nat.ceil (2 / (45 * halfHeight)) : ℝ) * finalDelta := by
    rw [show
      pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
            normalization translation center scale sourcePoint 2 -
          pureWZ2Proposition64CombinedMap g slabCenter anchorHeight halfHeight
            normalization translation center scale
              (cellCorner sourceDelta cell) 2 =
        scale *
          ((sourcePoint 2 - cellCorner sourceDelta cell 2) / halfHeight) by
      simp [pureWZ2Proposition64CombinedMap,
        pureWZ2Proposition64IsotropicMap,
        pureWZ2Proposition64TranslatedMap, pureWZ2Proposition64Map, point3]
      ring]
    rw [abs_mul, abs_div, abs_of_pos hscalePos, abs_of_pos hhalfHeight]
    have hceil : 2 / (45 * halfHeight) ≤
        (Nat.ceil (2 / (45 * halfHeight)) : ℝ) :=
      Nat.le_ceil _
    calc
      scale *
          (|sourcePoint 2 - cellCorner sourceDelta cell 2| / halfHeight) ≤
        scale * ((2 * sourceDelta) / halfHeight) := by gcongr
      _ = (2 / (45 * halfHeight)) * finalDelta := by
        rw [hfinalScale]
        field_simp [hhalfHeight.ne']
      _ ≤ (Nat.ceil (2 / (45 * halfHeight)) : ℝ) * finalDelta := by
        gcongr
  exact ⟨by simpa using hmapZero, by simpa using hmapOne, hmapTwo⟩)
  convert hbound using 1 <;> omega

end Kakeya.Assouad

end
