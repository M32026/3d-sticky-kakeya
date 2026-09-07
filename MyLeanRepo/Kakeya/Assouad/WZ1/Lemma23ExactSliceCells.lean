import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GoodHeights
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SpatialGrid
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Genuine exact-slice cells for WZ1 Lemma 23

The global AD input is an exact horizontal-slice statement.  Generic active
cell representatives need not have a common real height, even when their
snapped centers have the same integer height label.  This module instead
discretizes one genuine planar slice: every retained cell carries a point of
the original shading at the same prescribed real height.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory Set

/-- Lift a planar point to the horizontal plane of height `z`. -/
def wz1Lemma23LiftSlicePoint (z : ℝ) (point : Point2) : Point3 :=
  point3 (point 0) (point 1) z

/-- Spatial cells meeting the genuine horizontal slice at height `z`. -/
def wz1Lemma23ExactSliceCells
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho : ℝ) (hrho : 0 < rho) (z : ℝ) :
    Finset (ℤ × ℤ × ℤ) := by
  classical
  exact
    (wz1Lemma23BoundedCells rho hrho).filter fun idx =>
      ∃ point ∈ wz1Lemma23PlanarSlice Y.union z,
        wz1Lemma23CellIndex rho
          (wz1Lemma23LiftSlicePoint z point) = idx

/-- A cell from one genuine horizontal slice. -/
abbrev WZ1Lemma23ExactSliceCell
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho : ℝ) (hrho : 0 < rho) (z : ℝ) :=
  {idx // idx ∈ wz1Lemma23ExactSliceCells Y rho hrho z}

/-- Membership supplies an actual point of the prescribed horizontal slice. -/
lemma wz1Lemma23_mem_exactSliceCells_iff
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (z : ℝ) (idx : ℤ × ℤ × ℤ) :
    idx ∈ wz1Lemma23ExactSliceCells Y rho hrho z ↔
      idx ∈ wz1Lemma23BoundedCells rho hrho ∧
        ∃ point ∈ wz1Lemma23PlanarSlice Y.union z,
          wz1Lemma23CellIndex rho
            (wz1Lemma23LiftSlicePoint z point) = idx := by
  classical
  simp [wz1Lemma23ExactSliceCells]

/-- Choose one genuine planar point in each exact-slice cell. -/
def wz1Lemma23ExactSliceRepresentative
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (z : ℝ)
    (cell : WZ1Lemma23ExactSliceCell Y rho hrho z) : Point2 :=
  Classical.choose
    ((wz1Lemma23_mem_exactSliceCells_iff
      Y hrho z cell.1).mp cell.property).2

/-- A total choice of planar center, used to form nondependent finite unions. -/
def wz1Lemma23ExactSliceCenter
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (z : ℝ)
    (idx : ℤ × ℤ × ℤ) : Point2 :=
  if hidx : idx ∈ wz1Lemma23ExactSliceCells Y rho hrho z then
    wz1Lemma23ExactSliceRepresentative Y hrho z ⟨idx, hidx⟩
  else
    0

/-- On an occupied exact-slice cell, the total center is its representative. -/
lemma wz1Lemma23ExactSliceCenter_eq
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (z : ℝ)
    {idx : ℤ × ℤ × ℤ}
    (hidx : idx ∈ wz1Lemma23ExactSliceCells Y rho hrho z) :
    wz1Lemma23ExactSliceCenter Y hrho z idx =
      wz1Lemma23ExactSliceRepresentative Y hrho z ⟨idx, hidx⟩ := by
  simp [wz1Lemma23ExactSliceCenter, hidx]

/-- The chosen representative belongs to the genuine planar slice. -/
lemma wz1Lemma23ExactSliceRepresentative_mem
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (z : ℝ)
    (cell : WZ1Lemma23ExactSliceCell Y rho hrho z) :
    wz1Lemma23ExactSliceRepresentative Y hrho z cell ∈
      wz1Lemma23PlanarSlice Y.union z :=
  (Classical.choose_spec
    ((wz1Lemma23_mem_exactSliceCells_iff
      Y hrho z cell.1).mp cell.property).2).1

/-- The lifted representative is an actual point of the original shading. -/
lemma wz1Lemma23ExactSliceRepresentative_mem_union
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (z : ℝ)
    (cell : WZ1Lemma23ExactSliceCell Y rho hrho z) :
    wz1Lemma23LiftSlicePoint z
        (wz1Lemma23ExactSliceRepresentative Y hrho z cell) ∈
      Y.union := by
  change point3
      (wz1Lemma23ExactSliceRepresentative Y hrho z cell 0)
      (wz1Lemma23ExactSliceRepresentative Y hrho z cell 1) z ∈
    Y.union
  rw [← wz1Lemma23_mem_planarSlice_iff]
  exact wz1Lemma23ExactSliceRepresentative_mem Y hrho z cell

/-- The lifted representative has the prescribed spatial-cell index. -/
lemma wz1Lemma23ExactSliceRepresentative_index
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (z : ℝ)
    (cell : WZ1Lemma23ExactSliceCell Y rho hrho z) :
    wz1Lemma23CellIndex rho
        (wz1Lemma23LiftSlicePoint z
          (wz1Lemma23ExactSliceRepresentative Y hrho z cell)) =
      cell.1 :=
  (Classical.choose_spec
    ((wz1Lemma23_mem_exactSliceCells_iff
      Y hrho z cell.1).mp cell.property).2).2

/-- Every exact-slice cell has the same snapped height index. -/
lemma wz1Lemma23ExactSliceCells_height
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (z : ℝ)
    {idx : ℤ × ℤ × ℤ}
    (hidx : idx ∈ wz1Lemma23ExactSliceCells Y rho hrho z) :
    idx.2.2 =
      Int.floor (z / gridSide (rho / 2)) := by
  rcases
      ((wz1Lemma23_mem_exactSliceCells_iff
        Y hrho z idx).mp hidx).2 with
    ⟨point, _, hpoint⟩
  have hcoord :=
    congr_arg (fun cell : ℤ × ℤ × ℤ => cell.2.2) hpoint
  simpa [wz1Lemma23CellIndex, rhoGridIndex, gridIndex,
    wz1Lemma23LiftSlicePoint, point3] using hcoord.symm

private lemma wz1Lemma23_liftSlicePoint_dist
    (z : ℝ) (first second : Point2) :
    dist (wz1Lemma23LiftSlicePoint z first)
        (wz1Lemma23LiftSlicePoint z second) =
      dist first second := by
  have hfirst :
      dist (wz1Lemma23LiftSlicePoint z first)
          (wz1Lemma23LiftSlicePoint z second) ^ 2 =
        (first 0 - second 0) ^ 2 +
          (first 1 - second 1) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simp [Fin.sum_univ_succ, Real.dist_eq,
      wz1Lemma23LiftSlicePoint, point3]
  have hsecond :
      dist first second ^ 2 =
        (first 0 - second 0) ^ 2 +
          (first 1 - second 1) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simp [Fin.sum_univ_succ, Real.dist_eq]
  have hnonneg3 :
      0 ≤ dist (wz1Lemma23LiftSlicePoint z first)
        (wz1Lemma23LiftSlicePoint z second) :=
    dist_nonneg
  have hnonneg2 : 0 ≤ dist first second := dist_nonneg
  nlinarith

/-- Every planar slice point is covered by its cell representative. -/
lemma wz1Lemma23_exactSlice_covered_two
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 2)
    (z : ℝ) :
    wz1Lemma23PlanarSlice Y.union z ⊆
      ⋃ idx ∈ wz1Lemma23ExactSliceCells Y rho hrho z,
        Metric.closedBall
          (wz1Lemma23ExactSliceCenter Y hrho z idx)
          rho := by
  intro point hpoint
  let lifted := wz1Lemma23LiftSlicePoint z point
  have hlifted : lifted ∈ Y.union := by
    simpa [lifted, wz1Lemma23LiftSlicePoint] using
      (wz1Lemma23_mem_planarSlice_iff.mp hpoint)
  let idx := wz1Lemma23CellIndex rho lifted
  have hbounded : idx ∈ wz1Lemma23BoundedCells rho hrho := by
    apply wz1Lemma23_index_mem_bounded_two hrho
    simpa [Metric.mem_closedBall, dist_zero_right] using hball hlifted
  have hidx :
      idx ∈ wz1Lemma23ExactSliceCells Y rho hrho z := by
    rw [wz1Lemma23_mem_exactSliceCells_iff]
    exact ⟨hbounded, point, hpoint, rfl⟩
  let cell : WZ1Lemma23ExactSliceCell Y rho hrho z :=
    ⟨idx, hidx⟩
  have hsame :
      wz1Lemma23CellIndex rho lifted =
        wz1Lemma23CellIndex rho
          (wz1Lemma23LiftSlicePoint z
            (wz1Lemma23ExactSliceRepresentative Y hrho z cell)) := by
    rw [wz1Lemma23ExactSliceRepresentative_index]
  have hdist3 :
      dist lifted
          (wz1Lemma23LiftSlicePoint z
            (wz1Lemma23ExactSliceRepresentative Y hrho z cell)) ≤
        rho :=
    wz1Lemma23_same_cell_dist hrho hsame
  have hdist2 :
      dist point
          (wz1Lemma23ExactSliceRepresentative Y hrho z cell) ≤
        rho := by
    rw [← wz1Lemma23_liftSlicePoint_dist z]
    exact hdist3
  exact Set.mem_iUnion₂.mpr
    ⟨idx, hidx, by
      simpa [Metric.mem_closedBall,
        wz1Lemma23ExactSliceCenter_eq Y hrho z hidx, cell] using hdist2⟩

/-- Unit-ball compatibility wrapper for exact-slice coverage. -/
lemma wz1Lemma23_exactSlice_covered
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (z : ℝ) :
    wz1Lemma23PlanarSlice Y.union z ⊆
      ⋃ idx ∈ wz1Lemma23ExactSliceCells Y rho hrho z,
        Metric.closedBall
          (wz1Lemma23ExactSliceCenter Y hrho z idx)
          rho := by
  apply wz1Lemma23_exactSlice_covered_two Y hrho
  intro point hpoint
  have h := hball hpoint
  simp only [Metric.mem_closedBall, dist_zero_right] at h ⊢
  linarith

/--
The genuine planar slice has area at most one radius-`rho` disk per occupied
exact-slice cell.
-/
theorem wz1_lemma23_exactSlice_area_le_two
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 2)
    (z : ℝ) :
    volume (wz1Lemma23PlanarSlice Y.union z) ≤
      ((wz1Lemma23ExactSliceCells Y rho hrho z).card : ENNReal) *
        (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) := by
  let cells := wz1Lemma23ExactSliceCells Y rho hrho z
  have hcover :
      wz1Lemma23PlanarSlice Y.union z ⊆
        ⋃ idx ∈ cells,
          Metric.closedBall
            (wz1Lemma23ExactSliceCenter Y hrho z idx)
            rho :=
    wz1Lemma23_exactSlice_covered_two Y hrho hball z
  calc
    volume (wz1Lemma23PlanarSlice Y.union z)
        ≤ volume
            (⋃ idx ∈ cells,
              Metric.closedBall
                (wz1Lemma23ExactSliceCenter Y hrho z idx)
                rho) :=
      measure_mono hcover
    _ ≤ ∑ idx ∈ cells,
          volume
            (Metric.closedBall
              (wz1Lemma23ExactSliceCenter Y hrho z idx)
              rho) :=
      measure_biUnion_finset_le cells fun idx =>
        Metric.closedBall
          (wz1Lemma23ExactSliceCenter Y hrho z idx)
          rho
    _ = ((cells.card : ℕ) : ENNReal) *
          (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) := by
      simp [EuclideanSpace.volume_closedBall_fin_two,
        Finset.sum_const]

/-- Unit-ball compatibility wrapper for the exact-slice area bound. -/
theorem wz1_lemma23_exactSlice_area_le
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (z : ℝ) :
    volume (wz1Lemma23PlanarSlice Y.union z) ≤
      ((wz1Lemma23ExactSliceCells Y rho hrho z).card : ENNReal) *
        (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) := by
  apply wz1_lemma23_exactSlice_area_le_two Y hrho
  intro point hpoint
  have h := hball hpoint
  simp only [Metric.mem_closedBall, dist_zero_right] at h ⊢
  linarith

/--
Select one genuine height whose occupied exact-slice cells retain the
three-dimensional volume lower bound.  All selected cells share one snapped
height index.
-/
theorem wz1_lemma23_exists_exactSlice_cells
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    {V : ENNReal} (hV : V ≤ volume Y.union) :
    ∃ z ∈ Set.Icc (-1 : ℝ) 1,
      V / 2 ≤
        ((wz1Lemma23ExactSliceCells Y rho hrho z).card : ENNReal) *
          (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) ∧
      ∀ idx ∈ wz1Lemma23ExactSliceCells Y rho hrho z,
        idx.2.2 = Int.floor (z / gridSide (rho / 2)) := by
  have hunion :
      Y.union = ⋃ i : Fin F.card, Y.carrier i := by
    ext point
    constructor
    · rintro ⟨i, hi⟩
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    · intro hpoint
      rcases Set.mem_iUnion.mp hpoint with ⟨i, hi⟩
      exact ⟨i, hi⟩
  have hmeas : MeasurableSet Y.union := by
    rw [hunion]
    exact MeasurableSet.iUnion fun i => Y.measurable_carrier i
  rcases
      wz1_lemma23_exists_good_height_slice
        hmeas hball hV with
    ⟨z, hz, hslice⟩
  refine ⟨z, hz, hslice.trans ?_, ?_⟩
  · exact wz1_lemma23_exactSlice_area_le Y hrho hball z
  · intro idx hidx
    exact wz1Lemma23ExactSliceCells_height Y hrho z hidx

end

end Kakeya.Assouad
