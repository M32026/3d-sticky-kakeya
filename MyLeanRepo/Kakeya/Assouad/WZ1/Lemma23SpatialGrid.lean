import MyLeanRepo.Kakeya.Assouad.WZ1.BalancedCellConstruction

/-!
# A finite spatial grid for WZ1 Lemma 23

The proof of Lemma 23 works with small cubes meeting one retained shading.
This module constructs those cubes directly from the final Proposition 9
configuration.  It does not require exact-cell provenance through the earlier
mild rescaling.

At parameter `rho`, we use `rhoGridIndex (rho / 2)`.  Hence points in one cell
are at distance at most `rho`.  Restricting the integer indices to the unit
ball makes the active family finite, and each active cell carries a chosen
representative point from the same shading.
-/

namespace Kakeya.Assouad

noncomputable section

/-- The Lemma 23 spatial cell index at diameter scale `rho`. -/
def wz1Lemma23CellIndex (rho : ℝ) (p : Point3) : ℤ × ℤ × ℤ :=
  rhoGridIndex (rho / 2) p

/-- The spatial cell with the prescribed grid index. -/
def wz1Lemma23Cell (rho : ℝ) (idx : ℤ × ℤ × ℤ) : Set Point3 :=
  {p | wz1Lemma23CellIndex rho p = idx}

/--
All grid indices that can meet the closed radius-two ball.  The historical
unit-ball applications are a special case, while the cropped paper window
`[-1,1]^3` also lies in this universe.
-/
def wz1Lemma23BoundedCells (rho : ℝ) (hrho : 0 < rho) :
    Finset (ℤ × ℤ × ℤ) :=
  gridIndicesInRadius 2 (rho / 2) (by positivity)

/-- Grid indices that can meet the radius-`R` ball. -/
def wz1Lemma23BoundedCellsInRadius
    (R rho : ℝ) (hrho : 0 < rho) : Finset (ℤ × ℤ × ℤ) :=
  gridIndicesInRadius R (rho / 2) (by positivity)

/-- Cells from the bounded grid that actually meet the shading. -/
def wz1Lemma23ActiveCells
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho : ℝ) (hrho : 0 < rho) : Finset (ℤ × ℤ × ℤ) := by
  classical
  exact
    (wz1Lemma23BoundedCells rho hrho).filter fun idx =>
      (Y.union ∩ wz1Lemma23Cell rho idx).Nonempty

/-- Active spatial cells inside the radius-`R` grid universe. -/
def wz1Lemma23ActiveCellsInRadius
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (R rho : ℝ) (hrho : 0 < rho) : Finset (ℤ × ℤ × ℤ) := by
  classical
  exact
    (wz1Lemma23BoundedCellsInRadius R rho hrho).filter fun idx =>
      (Y.union ∩ wz1Lemma23Cell rho idx).Nonempty

@[simp] theorem mem_wz1Lemma23ActiveCellsInRadius
    {delta R rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (idx : ℤ × ℤ × ℤ) :
    idx ∈ wz1Lemma23ActiveCellsInRadius Y R rho hrho ↔
      idx ∈ wz1Lemma23BoundedCellsInRadius R rho hrho ∧
        (Y.union ∩ wz1Lemma23Cell rho idx).Nonempty := by
  simp [wz1Lemma23ActiveCellsInRadius]

/-- The active-cell type used by the finite four-cycle construction. -/
abbrev WZ1Lemma23ActiveCell
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (rho : ℝ) (hrho : 0 < rho) :=
  {idx // idx ∈ wz1Lemma23ActiveCells Y rho hrho}

/-- Membership in the active-cell finset, with its genuine shading witness. -/
lemma wz1Lemma23_mem_active_iff
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (idx : ℤ × ℤ × ℤ) :
    idx ∈ wz1Lemma23ActiveCells Y rho hrho ↔
      idx ∈ wz1Lemma23BoundedCells rho hrho ∧
        (Y.union ∩ wz1Lemma23Cell rho idx).Nonempty := by
  classical
  simp [wz1Lemma23ActiveCells]

/-- The grid-index map is measurable. -/
lemma wz1Lemma23CellIndex_measurable {rho : ℝ} (hrho : 0 < rho) :
    Measurable (wz1Lemma23CellIndex rho) := by
  let scale : ℝ := gridSide (rho / 2)
  have hscale : 0 < scale := by
    dsimp only [scale, gridSide]
    positivity
  have hfloor : Measurable (Int.floor : ℝ → ℤ) :=
    Int.measurable_floor
  have hcoord :
      ∀ i : Fin 3, Measurable (fun p : Point3 => p i) := by
    intro i
    fun_prop
  have h0 : Measurable (fun p : Point3 => ⌊p 0 / scale⌋) :=
    hfloor.comp ((hcoord 0).div_const scale)
  have h1 : Measurable (fun p : Point3 => ⌊p 1 / scale⌋) :=
    hfloor.comp ((hcoord 1).div_const scale)
  have h2 : Measurable (fun p : Point3 => ⌊p 2 / scale⌋) :=
    hfloor.comp ((hcoord 2).div_const scale)
  have hformula :
      wz1Lemma23CellIndex rho =
        fun p => (⌊p 0 / scale⌋, ⌊p 1 / scale⌋, ⌊p 2 / scale⌋) := by
    funext p
    simp [wz1Lemma23CellIndex, rhoGridIndex, gridIndex, scale]
  rw [hformula]
  exact h0.prod (h1.prod h2)

/-- Every Lemma 23 spatial cell is measurable. -/
lemma wz1Lemma23Cell_measurable
    {rho : ℝ} (hrho : 0 < rho) (idx : ℤ × ℤ × ℤ) :
    MeasurableSet (wz1Lemma23Cell rho idx) := by
  exact
    (wz1Lemma23CellIndex_measurable hrho)
      (MeasurableSet.singleton idx)

/-- Points in one Lemma 23 cell are within `rho`. -/
lemma wz1Lemma23_same_cell_dist
    {rho : ℝ} (hrho : 0 < rho) {p q : Point3}
    (h : wz1Lemma23CellIndex rho p = wz1Lemma23CellIndex rho q) :
    dist p q ≤ rho := by
  have hmain :=
    grid_cell_diameter (rho := rho / 2) (by positivity)
      (show rhoGridIndex (rho / 2) p =
          rhoGridIndex (rho / 2) q from h)
  convert hmain using 1 <;> ring

/-- A unit-ball point has a bounded Lemma 23 cell index. -/
lemma wz1Lemma23_index_mem_bounded
    {rho : ℝ} (hrho : 0 < rho) {p : Point3}
    (hp : ‖p‖ ≤ 1) :
    wz1Lemma23CellIndex rho p ∈ wz1Lemma23BoundedCells rho hrho := by
  exact gridIndex_inRadius (R := 2) (by norm_num)
    (rho := rho / 2) (by positivity) (hp.trans (by norm_num))

/-- A radius-two point has an index in the default Lemma-23 universe. -/
lemma wz1Lemma23_index_mem_bounded_two
    {rho : ℝ} (hrho : 0 < rho) {p : Point3} (hp : ‖p‖ ≤ 2) :
    wz1Lemma23CellIndex rho p ∈ wz1Lemma23BoundedCells rho hrho := by
  exact gridIndex_inRadius (R := 2) (by norm_num)
    (rho := rho / 2) (by positivity) hp

/-- A radius-`R` point belongs to the radius-`R` cell universe. -/
lemma wz1Lemma23_index_mem_boundedInRadius
    {R rho : ℝ} (hR : 0 ≤ R) (hrho : 0 < rho) {p : Point3}
    (hp : ‖p‖ ≤ R) :
    wz1Lemma23CellIndex rho p ∈
      wz1Lemma23BoundedCellsInRadius R rho hrho := by
  exact gridIndex_inRadius hR (rho := rho / 2) (by positivity) hp

/-- Every shaded radius-`R` point belongs to an active radius-`R` cell. -/
lemma wz1Lemma23_index_mem_activeInRadius
    {delta R rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hR : 0 ≤ R) (hrho : 0 < rho)
    (hbound : ∀ p ∈ Y.union, ‖p‖ ≤ R)
    {p : Point3} (hp : p ∈ Y.union) :
    wz1Lemma23CellIndex rho p ∈
      wz1Lemma23ActiveCellsInRadius Y R rho hrho := by
  rw [mem_wz1Lemma23ActiveCellsInRadius]
  exact ⟨wz1Lemma23_index_mem_boundedInRadius hR hrho (hbound p hp),
    p, hp, rfl⟩

/-- Every shaded point belongs to an active cell. -/
lemma wz1Lemma23_index_mem_active
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    {p : Point3} (hp : p ∈ Y.union) :
    wz1Lemma23CellIndex rho p ∈ wz1Lemma23ActiveCells Y rho hrho := by
  rw [wz1Lemma23_mem_active_iff]
  constructor
  · apply wz1Lemma23_index_mem_bounded hrho
    simpa [Metric.mem_closedBall, dist_zero_right] using hball hp
  · exact ⟨p, hp, rfl⟩

/-- Every shaded point in the radius-two ball belongs to an active cell. -/
lemma wz1Lemma23_index_mem_active_two
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 2)
    {p : Point3} (hp : p ∈ Y.union) :
    wz1Lemma23CellIndex rho p ∈ wz1Lemma23ActiveCells Y rho hrho := by
  rw [wz1Lemma23_mem_active_iff]
  constructor
  · apply wz1Lemma23_index_mem_bounded_two hrho
    simpa [Metric.mem_closedBall, dist_zero_right] using hball hp
  · exact ⟨p, hp, rfl⟩

/-- Choose one genuine shaded representative from each active cell. -/
def wz1Lemma23CellRepresentative
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (cell : WZ1Lemma23ActiveCell Y rho hrho) : Point3 :=
  Classical.choose
    ((wz1Lemma23_mem_active_iff Y hrho cell.1).mp cell.property).2

/-- The chosen representative belongs to the original shading. -/
lemma wz1Lemma23CellRepresentative_mem_union
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (cell : WZ1Lemma23ActiveCell Y rho hrho) :
    wz1Lemma23CellRepresentative Y hrho cell ∈ Y.union :=
  (Classical.choose_spec
    ((wz1Lemma23_mem_active_iff Y hrho cell.1).mp cell.property).2).1

/-- The chosen representative has the prescribed active-cell index. -/
lemma wz1Lemma23CellRepresentative_index
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (cell : WZ1Lemma23ActiveCell Y rho hrho) :
    wz1Lemma23CellIndex rho
        (wz1Lemma23CellRepresentative Y hrho cell) =
      cell.1 :=
  (Classical.choose_spec
    ((wz1Lemma23_mem_active_iff Y hrho cell.1).mp cell.property).2).2

/-- Every shaded point is within `rho` of its active-cell representative. -/
lemma wz1Lemma23_point_close_to_representative
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    {p : Point3} (hp : p ∈ Y.union) :
    let cell : WZ1Lemma23ActiveCell Y rho hrho :=
      ⟨wz1Lemma23CellIndex rho p,
        wz1Lemma23_index_mem_active hrho hball hp⟩
    dist p (wz1Lemma23CellRepresentative Y hrho cell) ≤ rho := by
  dsimp only
  apply wz1Lemma23_same_cell_dist hrho
  simpa using
    (wz1Lemma23CellRepresentative_index Y hrho
      ⟨wz1Lemma23CellIndex rho p,
        wz1Lemma23_index_mem_active hrho hball hp⟩).symm

end

end Kakeya.Assouad
