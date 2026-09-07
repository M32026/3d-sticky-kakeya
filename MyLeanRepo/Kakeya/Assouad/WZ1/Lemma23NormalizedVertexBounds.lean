import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23NormalizedTripartitePackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedCellGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SpatialGrid

/-!
# Bounds for the normalized WZ1 Lemma 23 vertex classes

The paper applies Theorem 22 after restricting the source shading to one
height window of length `sqrt rho`.  Under that explicit support condition,
the normalized height graph lies in a fixed radius-two ball.  The two local
graph classes lie in a fixed radius-five ball using only the source unit-ball
support and the bounded local graph.
-/

namespace Kakeya.Assouad

noncomputable section

/-- The paper's single `sqrt rho` height-window condition on actual cells. -/
def WZ1Lemma23SingleHeightWindow
    (rho : ℝ) (cells : Finset (ℤ × ℤ × ℤ)) : Prop :=
  ∃ left : ℝ, ∀ idx ∈ cells,
    (wz1Lemma23SnappedPoint rho idx) (2 : Fin 3) ∈
      Set.Icc left (left + Real.sqrt rho)

/-- Two cells in one paper height window have snapped heights within `sqrt rho`. -/
lemma WZ1Lemma23SingleHeightWindow.height_sub_le
    {rho : ℝ} {cells : Finset (ℤ × ℤ × ℤ)}
    (hwindow : WZ1Lemma23SingleHeightWindow rho cells)
    {first second : ℤ × ℤ × ℤ}
    (hfirst : first ∈ cells) (hsecond : second ∈ cells) :
    |(wz1Lemma23SnappedPoint rho first) (2 : Fin 3) -
        (wz1Lemma23SnappedPoint rho second) (2 : Fin 3)| ≤
      Real.sqrt rho := by
  rcases hwindow with ⟨left, hwindow⟩
  have h1 := hwindow first hfirst
  have h2 := hwindow second hsecond
  rcases h1 with ⟨h1left, h1right⟩
  rcases h2 with ⟨h2left, h2right⟩
  rw [abs_le]
  constructor <;> linarith

private lemma wz1Lemma23_point2_norm_le_two
    (point : Point2)
    (h0 : |point 0| ≤ 1) (h1 : |point 1| ≤ 1) :
    ‖point‖ ≤ 2 := by
  have hsq :
      ‖point‖ ^ 2 = point 0 ^ 2 + point 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two]
  have h0sq : point 0 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (point 0)]
  have h1sq : point 1 ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (point 1)]
  nlinarith [norm_nonneg point]

private lemma wz1Lemma23_point2_norm_le_five
    (point : Point2)
    (h0 : |point 0| ≤ 4) (h1 : |point 1| ≤ 3 / 2) :
    ‖point‖ ≤ 5 := by
  have hsq :
      ‖point‖ ^ 2 = point 0 ^ 2 + point 1 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two]
  have h0sq : point 0 ^ 2 ≤ 16 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (point 0)]
  have h1sq : point 1 ^ 2 ≤ 9 / 4 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (point 1)]
  nlinarith [norm_nonneg point]

/-- An active cell center stays in the radius-`3/2` coordinate box when the
source carrier lies in the paper coordinate crop. -/
lemma wz1Lemma23_active_cell_center_coord_bound_of_coord
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hcoord : ∀ point ∈ Y.union, ∀ i : Fin 3, |point i| ≤ 1)
    {idx : ℤ × ℤ × ℤ}
    (hidx : idx ∈ wz1Lemma23ActiveCells Y rho hrho)
    (i : Fin 3) :
    |(wz1Lemma23SnappedPoint rho idx) i| ≤ 3 / 2 := by
  let cell : WZ1Lemma23ActiveCell Y rho hrho := ⟨idx, hidx⟩
  let point := wz1Lemma23CellRepresentative Y hrho cell
  have hpointMem : point ∈ Y.union :=
    wz1Lemma23CellRepresentative_mem_union Y hrho cell
  have hpointCoord : |point i| ≤ 1 := hcoord point hpointMem i
  have hpointIndex :
      wz1Lemma23CellIndex rho point = idx :=
    wz1Lemma23CellRepresentative_index Y hrho cell
  have hcoord :=
    ((wz1_lemma23_snapped_cell_geometry
      rho hrho hrho_one).2.1 idx point hpointIndex).1 i
  have hsnap :
      |(wz1Lemma23SnappedPoint rho idx) i - point i| ≤
        rho / 2 := by
    rw [abs_sub_comm]
    simpa [wz1Lemma23SnappedPoint] using hcoord
  calc
    |(wz1Lemma23SnappedPoint rho idx) i|
        = |point i +
            ((wz1Lemma23SnappedPoint rho idx) i - point i)| := by
          congr 1
          ring
    _ ≤ |point i| +
          |(wz1Lemma23SnappedPoint rho idx) i - point i| :=
      abs_add_le _ _
    _ ≤ 1 + rho / 2 := by gcongr
    _ ≤ 3 / 2 := by linarith

/-- Unit-ball compatibility wrapper for the active-center coordinate bound. -/
lemma wz1Lemma23_active_cell_center_coord_bound
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    {idx : ℤ × ℤ × ℤ}
    (hidx : idx ∈ wz1Lemma23ActiveCells Y rho hrho)
    (i : Fin 3) :
    |(wz1Lemma23SnappedPoint rho idx) i| ≤ 3 / 2 := by
  apply wz1Lemma23_active_cell_center_coord_bound_of_coord hrho hrho_one
  · intro point hpoint coordinate
    have hnorm : ‖point‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
    exact (PiLp.norm_apply_le point coordinate).trans hnorm
  · exact hidx

/-- One normalized snapped height-graph point has norm at most two. -/
lemma wz1Lemma23_normalized_height_point_bound
    {rho : ℝ} (hrho : 0 < rho)
    (f : ℝ → ℝ) (hf : LipschitzOnWith 1 f Set.univ)
    (baseHeightIndex : ℤ) (idx : ℤ × ℤ × ℤ)
    (hheight :
      |(wz1Lemma23SnappedPoint rho idx) (2 : Fin 3) -
          wz1Lemma23SnappedBaseHeight rho baseHeightIndex| ≤
        Real.sqrt rho) :
    ‖(1 / Real.sqrt rho) •
        wz1Lemma23SnappedHeightPoint
          rho f baseHeightIndex idx‖ ≤ 2 := by
  let baseHeight := wz1Lemma23SnappedBaseHeight rho baseHeightIndex
  let z :=
    (wz1Lemma23SnappedPoint rho idx) (2 : Fin 3) - baseHeight
  let point :=
    (1 / Real.sqrt rho) •
      wz1Lemma23SnappedHeightPoint rho f baseHeightIndex idx
  have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have hz : |z| ≤ Real.sqrt rho := by
    simpa [z, baseHeight] using hheight
  have hfz : |f (z + baseHeight) - f baseHeight| ≤ |z| := by
    have h :=
      hf.dist_le_mul (z + baseHeight) (by simp)
        baseHeight (by simp)
    simpa [Real.dist_eq] using h
  have hpoint0 : point 0 = z / Real.sqrt rho := by
    simp [point, z, baseHeight,
      wz1Lemma23SnappedHeightPoint,
      wz1Lemma23HeightGraphPoint]
    ring
  have hpoint1 :
      point 1 =
        (f (z + baseHeight) - f baseHeight) /
          Real.sqrt rho := by
    simp [point, z, baseHeight,
      wz1Lemma23SnappedHeightPoint,
      wz1Lemma23HeightGraphPoint,
      wz1Lemma23CenteredSlope]
    ring
  have h0 : |point 0| ≤ 1 := by
    rw [hpoint0, abs_div, abs_of_pos hsqrt]
    exact (div_le_one hsqrt).2 hz
  have h1 : |point 1| ≤ 1 := by
    rw [hpoint1, abs_div, abs_of_pos hsqrt]
    exact (div_le_one hsqrt).2 (hfz.trans hz)
  exact wz1Lemma23_point2_norm_le_two point h0 h1

/-- One actual snapped local-graph point has norm at most five under the
paper coordinate crop. -/
lemma wz1Lemma23_local_point_bound_of_coord
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hcoord : ∀ point ∈ Y.union, ∀ i : Fin 3, |point i| ≤ 1)
    (g : ℝ → ℝ) (hg : ∀ y, |g y| ≤ 2)
    {idx : ℤ × ℤ × ℤ}
    (hidx : idx ∈ wz1Lemma23ActiveCells Y rho hrho) :
    ‖wz1Lemma23SnappedLocalPoint rho g idx‖ ≤ 5 := by
  let y := (wz1Lemma23SnappedPoint rho idx) (1 : Fin 3)
  let point := wz1Lemma23SnappedLocalPoint rho g idx
  have hy : |y| ≤ 3 / 2 :=
    wz1Lemma23_active_cell_center_coord_bound_of_coord
      hrho hrho_one hcoord hidx 1
  have hgdiff : |g y - g 0| ≤ 4 := by
    calc
      |g y - g 0| ≤ |g y| + |g 0| := abs_sub _ _
      _ ≤ 2 + 2 := by
        gcongr
        · exact hg y
        · exact hg 0
      _ = 4 := by norm_num
  have hpoint0 : point 0 = -(g y - g 0) := by
    simp [point, y, wz1Lemma23SnappedLocalPoint,
      wz1Lemma23LocalGraphPoint, wz1Lemma23CenteredLocal]
  have hpoint1 : point 1 = y := by
    simp [point, y, wz1Lemma23SnappedLocalPoint,
      wz1Lemma23LocalGraphPoint]
  have h0 : |point 0| ≤ 4 := by
    rw [hpoint0, abs_neg]
    exact hgdiff
  have h1 : |point 1| ≤ 3 / 2 := by
    rw [hpoint1]
    exact hy
  exact wz1Lemma23_point2_norm_le_five point h0 h1

/-- Unit-ball compatibility wrapper for the local-point bound. -/
lemma wz1Lemma23_local_point_bound
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (g : ℝ → ℝ) (hg : ∀ y, |g y| ≤ 2)
    {idx : ℤ × ℤ × ℤ}
    (hidx : idx ∈ wz1Lemma23ActiveCells Y rho hrho) :
    ‖wz1Lemma23SnappedLocalPoint rho g idx‖ ≤ 5 := by
  apply wz1Lemma23_local_point_bound_of_coord hrho hrho_one
  · intro point hpoint coordinate
    have hnorm : ‖point‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
    exact (PiLp.norm_apply_le point coordinate).trans hnorm
  · exact hg
  · exact hidx

/--
The three actual vertex classes of a Lemma 23 package lie in fixed balls when
the source cells come from one `sqrt rho` height window.
-/
theorem WZ1Lemma23ActualTripartitePackage.vertex_bounds_of_coord
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hcoord : ∀ point ∈ Y.union, ∀ i : Fin 3, |point i| ≤ 1)
    {f g : ℝ → ℝ} (hf : LipschitzOnWith 1 f Set.univ)
    (hg : ∀ y, |g y| ≤ 2)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (hactive :
      cells ⊆ wz1Lemma23ActiveCells Y rho hrho)
    (hwindow : WZ1Lemma23SingleHeightWindow rho cells)
    {baseHeightIndex baseGlobalBin : ℤ}
    (package :
      WZ1Lemma23ActualTripartitePackage
        rho f g cells baseHeightIndex baseGlobalBin) :
    (∀ point ∈ wz1Lemma23NormalizedFirstVertices rho package.F,
        dist point 0 ≤ 2) ∧
      (∀ point ∈ package.G₁, dist point 0 ≤ 5) ∧
      ∀ point ∈ package.G₂, dist point 0 ≤ 5 := by
  have hcycleCells :
      ∀ path ∈ package.cycles,
        path.1 ∈ cells ∧ path.2.1 ∈ cells ∧
          path.2.2.1 ∈ cells ∧ path.2.2.2 ∈ cells := by
    intro path hpath
    have hbase :
        path ∈
          wz1Lemma23SnappedBaseCycles
            rho f g cells baseHeightIndex baseGlobalBin := by
      rwa [package.cycles_eq] at hpath
    have hfour :
        path ∈ wz1Lemma23SnappedFourCycles rho f g cells :=
      (Finset.mem_filter.mp hbase).1
    have hrelations :
        (path.1 ∈ cells ∧ path.2.1 ∈ cells ∧
          path.2.2.1 ∈ cells ∧ path.2.2.2 ∈ cells) ∧
        wz1Lemma23SameSnappedLocalGrain rho g
            path.1 path.2.1 ∧
        wz1Lemma23SameSnappedLocalGrain rho g
            path.2.2.2 path.2.2.1 ∧
        wz1Lemma23SnappedHeight path.1 =
            wz1Lemma23SnappedHeight path.2.2.2 ∧
        wz1Lemma23SnappedHeight path.2.1 =
            wz1Lemma23SnappedHeight path.2.2.1 ∧
        wz1Lemma23SnappedGlobalBin rho f path.2.1 =
            wz1Lemma23SnappedGlobalBin rho f path.2.2.1 := by
      simpa [wz1Lemma23SnappedFourCycles,
        wz1Lemma23FourCycles,
        Finset.mem_filter, Finset.mem_product] using hfour
    exact hrelations.1
  have hbaseHeight :
      ∀ path ∈ package.cycles,
        (wz1Lemma23SnappedPoint rho path.1) (2 : Fin 3) =
          wz1Lemma23SnappedBaseHeight rho baseHeightIndex := by
    intro path hpath
    have hbase :
        path ∈
          wz1Lemma23SnappedBaseCycles
            rho f g cells baseHeightIndex baseGlobalBin := by
      rwa [package.cycles_eq] at hpath
    have hheight :
        wz1Lemma23SnappedHeight path.1 = baseHeightIndex :=
      (Finset.mem_filter.mp hbase).2.1
    have hindex : path.1.2.2 = baseHeightIndex := by
      simpa [wz1Lemma23SnappedHeight] using hheight
    simp [wz1Lemma23SnappedPoint, wz1Lemma23CellCenter,
      wz1Lemma23SnappedBaseHeight, point3, hindex]
  constructor
  · intro point hpoint
    rw [package.F_eq] at hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨sourcePoint, hsourcePoint, rfl⟩
    rcases Finset.mem_image.mp hsourcePoint with
      ⟨path, hpath, rfl⟩
    have hcells := hcycleCells path hpath
    have hheight :
        |(wz1Lemma23SnappedPoint rho path.2.1) (2 : Fin 3) -
            wz1Lemma23SnappedBaseHeight rho baseHeightIndex| ≤
          Real.sqrt rho := by
      rw [← hbaseHeight path hpath]
      exact hwindow.height_sub_le hcells.2.1 hcells.1
    simpa [dist_zero_right] using
      wz1Lemma23_normalized_height_point_bound
        hrho f hf baseHeightIndex path.2.1 hheight
  · constructor
    · intro point hpoint
      rw [package.G₁_eq] at hpoint
      rcases Finset.mem_image.mp hpoint with
        ⟨path, hpath, rfl⟩
      have hidx := (hcycleCells path hpath).1
      simpa [dist_zero_right] using
        wz1Lemma23_local_point_bound_of_coord
          hrho hrho_one hcoord g hg (hactive hidx)
    · intro point hpoint
      rw [package.G₂_eq] at hpoint
      rcases Finset.mem_image.mp hpoint with
        ⟨path, hpath, rfl⟩
      have hidx := (hcycleCells path hpath).2.2.1
      simpa [dist_zero_right] using
        wz1Lemma23_local_point_bound_of_coord
          hrho hrho_one hcoord g hg (hactive hidx)

/-- Unit-ball compatibility wrapper for the normalized vertex bounds. -/
theorem WZ1Lemma23ActualTripartitePackage.vertex_bounds
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    {f g : ℝ → ℝ} (hf : LipschitzOnWith 1 f Set.univ)
    (hg : ∀ y, |g y| ≤ 2)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (hactive : cells ⊆ wz1Lemma23ActiveCells Y rho hrho)
    (hwindow : WZ1Lemma23SingleHeightWindow rho cells)
    {baseHeightIndex baseGlobalBin : ℤ}
    (package :
      WZ1Lemma23ActualTripartitePackage
        rho f g cells baseHeightIndex baseGlobalBin) :
    (∀ point ∈ wz1Lemma23NormalizedFirstVertices rho package.F,
        dist point 0 ≤ 2) ∧
      (∀ point ∈ package.G₁, dist point 0 ≤ 5) ∧
      ∀ point ∈ package.G₂, dist point 0 ≤ 5 := by
  apply package.vertex_bounds_of_coord hrho hrho_one
  · intro point hpoint coordinate
    have hnorm : ‖point‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
    exact (PiLp.norm_apply_le point coordinate).trans hnorm
  · exact hf
  · exact hg
  · exact hactive
  · exact hwindow

end

end Kakeya.Assouad
