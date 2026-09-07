import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ExactSliceCells

/-!
# Slice popularity preparation for WZ1 Lemma 23

The exact-slice construction is now applied separately on each occupied
height slab.  This preserves many different snapped height layers while every
cell inside one layer still carries a genuine common-height representative.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory Set

/-- Height indices of spatial cells that can meet the unit ball. -/
def wz1Lemma23BoundedHeightIndices
    (rho : ℝ) (hrho : 0 < rho) : Finset ℤ :=
  (wz1Lemma23BoundedCells rho hrho).image fun idx => idx.2.2

/-- The half-open real-height interval corresponding to one snapped layer. -/
def wz1Lemma23HeightInterval
    (rho : ℝ) (heightIndex : ℤ) : Set ℝ :=
  let side := gridSide (rho / 2)
  Set.Ico
    ((heightIndex : ℝ) * side)
    (((heightIndex : ℝ) + 1) * side)

/-- The corresponding three-dimensional horizontal slab. -/
def wz1Lemma23HeightSlab
    (rho : ℝ) (heightIndex : ℤ) : Set Point3 :=
  {point | point (2 : Fin 3) ∈
    wz1Lemma23HeightInterval rho heightIndex}

/-- One height slab has positive width. -/
lemma wz1Lemma23_heightInterval_nonempty
    {rho : ℝ} (hrho : 0 < rho) (heightIndex : ℤ) :
    ((heightIndex : ℝ) * gridSide (rho / 2) :
        ℝ) <
      ((heightIndex : ℝ) + 1) * gridSide (rho / 2) := by
  have hside : 0 < gridSide (rho / 2) := by
    simp [gridSide]
    positivity
  linarith

/-- Membership in a height slab is exactly a fixed floor value. -/
lemma wz1Lemma23_mem_heightSlab_iff
    {rho : ℝ} (hrho : 0 < rho)
    (heightIndex : ℤ) (point : Point3) :
    point ∈ wz1Lemma23HeightSlab rho heightIndex ↔
      Int.floor
          (point (2 : Fin 3) / gridSide (rho / 2)) =
        heightIndex := by
  have hside : 0 < gridSide (rho / 2) := by
    simp [gridSide]
    positivity
  rw [Int.floor_eq_iff]
  simp only [wz1Lemma23HeightSlab,
    wz1Lemma23HeightInterval, Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · rintro ⟨hlower, hupper⟩
    constructor
    · have h :=
        (le_div_iff₀ hside).2 hlower
      simpa using h
    · have h :=
        (div_lt_iff₀ hside).2 hupper
      simpa using h
  · rintro ⟨hlower, hupper⟩
    constructor
    · have h :=
        (le_div_iff₀ hside).1 hlower
      simpa using h
    · have h :=
        (div_lt_iff₀ hside).1 hupper
      simpa using h

/-- Distinct height slabs are disjoint. -/
lemma wz1Lemma23_heightSlab_disjoint
    {rho : ℝ} (hrho : 0 < rho)
    {first second : ℤ} (hne : first ≠ second) :
    Disjoint
      (wz1Lemma23HeightSlab rho first)
      (wz1Lemma23HeightSlab rho second) := by
  rw [Set.disjoint_left]
  intro point hfirst hsecond
  have h1 :=
    (wz1Lemma23_mem_heightSlab_iff hrho first point).mp hfirst
  have h2 :=
    (wz1Lemma23_mem_heightSlab_iff hrho second point).mp hsecond
  exact hne (h1.symm.trans h2)

/-- Every radius-two point lies in one bounded height slab. -/
lemma wz1Lemma23_radiusTwo_mem_boundedHeightSlab
    {rho : ℝ} (hrho : 0 < rho)
    {point : Point3} (hpoint : ‖point‖ ≤ 2) :
    ∃ heightIndex ∈ wz1Lemma23BoundedHeightIndices rho hrho,
      point ∈ wz1Lemma23HeightSlab rho heightIndex := by
  let idx := wz1Lemma23CellIndex rho point
  have hidx : idx ∈ wz1Lemma23BoundedCells rho hrho :=
    wz1Lemma23_index_mem_bounded_two hrho hpoint
  let heightIndex := idx.2.2
  have hheight :
      heightIndex ∈ wz1Lemma23BoundedHeightIndices rho hrho := by
    exact Finset.mem_image.mpr ⟨idx, hidx, rfl⟩
  refine ⟨heightIndex, hheight, ?_⟩
  apply (wz1Lemma23_mem_heightSlab_iff hrho heightIndex point).2
  rfl

/-- Unit-ball compatibility wrapper for bounded height slabs. -/
lemma wz1Lemma23_unitBall_mem_boundedHeightSlab
    {rho : ℝ} (hrho : 0 < rho)
    {point : Point3} (hpoint : ‖point‖ ≤ 1) :
    ∃ heightIndex ∈ wz1Lemma23BoundedHeightIndices rho hrho,
      point ∈ wz1Lemma23HeightSlab rho heightIndex :=
  wz1Lemma23_radiusTwo_mem_boundedHeightSlab hrho (hpoint.trans (by norm_num))

/-- The bounded height slabs cover a shading in the radius-two ball. -/
lemma wz1Lemma23_shading_covered_by_heightSlabs_two
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 2) :
    Y.union ⊆
      ⋃ heightIndex ∈ wz1Lemma23BoundedHeightIndices rho hrho,
        wz1Lemma23HeightSlab rho heightIndex := by
  intro point hpoint
  have hnorm : ‖point‖ ≤ 2 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
  rcases
      wz1Lemma23_radiusTwo_mem_boundedHeightSlab hrho hnorm with
    ⟨heightIndex, hheight, hslab⟩
  exact Set.mem_iUnion₂.mpr ⟨heightIndex, hheight, hslab⟩

/-- Unit-ball compatibility wrapper for height-slab coverage. -/
lemma wz1Lemma23_shading_covered_by_heightSlabs
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1) :
    Y.union ⊆
      ⋃ heightIndex ∈ wz1Lemma23BoundedHeightIndices rho hrho,
        wz1Lemma23HeightSlab rho heightIndex := by
  apply wz1Lemma23_shading_covered_by_heightSlabs_two Y hrho
  intro point hpoint
  have h := hball hpoint
  simp only [Metric.mem_closedBall, dist_zero_right] at h ⊢
  linarith

/--
Every bounded height slab has a genuine representative slice whose area is at
least the slab average.  Empty slabs are allowed and contribute zero.
-/
theorem wz1_lemma23_choose_slice_in_each_heightSlab
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hfinite : volume Y.union ≠ ⊤) :
    ∃ selectedHeight : ℤ → ℝ,
      ∀ heightIndex ∈ wz1Lemma23BoundedHeightIndices rho hrho,
        selectedHeight heightIndex ∈
            wz1Lemma23HeightInterval rho heightIndex ∧
          volume (Y.union ∩
              wz1Lemma23HeightSlab rho heightIndex) /
                ENNReal.ofReal (gridSide (rho / 2)) ≤
            volume
              (wz1Lemma23PlanarSlice Y.union
                (selectedHeight heightIndex)) := by
  have hmeas : MeasurableSet Y.union := by
    have hunion :
        Y.union = ⋃ i : Fin F.card, Y.carrier i := by
      ext point
      constructor
      · rintro ⟨i, hi⟩
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
      · intro hpoint
        rcases Set.mem_iUnion.mp hpoint with ⟨i, hi⟩
        exact ⟨i, hi⟩
    rw [hunion]
    exact MeasurableSet.iUnion fun i => Y.measurable_carrier i
  have hchoice :
      ∀ heightIndex : ℤ,
        ∃ z : ℝ,
          z ∈ wz1Lemma23HeightInterval rho heightIndex ∧
            volume (Y.union ∩
                wz1Lemma23HeightSlab rho heightIndex) /
                  ENNReal.ofReal (gridSide (rho / 2)) ≤
              volume (wz1Lemma23PlanarSlice Y.union z) := by
    intro heightIndex
    let side := gridSide (rho / 2)
    have hinterval :
        (heightIndex : ℝ) * side <
          ((heightIndex : ℝ) + 1) * side := by
      simpa [side] using
        wz1Lemma23_heightInterval_nonempty hrho heightIndex
    have h :=
      wz1_lemma23_exists_good_height_in_slab
        hmeas hfinite hinterval
    rcases h with ⟨z, hz, hbound⟩
    refine ⟨z, ?_, ?_⟩
    · simpa [wz1Lemma23HeightInterval, side] using hz
    · have hlength :
          ((heightIndex : ℝ) + 1) * side -
              (heightIndex : ℝ) * side =
            side := by
        ring
      rw [hlength] at hbound
      simpa [wz1Lemma23HeightSlab,
        wz1Lemma23HeightInterval, side] using hbound
  choose selectedHeight hselected using hchoice
  exact ⟨selectedHeight, fun heightIndex _ => hselected heightIndex⟩

/--
Exact-slice cells selected from different height slabs have different snapped
height indices.
-/
lemma wz1Lemma23_exactSliceCells_height_eq
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    {heightIndex : ℤ} {z : ℝ}
    (hz : z ∈ wz1Lemma23HeightInterval rho heightIndex)
    {idx : ℤ × ℤ × ℤ}
    (hidx : idx ∈ wz1Lemma23ExactSliceCells Y rho hrho z) :
    idx.2.2 = heightIndex := by
  have hheight :=
    wz1Lemma23ExactSliceCells_height Y hrho z hidx
  have hside : 0 < gridSide (rho / 2) := by
    simp [gridSide]
    positivity
  have hfloor :
      Int.floor (z / gridSide (rho / 2)) = heightIndex := by
    rw [Int.floor_eq_iff]
    rcases hz with ⟨hlower, hupper⟩
    constructor
    · exact (le_div_iff₀ hside).2 hlower
    · exact (div_lt_iff₀ hside).2 hupper
  exact hheight.trans hfloor

/-- Exact-slice cell families from distinct selected slabs are disjoint. -/
lemma wz1Lemma23_exactSliceCells_disjoint
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (selectedHeight : ℤ → ℝ)
    (hselected :
      ∀ heightIndex ∈ wz1Lemma23BoundedHeightIndices rho hrho,
        selectedHeight heightIndex ∈
          wz1Lemma23HeightInterval rho heightIndex)
    {first second : ℤ}
    (hfirst : first ∈ wz1Lemma23BoundedHeightIndices rho hrho)
    (hsecond : second ∈ wz1Lemma23BoundedHeightIndices rho hrho)
    (hne : first ≠ second) :
    Disjoint
      (wz1Lemma23ExactSliceCells
        Y rho hrho (selectedHeight first))
      (wz1Lemma23ExactSliceCells
        Y rho hrho (selectedHeight second)) := by
  rw [Finset.disjoint_left]
  intro idx hidxFirst hidxSecond
  have hheightFirst :
      idx.2.2 = first :=
    wz1Lemma23_exactSliceCells_height_eq
      Y hrho (hselected first hfirst) hidxFirst
  have hheightSecond :
      idx.2.2 = second :=
    wz1Lemma23_exactSliceCells_height_eq
      Y hrho (hselected second hsecond) hidxSecond
  exact hne (hheightFirst.symm.trans hheightSecond)

/--
Assemble the genuine exact-slice cells from all bounded height slabs.  The
union cardinality is exactly the sum of the per-layer cardinalities.
-/
theorem wz1_lemma23_assemble_slice_popularity_cells
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hfinite : volume Y.union ≠ ⊤) :
    ∃ selectedHeight : ℤ → ℝ,
      let heightIndices :=
        wz1Lemma23BoundedHeightIndices rho hrho
      let layerCells := fun heightIndex =>
        wz1Lemma23ExactSliceCells
          Y rho hrho (selectedHeight heightIndex)
      let cells := heightIndices.biUnion layerCells
      (∀ heightIndex ∈ heightIndices,
        selectedHeight heightIndex ∈
            wz1Lemma23HeightInterval rho heightIndex ∧
          volume (Y.union ∩
              wz1Lemma23HeightSlab rho heightIndex) /
                ENNReal.ofReal (gridSide (rho / 2)) ≤
            volume
              (wz1Lemma23PlanarSlice Y.union
                (selectedHeight heightIndex))) ∧
      cells.card =
        ∑ heightIndex ∈ heightIndices,
          (layerCells heightIndex).card ∧
      ∀ heightIndex ∈ heightIndices,
        ∀ idx ∈ layerCells heightIndex,
          idx.2.2 = heightIndex := by
  rcases
      wz1_lemma23_choose_slice_in_each_heightSlab
        Y hrho hfinite with
    ⟨selectedHeight, hselected⟩
  refine ⟨selectedHeight, hselected, ?_, ?_⟩
  · apply Finset.card_biUnion
    intro first hfirst second hsecond hne
    exact wz1Lemma23_exactSliceCells_disjoint
      Y hrho selectedHeight
      (fun heightIndex hheight =>
        (hselected heightIndex hheight).1)
      hfirst hsecond hne
  · intro heightIndex hheight idx hidx
    exact wz1Lemma23_exactSliceCells_height_eq
      Y hrho (hselected heightIndex hheight).1 hidx

/-- Every exact-slice cell is an actual active spatial cell of the shading. -/
lemma wz1Lemma23_exactSliceCells_subset_activeCells
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (z : ℝ) :
    wz1Lemma23ExactSliceCells Y rho hrho z ⊆
      wz1Lemma23ActiveCells Y rho hrho := by
  intro idx hidx
  rw [wz1Lemma23_mem_active_iff]
  rcases
      (wz1Lemma23_mem_exactSliceCells_iff
        Y hrho z idx).mp hidx with
    ⟨hbounded, point, hpoint, hpointIndex⟩
  refine ⟨hbounded, ?_⟩
  let lifted := wz1Lemma23LiftSlicePoint z point
  have hlifted : lifted ∈ Y.union := by
    simpa [lifted, wz1Lemma23LiftSlicePoint] using
      (wz1Lemma23_mem_planarSlice_iff.mp hpoint)
  have hcell : lifted ∈ wz1Lemma23Cell rho idx := by
    simpa [wz1Lemma23Cell, lifted] using hpointIndex
  exact ⟨lifted, hlifted, hcell⟩

/--
The union of the selected genuine slices is an actual active-cell family, and
its cardinality controls the full three-dimensional shaded volume.
-/
theorem wz1_lemma23_slice_popularity_cell_abundance_two
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 2) :
    ∃ selectedHeight : ℤ → ℝ,
      let heightIndices :=
        wz1Lemma23BoundedHeightIndices rho hrho
      let layerCells := fun heightIndex =>
        wz1Lemma23ExactSliceCells
          Y rho hrho (selectedHeight heightIndex)
      let cells := heightIndices.biUnion layerCells
      cells ⊆ wz1Lemma23ActiveCells Y rho hrho ∧
      volume Y.union ≤
        (cells.card : ENNReal) *
          ENNReal.ofReal (gridSide (rho / 2)) *
          (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) ∧
      (∀ heightIndex ∈ heightIndices,
        selectedHeight heightIndex ∈
            wz1Lemma23HeightInterval rho heightIndex ∧
          volume (Y.union ∩
              wz1Lemma23HeightSlab rho heightIndex) /
                ENNReal.ofReal (gridSide (rho / 2)) ≤
            volume
              (wz1Lemma23PlanarSlice Y.union
                (selectedHeight heightIndex))) ∧
      ∀ heightIndex ∈ heightIndices,
        ∀ idx ∈ layerCells heightIndex,
          idx.2.2 = heightIndex := by
  have hfinite : volume Y.union ≠ ⊤ := by
    have hballFinite :
        volume (Metric.closedBall (0 : Point3) 2) < ⊤ :=
      Metric.isBounded_closedBall.measure_lt_top
    exact
      ((measure_mono hball).trans_lt hballFinite).ne
  rcases
      wz1_lemma23_assemble_slice_popularity_cells
        Y hrho hfinite with
    ⟨selectedHeight, hselected, hcard, hheight⟩
  let heightIndices :=
    wz1Lemma23BoundedHeightIndices rho hrho
  let layerCells := fun heightIndex =>
    wz1Lemma23ExactSliceCells
      Y rho hrho (selectedHeight heightIndex)
  let cells := heightIndices.biUnion layerCells
  have hcellsActive :
      cells ⊆ wz1Lemma23ActiveCells Y rho hrho := by
    intro idx hidx
    rcases Finset.mem_biUnion.mp hidx with
      ⟨heightIndex, hheightIndex, hidxLayer⟩
    exact
      wz1Lemma23_exactSliceCells_subset_activeCells
        Y hrho (selectedHeight heightIndex) hidxLayer
  have hcover :
      Y.union ⊆
        ⋃ heightIndex ∈ heightIndices,
          Y.union ∩ wz1Lemma23HeightSlab rho heightIndex := by
    intro point hpoint
    have hslab :=
      wz1Lemma23_shading_covered_by_heightSlabs_two
        Y hrho hball hpoint
    rcases Set.mem_iUnion₂.mp hslab with
      ⟨heightIndex, hheightIndex, hpointSlab⟩
    exact Set.mem_iUnion₂.mpr
      ⟨heightIndex, hheightIndex, hpoint, hpointSlab⟩
  have hvolumeSum :
      volume Y.union ≤
        ∑ heightIndex ∈ heightIndices,
          volume
            (Y.union ∩
              wz1Lemma23HeightSlab rho heightIndex) := by
    exact
      (measure_mono hcover).trans
        (measure_biUnion_finset_le heightIndices fun heightIndex =>
          Y.union ∩ wz1Lemma23HeightSlab rho heightIndex)
  let side : ENNReal :=
    ENNReal.ofReal (gridSide (rho / 2))
  let disk : ENNReal :=
    ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi
  have hsidePos : 0 < side := by
    apply ENNReal.ofReal_pos.mpr
    simp [gridSide]
    positivity
  have hsideTop : side ≠ ⊤ := by
    simp [side]
  have hlayer :
      ∀ heightIndex ∈ heightIndices,
        volume
            (Y.union ∩
              wz1Lemma23HeightSlab rho heightIndex) ≤
          ((layerCells heightIndex).card : ENNReal) *
            disk * side := by
    intro heightIndex hheightIndex
    have hslice :=
      (hselected heightIndex hheightIndex).2
    have harea :=
      wz1_lemma23_exactSlice_area_le_two
        Y hrho hball (selectedHeight heightIndex)
    have hdiv :
        volume
              (Y.union ∩
                wz1Lemma23HeightSlab rho heightIndex) /
            side ≤
          ((layerCells heightIndex).card : ENNReal) *
            disk := by
      exact hslice.trans harea
    exact
      (ENNReal.div_le_iff hsidePos.ne' hsideTop).mp hdiv
  have hsum :
      (∑ heightIndex ∈ heightIndices,
          volume
            (Y.union ∩
              wz1Lemma23HeightSlab rho heightIndex)) ≤
        (cells.card : ENNReal) * side * disk := by
    calc
      (∑ heightIndex ∈ heightIndices,
          volume
            (Y.union ∩
              wz1Lemma23HeightSlab rho heightIndex))
          ≤ ∑ heightIndex ∈ heightIndices,
              ((layerCells heightIndex).card : ENNReal) *
                disk * side := by
            exact Finset.sum_le_sum fun heightIndex hheightIndex =>
              hlayer heightIndex hheightIndex
      _ = (∑ heightIndex ∈ heightIndices,
              ((layerCells heightIndex).card : ENNReal)) *
            disk * side := by
          rw [Finset.sum_mul, Finset.sum_mul]
      _ = (cells.card : ENNReal) * side * disk := by
          have hcardENN :
              (cells.card : ENNReal) =
                ∑ heightIndex ∈ heightIndices,
                  ((layerCells heightIndex).card : ENNReal) := by
            rw [hcard]
            norm_cast
          rw [← hcardENN]
          ring
  refine ⟨selectedHeight, hcellsActive, hvolumeSum.trans hsum,
    hselected, hheight⟩

/-- Unit-ball compatibility wrapper for slice popularity. -/
theorem wz1_lemma23_slice_popularity_cell_abundance
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1) :
    ∃ selectedHeight : ℤ → ℝ,
      let heightIndices :=
        wz1Lemma23BoundedHeightIndices rho hrho
      let layerCells := fun heightIndex =>
        wz1Lemma23ExactSliceCells
          Y rho hrho (selectedHeight heightIndex)
      let cells := heightIndices.biUnion layerCells
      cells ⊆ wz1Lemma23ActiveCells Y rho hrho ∧
      volume Y.union ≤
        (cells.card : ENNReal) *
          ENNReal.ofReal (gridSide (rho / 2)) *
          (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi) ∧
      (∀ heightIndex ∈ heightIndices,
        selectedHeight heightIndex ∈
            wz1Lemma23HeightInterval rho heightIndex ∧
          volume (Y.union ∩
              wz1Lemma23HeightSlab rho heightIndex) /
                ENNReal.ofReal (gridSide (rho / 2)) ≤
            volume
              (wz1Lemma23PlanarSlice Y.union
                (selectedHeight heightIndex))) ∧
      ∀ heightIndex ∈ heightIndices,
        ∀ idx ∈ layerCells heightIndex,
          idx.2.2 = heightIndex := by
  apply wz1_lemma23_slice_popularity_cell_abundance_two Y hrho
  intro point hpoint
  have h := hball hpoint
  simp only [Metric.mem_closedBall, dist_zero_right] at h ⊢
  linarith

end

end Kakeya.Assouad
