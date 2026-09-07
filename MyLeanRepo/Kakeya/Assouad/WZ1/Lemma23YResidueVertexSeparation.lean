import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23YResiduePreparedPackage

/-!
# Vertex separation for the actual y-residue Lemma 23 graph

The selected actual cells have `sqrt rho` separation between distinct
snapped y-layers.  This directly separates both local graph classes.
Independently, distinct snapped z-indices are one fine grid side apart; after
the paper's `rho^(-1/2)` normalization this separates the first graph class
at scale `sqrt rho / sqrt 3`.
-/

namespace Kakeya.Assouad

noncomputable section

private lemma wz1Lemma23_point2_coord_abs_le_dist
    (first second : Point2) (i : Fin 2) :
    |first i - second i| ≤ dist first second := by
  have h := PiLp.norm_apply_le (first - second) i
  simpa [dist_eq_norm, Real.norm_eq_abs] using h

private lemma wz1Lemma23_cell_center_z_diff
    (rho : ℝ) (first second : ℤ × ℤ × ℤ) :
    (wz1Lemma23CellCenter rho first) 2 -
        (wz1Lemma23CellCenter rho second) 2 =
      ((first.2.2 - second.2.2 : ℤ) : ℝ) *
        gridSide (rho / 2) := by
  simp [wz1Lemma23CellCenter, point3]
  ring

private lemma wz1Lemma23_distinct_z_center_separation
    {rho : ℝ} (hrho : 0 < rho)
    {first second : ℤ × ℤ × ℤ}
    (hne : first.2.2 ≠ second.2.2) :
    rho / Real.sqrt 3 ≤
      |(wz1Lemma23CellCenter rho first) 2 -
        (wz1Lemma23CellCenter rho second) 2| := by
  have hside :
      gridSide (rho / 2) = rho / Real.sqrt 3 := by
    simp [gridSide]
    ring
  have hsidePos : 0 < gridSide (rho / 2) := by
    rw [hside]
    positivity
  have hdiff :
      first.2.2 - second.2.2 ≠ 0 :=
    sub_ne_zero.mpr hne
  have hint :
      (1 : ℝ) ≤
        |((first.2.2 - second.2.2 : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hdiff
  rw [wz1Lemma23_cell_center_z_diff,
    abs_mul, abs_of_pos hsidePos, ← hside]
  nlinarith

/-- Distinct local graph points inherit the selected y-layer separation. -/
lemma wz1Lemma23_local_points_separated
    {rho : ℝ} (g : ℝ → ℝ)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (hySeparated :
      ∀ first ∈ cells, ∀ second ∈ cells,
        first.2.1 = second.2.1 ∨
          Real.sqrt rho ≤
            |(wz1Lemma23CellCenter rho first) 1 -
              (wz1Lemma23CellCenter rho second) 1|)
    {first second : ℤ × ℤ × ℤ}
    (hfirst : first ∈ cells) (hsecond : second ∈ cells)
    (hne :
      wz1Lemma23SnappedLocalPoint rho g first ≠
        wz1Lemma23SnappedLocalPoint rho g second) :
    Real.sqrt rho ≤
      dist
        (wz1Lemma23SnappedLocalPoint rho g first)
        (wz1Lemma23SnappedLocalPoint rho g second) := by
  rcases hySeparated first hfirst second hsecond with
    hsame | hseparated
  · exfalso
    apply hne
    have hy :
        (wz1Lemma23SnappedPoint rho first) (1 : Fin 3) =
          (wz1Lemma23SnappedPoint rho second) (1 : Fin 3) := by
      simp [wz1Lemma23SnappedPoint,
        wz1Lemma23CellCenter, point3, hsame]
    rw [wz1Lemma23SnappedLocalPoint,
      wz1Lemma23SnappedLocalPoint, hy]
  · calc
      Real.sqrt rho ≤
          |(wz1Lemma23CellCenter rho first) 1 -
            (wz1Lemma23CellCenter rho second) 1| :=
        hseparated
      _ =
          |(wz1Lemma23SnappedLocalPoint rho g first) 1 -
            (wz1Lemma23SnappedLocalPoint rho g second) 1| := by
        simp [wz1Lemma23SnappedLocalPoint,
          wz1Lemma23LocalGraphPoint,
          wz1Lemma23SnappedPoint]
      _ ≤
          dist
            (wz1Lemma23SnappedLocalPoint rho g first)
            (wz1Lemma23SnappedLocalPoint rho g second) :=
        wz1Lemma23_point2_coord_abs_le_dist _ _ 1

/--
Distinct normalized height graph points are separated by one normalized fine
z-grid side.
-/
lemma wz1Lemma23_normalized_height_points_separated
    {rho : ℝ} (hrho : 0 < rho)
    (f : ℝ → ℝ) (baseHeightIndex : ℤ)
    {first second : ℤ × ℤ × ℤ}
    (hne :
      (1 / Real.sqrt rho) •
          wz1Lemma23SnappedHeightPoint
            rho f baseHeightIndex first ≠
        (1 / Real.sqrt rho) •
          wz1Lemma23SnappedHeightPoint
            rho f baseHeightIndex second) :
    Real.sqrt rho / Real.sqrt 3 ≤
      dist
        ((1 / Real.sqrt rho) •
          wz1Lemma23SnappedHeightPoint
            rho f baseHeightIndex first)
        ((1 / Real.sqrt rho) •
          wz1Lemma23SnappedHeightPoint
            rho f baseHeightIndex second) := by
  have hzNe : first.2.2 ≠ second.2.2 := by
    intro hz
    apply hne
    have hheight :
        (wz1Lemma23SnappedPoint rho first) (2 : Fin 3) =
          (wz1Lemma23SnappedPoint rho second) (2 : Fin 3) := by
      simp [wz1Lemma23SnappedPoint,
        wz1Lemma23CellCenter, point3, hz]
    rw [wz1Lemma23SnappedHeightPoint,
      wz1Lemma23SnappedHeightPoint, hheight]
  have hcenter :=
    wz1Lemma23_distinct_z_center_separation hrho hzNe
  have hsqrt : 0 < Real.sqrt rho :=
    Real.sqrt_pos.mpr hrho
  have hscale :
      (rho / Real.sqrt 3) / Real.sqrt rho =
        Real.sqrt rho / Real.sqrt 3 := by
    have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
    field_simp [hsqrt.ne', hsqrt3]
    nlinarith [Real.sq_sqrt hrho.le]
  have hcoord :
      ((1 / Real.sqrt rho) •
          wz1Lemma23SnappedHeightPoint
            rho f baseHeightIndex first) 0 -
        ((1 / Real.sqrt rho) •
          wz1Lemma23SnappedHeightPoint
            rho f baseHeightIndex second) 0 =
      ((wz1Lemma23CellCenter rho first) 2 -
        (wz1Lemma23CellCenter rho second) 2) /
          Real.sqrt rho := by
    simp [wz1Lemma23SnappedHeightPoint,
      wz1Lemma23HeightGraphPoint,
      wz1Lemma23SnappedPoint]
    ring
  calc
    Real.sqrt rho / Real.sqrt 3 =
        (rho / Real.sqrt 3) / Real.sqrt rho :=
      hscale.symm
    _ ≤
        |(wz1Lemma23CellCenter rho first) 2 -
          (wz1Lemma23CellCenter rho second) 2| /
            Real.sqrt rho := by
      gcongr
    _ =
        |((1 / Real.sqrt rho) •
            wz1Lemma23SnappedHeightPoint
              rho f baseHeightIndex first) 0 -
          ((1 / Real.sqrt rho) •
            wz1Lemma23SnappedHeightPoint
              rho f baseHeightIndex second) 0| := by
      rw [hcoord, abs_div, abs_of_pos hsqrt]
    _ ≤
        dist
          ((1 / Real.sqrt rho) •
            wz1Lemma23SnappedHeightPoint
              rho f baseHeightIndex first)
          ((1 / Real.sqrt rho) •
            wz1Lemma23SnappedHeightPoint
              rho f baseHeightIndex second) :=
      wz1Lemma23_point2_coord_abs_le_dist _ _ 0

/--
All three vertex classes of the normalized actual graph are separated at the
common scale `sqrt rho / sqrt 3`.
-/
theorem WZ1Lemma23ActualTripartitePackage.vertex_separation
    {rho : ℝ} (hrho : 0 < rho)
    {f g : ℝ → ℝ}
    {cells : Finset (ℤ × ℤ × ℤ)}
    (hySeparated :
      ∀ first ∈ cells, ∀ second ∈ cells,
        first.2.1 = second.2.1 ∨
          Real.sqrt rho ≤
            |(wz1Lemma23CellCenter rho first) 1 -
              (wz1Lemma23CellCenter rho second) 1|)
    {baseHeightIndex baseGlobalBin : ℤ}
    (package :
      WZ1Lemma23ActualTripartitePackage
        rho f g cells baseHeightIndex baseGlobalBin) :
    (wz1Lemma23NormalizedFirstVertices rho package.F).IsDeltaSeparated
        (Real.sqrt rho / Real.sqrt 3) ∧
      package.G₁.IsDeltaSeparated
        (Real.sqrt rho / Real.sqrt 3) ∧
      package.G₂.IsDeltaSeparated
        (Real.sqrt rho / Real.sqrt 3) := by
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
  constructor
  · intro first hfirst second hsecond hne
    rcases Finset.mem_image.mp hfirst with
      ⟨firstSource, hfirstSource, rfl⟩
    rcases Finset.mem_image.mp hsecond with
      ⟨secondSource, hsecondSource, rfl⟩
    rw [package.F_eq] at hfirstSource hsecondSource
    rcases Finset.mem_image.mp hfirstSource with
      ⟨firstPath, hfirstPath, rfl⟩
    rcases Finset.mem_image.mp hsecondSource with
      ⟨secondPath, hsecondPath, rfl⟩
    exact
      wz1Lemma23_normalized_height_points_separated
        hrho f baseHeightIndex hne
  · constructor
    · intro first hfirst second hsecond hne
      rw [package.G₁_eq] at hfirst hsecond
      rcases Finset.mem_image.mp hfirst with
        ⟨firstPath, hfirstPath, rfl⟩
      rcases Finset.mem_image.mp hsecond with
        ⟨secondPath, hsecondPath, rfl⟩
      have hroot :=
        wz1Lemma23_local_points_separated
          g hySeparated
          (hcycleCells firstPath hfirstPath).1
          (hcycleCells secondPath hsecondPath).1 hne
      exact
        (div_le_self (Real.sqrt_nonneg rho)
          ((Real.one_le_sqrt).2 (by norm_num))).trans hroot
    · intro first hfirst second hsecond hne
      rw [package.G₂_eq] at hfirst hsecond
      rcases Finset.mem_image.mp hfirst with
        ⟨firstPath, hfirstPath, rfl⟩
      rcases Finset.mem_image.mp hsecond with
        ⟨secondPath, hsecondPath, rfl⟩
      have hroot :=
        wz1Lemma23_local_points_separated
          g hySeparated
          (hcycleCells firstPath hfirstPath).2.2.1
          (hcycleCells secondPath hsecondPath).2.2.1 hne
      exact
        (div_le_self (Real.sqrt_nonneg rho)
          ((Real.one_le_sqrt).2 (by norm_num))).trans hroot

/--
The normalized graph stored by the y-residue prepared package carries the
same three separation conclusions.
-/
theorem WZ1Lemma23YResiduePreparedPackage.vertex_separation
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    {residuePackage :
      WZ1Lemma23YResiduePackage globalPackage}
    {localPackage :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C globalPackage.cells}
    (package :
      WZ1Lemma23YResiduePreparedPackage
        globalPackage residuePackage localPackage) :
    package.prepared.normalized.F.IsDeltaSeparated
        (Real.sqrt rho / Real.sqrt 3) ∧
      package.prepared.normalized.G₁.IsDeltaSeparated
        (Real.sqrt rho / Real.sqrt 3) ∧
      package.prepared.normalized.G₂.IsDeltaSeparated
        (Real.sqrt rho / Real.sqrt 3) := by
  have h :=
    package.prepared.actual.vertex_separation
      globalPackage.rho_pos residuePackage.y_separated
  rw [package.prepared.normalized.F_eq,
    package.prepared.normalized.G₁_eq,
    package.prepared.normalized.G₂_eq,
    package.prepared.normalized_sourceF,
    package.prepared.normalized_sourceG₁,
    package.prepared.normalized_sourceG₂]
  exact h

end

end Kakeya.Assouad
