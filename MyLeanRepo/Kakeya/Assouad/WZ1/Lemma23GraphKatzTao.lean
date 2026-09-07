import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23WindowedPreparedGraph

/-!
# Katz--Tao bounds for the actual WZ1 Lemma 23 graph

Each Lemma 23 vertex class is a graph over one genuinely separated scalar
coordinate.  A radius-`r` planar ball projects to an interval of length
`2 * r`, so a `delta`-separated coordinate fiber contains at most
`2 * r / delta + 2 <= 4 * r / delta` points.  This gives the absolute
one-dimensional Katz--Tao bound required by the final Theorem 22 interface.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Separation in one coordinate implies metric separation. -/
lemma coordinateSeparated_isDeltaSeparated
    {E : DiscreteSet 2} {delta : ℝ}
    (coordinate : Fin 2)
    (hseparated :
      ∀ first ∈ E, ∀ second ∈ E, first ≠ second →
        delta ≤ |first coordinate - second coordinate|) :
    E.IsDeltaSeparated delta := by
  intro first hfirst second hsecond hne
  exact
    (hseparated first hfirst second hsecond hne).trans
      (by
        have h := PiLp.dist_apply_le first second coordinate
        simpa [Real.dist_eq] using h)

/--
A finite planar set separated in one coordinate is a one-dimensional
Katz--Tao set with absolute constant four.
-/
lemma coordinateSeparated_isKatzTao
    {E : DiscreteSet 2} {delta : ℝ}
    (hdelta : 0 < delta) (coordinate : Fin 2)
    (hseparated :
      ∀ first ∈ E, ∀ second ∈ E, first ≠ second →
        delta ≤ |first coordinate - second coordinate|) :
    E.IsKatzTao delta 1 4 := by
  intro center r hdelta_r hr_one
  let selected :=
    E.filter fun point => dist point center ≤ r
  let label : Point2 → ℤ := fun point =>
    Int.floor (point coordinate / delta)
  have hselectedMem :
      ∀ point ∈ selected, point ∈ E := by
    intro point hpoint
    exact (Finset.mem_filter.mp hpoint).1
  have hselectedBall :
      ∀ point ∈ selected, dist point center ≤ r := by
    intro point hpoint
    exact (Finset.mem_filter.mp hpoint).2
  have hlabelInjective : Set.InjOn label selected := by
    intro first hfirst second hsecond hlabel
    by_contra hne
    have hcoordSep :=
      hseparated first (hselectedMem first hfirst)
        second (hselectedMem second hsecond) hne
    have hclose :
        |first coordinate - second coordinate| < delta :=
      wz1Lemma23_abs_sub_lt_of_floor_div_eq
        hdelta hlabel
    linarith
  let lower : ℤ :=
    Int.floor ((center coordinate - r) / delta)
  let upper : ℤ :=
    Int.floor ((center coordinate + r) / delta)
  have hlabelRange :
      selected.image label ⊆ Finset.Icc lower upper := by
    intro index hindex
    rcases Finset.mem_image.mp hindex with
      ⟨point, hpoint, rfl⟩
    have hcoordDist :
        |point coordinate - center coordinate| ≤
          dist point center := by
      have h :=
        PiLp.dist_apply_le point center coordinate
      simpa [Real.dist_eq] using h
    have hcoordBall :
        |point coordinate - center coordinate| ≤ r :=
      hcoordDist.trans (hselectedBall point hpoint)
    have hlower :
        (center coordinate - r) / delta ≤
          point coordinate / delta := by
      apply div_le_div_of_nonneg_right _ hdelta.le
      linarith [(abs_le.mp hcoordBall).1]
    have hupper :
        point coordinate / delta ≤
          (center coordinate + r) / delta := by
      apply div_le_div_of_nonneg_right _ hdelta.le
      linarith [(abs_le.mp hcoordBall).2]
    exact Finset.mem_Icc.mpr
      ⟨Int.floor_mono hlower, Int.floor_mono hupper⟩
  have hlowerUpper : lower ≤ upper := by
    apply Int.floor_mono
    apply div_le_div_of_nonneg_right _ hdelta.le
    linarith [hdelta_r]
  have hcardImage :
      (selected.image label).card =
        selected.card :=
    Finset.card_image_of_injOn hlabelInjective
  have hcardInterval :
      ((Finset.Icc lower upper).card : ℝ) =
        (upper : ℝ) + 1 - (lower : ℝ) := by
    have h :=
      Int.card_Icc_of_le lower upper (by omega)
    exact_mod_cast h
  have hlowerApprox :
      (center coordinate - r) / delta - 1 <
        (lower : ℝ) := by
    have h :=
      Int.lt_floor_add_one
        ((center coordinate - r) / delta)
    linarith
  have hupperApprox :
      (upper : ℝ) ≤
        (center coordinate + r) / delta :=
    Int.floor_le _
  have hcardReal :
      (selected.card : ℝ) ≤ 4 * (r / delta) := by
    have hcardNat :
        selected.card ≤
          (Finset.Icc lower upper).card := by
      rw [← hcardImage]
      exact Finset.card_le_card hlabelRange
    have hcardCast :
        (selected.card : ℝ) ≤
          ((Finset.Icc lower upper).card : ℝ) := by
      exact_mod_cast hcardNat
    have hinterval :
        ((Finset.Icc lower upper).card : ℝ) <
          2 * (r / delta) + 2 := by
      rw [hcardInterval]
      have hraw :
          (upper : ℝ) + 1 - (lower : ℝ) <
            (center coordinate + r) / delta + 1 -
              ((center coordinate - r) / delta - 1) := by
        linarith
      calc
        (upper : ℝ) + 1 - (lower : ℝ) <
            (center coordinate + r) / delta + 1 -
              ((center coordinate - r) / delta - 1) := hraw
        _ = 2 * (r / delta) + 2 := by ring
    have hratio : 1 ≤ r / delta := by
      exact (le_div_iff₀ hdelta).2 (by simpa using hdelta_r)
    linarith
  change (selected.card : ENNReal) ≤
    (4 : ENNReal) * Kakeya.realRpowENN (r / delta) 1
  calc
    (selected.card : ENNReal) =
        ENNReal.ofReal (selected.card : ℝ) := by simp
    _ ≤ ENNReal.ofReal (4 * (r / delta)) :=
      ENNReal.ofReal_le_ofReal hcardReal
    _ =
        (4 : ENNReal) *
          Kakeya.realRpowENN (r / delta) 1 := by
      simp [Kakeya.realRpowENN, Real.rpow_one,
        ENNReal.ofReal_mul]

/-- Distinct actual local graph points are separated in coordinate one. -/
lemma wz1Lemma23_local_points_coordinate_separated
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
      |(wz1Lemma23SnappedLocalPoint rho g first) 1 -
        (wz1Lemma23SnappedLocalPoint rho g second) 1| := by
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
  · simpa [wz1Lemma23SnappedLocalPoint,
      wz1Lemma23LocalGraphPoint,
      wz1Lemma23SnappedPoint] using hseparated

/-- Distinct normalized height graph points are separated in coordinate zero. -/
private lemma wz1Lemma23_normalized_height_points_coordinate_separated
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
      |((1 / Real.sqrt rho) •
          wz1Lemma23SnappedHeightPoint
            rho f baseHeightIndex first) 0 -
        ((1 / Real.sqrt rho) •
          wz1Lemma23SnappedHeightPoint
            rho f baseHeightIndex second) 0| := by
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
  have hcenter :
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
      sub_ne_zero.mpr hzNe
    have hint :
        (1 : ℝ) ≤
          |((first.2.2 - second.2.2 : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hdiff
    have hcenterDiff :
        (wz1Lemma23CellCenter rho first) 2 -
            (wz1Lemma23CellCenter rho second) 2 =
          ((first.2.2 - second.2.2 : ℤ) : ℝ) *
            gridSide (rho / 2) := by
      simp [wz1Lemma23CellCenter, point3]
      ring
    rw [hcenterDiff, abs_mul, abs_of_pos hsidePos, ← hside]
    nlinarith
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
  rw [hcoord, abs_div, abs_of_pos hsqrt, ← hscale]
  gcongr

/--
All three actual normalized vertex classes are separated in their graph
parameter coordinate at the common graph scale.
-/
theorem WZ1Lemma23ActualTripartitePackage.vertex_coordinate_separation
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
    (∀ first ∈ wz1Lemma23NormalizedFirstVertices rho package.F,
        ∀ second ∈ wz1Lemma23NormalizedFirstVertices rho package.F,
          first ≠ second →
            Real.sqrt rho / Real.sqrt 3 ≤
              |first 0 - second 0|) ∧
      (∀ first ∈ package.G₁, ∀ second ∈ package.G₁,
        first ≠ second →
          Real.sqrt rho / Real.sqrt 3 ≤
            |first 1 - second 1|) ∧
      ∀ first ∈ package.G₂, ∀ second ∈ package.G₂,
        first ≠ second →
          Real.sqrt rho / Real.sqrt 3 ≤
            |first 1 - second 1| := by
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
      wz1Lemma23_normalized_height_points_coordinate_separated
        hrho f baseHeightIndex hne
  · constructor
    · intro first hfirst second hsecond hne
      rw [package.G₁_eq] at hfirst hsecond
      rcases Finset.mem_image.mp hfirst with
        ⟨firstPath, hfirstPath, rfl⟩
      rcases Finset.mem_image.mp hsecond with
        ⟨secondPath, hsecondPath, rfl⟩
      have hroot :=
        wz1Lemma23_local_points_coordinate_separated
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
        wz1Lemma23_local_points_coordinate_separated
          g hySeparated
          (hcycleCells firstPath hfirstPath).2.2.1
          (hcycleCells secondPath hsecondPath).2.2.1 hne
      exact
        (div_le_self (Real.sqrt_nonneg rho)
          ((Real.one_le_sqrt).2 (by norm_num))).trans hroot

/--
All three actual normalized vertex classes satisfy the absolute
one-dimensional Katz--Tao bound at the common graph scale.
-/
theorem WZ1Lemma23ActualTripartitePackage.vertex_katzTao
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
    (wz1Lemma23NormalizedFirstVertices rho package.F).IsKatzTao
        (Real.sqrt rho / Real.sqrt 3) 1 4 ∧
      package.G₁.IsKatzTao
        (Real.sqrt rho / Real.sqrt 3) 1 4 ∧
      package.G₂.IsKatzTao
        (Real.sqrt rho / Real.sqrt 3) 1 4 := by
  have hscalePos :
      0 < Real.sqrt rho / Real.sqrt 3 := by
    positivity
  rcases package.vertex_coordinate_separation
      hrho hySeparated with ⟨hF, hG₁, hG₂⟩
  exact
    ⟨coordinateSeparated_isKatzTao hscalePos 0 hF,
      coordinateSeparated_isKatzTao hscalePos 1 hG₁,
      coordinateSeparated_isKatzTao hscalePos 1 hG₂⟩

/--
The normalized graph stored by the y-residue prepared package carries the
same three graph-coordinate separation conclusions.
-/
theorem WZ1Lemma23YResiduePreparedPackage.vertex_coordinate_separation
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
    (∀ first ∈ package.prepared.normalized.F,
        ∀ second ∈ package.prepared.normalized.F,
          first ≠ second →
            Real.sqrt rho / Real.sqrt 3 ≤
              |first 0 - second 0|) ∧
      (∀ first ∈ package.prepared.normalized.G₁,
        ∀ second ∈ package.prepared.normalized.G₁,
          first ≠ second →
            Real.sqrt rho / Real.sqrt 3 ≤
              |first 1 - second 1|) ∧
      ∀ first ∈ package.prepared.normalized.G₂,
        ∀ second ∈ package.prepared.normalized.G₂,
          first ≠ second →
            Real.sqrt rho / Real.sqrt 3 ≤
              |first 1 - second 1| := by
  have h :=
    package.prepared.actual.vertex_coordinate_separation
      globalPackage.rho_pos residuePackage.y_separated
  rw [package.prepared.normalized.F_eq,
    package.prepared.normalized.G₁_eq,
    package.prepared.normalized.G₂_eq,
    package.prepared.normalized_sourceF,
    package.prepared.normalized_sourceG₁,
    package.prepared.normalized_sourceG₂]
  exact h

/--
The normalized graph stored by the y-residue prepared package carries the
same absolute Katz--Tao bounds.
-/
theorem WZ1Lemma23YResiduePreparedPackage.vertex_katzTao
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
    package.prepared.normalized.F.IsKatzTao
        (Real.sqrt rho / Real.sqrt 3) 1 4 ∧
      package.prepared.normalized.G₁.IsKatzTao
        (Real.sqrt rho / Real.sqrt 3) 1 4 ∧
      package.prepared.normalized.G₂.IsKatzTao
        (Real.sqrt rho / Real.sqrt 3) 1 4 := by
  have h :=
    package.prepared.actual.vertex_katzTao
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
