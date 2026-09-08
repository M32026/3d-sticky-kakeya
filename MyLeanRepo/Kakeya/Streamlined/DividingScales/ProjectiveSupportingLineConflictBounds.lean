import MyLeanRepo.Kakeya.Streamlined.DividingScales.ProjectiveSupportingLineCellGeometry
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.UniversalNonDistinctGeometry.Proof

/-!
# Supporting-line coordinate bounds for non-distinct tubes

Non-essential distinctness controls exactly the quotient geometry encoded by
`projectiveSupportingLineCoordinates`:

* projective direction error is `O(rho)`; and
* transverse supporting-line position error is `O(rho)`.

For radius-`rho` tubes whose first midpoint lies in the unit ball, every one
of the twelve real supporting-line coordinates differs by at most
`3000 * rho`.  No axial midpoint estimate is used or asserted.
-/

noncomputable section

namespace Kakeya.Streamlined

open GeometricLemmas

private lemma abs_coord_le_norm
    (point : Point3) (coordinate : Fin 3) :
    |point coordinate| ≤ ‖point‖ := by
  have hsquare :
      (point coordinate) ^ 2 ≤ ‖point‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum
      (fun index _ => sq_nonneg (point index))
      (Finset.mem_univ coordinate)
  nlinarith [sq_abs (point coordinate),
    abs_nonneg (point coordinate), norm_nonneg point]

private lemma supportingLineAnchor_dist_le_of_transverse_of_direction
    {delta : ℝ}
    {first second : Kakeya.DeltaTube delta}
    {transverseBound directionBound : ℝ}
    (hfirstMidpoint : ‖tubeMidpoint first‖ ≤ 1)
    (htransverse :
      ‖(tubeMidpoint first - tubeMidpoint second) -
          inner ℝ (tubeMidpoint first - tubeMidpoint second)
            second.direction • second.direction‖ ≤
        transverseBound)
    (hdirection :
      ‖first.direction - second.direction‖ ≤
        directionBound) :
    ‖tubeSupportingLineAnchor first -
        tubeSupportingLineAnchor second‖ ≤
      transverseBound + 2 * directionBound := by
  let midpointDifference :=
    tubeMidpoint first - tubeMidpoint second
  let transverse :=
    midpointDifference -
      inner ℝ midpointDifference second.direction •
        second.direction
  let firstProjection :=
    inner ℝ (tubeMidpoint first) first.direction •
      first.direction
  let secondProjection :=
    inner ℝ (tubeMidpoint first) second.direction •
      second.direction
  have hanchorIdentity :
      tubeSupportingLineAnchor first -
          tubeSupportingLineAnchor second =
        transverse + (secondProjection - firstProjection) := by
    dsimp only [tubeSupportingLineAnchor, projectiveLineAnchor,
      transverse, midpointDifference, firstProjection, secondProjection]
    rw [inner_sub_left]
    module
  have hprojectionIdentity :
      secondProjection - firstProjection =
        inner ℝ (tubeMidpoint first) second.direction •
            (second.direction - first.direction) +
          inner ℝ (tubeMidpoint first)
              (second.direction - first.direction) •
            first.direction := by
    dsimp only [secondProjection, firstProjection]
    rw [inner_sub_right]
    module
  have hfirstDirection : ‖first.direction‖ = 1 :=
    first.direction_unit
  have hsecondDirection : ‖second.direction‖ = 1 :=
    second.direction_unit
  have hdirectionBound : 0 ≤ directionBound :=
    (norm_nonneg (first.direction - second.direction)).trans hdirection
  have hinnerSecond :
      |inner ℝ (tubeMidpoint first) second.direction| ≤ 1 := by
    calc
      |inner ℝ (tubeMidpoint first) second.direction|
          ≤ ‖tubeMidpoint first‖ * ‖second.direction‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖tubeMidpoint first‖ := by
        rw [hsecondDirection, mul_one]
      _ ≤ 1 := hfirstMidpoint
  have hinnerDifference :
      |inner ℝ (tubeMidpoint first)
          (second.direction - first.direction)| ≤
        directionBound := by
    calc
      |inner ℝ (tubeMidpoint first)
          (second.direction - first.direction)|
          ≤ ‖tubeMidpoint first‖ *
              ‖second.direction - first.direction‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ 1 * directionBound := by
        apply mul_le_mul hfirstMidpoint
        · simpa [norm_sub_rev] using hdirection
        · exact norm_nonneg _
        · linarith [norm_nonneg (tubeMidpoint first)]
      _ = directionBound := one_mul _
  have hprojection :
      ‖secondProjection - firstProjection‖ ≤
        2 * directionBound := by
    rw [hprojectionIdentity]
    calc
      ‖inner ℝ (tubeMidpoint first) second.direction •
            (second.direction - first.direction) +
          inner ℝ (tubeMidpoint first)
              (second.direction - first.direction) •
            first.direction‖
          ≤
        ‖inner ℝ (tubeMidpoint first) second.direction •
            (second.direction - first.direction)‖ +
          ‖inner ℝ (tubeMidpoint first)
              (second.direction - first.direction) •
            first.direction‖ :=
        norm_add_le _ _
      _ =
        |inner ℝ (tubeMidpoint first) second.direction| *
            ‖second.direction - first.direction‖ +
          |inner ℝ (tubeMidpoint first)
              (second.direction - first.direction)| *
            ‖first.direction‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * directionBound + directionBound * 1 := by
        apply add_le_add
        · exact mul_le_mul hinnerSecond
            (by simpa [norm_sub_rev] using hdirection)
            (norm_nonneg _) (by norm_num)
        · exact mul_le_mul hinnerDifference
            hfirstDirection.le (norm_nonneg _) hdirectionBound
      _ = 2 * directionBound := by ring
  rw [hanchorIdentity]
  calc
    ‖transverse + (secondProjection - firstProjection)‖
        ≤ ‖transverse‖ + ‖secondProjection - firstProjection‖ :=
      norm_add_le _ _
    _ ≤ transverseBound + 2 * directionBound :=
      add_le_add htransverse hprojection

private lemma rankOneEntry_abs_sub_le_of_direction_close
    {first second : Point3}
    (hfirst : ‖first‖ = 1)
    (hsecond : ‖second‖ = 1)
    {bound : ℝ}
    (hclose : ‖first - second‖ ≤ bound)
    (i j : Fin 3) :
    |first i * first j - second i * second j| ≤
      2 * bound := by
  have hfirstCoordinate : |first i| ≤ 1 := by
    simpa [hfirst] using abs_coord_le_norm first i
  have hsecondCoordinate : |second j| ≤ 1 := by
    simpa [hsecond] using abs_coord_le_norm second j
  have hdifferenceI : |first i - second i| ≤ bound :=
    (abs_coord_le_norm (first - second) i).trans hclose
  have hdifferenceJ : |first j - second j| ≤ bound :=
    (abs_coord_le_norm (first - second) j).trans hclose
  have hidentity :
      first i * first j - second i * second j =
        first i * (first j - second j) +
          (first i - second i) * second j := by
    ring
  rw [hidentity]
  calc
    |first i * (first j - second j) +
        (first i - second i) * second j|
        ≤
      |first i * (first j - second j)| +
        |(first i - second i) * second j| :=
      abs_add_le _ _
    _ =
      |first i| * |first j - second j| +
        |first i - second i| * |second j| := by
      simp only [abs_mul]
    _ ≤ 1 * bound + bound * 1 := by
      exact add_le_add
        (mul_le_mul hfirstCoordinate hdifferenceJ
          (abs_nonneg _) (by linarith [abs_nonneg (first i)]))
        (mul_le_mul hdifferenceI hsecondCoordinate
          (abs_nonneg _) (by linarith [abs_nonneg (first i - second i)]))
    _ = 2 * bound := by ring

private lemma rankOneEntry_abs_sub_le_of_direction_close_or_reverse
    {first second : Point3}
    (hfirst : ‖first‖ = 1)
    (hsecond : ‖second‖ = 1)
    {bound : ℝ}
    (hclose :
      ‖first - second‖ ≤ bound ∨
        ‖first + second‖ ≤ bound)
    (i j : Fin 3) :
    |first i * first j - second i * second j| ≤
      2 * bound := by
  rcases hclose with hsame | hopposite
  · exact rankOneEntry_abs_sub_le_of_direction_close
      hfirst hsecond hsame i j
  · have hnegUnit : ‖-second‖ = 1 := by simp [hsecond]
    have hnegClose : ‖first - (-second)‖ ≤ bound := by
      simpa [sub_neg_eq_add] using hopposite
    have hbound :=
      rankOneEntry_abs_sub_le_of_direction_close
        hfirst hnegUnit hnegClose i j
    have hentry :
        (-second) i * (-second) j =
          second i * second j := by
      simp
    rw [hentry] at hbound
    exact hbound

/--
Non-essentially-distinct unit-ball tubes have close supporting-line anchors.
-/
theorem supportingLineAnchor_dist_le_of_not_essentiallyDistinct
    {rho : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    {first second : Kakeya.DeltaTube rho}
    (hfirstMidpoint : ‖tubeMidpoint first‖ ≤ 1)
    (hconflict :
      ¬ first.EssentiallyDistinct second) :
    ‖tubeSupportingLineAnchor first -
        tubeSupportingLineAnchor second‖ ≤
      3000 * rho := by
  have hgeometry :=
    universal_non_distinct_geometry
      hrho hrhoOne first second hconflict
  rcases hgeometry.2.1 with hsame | hopposite
  · have hbound :=
      supportingLineAnchor_dist_le_of_transverse_of_direction
        hfirstMidpoint hgeometry.1 hsame
    nlinarith
  · let reversed := reverseTube second
    have htransverse :
        ‖(tubeMidpoint first - tubeMidpoint reversed) -
            inner ℝ (tubeMidpoint first - tubeMidpoint reversed)
              reversed.direction • reversed.direction‖ ≤
          1000 * rho := by
      dsimp only [reversed]
      rw [reverseTube_midpoint]
      have hprojection :
          inner ℝ
              (tubeMidpoint first - tubeMidpoint second)
              (-second.direction) • (-second.direction) =
            inner ℝ
              (tubeMidpoint first - tubeMidpoint second)
              second.direction • second.direction := by
        rw [inner_neg_right]
        module
      change
        ‖(tubeMidpoint first - tubeMidpoint second) -
            inner ℝ (tubeMidpoint first - tubeMidpoint second)
              (-second.direction) • (-second.direction)‖ ≤
          1000 * rho
      rw [hprojection]
      exact hgeometry.1
    have hdirection :
        ‖first.direction - reversed.direction‖ ≤
          1000 * rho := by
      dsimp only [reversed]
      simpa [reverseTube, sub_neg_eq_add] using hopposite
    have hbound :=
      supportingLineAnchor_dist_le_of_transverse_of_direction
        hfirstMidpoint htransverse hdirection
    simpa only [reversed, tubeSupportingLineAnchor_reverseTube] using
      (hbound.trans (by nlinarith))

/--
Every real supporting-line coordinate of conflicting radius-`rho` tubes is
within `3000 * rho`.
-/
theorem projectiveSupportingLineCoordinates_abs_sub_le_of_not_essentiallyDistinct
    {rho : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    {first second : Kakeya.DeltaTube rho}
    (hfirstMidpoint : ‖tubeMidpoint first‖ ≤ 1)
    (hconflict :
      ¬ first.EssentiallyDistinct second)
    (coordinate : Fin 12) :
    |projectiveSupportingLineCoordinates first coordinate -
        projectiveSupportingLineCoordinates second coordinate| ≤
      3000 * rho := by
  have hgeometry :=
    universal_non_distinct_geometry
      hrho hrhoOne first second hconflict
  cases hcoordinate :
      projectiveSupportingLineCoordinateEquiv.symm coordinate with
  | inl anchorCoordinate =>
      have hanchor :=
        supportingLineAnchor_dist_le_of_not_essentiallyDistinct
          hrho hrhoOne hfirstMidpoint hconflict
      have hcoordinateBound :=
        (abs_coord_le_norm
          (tubeSupportingLineAnchor first -
            tubeSupportingLineAnchor second)
          anchorCoordinate).trans hanchor
      simpa [projectiveSupportingLineCoordinates,
        hcoordinate] using hcoordinateBound
  | inr directionCoordinates =>
      have hrankOne :=
        rankOneEntry_abs_sub_le_of_direction_close_or_reverse
          first.direction_unit second.direction_unit
          hgeometry.2.1 directionCoordinates.1
          directionCoordinates.2
      have htwo : 2 * (1000 * rho) ≤ 3000 * rho := by
        nlinarith
      exact (by
        simpa [projectiveSupportingLineCoordinates,
          hcoordinate] using hrankOne.trans htwo)

/--
The real-coordinate conflict bound converts to a fixed-modulus integer-label
bound whenever the grid density at this level is comparable with `rho⁻¹`.
-/
theorem projectiveSupportingLineGridLabel_abs_sub_lt_of_not_essentiallyDistinct
    {rho : ℝ}
    (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    {base level modulus : ℕ}
    {first second : Kakeya.DeltaTube rho}
    (hfirstMidpoint : ‖tubeMidpoint first‖ ≤ 1)
    (hconflict :
      ¬ first.EssentiallyDistinct second)
    (hmodulus :
      (3000 * rho) * (base ^ level : ℝ) + 1 <
        (modulus : ℝ))
    (coordinate : Fin 12) :
    |integerGridLabel base level
          (projectiveSupportingLineCoordinates first) coordinate -
        integerGridLabel base level
          (projectiveSupportingLineCoordinates second) coordinate| <
      (modulus : ℤ) := by
  apply integerGridLabel_abs_sub_lt_of_coordinate_abs_sub_le
  · intro current
    exact
      projectiveSupportingLineCoordinates_abs_sub_le_of_not_essentiallyDistinct
        hrho hrhoOne hfirstMidpoint hconflict current
  · exact hmodulus

end Kakeya.Streamlined
