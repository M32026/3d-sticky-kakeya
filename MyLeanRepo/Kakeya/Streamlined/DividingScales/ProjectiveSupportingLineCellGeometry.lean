import MyLeanRepo.Kakeya.Streamlined.DividingScales.ProjectiveDirectionTensorBounds
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ProjectiveMidpointTubeCellGeometry
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ProjectiveSupportingLineCoordinates
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.MidpointBound

/-!
# Quantitative geometry inside a supporting-line grid cell

Equal supporting-line floor labels give:

* line-anchor distance less than `3 * mesh`;
* projective direction distance at most `18 * mesh`;
* transverse midpoint displacement at most `21 * mesh` for unit-ball tubes.

Consequently, when `mesh ≤ rho`, one tube is contained in the `31`-dilation
of the radius-`rho` tube carried by the other supporting line.  This is the
paper-facing coaxial-line geometry; no axial midpoint control is asserted.
-/

noncomputable section

namespace Kakeya.Streamlined

open GeometricLemmas

private lemma point3_norm_sq (x : Point3) :
    ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

private lemma point3_norm_lt_three_mul_of_coord_abs_lt
    {x : Point3} {mesh : ℝ}
    (hmesh : 0 < mesh)
    (hcoord : ∀ i : Fin 3, |x i| < mesh) :
    ‖x‖ < 3 * mesh := by
  have h0 : (x 0) ^ 2 < mesh ^ 2 := by
    simpa only [sq_abs] using
      (sq_lt_sq₀ (abs_nonneg (x 0)) hmesh.le).2 (hcoord 0)
  have h1 : (x 1) ^ 2 < mesh ^ 2 := by
    simpa only [sq_abs] using
      (sq_lt_sq₀ (abs_nonneg (x 1)) hmesh.le).2 (hcoord 1)
  have h2 : (x 2) ^ 2 < mesh ^ 2 := by
    simpa only [sq_abs] using
      (sq_lt_sq₀ (abs_nonneg (x 2)) hmesh.le).2 (hcoord 2)
  have hnormSq := point3_norm_sq x
  have hnorm : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith

@[simp] theorem tubeSupportingLineAnchor_alignProjectiveTube
    {delta : ℝ}
    (reference candidate : Kakeya.DeltaTube delta) :
    tubeSupportingLineAnchor
        (alignProjectiveTube reference candidate) =
      tubeSupportingLineAnchor candidate := by
  by_cases hinner :
      0 ≤ inner ℝ reference.direction candidate.direction
  · simp [alignProjectiveTube, hinner]
  · simp [alignProjectiveTube, hinner]

@[simp] theorem dilatedTubeCarrier_alignProjectiveTube
    {delta A : ℝ}
    (reference candidate : Kakeya.DeltaTube delta) :
    dilatedTubeCarrier A
        (alignProjectiveTube reference candidate) =
      dilatedTubeCarrier A candidate := by
  by_cases hinner :
      0 ≤ inner ℝ reference.direction candidate.direction
  · simp [alignProjectiveTube, hinner]
  · simp [alignProjectiveTube, hinner]

@[simp] theorem projectiveSupportingLineCoordinates_withRadius
    {delta rho : ℝ}
    (tube : Kakeya.DeltaTube delta) :
    projectiveSupportingLineCoordinates (withRadius rho tube) =
      projectiveSupportingLineCoordinates tube := by
  rfl

/-- Same-cell supporting lines have close closest-point anchors. -/
theorem supportingLineAnchor_dist_lt_of_gridLabel_eq
    {delta : ℝ}
    {base level : ℕ}
    (hbase : 1 ≤ base)
    {first second : Kakeya.DeltaTube delta}
    (hlabel :
      integerGridLabel base level
          (projectiveSupportingLineCoordinates first) =
        integerGridLabel base level
          (projectiveSupportingLineCoordinates second)) :
    ‖tubeSupportingLineAnchor first -
        tubeSupportingLineAnchor second‖ <
      3 * (base ^ level : ℝ)⁻¹ := by
  have hbasePos : 0 < (base : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hbase)
  have hmesh : 0 < (base ^ level : ℝ)⁻¹ := by
    exact inv_pos.mpr (pow_pos hbasePos level)
  apply point3_norm_lt_three_mul_of_coord_abs_lt hmesh
  intro coordinate
  have hcoordinate :=
    abs_sub_lt_inv_pow_of_integerGridLabel_eq
      hbase hlabel
        (projectiveSupportingLineCoordinateEquiv
          (Sum.inl coordinate))
  change
    |tubeSupportingLineAnchor first coordinate -
      tubeSupportingLineAnchor second coordinate| <
      (base ^ level : ℝ)⁻¹
  simpa only [
    projectiveSupportingLineCoordinates_anchor] using hcoordinate

/-- Same-cell supporting lines have linearly close projective directions. -/
theorem alignedDirection_dist_le_of_supportingLineGridLabel_eq
    {delta : ℝ}
    {base level : ℕ}
    (hbase : 1 ≤ base)
    {first second : Kakeya.DeltaTube delta}
    (hlabel :
      integerGridLabel base level
          (projectiveSupportingLineCoordinates first) =
        integerGridLabel base level
          (projectiveSupportingLineCoordinates second)) :
    ‖first.direction -
        (alignProjectiveTube first second).direction‖ ≤
      18 * (base ^ level : ℝ)⁻¹ := by
  rw [alignProjectiveTube_direction]
  apply
    alignProjectiveDirection_dist_le_of_rankOne_entrywise_le
      first.direction_unit second.direction_unit
      (inv_nonneg.mpr (by positivity))
  intro i j
  have hcoordinate :=
    abs_sub_lt_inv_pow_of_integerGridLabel_eq
      hbase hlabel
        (projectiveSupportingLineCoordinateEquiv
          (Sum.inr (i, j)))
  simpa only [
    projectiveSupportingLineCoordinates_directionProduct] using
      hcoordinate.le

private lemma midpoint_eq_anchor_add_axial
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    tubeMidpoint tube =
      tubeSupportingLineAnchor tube +
        inner ℝ (tubeMidpoint tube) tube.direction •
          tube.direction := by
  simp only [tubeSupportingLineAnchor, projectiveLineAnchor]
  module

/--
For tubes in one supporting-line cell, a bound on the first stored midpoint
controls the transverse midpoint displacement at the line-mesh scale.  The
unit-ball constant `21` is the specialization `3 + 18 * 1`.
-/
theorem supportingLine_sameCell_transverseMidpoint_le_of_bound
    {delta : ℝ}
    {base level : ℕ}
    (hbase : 1 ≤ base)
    {R : ℝ} (hR : 0 ≤ R)
    {first second : Kakeya.DeltaTube delta}
    (hfirstMidpoint : ‖tubeMidpoint first‖ ≤ R)
    (hlabel :
      integerGridLabel base level
          (projectiveSupportingLineCoordinates first) =
        integerGridLabel base level
          (projectiveSupportingLineCoordinates second)) :
    ‖(tubeMidpoint first -
          tubeMidpoint (alignProjectiveTube first second)) -
        inner ℝ
          (tubeMidpoint first -
            tubeMidpoint (alignProjectiveTube first second))
          (alignProjectiveTube first second).direction •
            (alignProjectiveTube first second).direction‖ ≤
      (3 + 18 * R) * (base ^ level : ℝ)⁻¹ := by
  let aligned := alignProjectiveTube first second
  let firstAnchor := tubeSupportingLineAnchor first
  let secondAnchor := tubeSupportingLineAnchor aligned
  let firstAxial := inner ℝ (tubeMidpoint first) first.direction
  let secondAxial := inner ℝ (tubeMidpoint aligned) aligned.direction
  let transverse := fun vector : Point3 =>
    vector - inner ℝ vector aligned.direction • aligned.direction
  have halignedUnit : ‖aligned.direction‖ = 1 :=
    aligned.direction_unit
  have htransverseLinear :
      transverse
          (tubeMidpoint first - tubeMidpoint aligned) =
        transverse (firstAnchor - secondAnchor) +
          firstAxial • transverse first.direction := by
    have hfirst :=
      midpoint_eq_anchor_add_axial first
    have hsecond :=
      midpoint_eq_anchor_add_axial aligned
    have hsecondPerp :
        inner ℝ secondAnchor aligned.direction = 0 :=
      inner_tubeSupportingLineAnchor_direction aligned
    have hself :
        inner ℝ aligned.direction aligned.direction = 1 := by
      rw [real_inner_self_eq_norm_sq, halignedUnit]
      norm_num
    dsimp only [transverse]
    rw [hfirst, hsecond]
    dsimp only [firstAnchor, secondAnchor, firstAxial, secondAxial]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left,
      hsecondPerp, hself, mul_one]
    module
  have hanchor :
      ‖firstAnchor - secondAnchor‖ <
        3 * (base ^ level : ℝ)⁻¹ := by
    dsimp only [firstAnchor, secondAnchor, aligned]
    simpa only [tubeSupportingLineAnchor_alignProjectiveTube] using
      supportingLineAnchor_dist_lt_of_gridLabel_eq
        hbase hlabel
  have hdirection :
      ‖first.direction - aligned.direction‖ ≤
        18 * (base ^ level : ℝ)⁻¹ := by
    dsimp only [aligned]
    exact
      alignedDirection_dist_le_of_supportingLineGridLabel_eq
        hbase hlabel
  have hfirstAxial :
      |firstAxial| ≤ R := by
    dsimp only [firstAxial]
    calc
      |inner ℝ (tubeMidpoint first) first.direction|
          ≤ ‖tubeMidpoint first‖ * ‖first.direction‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖tubeMidpoint first‖ := by
        rw [first.direction_unit, mul_one]
      _ ≤ R := hfirstMidpoint
  have htransverseAnchor :
      ‖transverse (firstAnchor - secondAnchor)‖ ≤
        ‖firstAnchor - secondAnchor‖ :=
    norm_transverse_le halignedUnit _
  have htransverseDirection :
      ‖transverse first.direction‖ ≤
        ‖first.direction - aligned.direction‖ := by
    have heq :
        transverse first.direction =
          transverse (first.direction - aligned.direction) := by
      dsimp only [transverse]
      have hself :
          inner ℝ aligned.direction aligned.direction = 1 := by
        rw [real_inner_self_eq_norm_sq, halignedUnit]
        norm_num
      simp only [inner_sub_left, hself]
      module
    rw [heq]
    exact norm_transverse_le halignedUnit _
  change
    ‖transverse (tubeMidpoint first - tubeMidpoint aligned)‖ ≤
      (3 + 18 * R) * (base ^ level : ℝ)⁻¹
  rw [htransverseLinear]
  calc
    ‖transverse (firstAnchor - secondAnchor) +
        firstAxial • transverse first.direction‖
        ≤ ‖transverse (firstAnchor - secondAnchor)‖ +
            ‖firstAxial • transverse first.direction‖ :=
      norm_add_le _ _
    _ ≤ ‖firstAnchor - secondAnchor‖ +
          |firstAxial| * ‖transverse first.direction‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add htransverseAnchor le_rfl
    _ ≤ ‖firstAnchor - secondAnchor‖ +
          R * ‖first.direction - aligned.direction‖ := by
      gcongr
    _ ≤ (3 + 18 * R) * (base ^ level : ℝ)⁻¹ := by
      have hmesh : 0 ≤ (base ^ level : ℝ)⁻¹ := by positivity
      calc
        ‖firstAnchor - secondAnchor‖ +
              R * ‖first.direction - aligned.direction‖
            ≤ 3 * (base ^ level : ℝ)⁻¹ +
                R * (18 * (base ^ level : ℝ)⁻¹) := by
              exact add_le_add hanchor.le
                (mul_le_mul_of_nonneg_left hdirection hR)
        _ = (3 + 18 * R) * (base ^ level : ℝ)⁻¹ := by ring

/--
For unit-ball tubes in one supporting-line cell, transverse midpoint
displacement is controlled at the line-mesh scale, with no axial bound.
-/
theorem supportingLine_sameCell_transverseMidpoint_le
    {delta : ℝ}
    {base level : ℕ}
    (hbase : 1 ≤ base)
    {first second : Kakeya.DeltaTube delta}
    (hfirstMidpoint : ‖tubeMidpoint first‖ ≤ 1)
    (hlabel :
      integerGridLabel base level
          (projectiveSupportingLineCoordinates first) =
        integerGridLabel base level
          (projectiveSupportingLineCoordinates second)) :
    ‖(tubeMidpoint first -
          tubeMidpoint (alignProjectiveTube first second)) -
        inner ℝ
          (tubeMidpoint first -
            tubeMidpoint (alignProjectiveTube first second))
          (alignProjectiveTube first second).direction •
            (alignProjectiveTube first second).direction‖ ≤
      21 * (base ^ level : ℝ)⁻¹ := by
  simpa only [show (3 : ℝ) + 18 * 1 = 21 by norm_num] using
    supportingLine_sameCell_transverseMidpoint_le_of_bound
      hbase (R := (1 : ℝ)) (by norm_num) hfirstMidpoint hlabel

/--
The transverse midpoint estimate is orientation-free, so it can be stated
directly relative to the original second direction.
-/
theorem supportingLine_sameCell_transverseMidpoint_le_unoriented
    {delta : ℝ}
    {base level : ℕ}
    (hbase : 1 ≤ base)
    {first second : Kakeya.DeltaTube delta}
    (hfirstMidpoint : ‖tubeMidpoint first‖ ≤ 1)
    (hlabel :
      integerGridLabel base level
          (projectiveSupportingLineCoordinates first) =
        integerGridLabel base level
          (projectiveSupportingLineCoordinates second)) :
    ‖(tubeMidpoint first - tubeMidpoint second) -
        inner ℝ (tubeMidpoint first - tubeMidpoint second)
          second.direction • second.direction‖ ≤
      21 * (base ^ level : ℝ)⁻¹ := by
  have haligned :=
    supportingLine_sameCell_transverseMidpoint_le
      hbase hfirstMidpoint hlabel
  by_cases hinner :
      0 ≤ inner ℝ first.direction second.direction
  · simpa [alignProjectiveTube, hinner] using haligned
  · have hprojection :
        inner ℝ (tubeMidpoint first - tubeMidpoint second)
            (-second.direction) • (-second.direction) =
          inner ℝ (tubeMidpoint first - tubeMidpoint second)
            second.direction • second.direction := by
      rw [inner_neg_right]
      module
    rw [alignProjectiveTube, if_neg hinner] at haligned
    rw [reverseTube_midpoint] at haligned
    change
      ‖(tubeMidpoint first - tubeMidpoint second) -
          inner ℝ (tubeMidpoint first - tubeMidpoint second)
            (-second.direction) • (-second.direction)‖ ≤
        21 * (base ^ level : ℝ)⁻¹ at haligned
    rw [hprojection] at haligned
    exact haligned

/-- Same-cell direction tensors give the orientation-free direction field. -/
theorem supportingLine_sameCell_direction_close_or_reverse
    {delta : ℝ}
    {base level : ℕ}
    (hbase : 1 ≤ base)
    {first second : Kakeya.DeltaTube delta}
    (hlabel :
      integerGridLabel base level
          (projectiveSupportingLineCoordinates first) =
        integerGridLabel base level
          (projectiveSupportingLineCoordinates second)) :
    ‖first.direction - second.direction‖ ≤
        18 * (base ^ level : ℝ)⁻¹ ∨
      ‖first.direction + second.direction‖ ≤
        18 * (base ^ level : ℝ)⁻¹ := by
  apply direction_close_or_close_neg_of_rankOne_entrywise_le
    first.direction_unit second.direction_unit
    (inv_nonneg.mpr (by positivity))
  intro i j
  have hcoordinate :=
    abs_sub_lt_inv_pow_of_integerGridLabel_eq
      hbase hlabel
        (projectiveSupportingLineCoordinateEquiv
          (Sum.inr (i, j)))
  simpa only [
    projectiveSupportingLineCoordinates_directionProduct] using
      hcoordinate.le

/--
One supporting-line cell gives fixed-dilation containment at every coarser
radius absorbing the mesh.
-/
theorem carrier_subset_dilated_of_supportingLineGridLabel_eq
    {delta rho : ℝ}
    (hdelta : 0 ≤ delta)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hdeltaRho : delta ≤ rho)
    {base level : ℕ}
    (hbase : 1 ≤ base)
    (hmeshRho : (base ^ level : ℝ)⁻¹ ≤ rho)
    {first second : Kakeya.DeltaTube delta}
    (hfirstBall : first.IsInUnitBall)
    (hsecondBall : second.IsInUnitBall)
    (hlabel :
      integerGridLabel base level
          (projectiveSupportingLineCoordinates first) =
        integerGridLabel base level
          (projectiveSupportingLineCoordinates second)) :
    first.carrier ⊆
      dilatedTubeCarrier 31 (withRadius rho second) := by
  let firstRho := withRadius rho first
  let secondRho := withRadius rho second
  let aligned := alignProjectiveTube firstRho secondRho
  have hfirstMidpoint :
      ‖tubeMidpoint firstRho‖ ≤ 1 := by
    simpa only [firstRho, withRadius_midpoint] using
      tubeMidpoint_norm_le_one hfirstBall
  have hsecondMidpoint :
      ‖tubeMidpoint aligned‖ ≤ 1 := by
    dsimp only [aligned, secondRho]
    simpa only [alignProjectiveTube_midpoint, withRadius_midpoint] using
      tubeMidpoint_norm_le_one hsecondBall
  have hlabelRho :
      integerGridLabel base level
          (projectiveSupportingLineCoordinates firstRho) =
        integerGridLabel base level
          (projectiveSupportingLineCoordinates secondRho) := by
    simpa only [firstRho, secondRho,
      projectiveSupportingLineCoordinates_withRadius] using hlabel
  have htransverse :
      ‖(tubeMidpoint firstRho - tubeMidpoint aligned) -
          inner ℝ (tubeMidpoint firstRho - tubeMidpoint aligned)
            aligned.direction • aligned.direction‖ ≤
        21 * (base ^ level : ℝ)⁻¹ := by
    exact supportingLine_sameCell_transverseMidpoint_le
      hbase
      (first := firstRho) (second := secondRho)
      hfirstMidpoint
      hlabelRho
  have hdirection :
      ‖firstRho.direction -
          inner ℝ firstRho.direction aligned.direction •
            aligned.direction‖ ≤
        18 * (base ^ level : ℝ)⁻¹ := by
    have hclose :
        ‖firstRho.direction - aligned.direction‖ ≤
          18 * (base ^ level : ℝ)⁻¹ :=
      alignedDirection_dist_le_of_supportingLineGridLabel_eq
        hbase hlabelRho
    have hself :
        inner ℝ aligned.direction aligned.direction = 1 := by
      rw [real_inner_self_eq_norm_sq, aligned.direction_unit]
      norm_num
    have heq :
        firstRho.direction -
            inner ℝ firstRho.direction aligned.direction •
              aligned.direction =
          (firstRho.direction - aligned.direction) -
            inner ℝ
              (firstRho.direction - aligned.direction)
              aligned.direction • aligned.direction := by
      simp only [inner_sub_left, hself]
      module
    rw [heq]
    exact
      (norm_transverse_le aligned.direction_unit
        (firstRho.direction - aligned.direction)).trans hclose
  have hcriterion :
      ‖(tubeMidpoint firstRho - tubeMidpoint aligned) -
          inner ℝ (tubeMidpoint firstRho - tubeMidpoint aligned)
            aligned.direction • aligned.direction‖ +
        (1 / 2 : ℝ) *
          ‖firstRho.direction -
            inner ℝ firstRho.direction aligned.direction •
              aligned.direction‖ ≤
        (31 - 1) * rho := by
    nlinarith
  have hcontainedRho :
      firstRho.carrier ⊆
        dilatedTubeCarrier 31 aligned :=
    tube_contained_in_dilated_transverse_general
      hrho hrhoOne 31 1 (by norm_num) (by norm_num)
      firstRho aligned hfirstMidpoint hsecondMidpoint hcriterion
  have hfirstSubset :
      first.carrier ⊆ firstRho.carrier :=
    carrier_subset_withRadius hdeltaRho first
  exact hfirstSubset.trans <| by
    simpa only [aligned, firstRho, secondRho,
      dilatedTubeCarrier_alignProjectiveTube] using hcontainedRho

end Kakeya.Streamlined
