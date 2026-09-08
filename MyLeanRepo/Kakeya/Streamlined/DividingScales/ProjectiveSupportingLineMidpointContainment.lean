import MyLeanRepo.Kakeya.Streamlined.DividingScales.ProjectiveSupportingLineCellGeometry

/-!
# Supporting-line cell containment from bounded midpoints

The occupied supporting-line representatives keep the midpoint of an actual
unit-ball tube, but after changing the radius their full carriers need not
remain in the unit ball.  The same-cell containment argument only uses the
two midpoint bounds.  This module records that exact geometric hypothesis.
-/

noncomputable section

namespace Kakeya.Streamlined

open GeometricLemmas

/--
Two tubes in one supporting-line cell are contained after enlarging the
second radius, provided both stored midpoints remain in a fixed ball `B_R`.
The dilation `13 + 18 * R` is uniform in the scales and the family.
-/
theorem carrier_subset_dilated_of_supportingLineGridLabel_eq_of_midpoint_bound
    {sigma tau rho : ℝ}
    (hsigma : 0 ≤ sigma)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hsigmaRho : sigma ≤ rho)
    {base level : ℕ}
    (hbase : 1 ≤ base)
    (hmeshRho : (base ^ level : ℝ)⁻¹ ≤ rho)
    {R : ℝ} (hR : 0 ≤ R)
    {first : Kakeya.DeltaTube sigma}
    {second : Kakeya.DeltaTube tau}
    (hfirstMidpoint : ‖tubeMidpoint first‖ ≤ R)
    (hsecondMidpoint : ‖tubeMidpoint second‖ ≤ R)
    (hlabel :
      integerGridLabel base level
          (projectiveSupportingLineCoordinates first) =
        integerGridLabel base level
          (projectiveSupportingLineCoordinates second)) :
    first.carrier ⊆
      dilatedTubeCarrier (13 + 18 * R) (withRadius rho second) := by
  let firstRho := withRadius rho first
  let secondRho := withRadius rho second
  let aligned := alignProjectiveTube firstRho secondRho
  have hfirstMidpointRho :
      ‖tubeMidpoint firstRho‖ ≤ R := by
    simpa only [firstRho, withRadius_midpoint] using hfirstMidpoint
  have hsecondMidpointRho :
      ‖tubeMidpoint aligned‖ ≤ R := by
    dsimp only [aligned, secondRho]
    simpa only [alignProjectiveTube_midpoint, withRadius_midpoint] using
      hsecondMidpoint
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
        (3 + 18 * R) * (base ^ level : ℝ)⁻¹ := by
    exact supportingLine_sameCell_transverseMidpoint_le_of_bound
      hbase hR
      (first := firstRho) (second := secondRho)
      hfirstMidpointRho hlabelRho
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
        ((13 + 18 * R) - 1) * rho := by
    have hcoefficient : 0 ≤ 3 + 18 * R := by positivity
    have htransverseRho :
        (3 + 18 * R) * (base ^ level : ℝ)⁻¹ ≤
          (3 + 18 * R) * rho :=
      mul_le_mul_of_nonneg_left hmeshRho hcoefficient
    have hdirectionRho :
        18 * (base ^ level : ℝ)⁻¹ ≤ 18 * rho :=
      mul_le_mul_of_nonneg_left hmeshRho (by norm_num)
    nlinarith
  have hcontainedRho :
      firstRho.carrier ⊆
        dilatedTubeCarrier (13 + 18 * R) aligned :=
    tube_contained_in_dilated_transverse_general
      hrho hrhoOne (13 + 18 * R) R (by nlinarith) hR
      firstRho aligned hfirstMidpointRho hsecondMidpointRho hcriterion
  have hfirstSubset :
      first.carrier ⊆ firstRho.carrier :=
    carrier_subset_withRadius hsigmaRho first
  exact hfirstSubset.trans <| by
    simpa only [aligned, firstRho, secondRho,
      dilatedTubeCarrier_alignProjectiveTube] using hcontainedRho

/--
Two equal-radius tubes in one supporting-line cell are contained after
enlarging the second radius, provided both stored midpoints remain in `B₁`.
-/
theorem carrier_subset_dilated_of_supportingLineGridLabel_eq_of_midpoint
    {sigma tau rho : ℝ}
    (hsigma : 0 ≤ sigma)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (hsigmaRho : sigma ≤ rho)
    {base level : ℕ}
    (hbase : 1 ≤ base)
    (hmeshRho : (base ^ level : ℝ)⁻¹ ≤ rho)
    {first : Kakeya.DeltaTube sigma}
    {second : Kakeya.DeltaTube tau}
    (hfirstMidpoint : ‖tubeMidpoint first‖ ≤ 1)
    (hsecondMidpoint : ‖tubeMidpoint second‖ ≤ 1)
    (hlabel :
      integerGridLabel base level
          (projectiveSupportingLineCoordinates first) =
        integerGridLabel base level
          (projectiveSupportingLineCoordinates second)) :
    first.carrier ⊆
      dilatedTubeCarrier 31 (withRadius rho second) := by
  simpa only [show (13 : ℝ) + 18 * 1 = 31 by norm_num] using
    carrier_subset_dilated_of_supportingLineGridLabel_eq_of_midpoint_bound
      hsigma hrho hrhoOne hsigmaRho hbase hmeshRho
      (R := (1 : ℝ)) (by norm_num) hfirstMidpoint hsecondMidpoint hlabel

/--
Every tube of radius at most one whose stored midpoint lies in `B₁` is
contained in the fixed root tube after dilation by `1000`.
-/
theorem carrier_subset_dilated_unitScaleTube_of_midpoint
    {sigma : ℝ}
    (hsigma : 0 ≤ sigma)
    (hsigmaOne : sigma ≤ 1)
    (tube : Kakeya.DeltaTube sigma)
    (hmidpoint : ‖tubeMidpoint tube‖ ≤ 1) :
    tube.carrier ⊆ dilatedTubeCarrier 1000 unitScaleTube := by
  let unitRadiusTube := withRadius 1 tube
  have hunitMidpoint :
      ‖tubeMidpoint unitRadiusTube‖ ≤ 1 := by
    simpa only [unitRadiusTube, withRadius_midpoint] using hmidpoint
  have hrootMidpoint :
      ‖tubeMidpoint unitScaleTube‖ ≤ 1 := by
    have heq :
        tubeMidpoint unitScaleTube =
          (1 / 2 : ℝ) • unitScaleTube.direction := by
      simp [tubeMidpoint, unitScaleTube]
      <;> abel
    rw [heq, norm_smul, unitScaleTube.direction_unit]
    norm_num
  have htransverse :
      ‖(tubeMidpoint unitRadiusTube - tubeMidpoint unitScaleTube) -
          inner ℝ
            (tubeMidpoint unitRadiusTube - tubeMidpoint unitScaleTube)
            unitScaleTube.direction • unitScaleTube.direction‖ ≤
        2 := by
    calc
      _ ≤
          ‖tubeMidpoint unitRadiusTube -
            tubeMidpoint unitScaleTube‖ :=
        norm_transverse_le unitScaleTube.direction_unit _
      _ ≤
          ‖tubeMidpoint unitRadiusTube‖ +
            ‖tubeMidpoint unitScaleTube‖ :=
        norm_sub_le _ _
      _ ≤ 2 := by linarith
  have hdirection :
      ‖unitRadiusTube.direction -
          inner ℝ unitRadiusTube.direction unitScaleTube.direction •
            unitScaleTube.direction‖ ≤
        1 := by
    calc
      _ ≤ ‖unitRadiusTube.direction‖ :=
        norm_transverse_le unitScaleTube.direction_unit _
      _ = 1 := unitRadiusTube.direction_unit
  have hcriterion :
      ‖(tubeMidpoint unitRadiusTube - tubeMidpoint unitScaleTube) -
          inner ℝ
            (tubeMidpoint unitRadiusTube - tubeMidpoint unitScaleTube)
            unitScaleTube.direction • unitScaleTube.direction‖ +
        (1 / 2 : ℝ) *
          ‖unitRadiusTube.direction -
            inner ℝ unitRadiusTube.direction unitScaleTube.direction •
              unitScaleTube.direction‖ ≤
        (1000 - 1) * 1 := by
    nlinarith
  have hcontained :
      unitRadiusTube.carrier ⊆
        dilatedTubeCarrier 1000 unitScaleTube :=
    tube_contained_in_dilated_transverse_general
      (by norm_num) (by norm_num) 1000 1
      (by norm_num) (by norm_num)
      unitRadiusTube unitScaleTube
      hunitMidpoint hrootMidpoint hcriterion
  exact
    (carrier_subset_withRadius hsigmaOne tube).trans hcontained

end Kakeya.Streamlined
