import MyLeanRepo.Kakeya.Streamlined.DividingScales.ProjectiveDirectionTensorBounds
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ProjectiveMidpointTubeCoordinates
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeRadius

/-!
# Quantitative geometry inside a projective-midpoint tube cell

Two concrete tubes in the same twelve-dimensional floor-grid cell have close
midpoints and close projective directions at the same linear mesh scale.

The auxiliary `alignProjectiveTube` may reverse the parametrization of the
second tube relative to the first.  It never changes the second carrier.
Thus it is internal geometric bookkeeping and does not replace or modify a
public tube family.
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

/--
Orient `candidate` toward `reference` without changing the candidate's
geometric carrier.
-/
def alignProjectiveTube
    {delta : ℝ}
    (reference candidate : Kakeya.DeltaTube delta) :
    Kakeya.DeltaTube delta :=
  if 0 ≤ inner ℝ reference.direction candidate.direction then
    candidate
  else
    reverseTube candidate

@[simp] theorem alignProjectiveTube_carrier
    {delta : ℝ}
    (reference candidate : Kakeya.DeltaTube delta) :
    (alignProjectiveTube reference candidate).carrier =
      candidate.carrier := by
  by_cases hinner :
      0 ≤ inner ℝ reference.direction candidate.direction
  · simp [alignProjectiveTube, hinner]
  · simp [alignProjectiveTube, hinner]

@[simp] theorem alignProjectiveTube_midpoint
    {delta : ℝ}
    (reference candidate : Kakeya.DeltaTube delta) :
    tubeMidpoint (alignProjectiveTube reference candidate) =
      tubeMidpoint candidate := by
  by_cases hinner :
      0 ≤ inner ℝ reference.direction candidate.direction
  · simp [alignProjectiveTube, hinner]
  · simp [alignProjectiveTube, hinner]

@[simp] theorem alignProjectiveTube_direction
    {delta : ℝ}
    (reference candidate : Kakeya.DeltaTube delta) :
    (alignProjectiveTube reference candidate).direction =
      alignProjectiveDirection reference.direction candidate.direction := by
  by_cases hinner :
      0 ≤ inner ℝ reference.direction candidate.direction
  · simp [alignProjectiveTube, alignProjectiveDirection, hinner]
  · simp [alignProjectiveTube, alignProjectiveDirection, reverseTube, hinner]

@[simp] theorem withRadius_alignProjectiveTube_carrier
    {delta rho : ℝ}
    (reference candidate : Kakeya.DeltaTube delta) :
    (withRadius rho (alignProjectiveTube reference candidate)).carrier =
      (withRadius rho candidate).carrier := by
  by_cases hinner :
      0 ≤ inner ℝ reference.direction candidate.direction
  · simp [alignProjectiveTube, hinner]
  · rw [alignProjectiveTube, if_neg hinner]
    simp only [withRadius_carrier, reverseTube]
    rw [unitSegment_reverse]

/--
The midpoint coordinates of tubes in one projective-midpoint cell are close
at the exact floor-grid mesh scale.
-/
theorem tubeMidpoint_dist_lt_of_projectiveMidpointGridLabel_eq
    {delta : ℝ}
    {base level : ℕ}
    (hbase : 1 ≤ base)
    {first second : Kakeya.DeltaTube delta}
    (hlabel :
      integerGridLabel base level
          (projectiveMidpointTubeCoordinates first) =
        integerGridLabel base level
          (projectiveMidpointTubeCoordinates second)) :
    ‖tubeMidpoint first - tubeMidpoint second‖ <
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
        (projectiveMidpointCoordinateEquiv
          (Sum.inl coordinate))
  change
    |tubeMidpoint first coordinate -
      tubeMidpoint second coordinate| <
      (base ^ level : ℝ)⁻¹
  simpa only [
    projectiveMidpointTubeCoordinates_midpoint] using hcoordinate

/--
The rank-one direction slots of one cell give a linear direction estimate
after carrier-preserving relative orientation.
-/
theorem alignedDirection_dist_le_of_projectiveMidpointGridLabel_eq
    {delta : ℝ}
    {base level : ℕ}
    (hbase : 1 ≤ base)
    {first second : Kakeya.DeltaTube delta}
    (hlabel :
      integerGridLabel base level
          (projectiveMidpointTubeCoordinates first) =
        integerGridLabel base level
          (projectiveMidpointTubeCoordinates second)) :
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
        (projectiveMidpointCoordinateEquiv
          (Sum.inr (i, j)))
  exact (by
    simpa only [
      projectiveMidpointTubeCoordinates_directionProduct] using
        hcoordinate.le)

/--
Same-cell tubes have simultaneous midpoint and direction bounds against a
representative with exactly the second tube's carrier.
-/
theorem projectiveMidpoint_sameCell_geometry
    {delta : ℝ}
    {base level : ℕ}
    (hbase : 1 ≤ base)
    {first second : Kakeya.DeltaTube delta}
    (hlabel :
      integerGridLabel base level
          (projectiveMidpointTubeCoordinates first) =
        integerGridLabel base level
          (projectiveMidpointTubeCoordinates second)) :
    ‖tubeMidpoint first -
        tubeMidpoint (alignProjectiveTube first second)‖ <
        3 * (base ^ level : ℝ)⁻¹ ∧
      ‖first.direction -
        (alignProjectiveTube first second).direction‖ ≤
        18 * (base ^ level : ℝ)⁻¹ ∧
      (alignProjectiveTube first second).carrier =
        second.carrier := by
  constructor
  · simpa only [alignProjectiveTube_midpoint] using
      tubeMidpoint_dist_lt_of_projectiveMidpointGridLabel_eq
        hbase hlabel
  · exact ⟨
      alignedDirection_dist_le_of_projectiveMidpointGridLabel_eq
        hbase hlabel,
      alignProjectiveTube_carrier first second⟩

/--
At equal fine radius, one projective-midpoint cell has a strict full-carrier
representative after enlarging the representative radius by only a linear
multiple of the cell mesh.
-/
theorem carrier_subset_withRadius_of_projectiveMidpointGridLabel_eq
    {delta : ℝ}
    (hdelta : 0 ≤ delta)
    {base level : ℕ}
    (hbase : 1 ≤ base)
    {first second : Kakeya.DeltaTube delta}
    (hlabel :
      integerGridLabel base level
          (projectiveMidpointTubeCoordinates first) =
        integerGridLabel base level
          (projectiveMidpointTubeCoordinates second)) :
    first.carrier ⊆
      (withRadius
        (delta + 12 * (base ^ level : ℝ)⁻¹)
        second).carrier := by
  let aligned := alignProjectiveTube first second
  have hmidpoint :
      ‖tubeMidpoint first - tubeMidpoint aligned‖ ≤
        3 * (base ^ level : ℝ)⁻¹ := by
    dsimp only [aligned]
    exact
      (projectiveMidpoint_sameCell_geometry hbase hlabel).1.le
  have hdirection :
      ‖first.direction - aligned.direction‖ ≤
        18 * (base ^ level : ℝ)⁻¹ := by
    dsimp only [aligned]
    exact
      (projectiveMidpoint_sameCell_geometry hbase hlabel).2.1
  have hclose :
      ‖tubeMidpoint first -
          tubeMidpoint
            (withRadius
              (delta + 12 * (base ^ level : ℝ)⁻¹)
              aligned)‖ +
          ‖first.direction -
            (withRadius
              (delta + 12 * (base ^ level : ℝ)⁻¹)
              aligned).direction‖ / 2 +
          delta ≤
        delta + 12 * (base ^ level : ℝ)⁻¹ := by
    simp only [withRadius_midpoint, withRadius_direction]
    linarith
  have hcontained :
      first.carrier ⊆
        (withRadius
          (delta + 12 * (base ^ level : ℝ)⁻¹)
          aligned).carrier :=
    tube_contained_of_midpoint_direction_close
      hdelta first
        (withRadius
          (delta + 12 * (base ^ level : ℝ)⁻¹)
          aligned)
        hclose
  simpa only [
    aligned,
    withRadius_alignProjectiveTube_carrier] using hcontained

/--
Family parent equality supplies the same quantitative geometry for the two
indexed tubes.
-/
theorem tubeFamily_projectiveMidpoint_sameParent_geometry
    {delta : ℝ}
    (family : TubeFamily delta)
    {base level : ℕ}
    (hbase : 1 ≤ base)
    {first second : Fin family.card}
    (hparent :
      tubeProjectiveMidpointGridParent family base level first =
        tubeProjectiveMidpointGridParent family base level second) :
    ‖tubeMidpoint (family.tube first) -
        tubeMidpoint
          (alignProjectiveTube
            (family.tube first) (family.tube second))‖ <
        3 * (base ^ level : ℝ)⁻¹ ∧
      ‖(family.tube first).direction -
        (alignProjectiveTube
          (family.tube first) (family.tube second)).direction‖ ≤
        18 * (base ^ level : ℝ)⁻¹ ∧
      (alignProjectiveTube
        (family.tube first) (family.tube second)).carrier =
        (family.tube second).carrier := by
  apply projectiveMidpoint_sameCell_geometry hbase
  exact congrArg Subtype.val hparent

end Kakeya.Streamlined
