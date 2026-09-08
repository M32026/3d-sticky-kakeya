import MyLeanRepo.Kakeya.Streamlined.DividingScales.ProjectiveMidpointTubeCoordinates

/-!
# Orientation-invariant coordinates for supporting lines

The midpoint coordinate of a stored `DeltaTube` remembers where its unit
segment sits along the supporting line.  That endpoint-sensitive information
is useful for strict carrier containment, but it is not part of the paper's
coaxial-line geometry.

This module quotients out the axial coordinate.  A supporting line is encoded
by

* the point on the line closest to the origin; and
* the rank-one direction tensor `direction ⊗ direction`.

The resulting twelve coordinates are invariant under both reversing the
stored tube orientation and translating the chosen unit segment along its
axis.  Equality identifies supporting affine lines, not tube carriers.
-/

noncomputable section

namespace Kakeya.Streamlined

open GeometricLemmas

/-- Orthogonal projection of a point to the complement of a unit direction. -/
def projectiveLineAnchor (point direction : Point3) : Point3 :=
  point - inner ℝ point direction • direction

/-- The point of a tube's supporting line closest to the origin. -/
def tubeSupportingLineAnchor
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) : Point3 :=
  projectiveLineAnchor (tubeMidpoint tube) tube.direction

/-- The full affine supporting line of a concrete tube. -/
def tubeSupportingLine
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) : Set Point3 :=
  {point | ∃ parameter : ℝ,
    point =
      tubeSupportingLineAnchor tube +
        parameter • tube.direction}

/-- Axial translation does not change the closest-point line anchor. -/
theorem projectiveLineAnchor_add_smul
    {point direction : Point3}
    (hdirection : ‖direction‖ = 1)
    (parameter : ℝ) :
    projectiveLineAnchor
        (point + parameter • direction) direction =
      projectiveLineAnchor point direction := by
  have hself :
      inner ℝ direction direction = 1 := by
    rw [real_inner_self_eq_norm_sq, hdirection]
    norm_num
  simp only [projectiveLineAnchor, inner_add_left,
    real_inner_smul_left, hself, mul_one]
  module

/-- Reversing a unit direction does not change the closest-point anchor. -/
@[simp] theorem projectiveLineAnchor_neg_direction
    (point direction : Point3) :
    projectiveLineAnchor point (-direction) =
      projectiveLineAnchor point direction := by
  simp only [projectiveLineAnchor, inner_neg_right]
  module

/-- The midpoint and base give the same supporting-line anchor. -/
theorem tubeSupportingLineAnchor_eq_baseProjection
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    tubeSupportingLineAnchor tube =
      projectiveLineAnchor tube.base tube.direction := by
  simpa only [tubeSupportingLineAnchor, tubeMidpoint] using
    projectiveLineAnchor_add_smul
      tube.direction_unit (1 / 2 : ℝ)

/-- The anchor is perpendicular to the stored unit direction. -/
theorem inner_tubeSupportingLineAnchor_direction
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    inner ℝ (tubeSupportingLineAnchor tube) tube.direction = 0 := by
  have hself :
      inner ℝ tube.direction tube.direction = 1 := by
    rw [real_inner_self_eq_norm_sq, tube.direction_unit]
    norm_num
  calc
    inner ℝ (tubeSupportingLineAnchor tube) tube.direction =
        inner ℝ (tubeMidpoint tube) tube.direction -
          inner ℝ
            (inner ℝ (tubeMidpoint tube) tube.direction •
              tube.direction)
            tube.direction := by
          rw [tubeSupportingLineAnchor, projectiveLineAnchor,
            inner_sub_left]
    _ =
        inner ℝ (tubeMidpoint tube) tube.direction -
          inner ℝ (tubeMidpoint tube) tube.direction *
            inner ℝ tube.direction tube.direction := by
          rw [inner_smul_left]
          simp
    _ = 0 := by rw [hself]; ring

/-- Reversing a tube's parametrization preserves its supporting-line anchor. -/
@[simp] theorem tubeSupportingLineAnchor_reverseTube
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    tubeSupportingLineAnchor (reverseTube tube) =
      tubeSupportingLineAnchor tube := by
  change
    projectiveLineAnchor
        (tubeMidpoint (reverseTube tube)) (-tube.direction) =
      projectiveLineAnchor (tubeMidpoint tube) tube.direction
  rw [reverseTube_midpoint, projectiveLineAnchor_neg_direction]

/-- Reversing a tube's parametrization preserves its affine supporting line. -/
@[simp] theorem tubeSupportingLine_reverseTube
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    tubeSupportingLine (reverseTube tube) =
      tubeSupportingLine tube := by
  ext point
  constructor
  · rintro ⟨parameter, hpoint⟩
    refine ⟨-parameter, ?_⟩
    calc
      point =
          tubeSupportingLineAnchor (reverseTube tube) +
            parameter • (reverseTube tube).direction := hpoint
      _ =
          tubeSupportingLineAnchor tube +
            (-parameter) • tube.direction := by
            rw [tubeSupportingLineAnchor_reverseTube]
            simp only [reverseTube, neg_smul, smul_neg]
  · rintro ⟨parameter, hpoint⟩
    refine ⟨-parameter, ?_⟩
    calc
      point =
          tubeSupportingLineAnchor tube +
            parameter • tube.direction := hpoint
      _ =
          tubeSupportingLineAnchor (reverseTube tube) +
            (-parameter) • (reverseTube tube).direction := by
            rw [tubeSupportingLineAnchor_reverseTube]
            simp only [reverseTube]
            module

/-- Supporting-line coordinates use the same three-plus-nine slot layout. -/
abbrev ProjectiveSupportingLineCoordinateIndex :=
  ProjectiveMidpointCoordinateIndex

/-- Canonical enumeration of the twelve supporting-line coordinate slots. -/
def projectiveSupportingLineCoordinateEquiv :
    ProjectiveSupportingLineCoordinateIndex ≃ Fin 12 :=
  projectiveMidpointCoordinateEquiv

/--
Orientation- and axial-translation-invariant coordinate of one supporting
line.
-/
def projectiveSupportingLineCoordinates
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    Fin 12 → ℝ :=
  fun coordinate =>
    match projectiveSupportingLineCoordinateEquiv.symm coordinate with
    | Sum.inl anchorCoordinate =>
        tubeSupportingLineAnchor tube anchorCoordinate
    | Sum.inr directionCoordinates =>
        tube.direction directionCoordinates.1 *
          tube.direction directionCoordinates.2

/-- The coordinate equivalence exposes every line-anchor entry. -/
lemma projectiveSupportingLineCoordinates_anchor
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (coordinate : Fin 3) :
    projectiveSupportingLineCoordinates tube
        (projectiveSupportingLineCoordinateEquiv
          (Sum.inl coordinate)) =
      tubeSupportingLineAnchor tube coordinate := by
  simp [projectiveSupportingLineCoordinates,
    projectiveSupportingLineCoordinateEquiv]

/-- The coordinate equivalence exposes every rank-one direction entry. -/
lemma projectiveSupportingLineCoordinates_directionProduct
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (first second : Fin 3) :
    projectiveSupportingLineCoordinates tube
        (projectiveSupportingLineCoordinateEquiv
          (Sum.inr (first, second))) =
      tube.direction first * tube.direction second := by
  simp [projectiveSupportingLineCoordinates,
    projectiveSupportingLineCoordinateEquiv]

/-- Reversing the stored tube orientation preserves all line coordinates. -/
@[simp] theorem projectiveSupportingLineCoordinates_reverseTube
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    projectiveSupportingLineCoordinates (reverseTube tube) =
      projectiveSupportingLineCoordinates tube := by
  funext coordinate
  cases hcoordinate :
      projectiveSupportingLineCoordinateEquiv.symm coordinate with
  | inl anchorCoordinate =>
      simp [projectiveSupportingLineCoordinates, hcoordinate]
  | inr directionCoordinates =>
      simp [projectiveSupportingLineCoordinates, hcoordinate, reverseTube]

private lemma supportingLine_eq_of_anchor_eq_of_direction_eq
    {delta : ℝ}
    {first second : Kakeya.DeltaTube delta}
    (hanchor :
      tubeSupportingLineAnchor first =
        tubeSupportingLineAnchor second)
    (hdirection :
      first.direction = second.direction) :
    tubeSupportingLine first =
      tubeSupportingLine second := by
  ext point
  simp only [tubeSupportingLine, Set.mem_setOf_eq]
  rw [hanchor, hdirection]

private lemma supportingLine_eq_of_anchor_eq_of_direction_eq_neg
    {delta : ℝ}
    {first second : Kakeya.DeltaTube delta}
    (hanchor :
      tubeSupportingLineAnchor first =
        tubeSupportingLineAnchor second)
    (hdirection :
      first.direction = -second.direction) :
    tubeSupportingLine first =
      tubeSupportingLine second := by
  ext point
  constructor
  · rintro ⟨parameter, hpoint⟩
    refine ⟨-parameter, ?_⟩
    calc
      point =
          tubeSupportingLineAnchor first +
            parameter • first.direction := hpoint
      _ =
          tubeSupportingLineAnchor second +
            (-parameter) • second.direction := by
            rw [hanchor, hdirection]
            module
  · rintro ⟨parameter, hpoint⟩
    refine ⟨-parameter, ?_⟩
    calc
      point =
          tubeSupportingLineAnchor second +
            parameter • second.direction := hpoint
      _ =
          tubeSupportingLineAnchor first +
            (-parameter) • first.direction := by
            rw [hanchor, hdirection]
            module

/--
Equal projective supporting-line coordinates identify the same affine line.
They do not identify the stored unit segments or tube carriers.
-/
theorem supportingLine_eq_of_projectiveSupportingLineCoordinates_eq
    {delta : ℝ}
    {first second : Kakeya.DeltaTube delta}
    (hcoordinates :
      projectiveSupportingLineCoordinates first =
        projectiveSupportingLineCoordinates second) :
    tubeSupportingLine first =
      tubeSupportingLine second := by
  have hanchor :
      tubeSupportingLineAnchor first =
        tubeSupportingLineAnchor second := by
    ext coordinate
    have hvalue := congrFun hcoordinates
      (projectiveSupportingLineCoordinateEquiv
        (Sum.inl coordinate))
    simpa only [
      projectiveSupportingLineCoordinates_anchor] using hvalue
  have hrankOne :
      ∀ i j : Fin 3,
        first.direction i * first.direction j =
          second.direction i * second.direction j := by
    intro i j
    have hvalue := congrFun hcoordinates
      (projectiveSupportingLineCoordinateEquiv
        (Sum.inr (i, j)))
    simpa only [
      projectiveSupportingLineCoordinates_directionProduct] using hvalue
  rcases
      direction_eq_or_eq_neg_of_rankOne_eq
        first.direction_unit hrankOne with
    hdirection | hdirection
  · exact
      supportingLine_eq_of_anchor_eq_of_direction_eq
        hanchor hdirection
  · exact
      supportingLine_eq_of_anchor_eq_of_direction_eq_neg
        hanchor hdirection

/-- Family-level supporting-line coordinate map. -/
def tubeFamilyProjectiveSupportingLineCoordinates
    {delta : ℝ} (family : TubeFamily delta) :
    Fin family.card → Fin 12 → ℝ :=
  fun index =>
    projectiveSupportingLineCoordinates (family.tube index)

/-- Occupied supporting-line grid parents for a concrete tube family. -/
abbrev TubeProjectiveSupportingLineGridParent
    {delta : ℝ} (family : TubeFamily delta)
    (base level : ℕ) :=
  OccupiedIntegerGridLabel
    (tubeFamilyProjectiveSupportingLineCoordinates family)
    base level

/-- Parent assignment in the supporting-line grid. -/
def tubeProjectiveSupportingLineGridParent
    {delta : ℝ} (family : TubeFamily delta)
    (base level : ℕ)
    (index : Fin family.card) :
    TubeProjectiveSupportingLineGridParent family base level :=
  occupiedIntegerGridParent
    (tubeFamilyProjectiveSupportingLineCoordinates family)
    base level index

/-- The supporting-line grid inherits the generic adjacent refinement. -/
def tubeProjectiveSupportingLineGridAdjacentRefinement
    {delta : ℝ} (family : TubeFamily delta)
    {levels : ℕ}
    (base : ℕ) (hbase : 1 ≤ base) :
    AdjacentFiniteParentMapRefinement
      (Fin family.card)
      (fun level : Fin (levels + 1) =>
        TubeProjectiveSupportingLineGridParent
          family base level.val)
      (fun level index =>
        tubeProjectiveSupportingLineGridParent
          family base level.val index) :=
  occupiedIntegerGridAdjacentRefinement
    (tubeFamilyProjectiveSupportingLineCoordinates family)
    base hbase

end Kakeya.Streamlined
