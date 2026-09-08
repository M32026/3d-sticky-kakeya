import MyLeanRepo.Kakeya.Streamlined.DividingScales.OccupiedIntegerGridHierarchy
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeOrientation
import Mathlib.Data.Fintype.BigOperators

/-!
# Orientation-invariant midpoint coordinates for concrete tubes

A concrete `DeltaTube` is determined, up to reversing its parametrization, by

* its midpoint; and
* the rank-one matrix `direction ⊗ direction`.

The three midpoint coordinates and nine rank-one entries give a
twelve-dimensional Euclidean coordinate map.  It is invariant under
`reverseTube`, and equality of the coordinates implies equality of carriers.

This is the strict full-carrier coordinate boundary needed before applying
the generic occupied integer-grid hierarchy.  It does not yet prove that
nearby coordinate cells yield essentially-distinct coarse representatives or
the paper's Lemma 7.4 containment.
-/

noncomputable section

namespace Kakeya.Streamlined

open GeometricLemmas

/-- The three midpoint slots followed by the nine rank-one direction slots. -/
abbrev ProjectiveMidpointCoordinateIndex :=
  Fin 3 ⊕ (Fin 3 × Fin 3)

/-- The canonical equivalence between the coordinate index and `Fin 12`. -/
def projectiveMidpointCoordinateEquiv :
    ProjectiveMidpointCoordinateIndex ≃ Fin 12 := by
  have hcard :
      Fintype.card ProjectiveMidpointCoordinateIndex = 12 := by
    simp [ProjectiveMidpointCoordinateIndex]
  exact
    (Fintype.equivFin ProjectiveMidpointCoordinateIndex).trans
      (Equiv.cast (congrArg Fin hcard))

/--
Orientation-invariant twelve-dimensional coordinate of one concrete tube.
-/
def projectiveMidpointTubeCoordinates
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    Fin 12 → ℝ :=
  fun coordinate =>
    match projectiveMidpointCoordinateEquiv.symm coordinate with
    | Sum.inl midpointCoordinate =>
        tubeMidpoint tube midpointCoordinate
    | Sum.inr directionCoordinates =>
        tube.direction directionCoordinates.1 *
          tube.direction directionCoordinates.2

/-- The coordinate equivalence exposes every midpoint entry. -/
lemma projectiveMidpointTubeCoordinates_midpoint
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (coordinate : Fin 3) :
    projectiveMidpointTubeCoordinates tube
        (projectiveMidpointCoordinateEquiv (Sum.inl coordinate)) =
      tubeMidpoint tube coordinate := by
  simp [projectiveMidpointTubeCoordinates]

/-- The coordinate equivalence exposes every rank-one direction entry. -/
lemma projectiveMidpointTubeCoordinates_directionProduct
    {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (first second : Fin 3) :
    projectiveMidpointTubeCoordinates tube
        (projectiveMidpointCoordinateEquiv
          (Sum.inr (first, second))) =
      tube.direction first * tube.direction second := by
  simp [projectiveMidpointTubeCoordinates]

/-- Reversing the oriented parametrization preserves all twelve coordinates. -/
@[simp] theorem projectiveMidpointTubeCoordinates_reverseTube
    {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    projectiveMidpointTubeCoordinates (reverseTube tube) =
      projectiveMidpointTubeCoordinates tube := by
  funext coordinate
  cases hcoordinate :
      projectiveMidpointCoordinateEquiv.symm coordinate with
  | inl midpointCoordinate =>
      simp [projectiveMidpointTubeCoordinates, hcoordinate]
  | inr directionCoordinates =>
      simp [projectiveMidpointTubeCoordinates, hcoordinate, reverseTube]

/--
Equal rank-one tensors of unit directions differ by at most an overall sign.
-/
theorem direction_eq_or_eq_neg_of_rankOne_eq
    {first second : Point3}
    (hfirstUnit : ‖first‖ = 1)
    (hrankOne :
      ∀ i j : Fin 3,
        first i * first j = second i * second j) :
    first = second ∨ first = -second := by
  have hfirstNe : first ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hfirstUnit
    norm_num at hfirstUnit
  have hcoordinate :
      ∃ coordinate : Fin 3, first coordinate ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hfirstNe
    ext coordinate
    exact hnone coordinate
  rcases hcoordinate with ⟨coordinate, hcoordinateNe⟩
  have hsquare :
      first coordinate ^ 2 = second coordinate ^ 2 := by
    simpa [pow_two] using hrankOne coordinate coordinate
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsquare) with
    hsame | hopposite
  · left
    ext index
    have hproduct := hrankOne coordinate index
    rw [← hsame] at hproduct
    exact mul_left_cancel₀ hcoordinateNe hproduct
  · right
    ext index
    have hproduct := hrankOne coordinate index
    have hsecondCoordinate :
        second coordinate = -first coordinate := by
      linarith
    have hcancel :
        first coordinate * first index =
          first coordinate * (-second index) := by
      rw [hsecondCoordinate] at hproduct
      linarith
    have hindex :
        first index = -second index :=
      mul_left_cancel₀ hcoordinateNe hcancel
    simpa using hindex

/-- Midpoint and oriented direction determine the concrete tube structure. -/
lemma deltaTube_eq_of_midpoint_eq_of_direction_eq
    {delta : ℝ}
    {first second : Kakeya.DeltaTube delta}
    (hmidpoint :
      tubeMidpoint first = tubeMidpoint second)
    (hdirection : first.direction = second.direction) :
    first = second := by
  cases first with
  | mk firstBase firstDirection firstDirectionUnit =>
    cases second with
    | mk secondBase secondDirection secondDirectionUnit =>
      dsimp only at hdirection
      subst secondDirection
      have hbase : firstBase = secondBase := by
        dsimp only [tubeMidpoint] at hmidpoint
        exact add_right_cancel hmidpoint
      subst secondBase
      rfl

/-- Equal projective-midpoint coordinates have the same geometric carrier. -/
theorem carrier_eq_of_projectiveMidpointTubeCoordinates_eq
    {delta : ℝ}
    {first second : Kakeya.DeltaTube delta}
    (hcoordinates :
      projectiveMidpointTubeCoordinates first =
        projectiveMidpointTubeCoordinates second) :
    first.carrier = second.carrier := by
  have hmidpoint : tubeMidpoint first = tubeMidpoint second := by
    ext coordinate
    have hvalue := congrFun hcoordinates
      (projectiveMidpointCoordinateEquiv (Sum.inl coordinate))
    simpa only [
      projectiveMidpointTubeCoordinates_midpoint] using hvalue
  have hrankOne :
      ∀ i j : Fin 3,
        first.direction i * first.direction j =
          second.direction i * second.direction j := by
    intro i j
    have hvalue := congrFun hcoordinates
      (projectiveMidpointCoordinateEquiv (Sum.inr (i, j)))
    simpa only [
      projectiveMidpointTubeCoordinates_directionProduct] using hvalue
  rcases
      direction_eq_or_eq_neg_of_rankOne_eq
        first.direction_unit hrankOne with
    hdirection | hdirection
  · rw [deltaTube_eq_of_midpoint_eq_of_direction_eq
      hmidpoint hdirection]
  · have hreversed :
        first = reverseTube second := by
      apply deltaTube_eq_of_midpoint_eq_of_direction_eq
      · simpa using hmidpoint
      · simpa [reverseTube] using hdirection
    rw [hreversed, reverseTube_carrier]

/-- Family-level coordinate map ready for the occupied grid hierarchy. -/
def tubeFamilyProjectiveMidpointCoordinates
    {delta : ℝ} (family : TubeFamily delta) :
    Fin family.card → Fin 12 → ℝ :=
  fun index =>
    projectiveMidpointTubeCoordinates (family.tube index)

/--
Coordinate equality in a family is exactly strong enough to identify the
underlying geometric carrier, even if two stored tubes use opposite
orientations.
-/
theorem tubeFamily_carrier_eq_of_projectiveMidpointCoordinates_eq
    {delta : ℝ} (family : TubeFamily delta)
    {first second : Fin family.card}
    (hcoordinates :
      tubeFamilyProjectiveMidpointCoordinates family first =
        tubeFamilyProjectiveMidpointCoordinates family second) :
    (family.tube first).carrier =
      (family.tube second).carrier :=
  carrier_eq_of_projectiveMidpointTubeCoordinates_eq hcoordinates

/-- Occupied projective-midpoint grid parents for a concrete tube family. -/
abbrev TubeProjectiveMidpointGridParent
    {delta : ℝ} (family : TubeFamily delta)
    (base level : ℕ) :=
  OccupiedIntegerGridLabel
    (tubeFamilyProjectiveMidpointCoordinates family) base level

/-- Parent assignment in the twelve-dimensional strict tube grid. -/
def tubeProjectiveMidpointGridParent
    {delta : ℝ} (family : TubeFamily delta)
    (base level : ℕ)
    (index : Fin family.card) :
    TubeProjectiveMidpointGridParent family base level :=
  occupiedIntegerGridParent
    (tubeFamilyProjectiveMidpointCoordinates family)
    base level index

/-- The strict tube grid inherits the generic adjacent-refinement hierarchy. -/
def tubeProjectiveMidpointGridAdjacentRefinement
    {delta : ℝ} (family : TubeFamily delta)
    {levels : ℕ}
    (base : ℕ) (hbase : 1 ≤ base) :
    AdjacentFiniteParentMapRefinement
      (Fin family.card)
      (fun level : Fin (levels + 1) =>
        TubeProjectiveMidpointGridParent family base level.val)
      (fun level index =>
        tubeProjectiveMidpointGridParent family base level.val index) :=
  occupiedIntegerGridAdjacentRefinement
    (tubeFamilyProjectiveMidpointCoordinates family)
    base hbase

end Kakeya.Streamlined
