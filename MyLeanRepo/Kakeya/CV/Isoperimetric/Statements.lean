import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Isoperimetric input for Carbery--Valdimarsson

This file freezes the exact specialization of the Euclidean isoperimetric
inequality needed in the appendix of Carbery--Valdimarsson.  It is restricted
to polynomial sublevel regions inside the closed unit ball; the complementary
region is obtained by replacing `p` with `-p`.
-/

noncomputable section

open Set MeasureTheory
open scoped ENNReal MeasureTheory

namespace Kakeya.CV

/-- The ambient Euclidean space of dimension `n`. -/
abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The closed Euclidean unit ball. -/
def unitBall (n : ℕ) : Set (Point n) :=
  Metric.closedBall 0 1

/-- The Euclidean unit sphere. -/
def unitSphere (n : ℕ) : Set (Point n) :=
  Metric.sphere 0 1

/-- Evaluation of a real multivariable polynomial on Euclidean space. -/
def polynomialValue {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (x : Point n) : ℝ :=
  MvPolynomial.eval (fun i => x i) p

/-- The part of the polynomial sublevel set `{p ≤ 0}` inside the unit ball. -/
def polynomialSublevelInUnitBall {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    Set (Point n) :=
  unitBall n ∩ {x | polynomialValue p x ≤ 0}

/-- Hausdorff measure in codimension one. -/
def codimensionOneMeasure (n : ℕ) (s : Set (Point n)) : ℝ≥0∞ :=
  μH[(n : ℝ) - 1] s

/--
Standard two-dimensional surface area in `Point 3`.

Mathlib's raw `μH[2]` is normalized to be `4 / π` times planar Lebesgue
measure, so the standard geometric normalization is obtained by multiplying
by `π / 4`.
-/
def standardSurfaceArea3 (s : Set (Point 3)) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.pi / 4) * codimensionOneMeasure 3 s

/--
The three-dimensional isoperimetric input needed by the CV bisecting-ball
argument.

If a polynomial sublevel region occupies a proportion `a` of the unit ball,
then its topological boundary has at least `a ^ (2 / 3)` times the
two-dimensional Hausdorff measure of the unit sphere.

Only the dimension-three specialization is frozen because this is the form
consumed by the sticky Kakeya proof.
-/
def PolynomialRegionIsoperimetricStatement : Prop :=
  ∀ (p : MvPolynomial (Fin 3) ℝ) (a : ℝ),
    a ∈ Set.Icc 0 1 →
    volume (polynomialSublevelInUnitBall p) =
      ENNReal.ofReal a * volume (unitBall 3) →
    ENNReal.ofReal a ^ (2 / 3 : ℝ) *
        codimensionOneMeasure 3 (unitSphere 3) ≤
      codimensionOneMeasure 3 (frontier (polynomialSublevelInUnitBall p))

end Kakeya.CV
