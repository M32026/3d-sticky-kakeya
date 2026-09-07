import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic

/-!
# Isoperimetric Inequality — Basic Definitions

Common definitions and notation used throughout the isoperimetric proof.

## Main definitions
- `E n`: Euclidean space `ℝⁿ`
- `unitBall n`: the closed unit ball in `E n`
- `innerParallelBody U t`: the inner parallel body `{x ∈ U | infDist x Uᶜ > t}`

## Whiteprint
This module supports the root `isoperimetric` node and its dependencies.
-/

open scoped Pointwise

namespace Geometry

open Metric

/-- The Euclidean model space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The closed unit ball in `E n`. -/
abbrev unitBall (n : ℕ) : Set (E n) := closedBall (0 : E n) 1

/-- Inner parallel body of an open set `U` at distance `t`:
the set of points in `U` at distance strictly greater than `t` from the complement. -/
def innerParallelBody {α : Type*} [PseudoMetricSpace α] (U : Set α) (t : ℝ) : Set α :=
  {x | infDist x Uᶜ > t}

notation:70 U "₋[" t "]" => innerParallelBody U t

end Geometry
