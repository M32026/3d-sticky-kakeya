import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Between
import Mathlib.Topology.MetricSpace.HausdorffDimension

open MeasureTheory

/-- Three-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- A **Kakeya set** is a compact subset of three-dimensional Euclidean space
that contains a unit line segment pointing in every unit direction. -/
def IsKakeya (K : Set Space) : Prop :=
  IsCompact K ∧
    ∀ v : Space, ‖v‖ = 1 →
      ∃ x : Space, ∀ t : ℝ, t ∈ Set.Icc 0 1 → x + t • v ∈ K
