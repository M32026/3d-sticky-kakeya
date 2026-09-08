import Mathlib.Analysis.Asymptotics.ExpGrowth
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Minkowski dimensions

This module defines lower and upper Minkowski dimensions of a set in a
pseudo-metric space from the exponential growth of its covering numbers at
dyadic radii.

The values lie in `ENNReal`.  Thus the empty-set and infinite-covering-number
cases are included without separate finiteness conventions.
-/

noncomputable section

open ExpGrowth

namespace Metric

/-- Covering numbers at the dyadic radii `2⁻ⁿ`. -/
def dyadicCoveringSequence {X : Type*} [PseudoEMetricSpace X]
    (s : Set X) (n : ℕ) : ENNReal :=
  (coveringNumber (((2 : NNReal) ^ n)⁻¹) s : ENNReal)

/--
The lower Minkowski dimension, defined by the lower exponential growth of
dyadic covering numbers and normalized by `log 2`.
-/
def lowerMinkowskiDim {X : Type*} [PseudoEMetricSpace X]
    (s : Set X) : ENNReal :=
  (expGrowthInf (dyadicCoveringSequence s) / ENNReal.log 2).toENNReal

/--
The upper Minkowski dimension, defined by the upper exponential growth of
dyadic covering numbers and normalized by `log 2`.
-/
def upperMinkowskiDim {X : Type*} [PseudoEMetricSpace X]
    (s : Set X) : ENNReal :=
  (expGrowthSup (dyadicCoveringSequence s) / ENNReal.log 2).toENNReal

end Metric

namespace MeasureTheory

/--
The standard comparison between Hausdorff and Minkowski dimensions in an
arbitrary pseudo-metric space.
-/
def HausdorffMinkowskiDimensionComparisonStatement : Prop :=
  ∀ (X : Type*) [EMetricSpace X] (s : Set X),
    dimH s ≤ Metric.lowerMinkowskiDim s ∧
      Metric.lowerMinkowskiDim s ≤ Metric.upperMinkowskiDim s

end MeasureTheory
