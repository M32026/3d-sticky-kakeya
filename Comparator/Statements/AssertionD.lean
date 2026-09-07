import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section

open MeasureTheory

namespace Kakeya

abbrev Point3 := EuclideanSpace ℝ (Fin 3)

def unitSegment (base direction : Point3) : Set Point3 :=
  (fun t : ℝ => base + t • direction) '' Set.Icc 0 1

structure DeltaTube (δ : ℝ) where
  base : Point3
  direction : Point3
  direction_unit : ‖direction‖ = 1

namespace DeltaTube

def carrier {δ : ℝ} (T : DeltaTube δ) : Set Point3 :=
  Metric.cthickening δ (unitSegment T.base T.direction)

def volume {δ : ℝ} (T : DeltaTube δ) : ENNReal :=
  MeasureTheory.volume T.carrier

def unitBall : Set Point3 :=
  Metric.closedBall 0 1

def IsInUnitBall {δ : ℝ} (T : DeltaTube δ) : Prop :=
  T.carrier ⊆ unitBall

def EssentiallyDistinct {δ : ℝ} (T U : DeltaTube δ) : Prop :=
  MeasureTheory.volume (T.carrier ∩ U.carrier) ≤
    (2 : ENNReal)⁻¹ * max T.volume U.volume

end DeltaTube

def realRpowENN (x exponent : ℝ) : ENNReal :=
  ENNReal.ofReal (Real.rpow x exponent)

end Kakeya
