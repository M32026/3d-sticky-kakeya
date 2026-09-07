import MyLeanRepo.Kakeya.AssertionD
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Basic shared definitions for the Wolff hairbrush argument

Provides `angleBetween` and `thickenedTube` in the `Kakeya.Assouad` namespace,
shared by plane covering, cylinder intersection, and hairbrush volume bounds.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

variable {δ : ℝ}

/-- Angle between tube directions, in [0, π]. -/
def angleBetween {δ : ℝ} (T U : Kakeya.DeltaTube δ) : ℝ :=
  Real.arccos (inner ℝ T.direction U.direction)

/-- The r-neighborhood of T's axis segment. -/
def thickenedTube {δ : ℝ} (T : Kakeya.DeltaTube δ) (r : ℝ) : Set Point3 :=
  Metric.cthickening r (Kakeya.unitSegment T.base T.direction)

end Kakeya.Assouad

namespace Kakeya.Hairbrush

/-- Compatibility name for the shared tube-direction angle. -/
abbrev angleBetween {δ : ℝ} (T U : Kakeya.DeltaTube δ) : ℝ :=
  Kakeya.Assouad.angleBetween T U

end Kakeya.Hairbrush
