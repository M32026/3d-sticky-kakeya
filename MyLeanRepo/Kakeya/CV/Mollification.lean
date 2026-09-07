import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Mollified surface-area infrastructure

The paper averages directional surface area over a small ball in a
finite-dimensional polynomial coefficient space.  These definitions isolate
the analytic convolution and the averaged visibility body.
-/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace Kakeya.CV

/-- A finite-dimensional coefficient space for a polynomial family. -/
abbrev CoefficientSpace (N : ℕ) := EuclideanSpace ℝ (Fin N)

/-- Normalized average over an `ε`-ball in coefficient space. -/
def ballAverage {N : ℕ} (ε : ℝ) (f : CoefficientSpace N → ℝ)
    (x : CoefficientSpace N) : ℝ :=
  (volume (Metric.ball (0 : CoefficientSpace N) ε)).toReal⁻¹ *
    ∫ y in Metric.ball x ε, f y

/-- Average of a family of one-homogeneous directional masses. -/
def averagedDirectionalMass {P : Type*} [MeasurableSpace P]
    (μ : Measure P) (mass : P → Point 3 → ℝ≥0∞) (u : Point 3) : ℝ≥0∞ :=
  ∫⁻ q, mass q u ∂μ

/-- Visibility body associated to an averaged directional mass. -/
def averagedVisibilityBody {P : Type*} [MeasurableSpace P]
    (μ : Measure P) (mass : P → Point 3 → ℝ≥0∞) : Set (Point 3) :=
  unitBall 3 ∩ {u | averagedDirectionalMass μ mass u ≤ 1}

/-- Banach--Mazur style convergence about a fixed center. -/
def HomotheticConvergesAt (z : Point 3) (K : ℕ → Set (Point 3))
    (L : Set (Point 3)) : Prop :=
  ∀ α : ℝ, 1 < α →
    ∀ᶠ m in atTop, AreHomotheticallyCloseAt z α (K m) L

end Kakeya.CV
