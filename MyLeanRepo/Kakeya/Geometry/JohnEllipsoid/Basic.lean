import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section

open MeasureTheory
open scoped Pointwise Real

namespace JohnEllipsoid

section Basic

variable {X : Type*} [PseudoMetricSpace X] [AddCommMonoid X] [Module ℝ X] [MeasurableSpace X]

/-- The ellipsoid centered at `c` obtained as the image of the closed unit ball
under the invertible linear map `A`, followed by translation by `c`. -/
def ellipsoid (c : X) (A : X ≃ₗ[ℝ] X) : Set (X) :=
  c +ᵥ A '' Metric.closedBall 0 1

/-- A convex body is a compact convex set with nonempty interior. -/
def IsConvexBody (K : Set X) : Prop :=
  Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty

def IsOuterJohnEllipsoid (K : Set X) (c : X) (A : X ≃ₗ[ℝ] X) (μ : Measure X := by volume_tac) : Prop :=
  K ⊆ ellipsoid c A ∧ ∀ c' A', K ⊆ ellipsoid c' A' → μ (ellipsoid c A) ≤ μ (ellipsoid c' A')

end Basic

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

end JohnEllipsoid
