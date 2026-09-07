import MyLeanRepo.Kakeya.CV.Statements
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Basic definitions for the polynomial cylinder estimate

Shared definitions used across the polynomial cylinder estimate proof.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

variable {n : ℕ}

/-- The standard basis vector e₃ = (0, 0, 1) in `Point 3`. -/
def e3 : Point 3 := EuclideanSpace.single 2 1

/-- Projection from Point 3 to Point 2 dropping the third coordinate. -/
def proj2 (x : Point 3) : Point 2 :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => x (Fin.castSucc i))

/-- A z-graph over `U ⊆ Point 2`: points `(y₀, y₁, f(y₀, y₁))` for `y ∈ U`. -/
def zGraph (U : Set (Point 2)) (f : Point 2 → ℝ) : Set (Point 3) :=
  {x : Point 3 | proj2 x ∈ U ∧ x 2 = f (proj2 x)}

end Kakeya.CV
