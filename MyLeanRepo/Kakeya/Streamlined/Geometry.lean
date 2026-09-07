import MyLeanRepo.Kakeya.AssertionD
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Geometric objects for the streamlined three-dimensional Kakeya proof

This file contains data definitions only.  In particular, it does not assert
the existence of John ellipsoids or any Kakeya estimate.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-- The ambient Euclidean space. -/
abbrev Point3 := Kakeya.Point3

/-- An axis-parallel box centered at the origin, with the displayed side lengths. -/
def axisBox (a b c : ℝ) : Set Point3 :=
  {x |
    |x (0 : Fin 3)| ≤ a / 2 ∧
    |x (1 : Fin 3)| ≤ b / 2 ∧
    |x (2 : Fin 3)| ≤ c / 2}

/--
A geometric body is represented by its carrier.  Measurability and convexity
are predicates rather than fields, so the same indexed-family API can also be
used for intermediate measurable sets that are not convex.
-/
structure Body where
  carrier : Set Point3

namespace Body

/-- The body is Lebesgue measurable. -/
def IsMeasurable (K : Body) : Prop :=
  MeasurableSet K.carrier

/-- The body is convex. -/
def IsConvex (K : Body) : Prop :=
  Convex ℝ K.carrier

/-- Lebesgue volume of a body. -/
def volume (K : Body) : ENNReal :=
  MeasureTheory.volume K.carrier

/--
`K` has dimensions `a × b × c` in the specified rigid frame, up to the
multiplicative enlargement `A`.
-/
def HasDimensionsInFrame (K : Body) (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (a b c A : ℝ) : Prop :=
  0 < a ∧ a ≤ b ∧ b ≤ c ∧ 1 ≤ A ∧
    frame '' axisBox a b c ⊆ K.carrier ∧
    K.carrier ⊆ frame '' axisBox (A * a) (A * b) (A * c)

/--
`K` has Euclidean dimensions `a × b × c` up to factor `A`.  Only affine
isometries are allowed, so the numerical dimensions cannot be changed by an
arbitrary linear rescaling.
-/
def HasDimensions (K : Body) (a b c A : ℝ) : Prop :=
  ∃ frame : Point3 ≃ᵃⁱ[ℝ] Point3,
    HasDimensionsInFrame K frame a b c A

/-- A body comparable to an `a × b × 1` plank. -/
def IsPlank (K : Body) (a b A : ℝ) : Prop :=
  HasDimensions K a b 1 A

/-- A body comparable to a `θ × 1 × 1` slab. -/
def IsSlab (K : Body) (θ A : ℝ) : Prop :=
  HasDimensions K θ 1 1 A

end Body

/-- A tube viewed as a geometric body. -/
def tubeBody {δ : ℝ} (T : Kakeya.DeltaTube δ) : Body :=
  ⟨T.carrier⟩

/-- The closed unit ball used throughout the paper. -/
def unitBall : Body :=
  ⟨Kakeya.DeltaTube.unitBall⟩

end Kakeya.Streamlined
