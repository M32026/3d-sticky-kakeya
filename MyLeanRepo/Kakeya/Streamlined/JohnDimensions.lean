import MyLeanRepo.Kakeya.Geometry.OuterJohnEllipsoid
import MyLeanRepo.Kakeya.Streamlined.Basic

/-!
# Framed dimensions from the outer John ellipsoid

This module states the bridge from the standard Löwner--John ellipsoid API to
the framed box dimensions used in the streamlined Kakeya formalization.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
The outer John ellipsoid supplies uniformly comparable framed dimensions for
every three-dimensional convex body.
-/
def JohnToFramedDimensionsStatement : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧
    ∀ K : Body, JohnEllipsoid.IsConvexBody K.carrier →
      ∃ a b c : ℝ, ∃ frame : Point3 ≃ᵃⁱ[ℝ] Point3,
        K.HasDimensionsInFrame frame a b c A

end Kakeya.Streamlined
