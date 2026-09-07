import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement

/-!
# Shaded mass as twisted-projection fiber multiplicity

The multiplicity pigeonholed in Section 7 is not the number of projected
tube images containing a planar point.  For an arbitrary shading, it is the
integral of the original spatial point multiplicity along the fiber of the
twisted projection.

For `q = (u,z)`, the fiber is parametrized by
`y ↦ (u - f(z)y, y, z)`.  The resulting triangular change of coordinates
has Jacobian of absolute value one, so integrating the fiber multiplicity
over the plane recovers the total shaded mass.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
Spatial point multiplicity integrated along one fiber of `twistedProjection`.
-/
def projectedFiberMultiplicity
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (q : Point2) : ENNReal :=
  ∫⁻ y : ℝ,
    (Y.pointMultiplicity
      (point3 (q 0 - f (q 1) * y) y (q 1)) : ENNReal)

/--
Fubini/coarea identity for the twisted projection.

The first conclusion is needed to form measurable dyadic bands in `Point2`.
The second says that those bands decompose the actual shaded mass, without
replacing arbitrary shaded pieces by complete tube projections.
-/
def ProjectedFiberMassStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ f : SlopeFunction,
          Measurable (projectedFiberMultiplicity Y f) ∧
            (∫⁻ q : Point2, projectedFiberMultiplicity Y f q) = Y.mass

end Kakeya.Assouad
