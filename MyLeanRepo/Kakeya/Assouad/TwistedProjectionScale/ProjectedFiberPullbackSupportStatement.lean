import MyLeanRepo.Kakeya.Assouad.MultiplicityPigeonholing
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberMassStatement

/-!
# Exact support of a projected-fiber pullback shading

Restricting a shading to the preimage of a measurable planar set always gives
one inclusion of twisted supports.  If the fiber-integrated multiplicity is
nonzero at every point of that planar set, the reverse inclusion also holds.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
A measurable planar set on which `projectedFiberMultiplicity` is pointwise
nonzero is exactly the twisted union of its same-family pullback shading.

Pointwise nonzero fiber integral produces one fiber point with positive
spatial multiplicity, hence one original shaded carrier through that point.
This is stronger than an almost-everywhere support statement and is the form
needed for the retained dyadic bands, where a strict positive lower bound is
stored at every point.
-/
def ProjectedFiberPullbackSupportStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ f : SlopeFunction,
          ∀ X : Set Point2,
            ∀ hX : MeasurableSet X,
              (∀ q ∈ X,
                projectedFiberMultiplicity Y f q ≠ 0) →
                twistedUnion
                    (projectionPullbackShading Y f X hX) f =
                  X

end Kakeya.Assouad
