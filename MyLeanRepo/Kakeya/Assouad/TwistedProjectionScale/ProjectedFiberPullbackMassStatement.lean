import MyLeanRepo.Kakeya.Assouad.MultiplicityPigeonholing
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberMassStatement

/-!
# Mass of a measurable twisted-projection pullback

After selecting a measurable subset of the planar projected set, Section 7
pulls it back to every carrier of the original indexed family.  The retained
aggregate shaded mass is exactly the integral of the fiber multiplicity over
that planar subset.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
Restricting a shading by a measurable planar set commutes with the
fiber-mass disintegration of the twisted projection.

This is an exact identity for arbitrary measurable shadings.  No compactness,
vertical-chart, parameter, or slope hypotheses are needed.
-/
def ProjectedFiberPullbackMassStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ f : SlopeFunction,
          ∀ X : Set Point2,
            ∀ hX : MeasurableSet X,
              (projectionPullbackShading Y f X hX).mass =
                ∫⁻ q in X, projectedFiberMultiplicity Y f q

end Kakeya.Assouad
