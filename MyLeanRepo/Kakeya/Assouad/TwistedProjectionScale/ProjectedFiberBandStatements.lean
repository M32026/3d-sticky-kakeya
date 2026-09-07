import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.Bounds
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.DyadicIntegralBandStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberMultiplicityCapStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberPullbackMassStatement

/-!
# A same-family shading from one projected-fiber multiplicity band

This is the first assembly after the corrected Section 7 multiplicity
boundary.  It selects one dyadic band of the fiber-integrated spatial
multiplicity and pulls that planar band back to every carrier of the original
indexed tube family.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- The fixed planar rectangle containing all normalized twisted projections. -/
def section7ProjectionRectangle : Set Point2 :=
  {q | |q 0| ≤ 51 ∧ |q 1| ≤ 1}

/--
One projected-fiber multiplicity band and its same-family pullback shading.

The retained mass is measured exactly, not through projected tube-count
multiplicity.  The planar band records both pointwise fiber bounds and the
global integral fraction selected by dyadic pigeonholing.
-/
structure ProjectedFiberBandData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (threshold : ENNReal)
    (levelCount : ℕ) where
  bandIndex : ℕ
  bandIndex_le : bandIndex ≤ levelCount
  band : Set Point2
  band_eq :
    band =
      dyadicValueBand
        (projectedFiberMultiplicity Y f) threshold bandIndex
  band_measurable : MeasurableSet band
  band_subset_rectangle :
    band ⊆ section7ProjectionRectangle
  shading : Kakeya.Streamlined.TubeShading F
  shading_eq :
    shading =
      projectionPullbackShading Y f band band_measurable
  subshading : IsSubshading shading Y
  mass_identity :
    shading.mass =
      ∫⁻ q in band, projectedFiberMultiplicity Y f q
  mass_retention :
    Y.mass ≤ 2 * (levelCount + 1 : ENNReal) * shading.mass
  fiber_lower :
    ∀ q ∈ band,
      threshold * (2 ^ bandIndex : ENNReal) ≤
        projectedFiberMultiplicity Y f q
  fiber_upper :
    ∀ q ∈ band,
      projectedFiberMultiplicity Y f q <
        threshold * (2 ^ (bandIndex + 1) : ENNReal)
  twisted_subset :
    twistedUnion shading f ⊆ band

/--
Assemble one genuine same-family projected-fiber band.

The geometric hypotheses put the support of the fiber multiplicity inside
`section7ProjectionRectangle`.  The explicit low-tail premise and dyadic
range premise are the two quantitative facts needed before invoking the
generic integral-band selector.
-/
def ProjectedFiberBandStatement : Prop :=
  ProjectedFiberMassStatement →
    ProjectedFiberMultiplicityCapStatement →
      ProjectedFiberPullbackMassStatement →
        DyadicIntegralBandStatement →
          ∀ {delta : ℝ},
            0 < delta → delta ≤ 1 →
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              F.Nonempty →
              IsInVerticalChart F →
              (∀ i : Fin F.card,
                |(tubeParams i).a| ≤ 12 ∧
                  |(tubeParams i).b| ≤ 12 ∧
                  |(tubeParams i).c| ≤ 2 ∧
                  |(tubeParams i).d| ≤ 2) →
              ∀ Y : Kakeya.Streamlined.TubeShading F,
                Y.union ⊆ horizontalSlab 0 1 →
                Y.mass ≠ 0 →
                Y.mass ≠ ⊤ →
                ∀ f : SlopeFunction,
                  f.IsNonsingular → f 0 = 0 →
                  ∀ threshold : ENNReal,
                    threshold ≠ 0 →
                    threshold ≠ ⊤ →
                    2 *
                        (threshold *
                          volume section7ProjectionRectangle) ≤
                      Y.mass →
                    ∀ levelCount : ℕ,
                      ENNReal.ofReal (6 * delta) * F.enncard ≤
                        threshold *
                          (2 ^ levelCount : ENNReal) →
                      Nonempty
                        (ProjectedFiberBandData
                          Y f threshold levelCount)

end Kakeya.Assouad
