import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridAtomizationStatement

/-!
# Projected measure versus area inside one fiber-multiplicity band

On a dyadic projected-fiber band the density
`projectedFiberMultiplicity Y f` lies between one value `lambda` and
`2 * lambda`.  Integrating over any measurable subset converts projected
fiber measure to planar Lebesgue area with the same factor-two comparison.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Lower endpoint of the selected projected-fiber dyadic band. -/
def projectedFiberBandValue
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    {threshold : ENNReal}
    {levelCount : ℕ}
    (bandData : ProjectedFiberBandData Y f threshold levelCount) :
    ENNReal :=
  threshold * (2 ^ bandData.bandIndex : ENNReal)

/--
Projected-fiber measure and planar area are comparable on every measurable
subset of one dyadic fiber-multiplicity band.

This is the measure-to-area bridge needed after OS branching.  It uses the
fiber-integrated density, not projected tube-count multiplicity.
-/
def ProjectedFiberBandMeasureAreaComparisonStatement : Prop :=
  ∀ {delta : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ f : SlopeFunction,
          ∀ {threshold : ENNReal},
            ∀ {levelCount : ℕ},
              ∀ bandData :
                  ProjectedFiberBandData
                    Y f threshold levelCount,
                ∀ X : Set Point2,
                  MeasurableSet X →
                  X ⊆ bandData.band →
                    projectedFiberBandValue Y f bandData *
                        volume X ≤
                      projectedFiberMeasure Y f X ∧
                    projectedFiberMeasure Y f X ≤
                      2 * projectedFiberBandValue Y f bandData *
                        volume X

end Kakeya.Assouad
