import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.WeightedSelection
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameter4FiberRegularizationStatement

/-!
# Shaded mass bounds for regularized exact four-parameter fibers

After per-tube mass pruning, every active tube carries at least `threshold`
shaded mass and at most one tube volume.  Dyadic regularization of complete
exact `(a,b,c,d)` fibers then gives uniform two-sided mass bounds for every
selected parameter point.

The total-mass retention conclusion is written without division:

`threshold * Y.mass ≤ logLoss * tubeVolume * selectedMass`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Shaded mass carried by one exact four-parameter fiber. -/
def tubeParameter4FiberShadedMass
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading family)
    (indices : Finset (Fin family.card))
    (point : Point 4) : ENNReal :=
  ∑ index ∈
      indices.filter fun index =>
        indexedTubeParameterPoint4 index = point,
    volume (shading.carrier index)

/--
Per-tube fullness and complete-fiber cardinality regularization imply:

* each selected exact parameter fiber has mass between
  `fiberMultiplicity * threshold` and
  `2 * fiberMultiplicity * deltaTubeVolume delta`;
* the selected complete fibers retain total shaded mass in the
  cancellation-free product form displayed below.
-/
def TubeParameter4FiberMassBoundsStatement : Prop :=
  TubeVolumeScalingStatement →
    ∀ {delta : ℝ},
      0 < delta →
      delta ≤ 1 →
      ∀ family : Kakeya.Streamlined.TubeFamily delta,
        ∀ shading : Kakeya.Streamlined.TubeShading family,
          ∀ threshold : ENNReal,
            threshold ≠ 0 →
            HasPerTubeMass shading threshold →
            let active := positiveMassIndices shading
            ∀ regularized :
                TubeParameter4FiberRegularizationData family active,
              (∀ point ∈
                  regularized.selected.image indexedTubeParameterPoint4,
                (regularized.fiberMultiplicity : ENNReal) * threshold ≤
                    tubeParameter4FiberShadedMass
                      shading regularized.selected point ∧
                  tubeParameter4FiberShadedMass
                      shading regularized.selected point ≤
                    (2 * regularized.fiberMultiplicity : ENNReal) *
                      Kakeya.deltaTubeVolume delta) ∧
              threshold * shading.mass ≤
                (Nat.log 2 active.card + 1 : ENNReal) *
                    Kakeya.deltaTubeVolume delta *
                  (selectedTubeShading
                    shading regularized.selected).mass

end Kakeya.Assouad
