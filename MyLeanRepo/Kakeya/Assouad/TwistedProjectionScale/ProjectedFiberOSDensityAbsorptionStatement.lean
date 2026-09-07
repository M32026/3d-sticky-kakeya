import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberAtomizationToOSStatement

/-!
# Density absorption after projected-fiber OS uniformization

The projected-fiber band, terminal atomization, and weighted OS pruning each
lose an explicit finite factor.  Once their product is at most
`delta^(-3*eta)`, an original `delta^eta`-dense shading yields a final
same-family `delta^(4*eta)`-dense shading.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Mass loss from selecting one projected-fiber multiplicity band. -/
def projectedFiberBandLoss (levelCount : ℕ) : ENNReal :=
  2 * (levelCount + 1 : ENNReal)

/-- Mass loss from terminal planar-grid atomization. -/
def projectedFiberAtomizationLoss
    (base levels indexBound : ℕ) : ENNReal :=
  ((2 *
      (Nat.log 2
        (2 *
          (boundedPlanarGridCenters
            base levels indexBound).card) +
        1) : ℕ) : ENNReal)

/-- Mass loss from weighted OS pruning of the locally bounded planar tree. -/
def projectedFiberOSLoss
    (base levels : ℕ) : ENNReal :=
  (2 : ENNReal) *
    ((((2 *
        (Nat.log 2 ((base + 1) ^ 2) + 1)) ^
      (levels + 1) : ℕ)) : ENNReal)

/-- Product of all losses from the original shading to the OS-uniform one. -/
def projectedFiberTotalLoss
    (levelCount base levels indexBound : ℕ) : ENNReal :=
  projectedFiberBandLoss levelCount *
    projectedFiberAtomizationLoss base levels indexBound *
      projectedFiberOSLoss base levels

/--
The same-family dense projected refinement used by the later local-to-global
cinematic continuation.
-/
structure ProjectedFiberOSDensityData
    {delta eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    {threshold : ENNReal}
    {levelCount : ℕ}
    (bandData : ProjectedFiberBandData Y f threshold levelCount)
    (base levels indexBound : ℕ)
    (atomized :
      ProjectedFiberGridAtomizationData
        Y f bandData base levels indexBound)
    (uniform :
      ProjectedFiberOSUniformData
        Y f bandData base levels indexBound atomized) where
  globalShading : Kakeya.Streamlined.TubeShading F
  globalShading_eq : globalShading = uniform.shading
  subshading : IsSubshading globalShading Y
  density :
    globalShading.IsLambdaDense
      (Kakeya.realRpowENN delta (4 * eta))
  slab :
    globalShading.union ⊆ horizontalSlab 0 1
  twisted_subset :
    twistedUnion globalShading f ⊆ uniform.retainedBand

/--
Absorb the complete projected-fiber uniformization loss into three additional
powers of `delta^eta`.

The theorem consumes the actual loss factors recorded by the closed data
structures.  It does not estimate grid cardinalities or logarithms; those
small-scale estimates are a separate arithmetic producer.
-/
def ProjectedFiberOSDensityAbsorptionStatement : Prop :=
  ∀ {delta eta : ℝ},
    0 < delta → delta ≤ 1 →
    0 < eta →
      ∀ F : Kakeya.Streamlined.TubeFamily delta,
        ∀ Y : Kakeya.Streamlined.TubeShading F,
          Y.IsLambdaDense
              (Kakeya.realRpowENN delta eta) →
          Y.union ⊆ horizontalSlab 0 1 →
          ∀ f : SlopeFunction,
            ∀ {threshold : ENNReal},
              ∀ {levelCount : ℕ},
                ∀ bandData :
                    ProjectedFiberBandData
                      Y f threshold levelCount,
                  ∀ base levels indexBound : ℕ,
                    ∀ atomized :
                        ProjectedFiberGridAtomizationData
                          Y f bandData base levels indexBound,
                      ∀ uniform :
                          ProjectedFiberOSUniformData
                            Y f bandData
                            base levels indexBound atomized,
                        projectedFiberTotalLoss
                            levelCount base levels indexBound ≤
                          Kakeya.realRpowENN delta (-3 * eta) →
                        Nonempty
                          (ProjectedFiberOSDensityData
                            (eta := eta)
                            Y f bandData
                            base levels indexBound atomized uniform)

end Kakeya.Assouad
