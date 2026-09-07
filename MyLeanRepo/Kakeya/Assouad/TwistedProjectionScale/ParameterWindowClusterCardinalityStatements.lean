import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterFrostmanStatement

/-!
# Cardinality after a parameter window

The positive-window proof first retains a global shading with density exponent
`densityLoss`, then selects one `c`-window at the cost `delta / 8`.
Weighted parameter clustering supplies

`lambda ≤ 100000 * regularizationLoss * (C * delta²) * #points`.

If `C ≤ delta^(-frostmanLoss)`, this gives the natural center exponent
`-1 + densityLoss + frostmanLoss`, up to the logarithmic regularization loss.
The target exponent must therefore be strictly larger than the sum of those
two losses.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Absorb the weighted-cluster regularization loss into a prescribed center
cardinality exponent.

The explicit logarithmic premise is supplied by `exists_delta_log_absorbed`
after the three loss exponents have been chosen.  Separating that generic
small-scale lemma from the ENNReal cluster algebra keeps the interface
reusable by later Section 7 repairs.
-/
def ParameterWindowClusterCardinalityStatement : Prop :=
  ∀ {delta densityLoss frostmanLoss targetLoss gamma : ℝ},
    0 < delta →
    delta < 1 →
    0 < densityLoss →
    0 < frostmanLoss →
    densityLoss + frostmanLoss < 1 →
    gamma = targetLoss - (densityLoss + frostmanLoss) →
    0 < gamma →
    ∀ {F : Kakeya.Streamlined.TubeFamily delta},
      ∀ {Y : Kakeya.Streamlined.TubeShading F},
        ∀ {C lambda : ENNReal},
          ∀ clustered :
              TubeParameterClusterFrostmanData F Y C lambda delta,
            C ≤ Kakeya.realRpowENN delta (-frostmanLoss) →
            lambda =
                ENNReal.ofReal (delta / 8) *
                  Kakeya.realRpowENN delta densityLoss →
            1600 * (1 + Real.log delta⁻¹) ≤
                Real.rpow delta (-gamma) →
              Kakeya.realRpowENN delta (-1 + targetLoss) ≤
                100000 * clustered.points.enncard

end Kakeya.Assouad
