import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberOSDensityAbsorptionStatement

/-!
# Parameters for the projected-fiber multiplicity band

The pointwise projected-fiber cap is proportional to the indexed cardinality
of the tube family.  The lower shaded mass is proportional to the same
cardinality.  Consequently the dyadic range can be chosen with only a
logarithmic loss, uniformly under replication of indexed tubes.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
Choose a positive multiplicity threshold and a finite dyadic range whose band
loss costs at most one power of `delta^(-eta)`.

The output contains exactly the quantitative premises needed by
`ProjectedFiberBandStatement`.  In particular, it does not assume an absolute
cardinality bound or essential distinctness; both the lower mass and the
fiber cap scale with `F.enncard`.
-/
def ProjectedFiberBandParameterSelectionStatement : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧ delta₀ < 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : Kakeya.Streamlined.TubeFamily delta,
            F.Nonempty →
              ∀ Y : Kakeya.Streamlined.TubeShading F,
                Y.IsLambdaDense
                    (Kakeya.realRpowENN delta eta) →
                  ∃ threshold : ENNReal,
                    ∃ levelCount : ℕ,
                      threshold ≠ 0 ∧
                      threshold ≠ ⊤ ∧
                      Y.mass ≠ 0 ∧
                      Y.mass ≠ ⊤ ∧
                      2 *
                          (threshold *
                            volume section7ProjectionRectangle) ≤
                        Y.mass ∧
                      ENNReal.ofReal (6 * delta) * F.enncard ≤
                        threshold *
                          (2 ^ levelCount : ENNReal) ∧
                      projectedFiberBandLoss levelCount ≤
                        Kakeya.realRpowENN delta (-eta)

end Kakeya.Assouad
