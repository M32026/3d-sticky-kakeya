import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberMassStatement

/-!
# Pointwise cap for twisted-projection fiber mass

For a vertical-chart tube, every horizontal slice has `y`-diameter at most
`6 * delta`.  The intersection with one exact twisted-projection fiber is a
subset of such a slice.  Summing over the indexed family therefore bounds
the integrated spatial multiplicity on every projection fiber.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The fiber-integrated multiplicity is at most one slice length per indexed
tube.

No distinctness, parameter non-concentration, compactness, or nonsingularity
is needed.  The slope function only specifies which affine line inside the
horizontal slice parametrizes the projection fiber.
-/
def ProjectedFiberMultiplicityCapStatement : Prop :=
  ∀ {delta : ℝ},
    0 < delta →
    ∀ F : Kakeya.Streamlined.TubeFamily delta,
      IsInVerticalChart F →
      ∀ Y : Kakeya.Streamlined.TubeShading F,
        ∀ f : SlopeFunction,
          ∀ q : Point2,
            projectedFiberMultiplicity Y f q ≤
              ENNReal.ofReal (6 * delta) * F.enncard

end Kakeya.Assouad
