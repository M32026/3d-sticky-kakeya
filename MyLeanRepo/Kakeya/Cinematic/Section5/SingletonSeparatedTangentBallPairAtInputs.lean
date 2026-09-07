import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Separated tangent balls from one retained tangent

When the common support is too small to divide by the number of ambient
covering balls, the normal `q`-pigeonhole is unavailable.  For the fallback
`q = 1`, one retained tangent in a covering ball and the half-mass bound on
its `11r` enlargement already force a second retained tangent outside that
enlargement.  Covering the second tangent gives the separated ball pair.
-/

namespace Kakeya.Cinematic

def SingletonSeparatedTangentBallPairAtStatement : Prop :=
  ∀ {delta t r tangency : ℝ},
    0 < r →
    ∀ (H : FiniteFunctionFamily),
      ∀ (R : RectangleFamily delta t),
        ∀ (T : Fin R.card → FiniteFunctionFamily),
          (∀ i, (T i).carrier ⊆ H.carrier) →
          ∀ (centers : Finset C2Function),
            centers.Nonempty →
            (∀ i,
              (T i).carrier ⊆
                ⋃ c ∈ centers, c2Ball c r) →
            (∀ i, (T i).carrier.Nonempty) →
            (∀ i, ∀ function ∈ (T i).carrier,
              (R.rectangle i).IsLambdaTangent
                function tangency) →
            (∀ i, ∀ c ∈ centers,
              2 * RectangleFamily.tangentCount
                    (R.rectangle i)
                    ((T i).cluster c (11 * r))
                    tangency ≤
                RectangleFamily.tangentCount
                  (R.rectangle i) (T i) tangency) →
            ∀ i,
              ∃ c ∈ centers, ∃ d ∈ centers,
                10 * r ≤ c2Distance c d ∧
                1 ≤ RectangleFamily.tangentCount
                    (R.rectangle i) (H.cluster c r)
                    tangency ∧
                1 ≤ RectangleFamily.tangentCount
                    (R.rectangle i) (H.cluster d r)
                    tangency ∧
                (H.cluster c r).AreSeparated
                  (H.cluster d r) (8 * r)

end Kakeya.Cinematic
