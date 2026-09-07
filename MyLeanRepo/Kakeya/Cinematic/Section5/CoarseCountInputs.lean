import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Normal-regime coarse rectangle count
-/

namespace Kakeya.Cinematic

/--
Apply the full robust Proposition 26 after the rectangle-dependent cluster
selection and shared-pair pigeonhole.
-/
def NormalCoarseRectangleCountStatement : Prop :=
  FiberwiseSeparatedTangentBallPairAtStatement →
    SharedTangentBallPairPigeonholeAtStatement →
    BipartiteTangencyRobustFullStatement →
      ∀ K : ℝ, 1 ≤ K →
        ∃ C : ℝ, 1 ≤ C ∧
          ∀ {family : Set C2Function},
            HasCinematicCurvature family K →
            ∀ {I : ParameterInterval},
              I.IsControlled K →
              ∀ {delta t r tangency A : ℝ},
                0 < delta →
                0 < t →
                delta ≤ t →
                t ≤ 1 →
                0 < r →
                5 ≤ tangency →
                1 ≤ A →
                t / A = 8 * r →
                delta ≤ A * t →
                ∀ (H : FiniteFunctionFamily),
                  H.carrier ⊆ family →
                  (∀ f ∈ H.carrier, ∀ g ∈ H.carrier,
                    dist f g ≤ 6 * t) →
                  ∀ (R : RectangleFamily delta t),
                    R.CentersIn family →
                    R.IsOverCentralQuarterOf I →
                    R.IsPairwiseIncomparable family 100 →
                    R.Nonempty →
                    ∀ (T : Fin R.card → FiniteFunctionFamily),
                      (∀ i, (T i).carrier ⊆ H.carrier) →
                      ∀ (centers : Finset C2Function),
                        centers.Nonempty →
                        (∀ i, (T i).carrier ⊆
                          ⋃ c ∈ centers, c2Ball c r) →
                        ∀ q : ℕ, 0 < q →
                          (∀ i,
                            2 * centers.card * q ≤
                              RectangleFamily.tangentCount
                                (R.rectangle i) (T i) tangency) →
                          (∀ i, ∀ c ∈ centers,
                            2 * RectangleFamily.tangentCount
                                  (R.rectangle i)
                                  ((T i).cluster c (11 * r))
                                  tangency ≤
                              RectangleFamily.tangentCount
                                (R.rectangle i) (T i) tangency) →
                          ∃ c ∈ centers, ∃ d ∈ centers,
                            (H.cluster c r).AreSeparated
                              (H.cluster d r) (8 * r) ∧
                            ∃ S : RectangleSubfamily R,
                              S.family.Nonempty ∧
                              (∀ j,
                                q ≤ RectangleFamily.tangentCount
                                    (S.family.rectangle j)
                                    (H.cluster c r) tangency ∧
                                q ≤ RectangleFamily.tangentCount
                                    (S.family.rectangle j)
                                    (H.cluster d r) tangency) ∧
                              (R.card : ℝ) ≤
                                (centers.card : ℝ)^2 *
                                  (C * Real.rpow tangency C *
                                    Real.rpow A C *
                                    Real.rpow
                                      (RectangleFamily.bipartiteNormalizedCount
                                        (H.cluster c r) (H.cluster d r) q q)
                                      (3 / 2 : ℝ) *
                                    Real.log
                                      (RectangleFamily.bipartiteNormalizedCount
                                        (H.cluster c r) (H.cluster d r) q q))

end Kakeya.Cinematic
