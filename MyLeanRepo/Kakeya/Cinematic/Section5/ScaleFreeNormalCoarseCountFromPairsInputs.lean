import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseCountFromPairsInputs

/-!
# Scale-free normal coarse count from explicit cluster pairs

The normalized explicit-pair theorem assumes the coarse rectangle second
parameter is at most one.  Positive vertical scaling preserves all cluster
pair witnesses, tangent counts, normalized counts, finite cardinalities, and
the geometric scale identity.  This statement transfers the normalized
result back to an arbitrary positive second parameter.
-/

namespace Kakeya.Cinematic

def ScaleFreeNormalCoarseRectangleCountFromPairsStatement : Prop :=
  SharedTangentBallPairPigeonholeAtStatement →
    BipartiteTangencyRobustFullStatement →
    NormalCoarseRectangleCountFromPairsStatement →
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
                  ∀ (centers : Finset C2Function),
                    centers.Nonempty →
                    ∀ q : ℕ, 0 < q →
                      (∀ i,
                        ∃ c ∈ centers, ∃ d ∈ centers,
                          10 * r ≤ c2Distance c d ∧
                          q ≤ RectangleFamily.tangentCount
                              (R.rectangle i)
                              (H.cluster c r) tangency ∧
                          q ≤ RectangleFamily.tangentCount
                              (R.rectangle i)
                              (H.cluster d r) tangency ∧
                          (H.cluster c r).AreSeparated
                            (H.cluster d r) (8 * r)) →
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
                                    (H.cluster c r)
                                    (H.cluster d r) q q)
                                  (3 / 2 : ℝ) *
                                Real.log
                                  (RectangleFamily.bipartiteNormalizedCount
                                    (H.cluster c r)
                                    (H.cluster d r) q q))

end Kakeya.Cinematic
