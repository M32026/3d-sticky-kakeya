import MyLeanRepo.Kakeya.Cinematic.Section5.SingletonClusterCoarseCardinality

/-!
# Singleton cluster coarse cardinality from a witness subfamily

The explicit-pair Proposition 26 output bounds an outer coarse cardinality
while its tangent-count lower bounds live on a nonempty witness subfamily.
This statement separates those two roles.
-/

namespace Kakeya.Cinematic

def SingletonClusterCoarseCardinalityWitnessStatement : Prop :=
  ∀ {delta t : ℝ}
      (witness : RectangleFamily delta t)
      (coarseCard : ℕ)
      (H : FiniteFunctionFamily)
      (leftCenter rightCenter : C2Function)
      (radius tangency coefficient : ℝ),
    witness.Nonempty →
    (∀ i,
      1 ≤ RectangleFamily.tangentCount
        (witness.rectangle i)
        (H.cluster leftCenter radius) tangency ∧
      1 ≤ RectangleFamily.tangentCount
        (witness.rectangle i)
        (H.cluster rightCenter radius) tangency) →
    0 ≤ coefficient →
    (coarseCard : ℝ) ≤
      coefficient *
        (Real.rpow
            (RectangleFamily.bipartiteNormalizedCount
              (H.cluster leftCenter radius)
              (H.cluster rightCenter radius) 1 1)
            (3 / 2 : ℝ) *
          Real.log
            (RectangleFamily.bipartiteNormalizedCount
              (H.cluster leftCenter radius)
              (H.cluster rightCenter radius) 1 1)) →
    (coarseCard : ℝ) ≤
      coefficient *
        (Real.rpow (2 * (H.card : ℝ)) (3 / 2 : ℝ) *
          Real.log (2 * (H.card : ℝ)))

end Kakeya.Cinematic
