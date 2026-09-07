import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseCountAlgebra

/-!
# Coarse cardinality from singleton cluster counts

In the `q_cluster = 1` branch, nonempty rectangle-wise tangent clusters force
the bipartite normalized count to be at least two.  Since both clusters lie in
one ambient finite family, the same count is at most twice the ambient
cardinality.  This statement isolates the monotone transfer of the
`N^(3/2) * log N` factor between those two bounds.
-/

noncomputable section

namespace Kakeya.Cinematic

def SingletonClusterCoarseCardinalityStatement : Prop :=
  ∀ {delta t : ℝ}
      (R : RectangleFamily delta t)
      (H : FiniteFunctionFamily)
      (leftCenter rightCenter : C2Function)
      (radius tangency coefficient : ℝ),
    R.Nonempty →
    (∀ i,
      1 ≤ RectangleFamily.tangentCount
        (R.rectangle i) (H.cluster leftCenter radius) tangency ∧
      1 ≤ RectangleFamily.tangentCount
        (R.rectangle i) (H.cluster rightCenter radius) tangency) →
    0 ≤ coefficient →
    (R.card : ℝ) ≤
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
    (R.card : ℝ) ≤
      coefficient *
        (Real.rpow (2 * (H.card : ℝ)) (3 / 2 : ℝ) *
          Real.log (2 * (H.card : ℝ)))

end Kakeya.Cinematic
