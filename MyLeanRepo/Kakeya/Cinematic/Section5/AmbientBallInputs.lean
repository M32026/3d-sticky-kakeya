import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.ClusterDefinitions

/-!
# Bounded-overlap ambient ball cover

The first two-ends reduction in PYZ Section 5 is performed inside one fixed
ambient metric ball. A finite maximal net supplies those ambient balls, while
doubling bounds how many triple dilates can contain one function.
-/

namespace Kakeya.Cinematic

def FiniteAmbientBallCoverStatement : Prop :=
  ∀ {K D t : ℝ},
    1 ≤ D →
    0 < t →
    ∀ {family : Set C2Function},
      IsCinematicFamily family K D →
      ∀ (F : FiniteFunctionFamily),
        F.carrier ⊆ family →
        ∃ centers : Finset C2Function,
          (centers : Set C2Function) ⊆ F.carrier ∧
          (∀ f ∈ F.carrier,
            ∃ c ∈ centers, c2Distance f c ≤ t) ∧
          (∀ c ∈ centers, ∀ d ∈ centers, c ≠ d →
            t < c2Distance c d) ∧
          (∀ c ∈ centers,
            (F.cluster c (3 * t)).carrier ⊆ family) ∧
          (∀ c ∈ centers,
            ∀ f ∈ (F.cluster c (3 * t)).carrier,
              ∀ g ∈ (F.cluster c (3 * t)).carrier,
                c2Distance f g ≤ 6 * t) ∧
          (∑ c ∈ centers, ((F.cluster c (3 * t)).card : ℝ)) ≤
            D ^ 3 * (F.card : ℝ)

end Kakeya.Cinematic
