import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Finite density-test nets for bounded tube families

The random-motion union bound needs a finite family of convex test sets fixed
before the random translations are sampled.  The test family must retain the
fact that the moving bodies are `δ`-tubes; support containment and a lower
volume bound alone do not give the polynomial-size net used in the paper.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined.RandomTranslation

/--
A tube-specific finite test family.  Density control on the displayed convex
sets controls `deltaMax` for every `δ`-tube family in the radius-10 ball.
-/
structure TubeDensityTestNet (δ : ℝ) where
  testSets : Finset (Set Point3)
  testSets_convex : ∀ K ∈ testSets, Convex ℝ K
  testSets_measurable : ∀ K ∈ testSets, MeasurableSet K
  testSets_volume_pos : ∀ K ∈ testSets, 0 < volume K
  testSets_volume_ne_top : ∀ K ∈ testSets, volume K ≠ ⊤
  testSets_supported :
    ∀ K ∈ testSets, K ⊆ Metric.closedBall (0 : Point3) 20
  testSets_closed : ∀ K ∈ testSets, IsClosed K
  lossFactor : ENNReal
  one_le_lossFactor : 1 ≤ lossFactor
  lossFactor_ne_top : lossFactor ≠ ⊤
  density_suffices :
    ∀ G : TubeFamily δ,
      (∀ i, (G.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 10) →
      ∀ C : ENNReal,
        (∀ K ∈ testSets, G.toBodyFamily.density K ≤ C) →
        G.toBodyFamily.deltaMax ≤ lossFactor * C

/--
There is a universal polynomial-size tube-specific density-test net with
uniform finite loss.
-/
def TubeDensityTestNetStatement : Prop :=
  ∃ A : ℕ, 0 < A ∧
    ∃ L : ENNReal, 1 ≤ L ∧ L ≠ ⊤ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ∃ net : TubeDensityTestNet δ,
          net.lossFactor ≤ L ∧
          (net.testSets.card : ℝ) ≤ (1 / δ) ^ A

end Kakeya.Streamlined.RandomTranslation
