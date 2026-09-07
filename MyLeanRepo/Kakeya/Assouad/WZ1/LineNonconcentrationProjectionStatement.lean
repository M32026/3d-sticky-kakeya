import MyLeanRepo.Kakeya.Assouad.WZ1.DiscreteToSmoothedThinTubesStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.OSWCommonSimilarityTransportStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.SharpSmoothedFrostmanStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedToDiscreteThinTubesStatement

/-!
# WZ1 Proposition 41

Weak non-concentration near lines implies a large dot-difference projection.
All OSW/discretization bridges are explicit inputs.
-/

namespace Kakeya.Assouad

/--
WZ1 Proposition 41 in the finite-set model.

For fixed `epsilon`, the Frostman loss exponent `lambda` is chosen before
`zeta`; hence `lambda` depends only on `epsilon`, exactly as in the paper.
The graph-density exponent `alpha` and the scale threshold may also depend on
`zeta`.

The proof route is fixed:
1. apply Lemma 44 in both ordered directions;
2. normalize both sets by one common similarity;
3. transport the discrete witnesses and Frostman estimates;
4. smooth, use the sharp all-scale ball bound, and iterate OSW one step at a
   time until reaching exponent `1 - epsilon / 16`;
5. lower the measure exponent to that target, unsmooth, transport back, and
   upgrade the discrete exponent to one;
6. apply Lemma 40 and absorb all fixed powers and constants by shrinking
   `lambda`, `alpha`, and `delta₀`.
-/
def WZ1LineNonconcentrationProjectionStatement : Prop :=
  RadialBootstrappingMeasureThinTubesInput →
  WZ1QuarterThinTubesStatement →
  WZ1ThinTubesLargeDotProductStatement →
  WZ1OSWSupportNormalizationStatement →
  WZ1OSWCommonSimilarityTransportStatement →
  WZ1DiscreteToSmoothedThinTubesStatement →
  WZ1SharpSmoothedFrostmanStatement →
  WZ1SmoothedToDiscreteThinTubesStatement →
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 →
      ∃ lambda : ℝ, 0 < lambda ∧
        ∀ zeta : ℝ, 0 < zeta → zeta < 1 →
          ∃ alpha delta₀ : ℝ,
            0 < alpha ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
            ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
              ∀ F G₁ G₂ : DiscreteSet 2,
                F.Nonempty → G₁.Nonempty → G₂.Nonempty →
                F.IsInUnitBall →
                G₁.IsInUnitBall →
                G₂.IsInUnitBall →
                F.IsDeltaSeparated delta →
                G₁.IsDeltaSeparated delta →
                G₂.IsDeltaSeparated delta →
                F.IsFrostman delta 1
                  (Kakeya.realRpowENN delta (-lambda)) →
                G₁.IsFrostman delta 1
                  (Kakeya.realRpowENN delta (-lambda)) →
                G₂.IsFrostman delta 1
                  (Kakeya.realRpowENN delta (-lambda)) →
                WZ1StandardSeparation F G₁ G₂ →
                WZ1LineNonConcentration delta lambda zeta G₁ →
                WZ1LineNonConcentration delta lambda zeta G₂ →
                  ∀ H : Finset (Point2 × Point2 × Point2),
                    WZ1UniformTripleDensity
                        (Kakeya.realRpowENN delta alpha)
                        F G₁ G₂ H →
                      Kakeya.realRpowENN delta (epsilon - 1) ≤
                        (↑(Metric.externalCoveringNumber
                          (Real.toNNReal delta)
                          (wz1DotDifferenceSet H)) : ENNReal)

end Kakeya.Assouad
