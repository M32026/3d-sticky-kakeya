import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFullBlockStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FrostmanToKatzTaoWeightedCard

/-!
# Prune one local block from its Frostman certificate

The spacing producer supplies an exponent-`1-epsilon²` Frostman certificate
and its matching weighted-cardinality bound. Katz--Tao extraction keeps that
nonconcentration exponent, while its cardinality loss is absorbed before
recording the weaker exponent `1-20*epsilon²` needed by amplification.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Normalize a parameter block of radius `blockScale / 10` to the unit ball. -/
def normalizedParameterBlock
    (points : DiscreteSet 3)
    (center : Point 3)
    (blockScale : ℝ) :
    DiscreteSet 3 :=
  points.image fun p =>
    blockScale⁻¹ • (p - center)

/-- Fine scale after normalizing a block of radius `blockScale / 10`. -/
def normalizedParameterBlockFineScale
    (delta blockScale : ℝ) : ℝ :=
  delta / blockScale

/--
Finite-scale Hausdorff content lower bound, using covers by finitely many
closed balls with radii between `fineScale` and one.
-/
def HasFiniteScaleHausdorffContent
    {n : ℕ}
    (A : DiscreteSet n)
    (fineScale s : ℝ)
    (kappa : ENNReal) : Prop :=
  ∀ m : ℕ,
    ∀ center : Fin m → Point n,
      ∀ radius : Fin m → ℝ,
        (∀ i, fineScale ≤ radius i ∧ radius i ≤ 1) →
        (A : Set (Point n)) ⊆
          ⋃ i, Metric.closedBall (center i) (radius i) →
        kappa ≤
          ∑ i, Kakeya.realRpowENN (radius i) s

/-- The pruned full local block with exact candidate provenance. -/
structure ParameterLocalFrostmanBlockPruningData
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    (candidatePoints : DiscreteSet 3)
    (candidateCenter : Point 3)
    (candidateScale : ℝ) where
  block : ParameterLocalFullBlockData clustered epsilon
  blockScale_eq : block.blockScale = candidateScale
  localCenter_eq : block.localCenter = candidateCenter
  sourcePoints_subset_candidate :
    block.sourcePoints ⊆ candidatePoints

/--
Extract a fixed-constant Katz--Tao block from the Frostman and weighted
cardinality certificates. The Katz--Tao exponent remains `1-epsilon²`;
only the retained cardinality is recorded at exponent `1-20*epsilon²`.
-/
def ParameterLocalFrostmanBlockPruningStatement : Prop :=
  ∀ epsilon : ℝ,
    0 < epsilon →
    epsilon < 1 / 10 →
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧ delta₀ < 1 ∧
          ∀ delta : ℝ,
            0 < delta →
            delta ≤ delta₀ →
              ∀ F : Kakeya.Streamlined.TubeFamily delta,
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  ∀ C lambda : ENNReal,
                    ∀ clustered :
                        TubeParameterClusterFrostmanData
                          F Y C lambda delta,
              ∀ blockScale : ℝ,
                0 < blockScale →
                delta ≤ blockScale →
                10 * delta < blockScale →
                100 * blockScale ≤ 1 →
                Real.rpow delta (1 - epsilon ^ 2) <
                  blockScale / 10 →
                  ∀ blockCenter : Point 3,
                    ∀ candidatePoints : DiscreteSet 3,
                      candidatePoints.Nonempty →
                      candidatePoints ⊆ clustered.points →
                      (∀ p ∈ candidatePoints,
                        dist p blockCenter ≤ blockScale / 10) →
                      ∀ c0 : ℝ,
                        (∀ i,
                          clustered.shading.carrier i ≠ ∅ →
                            |(tubeParams i).c - c0| ≤ delta / 2) →
                      let fineScale : ℝ :=
                        normalizedParameterBlockFineScale
                          delta blockScale
                      let normalized : DiscreteSet 3 :=
                        normalizedParameterBlock
                          candidatePoints blockCenter blockScale
                      normalized.IsFrostman
                        fineScale
                        (1 - epsilon ^ 2)
                        (Kakeya.realRpowENN
                          fineScale (-12 * epsilon ^ 2)) →
                      Kakeya.realRpowENN
                          fineScale (-(1 - epsilon ^ 2)) ≤
                        Kakeya.realRpowENN fineScale
                            (-12 * epsilon ^ 2) *
                          normalized.enncard →
                      weightedFrostmanToKatzTaoConstant
                          (1 - epsilon ^ 2) *
                          ENNReal.ofReal
                            (1 + Real.log fineScale⁻¹) *
                          Kakeya.realRpowENN fineScale
                            (7 * epsilon ^ 2) ≤
                        100000 →
                      Nonempty
                        (ParameterLocalFrostmanBlockPruningData
                          (clustered := clustered)
                          (epsilon := epsilon)
                          candidatePoints blockCenter blockScale)

end Kakeya.Assouad
