import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FirstCrossing
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FrostmanToKatzTaoWeightedCard
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.MultiscaleCardinalityUniformRefinement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalFrostmanBlockPruningStatement

/-!
# Candidate local parameter block from the spacing profile

This is the paper's spacing-lemma producer before the final
Frostman-to-Katz--Tao pruning.  It uniformizes the collapsed center set,
selects the first scale-profile crossing, and returns one local block whose
affine normalization has the stronger exponent-`1-epsilon²` Frostman
certificate.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Candidate block produced by the multiscale spacing argument. -/
structure ParameterLocalSpacingCandidateData
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    (clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta) where
  blockScale : ℝ
  blockScale_pos : 0 < blockScale
  ten_delta_lt : 10 * delta < blockScale
  blockScale_small : 100 * blockScale ≤ 1
  separated_scale :
    Real.rpow delta (1 - epsilon ^ 2) <
      blockScale / 10
  blockCenter : Point 3
  points : DiscreteSet 3
  points_nonempty : points.Nonempty
  points_subset : points ⊆ clustered.points
  points_containment :
    ∀ p ∈ points,
      dist p blockCenter ≤ blockScale / 10
  normalized_frostman :
    let fineScale : ℝ :=
      normalizedParameterBlockFineScale delta blockScale
    let normalized : DiscreteSet 3 :=
      normalizedParameterBlock points blockCenter blockScale
    normalized.IsFrostman
      fineScale
      (1 - epsilon ^ 2)
      (Kakeya.realRpowENN fineScale (-12 * epsilon ^ 2))
  normalized_cardinality :
    let fineScale : ℝ :=
      normalizedParameterBlockFineScale delta blockScale
    let normalized : DiscreteSet 3 :=
      normalizedParameterBlock points blockCenter blockScale
    Kakeya.realRpowENN
        fineScale (-(1 - epsilon ^ 2)) ≤
      Kakeya.realRpowENN fineScale
          (-12 * epsilon ^ 2) *
        normalized.enncard
  normalized_extraction_absorption :
    let fineScale : ℝ :=
      normalizedParameterBlockFineScale delta blockScale
    weightedFrostmanToKatzTaoConstant
          (1 - epsilon ^ 2) *
        ENNReal.ofReal (1 + Real.log fineScale⁻¹) *
        Kakeya.realRpowENN fineScale
          (7 * epsilon ^ 2) ≤
      100000

/--
Construct the local Frostman candidate required by
`ParameterLocalFrostmanBlockPruningStatement`.

The input only assumes the replication-invariant clustered package and its
near-one-dimensional cardinality lower bound.  The conclusion records the
local normalized Frostman, weighted-cardinality, and extraction-absorption
certificates used by the downstream pruning theorem.  It deliberately does not
compare the selected block with the full ambient point count: that stronger
claim is absent from paper Lemma 7.10 and fails for higher-dimensional ambient
parameter sets.

The proof must use the multiscale uniform tree and the first-crossing
arithmetic; an arbitrary dense cube or a bad-root/minimal-cube argument does
not provide the normalized Frostman certificate.
-/
def ParameterLocalSpacingCandidateStatement : Prop :=
  ScaleProfileCrossingStatement →
    ∀ epsilon : ℝ,
      0 < epsilon →
      epsilon < 1 / 10 →
        ∃ etaMax delta₀ : ℝ,
          0 < etaMax ∧
          etaMax ≤ epsilon ^ 2 / 1000 ∧
          0 < delta₀ ∧
          delta₀ < 1 ∧
            ∀ eta : ℝ,
              0 < eta →
              eta ≤ etaMax →
                ∀ delta : ℝ,
                  0 < delta →
                  delta ≤ delta₀ →
                    ∀ F : Kakeya.Streamlined.TubeFamily delta,
                      ∀ Y : Kakeya.Streamlined.TubeShading F,
                        ∀ C lambda : ENNReal,
                          ∀ clustered :
                              TubeParameterClusterFrostmanData
                                F Y C lambda delta,
                            Kakeya.realRpowENN
                                delta (-1 + eta) ≤
                              100000 * clustered.points.enncard →
                              Nonempty
                                (ParameterLocalSpacingCandidateData
                                  (epsilon := epsilon) clustered)

end Kakeya.Assouad
