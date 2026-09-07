import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockCinematicStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterLocalRepresentativeBlock

/-!
# Cinematic pullback for one representative tube per local parameter

Paper Lemma 7.12 applies the cinematic estimate to a set of collapsed
`(a,b,d)` parameters.  The copied family must therefore contain one actual
source tube for each selected local parameter, not every indexed tube assigned
to the same parameter center.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- Absolute cinematic assignment cap after one-tube-per-parameter reindexing. -/
def parameterBlockRepresentativeCopiedFiberCap : ENNReal :=
  12500000

/-- The representative copied-shading pullback used in paper Lemma 7.12. -/
structure ParameterBlockRepresentativeCinematicPullbackData
    {delta epsilon : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C lambda : ENNReal}
    {clustered :
      TubeParameterClusterFrostmanData F Y C lambda delta}
    (localBlock : ParameterLocalFullBlockData clustered epsilon)
    (representatives : ParameterLocalRepresentativeBlockData localBlock)
    (amplification :
      ParameterBlockAmplificationData
        delta localBlock.blockScale
        (1 - 20 * epsilon ^ 2) localBlock.centeredPoints)
    (f : SlopeFunction)
    (pyzLoss : ℝ)
    (perTubeThreshold : ENNReal) where
  shading :
    Kakeya.Streamlined.TubeShading
      (parameterLocalRepresentativeFamily representatives)
  subshading :
    IsSubshading shading
      (parameterLocalRepresentativeShading representatives)
  half_representative_mass :
    (1 / 2 : ENNReal) *
        (parameterLocalRepresentativeShading representatives).mass ≤
      shading.mass
  mass_lower :
    (1 / 2 : ENNReal) *
        (perTubeThreshold * localBlock.sourcePoints.enncard) ≤
      shading.mass
  volume_lower :
    volume (twistedUnion shading f) ≥
      (((amplification.translations.enncard * shading.mass /
            ENNReal.ofReal (20 * delta)) /
          (parameterBlockRepresentativeCopiedFiberCap *
            ENNReal.ofReal
              (Real.rpow delta (-pyzLoss)))) ^ 3) /
        amplification.translations.enncard

/--
Copy the representative local shading, apply the cinematic estimate, and pull
the projected area back to the source representative block.

The assignment fiber cap is absolute because translated local parameter
copies are disjoint and `representatives.sourceIndex` is injective.  Indexed
duplicates in the ambient family never enter this copied cinematic family.
-/
def ParameterBlockRepresentativeCinematicPullbackStatement : Prop :=
  HalfParameterCinematicPYZGeneralStatement →
    CompactSubshadingSelectionStatement →
      CompactTubeTwistedProjectionAreaStatement →
        AssignedCurveProjectionContainmentFromVerticalChartStatement →
          ∀ epsilon pyzLoss : ℝ,
            0 < epsilon → epsilon < 1 / 10 →
            0 < pyzLoss →
              ∃ delta₀ : ℝ,
                0 < delta₀ ∧ delta₀ < 1 ∧
                ∀ delta : ℝ,
                  0 < delta → delta ≤ delta₀ →
                  ∀ F : Kakeya.Streamlined.TubeFamily delta,
                    IsInVerticalChart F →
                    ∀ Y : Kakeya.Streamlined.TubeShading F,
                      ∀ C lambda : ENNReal,
                        ∀ clustered :
                            TubeParameterClusterFrostmanData
                              F Y C lambda delta,
                          clustered.shading.union ⊆ horizontalSlab 0 1 →
                          ∀ localBlock :
                              ParameterLocalFullBlockData
                                clustered epsilon,
                            ∀ representatives :
                                ParameterLocalRepresentativeBlockData
                                  localBlock,
                              ∀ amplification :
                                  ParameterBlockAmplificationData
                                    delta localBlock.blockScale
                                    (1 - 20 * epsilon ^ 2)
                                    localBlock.centeredPoints,
                                ∀ perTubeThreshold : ENNReal,
                                  perTubeThreshold ≠ 0 →
                                  perTubeThreshold ≠ ⊤ →
                                  HasPerTubeMass
                                    clustered.shading perTubeThreshold →
                                  ∀ f : SlopeFunction,
                                    f.IsNonsingular → f 0 = 0 →
                                    Nonempty
                                      (ParameterBlockRepresentativeCinematicPullbackData
                                        localBlock representatives
                                        amplification f pyzLoss
                                        perTubeThreshold)

end Kakeya.Assouad
