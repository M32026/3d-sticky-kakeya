import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockRepresentativeCinematicStatements
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.PositiveWindowStatements

/-!
# Globalize one local cinematic parameter block

The local parameter block used in Section 7 is only a certificate for the
global projected set.  It is not the final same-family shading.

The paper first restricts the original shading by a multiplicity band and an
approximately uniform subset of its twisted projection.  It then selects one
parameter block, amplifies that block, applies the cinematic estimate, and
uses projection uniformity to compare the local projected piece with the
coarse neighborhood of the global projected set.

This module freezes that missing boundary.  The continuation is quantified
over the later `c`-window, weighted parameter clusters, local block,
amplification, and cinematic pullback.  Their types preserve all source
provenance, while the explicit window-mass premise prevents an empty or
arbitrarily small local certificate from globalizing.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
The spacing loss used inside paper Lemma 7.12.

The same exponent must control the selected block scale and the outer
one-scale growth.  Replacing it by `epsilon / 100` proves only the weaker
lower bound `delta^(1 - (epsilon / 100)^2) < rho`.
-/
def parameterBlockProjectionWorkingEpsilon
    (epsilon : ℝ) : ℝ :=
  epsilon

/--
The cinematic loss is cubic in the one-scale exponent budget.

After taking `rho` to be the selected local-block scale, the quadratic
spacing losses cancel against the scale-growth lower bound.  A linear loss
such as `epsilon / 100` does not cancel and makes the final absorption false
for small `epsilon`.
-/
def parameterBlockProjectionPYZLoss
    (epsilon : ℝ) : ℝ :=
  epsilon ^ 3 / 100

/-- Per-tube mass retained before the local parameter selection in Lemma 7.12. -/
def parameterBlockProjectionPerTubeThreshold
    (delta eta : ℝ) : ENNReal :=
  (1 / 2 : ENNReal) *
    Kakeya.realRpowENN delta (4 * eta) *
      Kakeya.deltaTubeVolume delta

/--
A same-family projection-uniform refinement together with the exact
local-to-global continuation used after the cinematic pullback.

`globalShading` is the final candidate in the positive-window estimate.  The
later `windowedShading` may lose the paper's explicit `delta / 8` factor when
one `c`-window is selected.  The local pullback remains indexed by the
reindexed local family, but its type records the selected source block and
all amplification data needed to compare it with
`twistedUnion globalShading f`.
-/
structure ParameterBlockProjectionUniformData
    {delta epsilon eta rhoMax : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (C : ENNReal)
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction) where
  globalShading : Kakeya.Streamlined.TubeShading F
  subshading : IsSubshading globalShading Y
  density :
    globalShading.IsLambdaDense
      (Kakeya.realRpowENN delta (4 * eta))
  slab :
    globalShading.union ⊆ horizontalSlab 0 1
  fullShading : Kakeya.Streamlined.TubeShading F
  full_subshading : IsSubshading fullShading globalShading
  full_whole :
    IsWholeTubeSubshading fullShading globalShading
  full_mass :
    (1 / 2 : ENNReal) * globalShading.mass ≤ fullShading.mass
  full_per_tube :
    HasPerTubeMass fullShading
      (parameterBlockProjectionPerTubeThreshold delta eta)
  globalize :
    ∀ (c0 : ℝ),
      ∀ (windowedShading : Kakeya.Streamlined.TubeShading F),
      IsSubshading windowedShading fullShading →
      ENNReal.ofReal (delta / 8) * fullShading.mass ≤
        windowedShading.mass →
      IsWholeTubeSubshading windowedShading fullShading →
      (∀ i, windowedShading.carrier i ≠ ∅ →
        |(tubeParams i).c - c0| ≤ delta / 2) →
      let lambda : ENNReal :=
        ENNReal.ofReal (delta / 8) *
          Kakeya.realRpowENN delta (5 * eta)
      ∀ clustered :
          TubeParameterClusterFrostmanData
            F windowedShading C lambda delta,
        ∀ localBlock :
            ParameterLocalFullBlockData clustered
              (parameterBlockProjectionWorkingEpsilon epsilon),
          ∀ representatives :
              ParameterLocalRepresentativeBlockData localBlock,
            ∀ amplification :
                ParameterBlockAmplificationData
                  delta localBlock.blockScale
                  (1 - 20 *
                    (parameterBlockProjectionWorkingEpsilon epsilon) ^ 2)
                  localBlock.centeredPoints,
              ∀ pullback :
                    ParameterBlockRepresentativeCinematicPullbackData
                      localBlock representatives amplification f
                        (parameterBlockProjectionPYZLoss epsilon)
                        (parameterBlockProjectionPerTubeThreshold
                          delta eta),
                ∃ rho : ℝ,
                  Real.rpow delta (1 - epsilon ^ 2) < rho ∧
                    rho ≤ rhoMax ∧
                      volume (twistedUnion globalShading f) ≥
                        Kakeya.realRpowENN (delta / rho) epsilon *
                          volume
                            (Metric.cthickening rho
                              (twistedUnion globalShading f))

/--
Produce the projection-uniform continuation before selecting the local
parameter block.

The strict loss relation leaves room for multiplicity pigeonholing, inner
regularization, and the finite uniform-refinement loss.  The threshold is
chosen before the concrete family and shading.  The theorem must construct a
genuine same-family subshading; it may not return the local reindexed
pullback shading as the global output.
-/
def ParameterBlockProjectionUniformizationStatement : Prop :=
  ∀ epsilon rhoMax eta : ℝ,
    0 < epsilon → epsilon < 1 / 100 →
    0 < rhoMax → rhoMax ≤ 1 →
    1 / 100 ≤ rhoMax →
    0 < eta → 1000 * eta < epsilon ^ 3 →
      ∃ delta₀ : ℝ,
        0 < delta₀ ∧ delta₀ < 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ F : Kakeya.Streamlined.TubeFamily delta,
              F.Nonempty →
              IsInVerticalChart F →
              (∀ i : Fin F.card,
                |(tubeParams i).a| ≤ 12 ∧
                  |(tubeParams i).b| ≤ 12 ∧
                  |(tubeParams i).c| ≤ 2 ∧
                  |(tubeParams i).d| ≤ 2) →
              ∀ C : ENNReal,
                1 ≤ C →
                C ≠ ⊤ →
                C ≤ Kakeya.realRpowENN delta (-eta) →
                TubeParameterFrostmanBound F C →
                ∀ Y : Kakeya.Streamlined.TubeShading F,
                  Y.IsLambdaDense
                      (Kakeya.realRpowENN delta eta) →
                  Y.union ⊆ horizontalSlab 0 1 →
                  ∀ f : SlopeFunction,
                    f.IsNonsingular → f 0 = 0 →
                      Nonempty
                        (ParameterBlockProjectionUniformData
                          (epsilon := epsilon) (eta := eta)
                          (rhoMax := rhoMax) C Y f)

end Kakeya.Assouad
