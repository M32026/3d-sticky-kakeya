import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseLineTransferBasics

/-!
# One-endpoint line synthesis in Proposition 8.9 wide branch

The old coarse-line target tried to prove both endpoint estimates and all
parameter absorption in one theorem.  The paper-faithful reusable boundary is
one endpoint at a time: combine the ambient weighted raw strip estimate, the
common-strip geometry, the selected-source retention, and the balanced coarse
Frostman estimate.

The output retains the factor-two `projectionLambda` margin needed by the
subsequent fixed-cell normalization.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/--
Synthesize line nonconcentration for one balanced endpoint coarse set.

The affine map and rescaling parameters are fixed to the actual wide-branch
normalization; callers cannot supply a summary constant inequality.  The
active endpoint class must retain the exact worst-case density fraction
available at both real call sites:

`(((1 / 256) * delta^eta) / 16) * |ambient| ≤ |active|`.

Without this premise an arbitrary one-dimensional subset of a valid ambient
set can survive as the coarse output and violate line nonconcentration.
-/
def WZ1WideCoarseEndpointLineSynthesisStatement : Prop :=
  ∀ epsilon : ℝ,
    ∀ parameters : WZ1Proposition8_9Parameters epsilon,
    0 < epsilon → epsilon < 1 →
      ∃ etaCap : ℝ,
        0 < etaCap ∧
        ∀ eta : ℝ, 0 < eta → eta ≤ etaCap →
          ∃ delta₀ : ℝ,
            0 < delta₀ ∧ delta₀ ≤ 1 ∧
            ∀ {delta : ℝ}
              {F G₁ G₂ ambient active : DiscreteSet 2}
              {H : Finset (Point2 × Point2 × Point2)},
              0 < delta → delta ≤ delta₀ →
              ∀ data :
                WZ1Proposition8_9CommonStripData
                  delta epsilon eta parameters F G₁ G₂ H,
                Real.rpow delta (1 - epsilon / 10) <
                    data.width →
                  ∀ rawWidth : ℝ,
                    0 < rawWidth →
                    data.width ≤
                        Real.rpow delta (-parameters.stripEpsilon) *
                          rawWidth →
                    WZ1WeightedRawStripNonconcentration
                        delta parameters.zeta rawWidth
                        ((256 : ENNReal) *
                          Kakeya.realRpowENN delta (-eta))
                        ambient →
                    ambient.IsFrostman delta 1
                      (Kakeya.realRpowENN
                        delta (-parameters.workingLambda)) →
                    ambient.IsInUnitBall →
                    (∀ point ∈ ambient,
                      point ∈
                        wz1LineNeighborhood
                          data.base data.direction data.width) →
                    active ⊆ ambient →
                    (((1 / 256 : ENNReal) *
                        Kakeya.realRpowENN delta eta) / 16) *
                        ambient.enncard ≤
                      active.enncard →
                    ∀ rescale :
                      WZ1AnisotropicFrostmanRescalingData
                        active
                        (wideCoarsePhiG
                          data.direction data.width data.width_pos
                          data.base 0 data.direction_unit)
                        delta data.width
                        (parameters.stripEpsilon * eta / 10)
                        (Kakeya.realRpowENN
                          delta (-(2 * parameters.workingLambda))),
                      WZ1LineNonConcentration
                        (delta / data.width)
                        (parameters.projectionLambda / 2)
                        parameters.zeta rescale.coarse

/-- The generic endpoint theorem mechanically supplies both old endpoint fields. -/
def WZ1WideCoarseLineFromEndpointSynthesisStatement : Prop :=
  WZ1WideCoarseEndpointLineSynthesisStatement →
    WZ1Proposition8_9WideCoarseLineNonconcentrationStatement

end Kakeya.Assouad
