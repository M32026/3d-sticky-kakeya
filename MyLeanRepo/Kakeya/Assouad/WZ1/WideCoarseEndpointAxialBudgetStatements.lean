import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseAxialFrostman
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointAxialGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointRawCounting
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointRawBudgetAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointPowerArithmetic
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointScaleAbsorption
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointSourceBudget
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointParameterGap

/-!
# Budget split for the axial endpoint regime

Write a coarse unit normal in the common-strip frame as
`a * direction + b * perp(direction)`.  Its exact pullback has coefficients
`a` and `b / width`.  We split at

`|b| / width ≤ |a| / 2`.

In the first branch the normalized pullback is projectively transverse to
the common source strip.  It is split at
`width = tau^(3 * projectionLambda / 20)`: below that threshold use the
two-strip Frostman bound, and above it use the supplied raw-strip estimate.
In the complementary branch the exact source radius is comparable to
`width * radius / |b|`.  Split at the same power of `tau`: below that
threshold the small projective angle still gives a two-strip Frostman ball,
while above it the factor `1 / |b|` is paid for by the target
`tau^(-projectionLambda / 2)` margin while retaining a strict exponent gap.
-/

namespace Kakeya.Assouad

/-- The exact pullback is dominated by its component parallel to the common
strip direction.  Consequently its normalized source normal is projectively
transverse to the common-strip normal. -/
def WZ1WideCoarseEndpointAxialProjectiveBranch
    (direction normal : Point2) (width : ℝ) : Prop :=
  |inner ℝ normal (wz1Perp2 direction)| / width ≤
    |inner ℝ normal direction| / 2

/-- The common-strip width is in the Frostman-controlled part of the
fixed-projective-angle branch. -/
def WZ1WideCoarseEndpointAxialProjectiveSmallWidth
    {epsilon delta : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {eta : ℝ}
    (data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H) : Prop :=
  data.width ≤
    Real.rpow
      (delta / data.width)
      (3 * parameters.projectionLambda / 20)

/-- In the near-common-normal branch, the perpendicular coarse coefficient
is still below the target projection threshold. -/
def WZ1WideCoarseEndpointAxialSmallCoefficient
    {epsilon delta : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {eta : ℝ}
    (data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H)
    (normal : Point2) : Prop :=
  |inner ℝ normal (wz1Perp2 data.direction)| ≤
    Real.rpow
      (delta / data.width)
      (3 * parameters.projectionLambda / 20)

/-- The small-width, fixed-projective-angle two-strip/Frostman
source-budget leaf. -/
def WZ1WideCoarseEndpointAxialProjectiveFrostmanBudgetStatement : Prop :=
  ∀ epsilon : ℝ,
    ∀ parameters : WZ1Proposition8_9Parameters epsilon,
      0 < epsilon → epsilon < 1 →
        ∃ etaCap : ℝ, 0 < etaCap ∧
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
                  ∀ input :
                    WZ1WideCoarseEndpointLineInput
                      (ambient := ambient) (active := active)
                      parameters data,
                    ∀ normal : Point2, ‖normal‖ = 1 →
                      |inner ℝ normal
                          (wz1Perp2 data.direction)| < 1 / 2 →
                      WZ1WideCoarseEndpointAxialProjectiveBranch
                        data.direction normal data.width →
                      WZ1WideCoarseEndpointAxialProjectiveSmallWidth
                        parameters data →
                      ∀ level radius : ℝ,
                        delta / data.width ≤ radius →
                        radius ≤ 1 →
                        WZ1WideCoarseEndpointSourceBudget
                          (ambient := ambient) (active := active)
                          parameters input normal level radius

/-- The large-width raw-strip source-budget leaf in the
fixed-projective-angle regime. -/
def WZ1WideCoarseEndpointAxialProjectiveRawBudgetStatement : Prop :=
  ∀ epsilon : ℝ,
    ∀ parameters : WZ1Proposition8_9Parameters epsilon,
      0 < epsilon → epsilon < 1 →
        ∃ etaCap : ℝ, 0 < etaCap ∧
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
                  ∀ input :
                    WZ1WideCoarseEndpointLineInput
                      (ambient := ambient) (active := active)
                      parameters data,
                    ∀ normal : Point2, ‖normal‖ = 1 →
                      |inner ℝ normal
                          (wz1Perp2 data.direction)| < 1 / 2 →
                      WZ1WideCoarseEndpointAxialProjectiveBranch
                        data.direction normal data.width →
                      ¬ WZ1WideCoarseEndpointAxialProjectiveSmallWidth
                        parameters data →
                      ∀ level radius : ℝ,
                        delta / data.width ≤ radius →
                        radius ≤ 1 →
                        WZ1WideCoarseEndpointSourceBudget
                          (ambient := ambient) (active := active)
                          parameters input normal level radius

/-- The small-coefficient two-strip/Frostman source-budget leaf after the
pullback has entered the near-common-normal regime. -/
def WZ1WideCoarseEndpointAxialSmallCoefficientBudgetStatement : Prop :=
  ∀ epsilon : ℝ,
    ∀ parameters : WZ1Proposition8_9Parameters epsilon,
      0 < epsilon → epsilon < 1 →
        ∃ etaCap : ℝ, 0 < etaCap ∧
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
                  ∀ input :
                    WZ1WideCoarseEndpointLineInput
                      (ambient := ambient) (active := active)
                      parameters data,
                    ∀ normal : Point2, ‖normal‖ = 1 →
                      |inner ℝ normal
                          (wz1Perp2 data.direction)| < 1 / 2 →
                      ¬ WZ1WideCoarseEndpointAxialProjectiveBranch
                        data.direction normal data.width →
                      WZ1WideCoarseEndpointAxialSmallCoefficient
                        parameters data normal →
                      ∀ level radius : ℝ,
                        delta / data.width ≤ radius →
                        radius ≤ 1 →
                        WZ1WideCoarseEndpointSourceBudget
                          (ambient := ambient) (active := active)
                          parameters input normal level radius

/-- The large-coefficient exact-denominator/weighted-raw-strip
source-budget leaf in the complementary axial regime. -/
def WZ1WideCoarseEndpointAxialDenominatorBudgetStatement : Prop :=
  ∀ epsilon : ℝ,
    ∀ parameters : WZ1Proposition8_9Parameters epsilon,
      0 < epsilon → epsilon < 1 →
        ∃ etaCap : ℝ, 0 < etaCap ∧
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
                  ∀ input :
                    WZ1WideCoarseEndpointLineInput
                      (ambient := ambient) (active := active)
                      parameters data,
                    ∀ normal : Point2, ‖normal‖ = 1 →
                      |inner ℝ normal
                          (wz1Perp2 data.direction)| < 1 / 2 →
                      ¬ WZ1WideCoarseEndpointAxialProjectiveBranch
                        data.direction normal data.width →
                      ¬ WZ1WideCoarseEndpointAxialSmallCoefficient
                        parameters data normal →
                      ∀ level radius : ℝ,
                        delta / data.width ≤ radius →
                        radius ≤ 1 →
                        WZ1WideCoarseEndpointSourceBudget
                          (ambient := ambient) (active := active)
                          parameters input normal level radius

/-- The two exact axial source-budget leaves imply the previous axial
endpoint statement. -/
def WZ1WideCoarseEndpointAxialBudgetAssemblyStatement : Prop :=
  WZ1WideCoarseEndpointAxialProjectiveFrostmanBudgetStatement →
    WZ1WideCoarseEndpointAxialProjectiveRawBudgetStatement →
      WZ1WideCoarseEndpointAxialSmallCoefficientBudgetStatement →
        WZ1WideCoarseEndpointAxialDenominatorBudgetStatement →
          WZ1WideCoarseEndpointAxialStatement

end Kakeya.Assouad
