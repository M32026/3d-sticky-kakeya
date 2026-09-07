import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointAxialBudgetStatements

/-!
# Fine split of the two axial Frostman endpoint leaves

Each regime is separated into:

* a finite two-strip geometry/counting statement, conditional on the
  resulting Frostman ball having radius at most one;
* an asymptotic scalar statement proving that radius side condition and
  paying the explicit coefficient from the target projection power.
-/

namespace Kakeya.Assouad

open scoped ENNReal

noncomputable def wideCoarseEndpointSourceRawRadius
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H)
    (normal : Point2) (radius : ℝ) : ℝ :=
  max delta
    ((radius + delta / data.width) /
      ‖wideCoarsePhiGPullbackVector
        data.direction data.width normal‖)

noncomputable def wideCoarseEndpointProjectiveFrostmanBallRadius
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H)
    (normal : Point2) (radius : ℝ) : ℝ :=
  6 * max data.width
    (wideCoarseEndpointSourceRawRadius data normal radius)

noncomputable def wideCoarseEndpointSmallCoefficientTheta
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H)
    (normal : Point2) : ℝ :=
  |inner ℝ normal data.direction| /
    ‖wideCoarsePhiGPullbackVector
      data.direction data.width normal‖

noncomputable def wideCoarseEndpointSmallCoefficientFrostmanBallRadius
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H)
    (normal : Point2) (radius : ℝ) : ℝ :=
  6 * max data.width
      (wideCoarseEndpointSourceRawRadius data normal radius) /
    wideCoarseEndpointSmallCoefficientTheta data normal

noncomputable def wideCoarseEndpointFrostmanCoefficient
    {epsilon eta delta : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    {F G₁ G₂ ambient active : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    (input :
      WZ1WideCoarseEndpointLineInput
        (ambient := ambient) (active := active)
        parameters data)
    (ballRadius : ℝ) : ENNReal :=
  Kakeya.realRpowENN delta (-parameters.workingLambda) *
    Kakeya.realRpowENN ballRadius 1 *
    (wideCoarseEndpointActiveFraction delta eta)⁻¹ *
    (wideCoarseEndpointRescaleFraction
      delta data.width
      (parameters.stripEpsilon * eta / 10))⁻¹ *
    2

noncomputable def wideCoarseEndpointTargetCoefficient
    {epsilon eta delta : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H)
    (radius : ℝ) : ENNReal :=
  Kakeya.realRpowENN
    (Real.rpow
        (delta / data.width)
        (-(parameters.projectionLambda / 2)) *
      radius)
    parameters.zeta

def WZ1WideCoarseEndpointFrostmanCountBound
    {epsilon eta delta : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    {F G₁ G₂ ambient active : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    (input :
      WZ1WideCoarseEndpointLineInput
        (ambient := ambient) (active := active)
        parameters data)
    (normal : Point2) (level radius ballRadius : ℝ) : Prop :=
  let pullback :=
    wideCoarsePhiGPullbackVector
      data.direction data.width normal
  let sourceNormal := (1 / ‖pullback‖) • pullback
  let sourceLevel :=
    (level -
      inner ℝ
        (wideCoarsePhiG
          data.direction data.width data.width_pos
          data.base 0 data.direction_unit 0)
        normal) /
      ‖pullback‖
  let rawRadius :=
    wideCoarseEndpointSourceRawRadius data normal radius
  ((input.rescale.selected.filter fun point =>
      |inner ℝ point sourceNormal - sourceLevel| ≤
        rawRadius).card : ENNReal) ≤
    wideCoarseEndpointFrostmanCoefficient
        parameters input ballRadius *
      (input.rescale.fiberMultiplicity : ENNReal) *
      input.rescale.coarse.enncard

def WZ1WideCoarseEndpointProjectiveFrostmanCountStatement : Prop :=
  ∀ {epsilon eta delta : ℝ},
    ∀ {F G₁ G₂ ambient active : DiscreteSet 2},
      ∀ {H : Finset (Point2 × Point2 × Point2)},
        ∀ parameters : WZ1Proposition8_9Parameters epsilon,
          0 < delta →
          ∀ data :
            WZ1Proposition8_9CommonStripData
              delta epsilon eta parameters F G₁ G₂ H,
            ∀ input :
              WZ1WideCoarseEndpointLineInput
                (ambient := ambient) (active := active)
                parameters data,
              ∀ normal : Point2, ‖normal‖ = 1 →
                |inner ℝ normal (wz1Perp2 data.direction)| < 1 / 2 →
                WZ1WideCoarseEndpointAxialProjectiveBranch
                  data.direction normal data.width →
                WZ1WideCoarseEndpointAxialProjectiveSmallWidth
                  parameters data →
                ∀ level radius : ℝ,
                  delta / data.width ≤ radius →
                  wideCoarseEndpointProjectiveFrostmanBallRadius
                      data normal radius ≤ 1 →
                    WZ1WideCoarseEndpointFrostmanCountBound
                      parameters input normal level radius
                      (wideCoarseEndpointProjectiveFrostmanBallRadius
                        data normal radius)

def WZ1WideCoarseEndpointProjectiveFrostmanScalarStatement : Prop :=
  ∀ epsilon : ℝ,
    ∀ parameters : WZ1Proposition8_9Parameters epsilon,
      0 < epsilon → epsilon < 1 →
        ∃ etaCap : ℝ, 0 < etaCap ∧
          ∀ eta : ℝ, 0 < eta → eta ≤ etaCap →
            ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
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
                      ∀ radius : ℝ,
                        delta / data.width ≤ radius →
                        radius ≤ 1 →
                        ¬ (2 : ENNReal) ≤
                          wideCoarseEndpointTargetCoefficient
                            parameters data radius →
                          wideCoarseEndpointProjectiveFrostmanBallRadius
                              data normal radius ≤ 1 ∧
                            wideCoarseEndpointFrostmanCoefficient
                                parameters input
                                (wideCoarseEndpointProjectiveFrostmanBallRadius
                                  data normal radius) ≤
                              wideCoarseEndpointTargetCoefficient
                                parameters data radius

def WZ1WideCoarseEndpointSmallCoefficientFrostmanCountStatement : Prop :=
  ∀ {epsilon eta delta : ℝ},
    ∀ {F G₁ G₂ ambient active : DiscreteSet 2},
      ∀ {H : Finset (Point2 × Point2 × Point2)},
        ∀ parameters : WZ1Proposition8_9Parameters epsilon,
          0 < delta →
          ∀ data :
            WZ1Proposition8_9CommonStripData
              delta epsilon eta parameters F G₁ G₂ H,
            ∀ input :
              WZ1WideCoarseEndpointLineInput
                (ambient := ambient) (active := active)
                parameters data,
              ∀ normal : Point2, ‖normal‖ = 1 →
                |inner ℝ normal (wz1Perp2 data.direction)| < 1 / 2 →
                ¬ WZ1WideCoarseEndpointAxialProjectiveBranch
                  data.direction normal data.width →
                WZ1WideCoarseEndpointAxialSmallCoefficient
                  parameters data normal →
                ∀ level radius : ℝ,
                  delta / data.width ≤ radius →
                  wideCoarseEndpointSmallCoefficientFrostmanBallRadius
                      data normal radius ≤ 1 →
                    WZ1WideCoarseEndpointFrostmanCountBound
                      parameters input normal level radius
                      (wideCoarseEndpointSmallCoefficientFrostmanBallRadius
                        data normal radius)

def WZ1WideCoarseEndpointSmallCoefficientFrostmanScalarStatement : Prop :=
  ∀ epsilon : ℝ,
    ∀ parameters : WZ1Proposition8_9Parameters epsilon,
      0 < epsilon → epsilon < 1 →
        ∃ etaCap : ℝ, 0 < etaCap ∧
          ∀ eta : ℝ, 0 < eta → eta ≤ etaCap →
            ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
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
                      ∀ radius : ℝ,
                        delta / data.width ≤ radius →
                        radius ≤ 1 →
                        ¬ (2 : ENNReal) ≤
                          wideCoarseEndpointTargetCoefficient
                            parameters data radius →
                          wideCoarseEndpointSmallCoefficientFrostmanBallRadius
                              data normal radius ≤ 1 ∧
                            wideCoarseEndpointFrostmanCoefficient
                                parameters input
                                (wideCoarseEndpointSmallCoefficientFrostmanBallRadius
                                  data normal radius) ≤
                              wideCoarseEndpointTargetCoefficient
                                parameters data radius

end Kakeya.Assouad
