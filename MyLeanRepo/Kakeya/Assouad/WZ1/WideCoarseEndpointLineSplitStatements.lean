import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointLineStatements

/-!
# Restricted-normal leaves for wide coarse endpoint line synthesis

The exact affine pullback has two genuinely different normal regimes.  This
module freezes them separately while keeping the supplied raw strip width,
ambient/active provenance, affine map, and rescaling package unchanged.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- All fixed data supplied to one call of the endpoint synthesis theorem. -/
structure WZ1WideCoarseEndpointLineInput
    {epsilon eta delta : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    {F G₁ G₂ ambient active : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H) where
  width_large :
    Real.rpow delta (1 - epsilon / 10) < data.width
  rawWidth : ℝ
  rawWidth_pos : 0 < rawWidth
  width_le_raw :
    data.width ≤
      Real.rpow delta (-parameters.stripEpsilon) * rawWidth
  raw_nonconcentration :
    WZ1WeightedRawStripNonconcentration
      delta parameters.zeta rawWidth
      ((256 : ENNReal) * Kakeya.realRpowENN delta (-eta))
      ambient
  ambient_frostman :
    ambient.IsFrostman delta 1
      (Kakeya.realRpowENN
        delta (-parameters.workingLambda))
  ambient_ball : ambient.IsInUnitBall
  ambient_strip :
    ∀ point ∈ ambient,
      point ∈
        wz1LineNeighborhood
          data.base data.direction data.width
  active_subset : active ⊆ ambient
  active_retention :
    (((1 / 256 : ENNReal) *
        Kakeya.realRpowENN delta eta) / 16) *
        ambient.enncard ≤
      active.enncard
  rescale :
    WZ1AnisotropicFrostmanRescalingData
      active
      (wideCoarsePhiG
        data.direction data.width data.width_pos
        data.base 0 data.direction_unit)
      delta data.width
      (parameters.stripEpsilon * eta / 10)
      (Kakeya.realRpowENN
        delta (-(2 * parameters.workingLambda)))

/-- The line-nonconcentration conclusion restricted to one test normal. -/
def WZ1WideCoarseEndpointNormalBound
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
    (normal : Point2) : Prop :=
  ∀ level radius : ℝ,
    delta / data.width ≤ radius →
    radius ≤ 1 →
      ((input.rescale.coarse.filter fun point =>
        |inner ℝ point normal - level| ≤ radius).card :
          ENNReal) ≤
        Kakeya.realRpowENN
            (Real.rpow
              (delta / data.width)
              (-(parameters.projectionLambda / 2)) *
              radius)
            parameters.zeta *
          input.rescale.coarse.enncard

/--
The exact-pullback transverse-coefficient leaf.

The coefficient is measured in the common-strip frame.  This regime retains
the `width` gain in the denominator
`‖wideCoarsePhiGPullbackVector direction width normal‖`; the supplied
`rawWidth` may not be replaced by an independently chosen value.
-/
def WZ1WideCoarseEndpointTransverseStatement : Prop :=
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
                      1 / 2 ≤
                        |inner ℝ normal
                          (wz1Perp2 data.direction)| →
                      WZ1WideCoarseEndpointNormalBound
                        (ambient := ambient) (active := active)
                        parameters input normal

/--
The exact-pullback axial-coefficient leaf.

The coarse normal has a small perpendicular-frame coefficient, but after
pullback that coefficient is divided by `width`.  The proof must therefore
split again using the actual normalized pullback angle: use the intersection
with the supplied common source strip and ambient Frostman control in the
projectively transverse subcase, and use the exact denominator/radius gain in
the nearly parallel subcase.  It may not weaken away that denominator.
-/
def WZ1WideCoarseEndpointAxialStatement : Prop :=
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
                      WZ1WideCoarseEndpointNormalBound
                        (ambient := ambient) (active := active)
                        parameters input normal

/-- The two restricted-normal leaves imply the original frozen endpoint API. -/
def WZ1WideCoarseEndpointLineSplitAssemblyStatement : Prop :=
  WZ1WideCoarseEndpointTransverseStatement →
    WZ1WideCoarseEndpointAxialStatement →
      WZ1WideCoarseEndpointLineSynthesisStatement

end Kakeya.Assouad
