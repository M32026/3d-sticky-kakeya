import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterBlockTranslation

/-!
# Local parameter-block translation amplification

Section 7 does not pay the cardinality ratio between a local Katz--Tao subset
and the entire weighted center set.  It translates one local pattern into
many disjoint parameter blocks, applies the cinematic estimate to their
union, and pulls the resulting area bound back to the original block using
fiberwise translation invariance.

This module freezes only that missing combinatorial/geometric package.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- The disjoint translated copies of one local parameter pattern. -/
def amplifiedParameterSet
    (points : DiscreteSet 3) (translations : DiscreteSet 3) :
    DiscreteSet 3 :=
  translations.biUnion (translateParameterSet points)

/--
Data produced by the finite-set version of Section 7's `lem: construct`.
-/
structure ParameterBlockAmplificationData
    (fineScale blockScale s : ℝ)
    (localPoints : DiscreteSet 3) where
  translations : DiscreteSet 3
  translations_nonempty : translations.Nonempty
  translations_card_lower :
    Kakeya.realRpowENN blockScale (-1) ≤
      100000 * translations.enncard
  translations_card_upper :
    translations.enncard ≤
      8 * Kakeya.realRpowENN blockScale (-1)
  translated_disjoint :
    Set.PairwiseDisjoint
      (translations : Set (Point 3))
      (translateParameterSet localPoints)
  amplified : DiscreteSet 3
  amplified_eq :
    amplified =
      amplifiedParameterSet localPoints translations
  amplified_in_unitBall :
    amplified.IsInUnitBall
  amplified_half :
    ∀ p ∈ amplified,
      |p 0| ≤ 1 / 2 ∧
        |p 1| ≤ 1 / 2 ∧
        |p 2| ≤ 1 / 2
  amplified_katzTao :
    amplified.IsKatzTao fineScale 1 100000
  amplified_card_lower :
    Kakeya.realRpowENN (blockScale / fineScale) s *
        Kakeya.realRpowENN blockScale (-1) ≤
      10000000000 * amplified.enncard
  amplified_card_eq :
    amplified.enncard =
      translations.enncard * localPoints.enncard
  copy_source :
    ∀ v ∈ translations,
      ∀ p ∈ localPoints,
        p + v ∈ amplified

/--
Produce the local-block translation amplification package.

The local pattern already satisfies the Katz--Tao condition at the fine
scale, lies inside one block of radius `blockScale / 10`, and has the full
local cardinality `(blockScale / fineScale)^s` up to the displayed absolute
constant.  As in paper Lemma 7.11, the proof places approximately
`blockScale⁻¹` disjoint copies at spacing comparable to
`blockScale^(1/3)`.  Their union is a one-dimensional Katz--Tao set; the
cardinality lower bound is kept in the direct product form
`(blockScale / fineScale)^s * blockScale⁻¹`.  It may not use a crude ratio
between this local pattern and an unrelated ambient set.
-/
def ParameterBlockAmplificationStatement : Prop :=
  ∀ fineScale blockScale ktExponent s : ℝ,
    0 < fineScale →
    fineScale ≤ blockScale →
    100 * blockScale ≤ 1 →
    0 < ktExponent →
    ktExponent ≤ 1 →
    0 < s →
    s ≤ ktExponent →
    ∀ localCenter : Point 3,
      dist localCenter 0 ≤ 1 / 2 →
      ∀ localPoints : DiscreteSet 3,
        localPoints.Nonempty →
        (∀ p ∈ localPoints,
          dist p localCenter ≤ blockScale / 10) →
        localPoints.IsKatzTao fineScale ktExponent 100 →
        Kakeya.realRpowENN
            (blockScale / fineScale) s ≤
          100000 * localPoints.enncard →
        Nonempty
          (ParameterBlockAmplificationData
            fineScale blockScale s localPoints)

end Kakeya.Assouad
