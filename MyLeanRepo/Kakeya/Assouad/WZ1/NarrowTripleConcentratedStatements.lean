import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadConcentrationStatements

/-!
# Final triple-concentrated leaf in the narrow Proposition 8.9 branch

All finite pigeonholing and the two spread alternatives have already been
performed before this boundary.  The remaining package records one actual
concentrated `G₁` fiber, one actual concentrated `G₂` subfiber, and one actual
concentrated first-coordinate fiber over a fixed endpoint pair.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- The exact obstruction left after all three dot-value dichotomies
concentrate and the endpoint displacement is non-transverse to the common
strip direction. -/
structure WZ1NarrowTripleConcentratedData
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H)
    (concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon data.width
        data.selectedF data.selectedG₁ data.selectedG₂
        data.refinedH data.direction) where
  second : Point2
  second_mem : second ∈ concentration.points
  thirdPoints : DiscreteSet 2
  thirdPoints_subset : thirdPoints ⊆ data.selectedG₂
  thirdPoints_card :
    2 * Kakeya.realRpowENN delta (epsilon - 1) ≤
      (thirdPoints.card : ENNReal)
  thirdBase : Point2
  thirdPoints_strip :
    ∀ third ∈ thirdPoints,
      third ∈
        wz1LineNeighborhood thirdBase data.direction delta
  thirdLongitudinalCenter : ℝ
  thirdPoints_longitudinal :
    ∀ third ∈ thirdPoints,
      |inner ℝ third data.direction - thirdLongitudinalCenter| ≤
        delta / (4 * data.width)
  thirdDotCenter : ℝ
  thirdPoints_dot_concentrated :
    ∀ third ∈ thirdPoints,
      |inner ℝ concentration.first (second - third) -
          thirdDotCenter| ≤ delta
  thirdPoints_actual :
    ∀ third ∈ thirdPoints,
      (concentration.first, second, third) ∈ data.refinedH
  rawThirdMargin :
    WZ1NarrowRawFiberMargin
      delta epsilon data.width data.selectedG₂ thirdPoints
      data.direction thirdLongitudinalCenter
      (fun third =>
        (concentration.first, second, third) ∈ data.refinedH)
      (fun third =>
        inner ℝ concentration.first (second - third))
      thirdDotCenter
  third : Point2
  third_mem : third ∈ thirdPoints
  firstPoints : DiscreteSet 2
  firstPoints_subset : firstPoints ⊆ data.selectedF
  firstPoints_card :
    192 * Real.rpow delta (9 * epsilon / 10 - 1) ≤
      (firstPoints.card : ℝ)
  firstPoints_actual :
    ∀ first ∈ firstPoints,
      (first, second, third) ∈ data.refinedH
  firstDotCenter : ℝ
  firstPoints_dot_concentrated :
    ∀ first ∈ firstPoints,
      |inner ℝ first (second - third) - firstDotCenter| ≤ delta
  endpointDirection : Point2
  endpointDirection_eq :
    endpointDirection =
      (1 / ‖second - third‖) • (second - third)
  endpointDirection_unit : ‖endpointDirection‖ = 1
  nontransverse :
    1 / Real.sqrt 2 <
      |inner ℝ endpointDirection data.direction|

/--
Starting from one concentrated actual `G₁` fiber, all closed fiber
pigeonholes either already produce genuine dot-spread data or produce the
full triple-concentrated obstruction package.
-/
def WZ1NarrowTripleConcentratedProductionStatement : Prop :=
  ∀ {delta epsilon eta : ℝ},
    ∀ {F G₁ G₂ : DiscreteSet 2},
      ∀ {H : Finset (Point2 × Point2 × Point2)},
        ∀ parameters : WZ1Proposition8_9Parameters epsilon,
          0 < delta → delta ≤ 1 →
          0 < epsilon → epsilon < 1 →
          0 < eta → eta ≤ epsilon / 20 →
          ∀ data :
            WZ1Proposition8_9CommonStripData
              delta epsilon eta parameters F G₁ G₂ H,
            data.width ≤ 1 / 4 →
            data.width ≤ Real.rpow delta (1 - epsilon / 10) →
            (1200000 : ℝ) *
                Real.rpow delta (7 * epsilon / 10) ≤ 1 →
            ∀ concentration :
              NarrowDotSpreadG1Concentrated
                delta epsilon data.width
                data.selectedF data.selectedG₁ data.selectedG₂
                data.refinedH data.direction,
              Nonempty
                  (WZ1Proposition8_9NarrowDotSpreadData
                    delta epsilon eta data.refinedH) ∨
                Nonempty
                  (WZ1NarrowTripleConcentratedData
                    parameters data concentration)

/-- Resolve only the final actual triple-concentrated, non-transverse
configuration.  This is the sole mathematical leaf left after the tracked
reduction. -/
def WZ1NarrowTripleConcentratedResolutionStatement : Prop :=
  ∀ {delta epsilon eta : ℝ},
    ∀ {F G₁ G₂ : DiscreteSet 2},
      ∀ {H : Finset (Point2 × Point2 × Point2)},
        ∀ parameters : WZ1Proposition8_9Parameters epsilon,
          0 < delta → delta ≤ 1 →
          0 < epsilon → epsilon < 1 →
          0 < eta → eta ≤ epsilon / 20 →
          ∀ data :
            WZ1Proposition8_9CommonStripData
              delta epsilon eta parameters F G₁ G₂ H,
            data.width ≤ 1 / 4 →
            data.width ≤ Real.rpow delta (1 - epsilon / 10) →
            (1200000 : ℝ) *
                Real.rpow delta (7 * epsilon / 10) ≤ 1 →
            ∀ concentration :
              NarrowDotSpreadG1Concentrated
                delta epsilon data.width
                data.selectedF data.selectedG₁ data.selectedG₂
                data.refinedH data.direction,
              WZ1NarrowTripleConcentratedData
                  parameters data concentration →
                WZ1Proposition8_9AlternativeA
                    delta epsilon
                    data.selectedF data.selectedG₁ data.selectedG₂ ∨
                  Nonempty
                    (WZ1Proposition8_9NarrowDotSpreadData
                      delta epsilon eta data.refinedH)

/-- The final obstruction resolver is sufficient for the original
synchronization interface. -/
def WZ1NarrowConcentrationReductionStatement : Prop :=
  WZ1NarrowTripleConcentratedResolutionStatement →
    WZ1Proposition8_9NarrowConcentrationSynchronizationStatement

end Kakeya.Assouad
