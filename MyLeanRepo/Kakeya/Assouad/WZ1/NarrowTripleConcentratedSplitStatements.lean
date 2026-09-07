import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowTripleConcentratedStatements

/-!
# Alignment split for the final narrow triple-concentrated obstruction

The concentrated `G₁` fiber already lies in one actual `delta`-strip.  The
remaining obstruction is split according to whether the supplied actual
`F` fiber lies in the matching origin-centered orthogonal `delta`-strip and
whether the supplied actual `G₂` fiber lies in the same affine `delta`-strip
as that `G₁` fiber.  If both align, Alternative A is a counting consequence;
only the two escape branches retain mathematical content.
-/

namespace Kakeya.Assouad

/-- The supplied actual first-coordinate fiber already has enough points in
the origin-centered orthogonal strip required by Alternative A. -/
def WZ1NarrowFirstFiberAligned
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon data.width
        data.selectedF data.selectedG₁ data.selectedG₂
        data.refinedH data.direction}
    (obstruction :
      WZ1NarrowTripleConcentratedData
        parameters data concentration) : Prop :=
  Kakeya.realRpowENN delta (epsilon - 1) ≤
    wz1DiscreteLineCount
      obstruction.firstPoints
      0 (wz1Perp2 data.direction) delta

/-- The supplied actual third-coordinate fiber already has enough points in
the same affine `delta`-strip as the concentrated `G₁` fiber. -/
def WZ1NarrowThirdFiberAligned
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    {concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon data.width
        data.selectedF data.selectedG₁ data.selectedG₂
        data.refinedH data.direction}
    (obstruction :
      WZ1NarrowTripleConcentratedData
        parameters data concentration) : Prop :=
  Kakeya.realRpowENN delta (epsilon - 1) ≤
    wz1DiscreteLineCount
      obstruction.thirdPoints
      concentration.base data.direction delta

/-- Resolve the final narrow obstruction when the supplied actual
first-coordinate fiber escapes the required origin-centered strip. -/
def WZ1NarrowFirstFiberEscapeStatement : Prop :=
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
              ∀ obstruction :
                WZ1NarrowTripleConcentratedData
                  parameters data concentration,
                ¬ WZ1NarrowFirstFiberAligned obstruction →
                  WZ1Proposition8_9AlternativeA
                      delta epsilon
                      data.selectedF data.selectedG₁ data.selectedG₂ ∨
                    Nonempty
                      (WZ1Proposition8_9NarrowDotSpreadData
                        delta epsilon eta data.refinedH)

/-- Resolve the remaining narrow obstruction when the first-coordinate
fiber aligns but the supplied actual third-coordinate fiber escapes the
concentrated `G₁` strip. -/
def WZ1NarrowThirdFiberEscapeStatement : Prop :=
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
              ∀ obstruction :
                WZ1NarrowTripleConcentratedData
                  parameters data concentration,
                WZ1NarrowFirstFiberAligned obstruction →
                ¬ WZ1NarrowThirdFiberAligned obstruction →
                  WZ1Proposition8_9AlternativeA
                      delta epsilon
                      data.selectedF data.selectedG₁ data.selectedG₂ ∨
                    Nonempty
                      (WZ1Proposition8_9NarrowDotSpreadData
                        delta epsilon eta data.refinedH)

/-- The two escape leaves imply the previous triple-concentrated resolver. -/
def WZ1NarrowTripleConcentratedSplitAssemblyStatement : Prop :=
  WZ1NarrowFirstFiberEscapeStatement →
    WZ1NarrowThirdFiberEscapeStatement →
      WZ1NarrowTripleConcentratedResolutionStatement

end Kakeya.Assouad
