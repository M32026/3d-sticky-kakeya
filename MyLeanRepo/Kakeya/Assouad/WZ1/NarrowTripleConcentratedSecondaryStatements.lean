import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowDotSpreadSpreadBranch
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowFamilyCenterPigeonhole
import MyLeanRepo.Kakeya.Assouad.WZ1.NarrowTripleConcentratedEscapeWitnesses

/-!
# Secondary-concentration leaves for the final narrow obstruction

The common spread-or-concentrate theorem is applied only to a literal escaped
edge.  Its spread branch is already closed.  These two leaves therefore start
after the complementary branch has produced a second concentrated actual
`G₁` fiber anchored at the escaped edge.
-/

namespace Kakeya.Assouad

/-- Resolve first-fiber escape after the escaped actual edge has produced an
anchored secondary `G₁` concentration and the closed reduction has produced
its full secondary triple obstruction. -/
def WZ1NarrowFirstFiberSecondaryResolutionStatement : Prop :=
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
                ∀ first : Point2,
                  first ∈ obstruction.firstPoints →
                  (first, obstruction.second, obstruction.third) ∈
                    data.refinedH →
                  first ∉
                    wz1LineNeighborhood
                      0 (wz1Perp2 data.direction) delta →
                  ∀ secondary :
                    NarrowDotSpreadG1Concentrated
                      delta epsilon data.width
                      data.selectedF data.selectedG₁ data.selectedG₂
                      data.refinedH data.direction,
                    secondary.AnchoredAt first obstruction.third →
                    ∀ secondaryObstruction :
                      WZ1NarrowTripleConcentratedData
                        parameters data secondary,
                      WZ1Proposition8_9AlternativeA
                          delta epsilon
                          data.selectedF data.selectedG₁ data.selectedG₂ ∨
                        Nonempty
                          (WZ1Proposition8_9NarrowDotSpreadData
                            delta epsilon eta data.refinedH)

/-- Resolve third-fiber escape after the escaped actual edge has produced an
anchored secondary `G₁` concentration and the closed reduction has produced
its full secondary triple obstruction. -/
def WZ1NarrowThirdFiberSecondaryResolutionStatement : Prop :=
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
                ∀ third : Point2,
                  third ∈ obstruction.thirdPoints →
                  (concentration.first, obstruction.second, third) ∈
                    data.refinedH →
                  third ∉
                    wz1LineNeighborhood
                      concentration.base data.direction delta →
                  ∀ secondary :
                    NarrowDotSpreadG1Concentrated
                      delta epsilon data.width
                      data.selectedF data.selectedG₁ data.selectedG₂
                      data.refinedH data.direction,
                    secondary.AnchoredAt concentration.first third →
                    ∀ secondaryObstruction :
                      WZ1NarrowTripleConcentratedData
                        parameters data secondary,
                      WZ1Proposition8_9AlternativeA
                          delta epsilon
                          data.selectedF data.selectedG₁ data.selectedG₂ ∨
                        Nonempty
                          (WZ1Proposition8_9NarrowDotSpreadData
                            delta epsilon eta data.refinedH)

/-- One complete secondary obstruction anchored at a supplied actual
first/third endpoint pair. -/
structure WZ1NarrowSecondaryObstructionPackage
    {delta epsilon eta : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    (data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H)
    (first third : Point2) where
  concentration :
    NarrowDotSpreadG1Concentrated
      delta epsilon data.width
      data.selectedF data.selectedG₁ data.selectedG₂
      data.refinedH data.direction
  anchored : concentration.AnchoredAt first third
  obstruction :
    WZ1NarrowTripleConcentratedData
      parameters data concentration

/-- One complete secondary obstruction for every escaped actual third
vertex of a primary obstruction. -/
structure WZ1NarrowThirdEscapeSecondaryFamily
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
    (primary :
      WZ1NarrowTripleConcentratedData
        parameters data concentration) where
  package :
    ∀ third : Point2,
      third ∈ wz1NarrowThirdEscapedPoints primary →
        WZ1NarrowSecondaryObstructionPackage
          parameters data concentration.first third

/-- A complete secondary obstruction for every escaped actual first vertex.
The family retains the full paper-scale escaped set and does not collapse it
to one arbitrary point. -/
structure WZ1NarrowFirstEscapeSecondaryFamily
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
    (primary :
      WZ1NarrowTripleConcentratedData
        parameters data concentration) where
  package :
    ∀ first : Point2,
      first ∈ wz1NarrowFirstEscapedPoints primary →
        WZ1NarrowSecondaryObstructionPackage
          parameters data first primary.third

/-- A quantitative subfamily on which every secondary first fiber escapes. -/
structure WZ1NarrowFirstEscapeSecondaryFirstEscapeData
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
    (primary :
      WZ1NarrowTripleConcentratedData
        parameters data concentration)
    (family : WZ1NarrowFirstEscapeSecondaryFamily primary) where
  points :
    Finset
      {first // first ∈ wz1NarrowFirstEscapedPoints primary}
  cardinality :
    ((wz1NarrowFirstEscapedPoints primary).card : ℝ) / 2 ≤
      (points.card : ℝ)
  first_escape :
    ∀ first ∈ points,
      ¬ WZ1NarrowFirstFiberAligned
        (family.package first.1 first.2).obstruction

/-- A quantitative subfamily on which every secondary first fiber aligns. -/
structure WZ1NarrowFirstEscapeSecondaryFirstAlignedData
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
    (primary :
      WZ1NarrowTripleConcentratedData
        parameters data concentration)
    (family : WZ1NarrowFirstEscapeSecondaryFamily primary) where
  points :
    Finset
      {first // first ∈ wz1NarrowFirstEscapedPoints primary}
  cardinality :
    ((wz1NarrowFirstEscapedPoints primary).card : ℝ) / 2 ≤
      (points.card : ℝ)
  first_aligned :
    ∀ first ∈ points,
      WZ1NarrowFirstFiberAligned
        (family.package first.1 first.2).obstruction

/-- Cardinality required from a separated family of secondary dot centers
in order to close the existing narrow dot-spread exponent bound. -/
noncomputable def wz1NarrowFirstEscapeCenterSpreadCardinality
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
    (_primary :
      WZ1NarrowTripleConcentratedData
        parameters data concentration) : ℝ :=
  Real.rpow delta
      (eta + parameters.workingLambda - 9 * epsilon / 10) /
    147456

/-- Pigeonhole threshold which guarantees that the complementary separated
secondary-center family has the cardinality above. -/
noncomputable def wz1NarrowFirstEscapeCenterConcentrationThreshold
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
    (primary :
      WZ1NarrowTripleConcentratedData
        parameters data concentration)
    (family : WZ1NarrowFirstEscapeSecondaryFamily primary)
    (escapeData :
      WZ1NarrowFirstEscapeSecondaryFirstEscapeData
        primary family) : ℝ :=
  (escapeData.points.card : ℝ) /
    (3 * wz1NarrowFirstEscapeCenterSpreadCardinality primary)

/-- The only residual output after pigeonholing the secondary dot centers
over the full escaped first-coordinate family. -/
structure WZ1NarrowFirstEscapeCenterConcentratedData
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
    (primary :
      WZ1NarrowTripleConcentratedData
        parameters data concentration)
    (family : WZ1NarrowFirstEscapeSecondaryFamily primary)
    (escapeData :
      WZ1NarrowFirstEscapeSecondaryFirstEscapeData
        primary family) where
  center : ℝ
  points :
    Finset
      {first // first ∈ wz1NarrowFirstEscapedPoints primary}
  points_subset : points ⊆ escapeData.points
  cardinality :
    wz1NarrowFirstEscapeCenterConcentrationThreshold
        primary family escapeData ≤
      (points.card : ℝ)
  concentrated :
    ∀ first ∈ points,
      |(family.package first.1 first.2).concentration.dotCenter -
          center| ≤
        3 * delta

/-- First-family comparison when every secondary obstruction still has an
escaping first fiber. -/
def WZ1NarrowFirstEscapeAllSecondaryFirstEscapeStatement : Prop :=
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
              ∀ primary :
                WZ1NarrowTripleConcentratedData
                  parameters data concentration,
                ¬ WZ1NarrowFirstFiberAligned primary →
                ∀ family :
                  WZ1NarrowFirstEscapeSecondaryFamily primary,
                  (∀ first hfirst,
                    ¬ WZ1NarrowFirstFiberAligned
                      (family.package first hfirst).obstruction) →
                    WZ1Proposition8_9AlternativeA
                        delta epsilon
                        data.selectedF data.selectedG₁ data.selectedG₂ ∨
                      Nonempty
                        (WZ1Proposition8_9NarrowDotSpreadData
                          delta epsilon eta data.refinedH)

/-- Resolve a quantitative subfamily on which the secondary first fibers
escape. -/
def WZ1NarrowFirstEscapeSecondaryFirstEscapeFamilyStatement : Prop :=
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
              ∀ primary :
                WZ1NarrowTripleConcentratedData
                  parameters data concentration,
                ¬ WZ1NarrowFirstFiberAligned primary →
                ∀ family :
                  WZ1NarrowFirstEscapeSecondaryFamily primary,
                  ∀ escapeData :
                    WZ1NarrowFirstEscapeSecondaryFirstEscapeData
                      primary family,
                    WZ1Proposition8_9AlternativeA
                        delta epsilon
                        data.selectedF data.selectedG₁ data.selectedG₂ ∨
                      Nonempty
                        (WZ1Proposition8_9NarrowDotSpreadData
                          delta epsilon eta data.refinedH)

/-- Resolve only the secondary-center concentrated remainder of the first
escape family.  The complementary center-spread branch is closed. -/
def WZ1NarrowFirstEscapeCenterConcentratedResolutionStatement : Prop :=
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
              ∀ primary :
                WZ1NarrowTripleConcentratedData
                  parameters data concentration,
                ¬ WZ1NarrowFirstFiberAligned primary →
                ∀ family :
                  WZ1NarrowFirstEscapeSecondaryFamily primary,
                  ∀ escapeData :
                    WZ1NarrowFirstEscapeSecondaryFirstEscapeData
                      primary family,
                  ∀ centerData :
                    WZ1NarrowFirstEscapeCenterConcentratedData
                      primary family escapeData,
                    WZ1Proposition8_9AlternativeA
                        delta epsilon
                        data.selectedF data.selectedG₁ data.selectedG₂ ∨
                      Nonempty
                        (WZ1Proposition8_9NarrowDotSpreadData
                          delta epsilon eta data.refinedH)

/-- Resolve the remainder after both the secondary `G₁` dot centers and the
secondary-obstruction first-fiber dot centers concentrate. -/
def WZ1NarrowFirstEscapeTwoCenterConcentratedResolutionStatement : Prop :=
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
              ∀ primary :
                WZ1NarrowTripleConcentratedData
                  parameters data concentration,
                ¬ WZ1NarrowFirstFiberAligned primary →
                ∀ family :
                  WZ1NarrowFirstEscapeSecondaryFamily primary,
                  ∀ escapeData :
                    WZ1NarrowFirstEscapeSecondaryFirstEscapeData
                      primary family,
                  ∀ centerData :
                    WZ1NarrowFirstEscapeCenterConcentratedData
                      primary family escapeData,
                  ∀ firstCenterData :
                    WZ1NarrowFamilyCenterConcentratedData
                      centerData.points
                      (fun first =>
                        (family.package first.1 first.2).obstruction.firstDotCenter)
                      delta epsilon eta parameters.workingLambda,
                    WZ1Proposition8_9AlternativeA
                        delta epsilon
                        data.selectedF data.selectedG₁ data.selectedG₂ ∨
                      Nonempty
                        (WZ1Proposition8_9NarrowDotSpreadData
                          delta epsilon eta data.refinedH)

/-- First-family comparison after one secondary first fiber aligns but its
third fiber still escapes. -/
def WZ1NarrowFirstEscapeAlignedSecondaryThirdEscapeStatement : Prop :=
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
              ∀ primary :
                WZ1NarrowTripleConcentratedData
                  parameters data concentration,
                ¬ WZ1NarrowFirstFiberAligned primary →
                ∀ family :
                  WZ1NarrowFirstEscapeSecondaryFamily primary,
                  ∀ first hfirst,
                    WZ1NarrowFirstFiberAligned
                        (family.package first hfirst).obstruction →
                      ¬ WZ1NarrowThirdFiberAligned
                        (family.package first hfirst).obstruction →
                        WZ1Proposition8_9AlternativeA
                            delta epsilon
                            data.selectedF data.selectedG₁
                            data.selectedG₂ ∨
                          Nonempty
                            (WZ1Proposition8_9NarrowDotSpreadData
                              delta epsilon eta data.refinedH)

/-- Resolve the quantitative branch in which at least half of the escaped
first vertices have an aligned secondary first fiber but an escaping
secondary third fiber. -/
def WZ1NarrowFirstEscapeAlignedFamilyThirdEscapeStatement : Prop :=
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
              ∀ primary :
                WZ1NarrowTripleConcentratedData
                  parameters data concentration,
                ¬ WZ1NarrowFirstFiberAligned primary →
                ∀ family :
                  WZ1NarrowFirstEscapeSecondaryFamily primary,
                  ∀ alignedData :
                    WZ1NarrowFirstEscapeSecondaryFirstAlignedData
                      primary family,
                    (∀ first ∈ alignedData.points,
                      ¬ WZ1NarrowThirdFiberAligned
                        (family.package first.1 first.2).obstruction) →
                      WZ1Proposition8_9AlternativeA
                          delta epsilon
                          data.selectedF data.selectedG₁ data.selectedG₂ ∨
                        Nonempty
                          (WZ1Proposition8_9NarrowDotSpreadData
                            delta epsilon eta data.refinedH)

/-- Resolve the remainder after the secondary third-fiber dot centers
concentrate over the large secondary-first-aligned family. -/
def WZ1NarrowFirstEscapeAlignedFamilyThirdCenterConcentratedStatement : Prop :=
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
              ∀ primary :
                WZ1NarrowTripleConcentratedData
                  parameters data concentration,
                ¬ WZ1NarrowFirstFiberAligned primary →
                ∀ family :
                  WZ1NarrowFirstEscapeSecondaryFamily primary,
                  ∀ alignedData :
                    WZ1NarrowFirstEscapeSecondaryFirstAlignedData
                      primary family,
                    (∀ first ∈ alignedData.points,
                      ¬ WZ1NarrowThirdFiberAligned
                        (family.package first.1 first.2).obstruction) →
                  ∀ centerData :
                    WZ1NarrowFamilyCenterConcentratedData
                      alignedData.points
                      (fun first =>
                        (family.package first.1 first.2).obstruction.thirdDotCenter)
                      delta epsilon eta parameters.workingLambda,
                    WZ1Proposition8_9AlternativeA
                        delta epsilon
                        data.selectedF data.selectedG₁ data.selectedG₂ ∨
                      Nonempty
                        (WZ1Proposition8_9NarrowDotSpreadData
                          delta epsilon eta data.refinedH)

/-- Third-escape comparison when the complete secondary obstruction has an
escaping first fiber. -/
def WZ1NarrowThirdEscapeSecondaryFirstEscapeStatement : Prop :=
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
              ∀ primary :
                WZ1NarrowTripleConcentratedData
                  parameters data concentration,
                WZ1NarrowFirstFiberAligned primary →
                ∀ third : Point2,
                  third ∈ primary.thirdPoints →
                  third ∉
                    wz1LineNeighborhood
                      concentration.base data.direction delta →
                  ∀ package :
                    WZ1NarrowSecondaryObstructionPackage
                      parameters data concentration.first third,
                    ¬ WZ1NarrowFirstFiberAligned package.obstruction →
                      WZ1Proposition8_9AlternativeA
                          delta epsilon
                          data.selectedF data.selectedG₁ data.selectedG₂ ∨
                        Nonempty
                          (WZ1Proposition8_9NarrowDotSpreadData
                            delta epsilon eta data.refinedH)

/-- Third-escape comparison when the secondary first fiber aligns but its
secondary third fiber still escapes. -/
def WZ1NarrowThirdEscapeSecondaryThirdEscapeStatement : Prop :=
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
              ∀ primary :
                WZ1NarrowTripleConcentratedData
                  parameters data concentration,
                WZ1NarrowFirstFiberAligned primary →
                ∀ third : Point2,
                  third ∈ primary.thirdPoints →
                  third ∉
                    wz1LineNeighborhood
                      concentration.base data.direction delta →
                  ∀ package :
                    WZ1NarrowSecondaryObstructionPackage
                      parameters data concentration.first third,
                    WZ1NarrowFirstFiberAligned package.obstruction →
                    ¬ WZ1NarrowThirdFiberAligned package.obstruction →
                      WZ1Proposition8_9AlternativeA
                          delta epsilon
                          data.selectedF data.selectedG₁ data.selectedG₂ ∨
                        Nonempty
                          (WZ1Proposition8_9NarrowDotSpreadData
                            delta epsilon eta data.refinedH)

/-- Resolve the full threshold-sized primary escaped-third family after
every secondary first fiber aligns and every secondary third fiber escapes. -/
def WZ1NarrowThirdEscapeAlignedFamilyThirdEscapeStatement : Prop :=
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
              ∀ primary :
                WZ1NarrowTripleConcentratedData
                  parameters data concentration,
                WZ1NarrowFirstFiberAligned primary →
                ¬ WZ1NarrowThirdFiberAligned primary →
                ∀ family :
                  WZ1NarrowThirdEscapeSecondaryFamily primary,
                  (∀ third hthird,
                    WZ1NarrowFirstFiberAligned
                      (family.package third hthird).obstruction) →
                  (∀ third hthird,
                    ¬ WZ1NarrowThirdFiberAligned
                      (family.package third hthird).obstruction) →
                    WZ1Proposition8_9AlternativeA
                        delta epsilon
                        data.selectedF data.selectedG₁ data.selectedG₂ ∨
                      Nonempty
                        (WZ1Proposition8_9NarrowDotSpreadData
                          delta epsilon eta data.refinedH)

/-- Resolve the remainder after the secondary third-fiber dot centers
concentrate over the full primary escaped-third family. -/
def WZ1NarrowThirdEscapeAlignedFamilyThirdCenterConcentratedStatement : Prop :=
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
              ∀ primary :
                WZ1NarrowTripleConcentratedData
                  parameters data concentration,
                WZ1NarrowFirstFiberAligned primary →
                ¬ WZ1NarrowThirdFiberAligned primary →
                ∀ family :
                  WZ1NarrowThirdEscapeSecondaryFamily primary,
                  (∀ third hthird,
                    WZ1NarrowFirstFiberAligned
                      (family.package third hthird).obstruction) →
                  (∀ third hthird,
                    ¬ WZ1NarrowThirdFiberAligned
                      (family.package third hthird).obstruction) →
                  let source :=
                    (wz1NarrowThirdEscapedPoints primary).attach
                  ∀ centerData :
                    WZ1NarrowFamilyCenterConcentratedData
                      source
                      (fun third =>
                        (family.package third.1 third.2).obstruction.thirdDotCenter)
                      delta epsilon eta parameters.workingLambda,
                    WZ1Proposition8_9AlternativeA
                        delta epsilon
                        data.selectedF data.selectedG₁ data.selectedG₂ ∨
                      Nonempty
                        (WZ1Proposition8_9NarrowDotSpreadData
                          delta epsilon eta data.refinedH)

end Kakeya.Assouad
