import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9NarrowSplitStatements

/-!
# Concentration boundary for the narrow dot-spread proof

The closed spread provider fixes one actual `(first, third)` fiber of the
refined tripartite graph.  If its dot values do not spread, it retains a
paper-scale subset of the second-coordinate fiber in one transverse
`delta`-strip.  The remaining mathematical leaf must synchronize the other
two vertex classes with that same affine line, or use the offset regime to
produce genuine separated dot values.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- A lightweight certificate for the pre-cell-pigeonhole actual fiber.
It deliberately depends only on scalar functions and finite sets, not on the
full Proposition 8.9 data package. -/
structure WZ1NarrowRawFiberMargin
    (delta epsilon width : ℝ)
    (ambient selected : DiscreteSet 2)
    (direction : Point2)
    (longitudinalCenter : ℝ)
    (actual : Point2 → Prop)
    (dotValue : Point2 → ℝ)
    (dotCenter : ℝ) where
  points : DiscreteSet 2
  selected_subset : selected ⊆ points
  subset : points ⊆ ambient
  card_lower :
    16 * Real.rpow delta (epsilon - 1) ≤
      (points.card : ℝ)
  transverseAnchor : Point2
  transverse :
    ∀ point ∈ points,
      |inner ℝ (point - transverseAnchor)
          (wz1Perp2 direction)| ≤
        35 * delta / 6
  longitudinal :
    ∀ point ∈ points,
      |inner ℝ point direction - longitudinalCenter| ≤
        delta / (4 * width)
  actual_mem : ∀ point ∈ points, actual point
  dot_concentrated :
    ∀ point ∈ points,
      |dotValue point - dotCenter| ≤ delta

/--
A concentrated subset of one actual second-coordinate graph fiber.

The fields `first`, `third`, and `actual_edges` preserve the graph provenance
needed by the remaining synchronization argument.  Merely recording an
unrelated subset of `G₁` in a strip would be too weak for that argument.
The producer retains twice the final line-count threshold so one later
half-family split does not destroy the paper-scale abundance.
-/
structure NarrowDotSpreadG1Concentrated
    (delta epsilon width : ℝ)
    (F G₁ G₂ : DiscreteSet 2)
    (H : Finset (Point2 × Point2 × Point2))
    (direction : Point2) where
  points : DiscreteSet 2
  subset : points ⊆ G₁
  card_lower :
    2 * Kakeya.realRpowENN delta (epsilon - 1) ≤
      (points.card : ENNReal)
  base : Point2
  strip :
    ∀ second ∈ points,
      second ∈ wz1LineNeighborhood base direction delta
  longitudinalCenter : ℝ
  longitudinal :
    ∀ second ∈ points,
      |inner ℝ second direction - longitudinalCenter| ≤
        delta / (4 * width)
  first : Point2
  third : Point2
  first_mem : first ∈ F
  third_mem : third ∈ G₂
  actual_edges :
    ∀ second ∈ points, (first, second, third) ∈ H
  dotCenter : ℝ
  dot_concentrated :
    ∀ second ∈ points,
      |inner ℝ first (second - third) - dotCenter| ≤ delta
  rawMargin :
    WZ1NarrowRawFiberMargin
      delta epsilon width G₁ points direction longitudinalCenter
      (fun second => (first, second, third) ∈ H)
      (fun second => inner ℝ first (second - third))
      dotCenter

/-- A concentrated second-coordinate fiber retaining the exact first and
third endpoints of the actual edge from which it was constructed. -/
def NarrowDotSpreadG1Concentrated.AnchoredAt
    {delta epsilon width : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {direction : Point2}
    (concentration :
      NarrowDotSpreadG1Concentrated
        delta epsilon width F G₁ G₂ H direction)
    (first third : Point2) : Prop :=
  concentration.first = first ∧ concentration.third = third

/--
The sole remaining finite-geometric leaf in the narrow common-strip branch.

Starting from the actual concentrated `G₁` fiber produced by the closed
spread-or-concentration theorem, either synchronize heavy `delta`-strips for
`F`, `G₁`, and `G₂` as in paper Alternative A, or prove that the offset
regime itself yields the required separated dot values.
-/
def WZ1Proposition8_9NarrowConcentrationSynchronizationStatement : Prop :=
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
              WZ1Proposition8_9AlternativeA
                  delta epsilon
                  data.selectedF data.selectedG₁ data.selectedG₂ ∨
                Nonempty
                  (WZ1Proposition8_9NarrowDotSpreadData
                    delta epsilon eta data.refinedH)

/--
Closed assembly boundary: the synchronization leaf plus the recovered
spread-or-concentration provider imply the original narrow dot-spread
statement.
-/
def WZ1Proposition8_9NarrowFromConcentrationStatement : Prop :=
  WZ1Proposition8_9NarrowConcentrationSynchronizationStatement →
    WZ1Proposition8_9NarrowDotSpreadStatement

end Kakeya.Assouad
