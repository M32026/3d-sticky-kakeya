import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49RadialCirclePacking

/-!
# Radial-projection output for WZ1 Lemma 49

The residual Kaufman branch applies radial projection to a coarsened
Frostman set lying in one strip and on one side of the viewpoint.  This file
freezes the reusable output without exposing implementation-specific helper
maps.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Radial normalization around a planar viewpoint. -/
def wz1Lemma49RadialDirection
    (viewpoint point : Point2) : Point2 :=
  (‖point - viewpoint‖⁻¹ : ℝ) • (point - viewpoint)

/--
The finite unit-direction set produced from a coarsened Frostman set by
radial projection.
-/
structure WZ1Lemma49RadialProjectionData
    (source : DiscreteSet 2)
    (viewpoint : Point2)
    (delta constant : ℝ) where
  directions : DiscreteSet 2
  directions_nonempty : directions.Nonempty
  unit :
    ∀ direction ∈ directions, ‖direction‖ = 1
  separated :
    directions.IsDeltaSeparated delta
  frostman :
    directions.IsFrostman delta 1
      (ENNReal.ofReal constant)
  source_image :
    directions =
      source.image
        (wz1Lemma49RadialDirection viewpoint)

/--
Geometry of the radial image before proving its Frostman bound.
-/
structure WZ1Lemma49RadialImageGeometry
    (source : DiscreteSet 2)
    (viewpoint : Point2)
    (delta : ℝ) where
  directions : DiscreteSet 2 :=
    source.image
      (wz1Lemma49RadialDirection viewpoint)
  directions_eq :
    directions =
      source.image
        (wz1Lemma49RadialDirection viewpoint)
  directions_nonempty : directions.Nonempty
  source_injective :
    Set.InjOn
      (wz1Lemma49RadialDirection viewpoint)
      (source : Set Point2)
  card_eq : directions.card = source.card
  unit :
    ∀ direction ∈ directions, ‖direction‖ = 1
  separated :
    directions.IsDeltaSeparated delta

/--
Paper-scale radial projection of a coarsened Frostman set in a strip.

The strip uses the centered convention `|perpendicular coordinate| ≤ W/2`.
The source is required to lie on the positive side of the viewpoint by at
least `D/2`.  The explicit scale window is exactly the one used by the
historical Lemma 49 argument.
-/
def WZ1Lemma49RadialProjectionConclusion : Prop :=
  ∀ {source : DiscreteSet 2}
    {delta rho C D W : ℝ}
    {base direction viewpoint : Point2},
    0 < delta →
    0 < rho →
    0 ≤ C →
    ‖direction‖ = 1 →
    0 < W →
    0 < D →
    source.IsDeltaSeparated rho →
    source.IsFrostman rho 1 (ENNReal.ofReal C) →
    (∀ point ∈ source,
      |inner ℝ (point - base) (wz1Perp2 direction)| ≤ W / 2) →
    source.IsInUnitBall →
    source.Nonempty →
    ‖viewpoint‖ ≤ 1 →
    (∀ point ∈ source,
      D / 2 ≤
        inner ℝ (point - viewpoint) (wz1Perp2 direction)) →
    W ≤ 120 * D * delta →
    (2050 * D + 604 + 16 / D) * delta ≤ rho →
    rho ≤ 1 →
    rho ≤ 3000 * (D + 1 / D) * delta →
      Nonempty
        (WZ1Lemma49RadialProjectionData
          source viewpoint delta
          (C * 10000 * (D + 1 / D)))

/--
Radial projection with the source-scale gap stated in its direct geometric
form.

At angular scale `delta`, the cone estimate bounds the diameter of one radial
fiber by

`4 * delta + 16 * delta / D + W + 4 * W / D`.

The paper chooses the source coarsening scale strictly above this quantity.
-/
def WZ1Lemma49RadialProjectionDirectConclusion : Prop :=
  ∀ {source : DiscreteSet 2}
    {delta rho C D W : ℝ}
    {base direction viewpoint : Point2},
    0 < delta →
    0 < rho →
    0 ≤ C →
    ‖direction‖ = 1 →
    0 < W →
    0 < D →
    source.IsDeltaSeparated rho →
    source.IsFrostman rho 1 (ENNReal.ofReal C) →
    (∀ point ∈ source,
      |inner ℝ (point - base) (wz1Perp2 direction)| ≤ W / 2) →
    source.IsInUnitBall →
    source.Nonempty →
    ‖viewpoint‖ ≤ 1 →
    (∀ point ∈ source,
      D / 2 ≤
        inner ℝ (point - viewpoint) (wz1Perp2 direction)) →
    4 * delta + 16 * delta / D + W + 4 * W / D < rho →
    rho ≤ 1 →
    rho ≤ 3000 * (D + 1 / D) * delta →
      Nonempty
        (WZ1Lemma49RadialProjectionData
          source viewpoint delta
          (C * 10000 * (D + 1 / D)))

end

end Kakeya.Assouad
